import
  std/[tables, sets],
  ../repr/[primitives, typebasics, arrays, valueconstr],
  ./typematch

proc checkType*(value: Value, t: Type): bool =
  template eachAre(iter; types: seq[Type]): untyped =
    let ts = types; var yes = true; var i = 0
    for it in iter:
      if (i >= ts.len) or (not checkType(it, ts[i])):
        yes = false; break
      inc i
    yes and i == types.len
  template eachAre(iter; typ: Type): untyped =
    let ty = typ; var yes = true
    for it in iter:
      if not checkType(it, ty):
        yes = false; break
    yes
  template eachAreTable(iter; kty, vty: Type): untyped =
    let kt = kty; let vt = vty; var yes = true
    for key, value in iter:
      if not checkType(key, kt) or not checkType(value, vt):
        yes = false; break
    yes
  let tValue = getTypeIfBoxed(value)
  if not isNoType(tValue):
    return match(t, tValue).matches
  var isBase = false
  var tnt = t.kind
  # XXX native type normalization here:
  var nativeArgs {.cursor.}: seq[Type]
  case t.kind
  of tyInstance:
    if t.instanceBase.nativeType != tyNoType:
      tnt = t.instanceBase.nativeType
      nativeArgs = t.instanceArgs
  of tyBase:
    isBase = true
    if t.typeBase.nativeType != tyNoType:
      tnt = t.typeBase.nativeType
  of tyNativeBase:
    isBase = true
    tnt = t.nativeBase
  of argNativeTypes:
    nativeArgs = t.nativeArgs
  of tyTuple:
    nativeArgs = t.elements
  else: discard
  result = case tnt
  of tyInstance, tyBase:
    let b = if t.kind == tyInstance: t.instanceBase else: t.typeBase
    not b.valueMatcher.isNil and
      b.valueMatcher(value, t)
  of tyNativeBase: false # should be unreachable
  of tyTuple, tyTupleConstructor:
    value.kind == vArray and (isBase or value.tupleValue.eachAre(nativeArgs))
  of tyNoneValue: value.kind == vNone
  of tyInt32: value.kind == vInt32
  of tyUint32: value.kind == vUint32
  of tyFloat32: value.kind == vFloat32
  of tyBool: value.kind == vBool
  of tyInt64: value.kind == vInt64
  of tyUint64: value.kind == vUint64
  of tyFloat64: value.kind == vFloat64
  of tyFunction:
    (value.kind == vFunction and match(value.functionValue.type, t).matches) or
      (value.kind == vLinearFunction and match(value.linearFunctionValue.type, t).matches) or
      # XXX [type-arming, functions, needs-testing] just expect this boxed i guess
      (value.kind == vNativeFunction and true #[match(value.nativeFunctionValue.type, t).matches]#)
  of tyReference:
    value.kind == vReference and (isBase or value.referenceValue.unref.checkType(nativeArgs[0]))
  of tyList:
    value.kind == vList and (isBase or value.listValue.value.unref.eachAre(nativeArgs[0]))
  of tyString: value.kind == vString
  of tySet:
    value.kind == vSet and (isBase or value.setValue.value.eachAre(nativeArgs[0]))
  of tyTable:
    value.kind == vTable and (isBase or value.tableValue.value.eachAreTable(nativeArgs[0], nativeArgs[1]))
  of tyType:
    value.kind == vType and (isBase or match(nativeArgs[0], value.typeValue.type).matches)
  of tyExpression: value.kind == vExpression
  of tyStatement: value.kind == vStatement
  of tyContext: value.kind == vContext
  of tyModule: value.kind == vModule
  of tyMemory: value.kind == vMemory
  of tyAny: true
  of tyAll, tyNoType: false
  of tyUnion:
    var res = false
    for ty in t.operands:
      if value.checkType(ty):
        res = true
        break
    res
  of tyIntersection:
    var res = true
    for ty in t.operands:
      if not value.checkType(ty):
        res = false
        break
    res
  of tyNot: not value.checkType(t.notType.unbox)
  of tySomeValue: false
  of tyParameter: value.checkType(t.parameter.bound.boundType)
  of tyValue: value.checkType(t.valueType.unbox) and t.value == value
  if result:
    for p, args in t.properties:
      if not p.valueMatcher.isNil:
        result = result and p.valueMatcher(value, args)
        if not result: return result
