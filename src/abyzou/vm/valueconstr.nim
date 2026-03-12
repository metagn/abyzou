import
  std/[sets, tables],
  ../util/box,
  ../language/expressions,
  ./[primitives, arrays, typebasics]

template withkind(k, val): Value =
  Value(kind: `v k`, `k Value`: val)
template withkindboxv(v, kv, val): untyped =
  Value(kind: `v`, `kv`: BoxedValue[typeof(val)](value: val))
template withkindbox(k, val): untyped =
  withkindboxv(`v k`, `k Value`, val)

proc toValue*(x: int32): Value {.inline.} = withkind(int32, x)
proc toValue*(x: uint32): Value {.inline.} = withkind(uint32, x)
proc toValue*(x: float32): Value {.inline.} = withkind(float32, x)
proc toValue*(x: bool): Value = withkind(bool, x)
proc toValue*(x: int64): Value = withkindbox(int64, x)
proc toValue*(x: uint64): Value = withkindbox(uint64, x)
proc toValue*(x: float64): Value =
  toValue(x.float32)
  #withkindbox(float64, x)
proc toValue*(x: int): Value =
  if x <= high(int32) and x >= low(int32):
    toValue(int32(x))
  else:
    toValue(int64(x))
proc toValue*(x: uint): Value =
  if x <= high(uint32):
    toValue(uint32(x))
  else:
    toValue(uint64(x))
proc toValue*(x: sink seq[Value]): Value = withkindbox(list, x)
proc toValue*(x: sink string): Value = withkindbox(string, x)
proc toValue*(x: sink Array[Value]): Value {.inline.} =
  template arr(a: untyped): untyped =
    when result.tupleValue is RefArray:
      toRefArray(a)
    else:
      toArray(a)
  withkind(array, arr x.toOpenArray(0, x.len - 1))
proc toValue*(x: Type): Value = Value(kind: vType, typeValue: BoxedValue[Type](type: TypeTy[x]))
proc toValue*(x: Box[Type]): Value = Value(kind: vType, typeValue: BoxedValue[Type](type: TypeTy[x.unbox]))
proc toValue*(x: sink HashSet[Value]): Value = withkindbox(set, x)
proc toValue*(x: sink Table[Value, Value]): Value = withkindbox(table, x)
proc toValue*(x: proc (args: openarray[Value]): Value {.nimcall.}): Value = withkind(nativeFunction, x)
proc toValue*(x: TreeWalkProgram): Value = withkindbox(function, x)
proc toValue*(x: LinearProgram): Value = withkindbox(linearFunction, x)
proc toValue*(x: Expression): Value = withkind(expression, x)
proc toValue*(x: Statement): Value = withkind(statement, x)
proc toValue*(x: Context): Value = withkindbox(context, x)
proc toValue*(x: Module): Value = withkind(module, x)

proc unboxStripType*(x: Value): Value {.inline.} =
  if x.kind == vBoxed: result = x.boxedValue.value
  else: result = x

proc setTypeIfBoxed*(x: Value, t: Type) {.inline.} =
  case x.kind
  of unboxedValueKinds: discard
  of vBoxed: x.boxedValue.type = t
  of vList: x.listValue.type = t
  of vString: x.stringValue.type = t
  of vInt64: x.int64Value.type = t
  of vUint64: x.uint64Value.type = t
  of vFloat64: x.float64Value.type = t
  of vType: x.typeValue.type = t
  of vSet: x.setValue.type = t
  of vTable: x.tableValue.type = t
  of vFunction: x.functionValue.type = t
  of vLinearFunction: x.linearFunctionValue.type = t
  of vContext: x.contextValue.type = t

proc getTypeIfBoxed*(x: Value): Type {.inline.} =
  case x.kind
  of unboxedValueKinds: discard
  of vBoxed: result = x.boxedValue.type
  of vList: result = x.listValue.type
  of vString: result = x.stringValue.type
  of vInt64: result = x.int64Value.type
  of vUint64: result = x.uint64Value.type
  of vFloat64: result = x.float64Value.type
  of vType: result = x.typeValue.type
  of vSet: result = x.setValue.type
  of vTable: result = x.tableValue.type
  of vFunction: result = x.functionValue.type
  of vLinearFunction: result = x.linearFunctionValue.type
  of vContext: result = x.contextValue.type

proc makeTyped*(x: var Value, t: Type) =
  if x.kind in unboxedValueKinds:
    let y = Value(kind: vBoxed, boxedValue: BoxedValue[Value](type: t, value: x))
    x = y
  else:
    setTypeIfBoxed(x, t)

when false:
  # XXX [serialization] this is probably important
  proc copy*(value: Value): Value =
    case value.kind
    of vNone, vInt64, vBool, vUint64, vFloat64,
      vInt32, vFloat32, vUint32,
      vType, vFunction, vNativeFunction: value
    of vList:
      var newSeq = newSeq[Value](value.listValue.unref.len)
      for i in 0 ..< newSeq.len:
        newSeq[i] = copy value.listValue.unref[i]
      toValue(newSeq)
    of vString: toValue(value.stringValue.unref)
    of vArray:
      var newArray = initArray[Value](value.tupleValue.unref.len)
      for i in 0 ..< newArray.len:
        newArray[i] = copy value.tupleValue.unref[i]
      toValue(newArray)
    of vEffect, vReference, vBoxed,
      vSet, vTable, vExpression, vStatement, vContext:
      # unimplemented
      value

  import ./pointertag

  proc fromValueObj*(v: ValueObj): PointerTaggedValue =
    when pointerTaggable:
      template fromPtr(name): untyped =
        cast[pointer](v.`name Value`).tagPointer(v.kind.uint16)
      result = PointerTaggedValue:
        case v.kind
        of vNone: 0'u64
        of vInteger, vBoolean: (v.kind.uint64 shl 48) or int32(v.integerValue).uint64
        of vUnsigned: (v.kind.uint64 shl 48) or int32(v.unsignedValue).uint64
        of vFloat: (v.kind.uint64 shl 48) or int32(v.floatValue).uint64
        of vList: fromPtr list
        of vString: fromPtr string
        of vArray: cast[pointer](v.tupleValue).tagPointer(v.kind.uint16)
        of vReference: fromPtr reference
        of vType: fromPtr type
        of vNativeFunction: fromPtr nativeFunction
        of vFunction: fromPtr function
        of vEffect: fromPtr effect
        of vSet: fromPtr set
        of vTable: fromPtr table
        of vExpression: fromPtr expression
        of vStatement: fromPtr statement
        of vContext: fromPtr context
    else:
      v.PointerTaggedValue

  proc toValueObj*(p: PointerTaggedValue): ValueObj =
    when pointerTaggable:
      let val = p.uint64
      result.kind = ValueKind(val shr 48)
      template castPointer(name) =
        result.`name Value` = cast[typeof(result.`name Value`)](untagPointer(val))
      case result.kind
      of vNone: discard
      of vInteger, vBoolean: result.integerValue = (val and high(uint32).uint64).int32.int
      of vUnsigned: result.unsignedValue = (val and high(uint32).uint64).uint
      of vFloat: result.floatValue = (val and high(uint32).uint64).float32.float
      of vList: castPointer list
      of vString: castPointer string
      of vArray: result.tupleValue = cast[typeof(result.tupleValue)](untagPointer(val))
      of vReference: castPointer reference
      of vType: castPointer type
      of vNativeFunction: castPointer nativeFunction
      of vFunction: castPointer function
      of vEffect: castPointer effect
      of vSet: castPointer set
      of vTable: castPointer table
      of vExpression: castPointer expression
      of vStatement: castPointer statement
      of vContext: castPointer context
    else:
      p.ValueObj
