import
  std/[hashes, tables, sets],
  skinsuit/equals,
  ./[primitives, arrays, ids]

template mix(x) =
  mixin hash
  result = result !& hash(x)

template idObject[T: ref](t: type T) {.dirty.} =
  proc hash*(p: t): Hash {.noSideEffect.} =
    if not p.isNil:
      mix p.id
    else:
      mix pointer(nil)
    result = !$ result

  proc `==`*(a, b: t): bool = a.isNil and b.isNil or (not a.isNil and not b.isNil and a.id == b.id)

idObject(TypeBase)
idObject(TypeParameter)
idObject(Variable)
idObject(Module)

proc hash*(v: BoxedValueObj): Hash {.noSideEffect.}
proc hash*(v: Value): Hash {.noSideEffect.}
proc hash*(v: Type): Hash {.noSideEffect.}

template hashRefObj(T): untyped {.dirty.} =
  proc hash*(v: T): Hash {.noSideEffect.} =
    if v.isNil:
      mix 0
    else:
      mix v[]
    result = !$ result

hashRefObj BoxedValue
hashRefObj(ref Value)
hashRefObj(ref Type)
hashRefObj Stack

template hashObj(T): untyped {.dirty.} =
  proc hash*(v: T): Hash {.noSideEffect.} =
    for f in fields(v):
      when f is ref:
        when compiles(hash(f[])):
          if not f.isNil:
            mix f[]
          else:
            mix cast[int](cast[pointer](f))
        else:
          mix cast[int](cast[pointer](f))
      else:
        mix f
    result = !$ result

hashObj BoxedValueObj
hashObj Value
hashObj Type

proc `==`*[T](a, b: BoxedValueObj[T]): bool {.noSideEffect.}
proc `==`*(a, b: Value): bool {.noSideEffect.}
proc `==`*(a, b: Type): bool {.noSideEffect.}
proc `==`*(a, b: StatementObj): bool {.noSideEffect.}

equals *(ref Value)
proc `==`*[T](a, b: BoxedValue[T]): bool {.noSideEffect.} =
  system.`==`(a, b) or (not a.isNil and not b.isNil and a[] == b[])
equals *(ref Type)
equals *(ref StatementObj)

equals *Value
proc `==`*[T](a, b: BoxedValueObj[T]): bool {.noSideEffect.} =
  a.type == b.type and (when compiles(a.value): a.value == b.value else: true)
equals *Type
equals *TypeMatch
equals *StatementObj

import strutils

proc `$`*(t: TypeParameter): string {.inline.} = t.name

proc `$`*(t: Type): string

proc `$`*(vt: Box[Type]): string =
  if vt.isNil:
    "None"
  else: $vt.unbox

proc `$`*(value: Value): string

proc `$`*[T](value: BoxedValueObj[T]): string =
  result = "Boxed(" & (when T isnot Type: $value.value else: "") & ")"

proc `$`*(value: BoxedValue): string =
  if value.isNil: "<nil>"
  else: $value[]

proc `$`*(module: Module): string

proc `$`*(value: Value): string =
  case value.kind
  of vNone: "()"
  of vInt32: $value.int32Value
  of vUint32: $value.uint32Value
  of vFloat32: $value.float32Value
  of vBool: $value.boolValue
  of vReference: "ref[" & $cast[int](value.referenceValue) & "](" & $value.referenceValue.unref & ")"
  of vArray:
    var s = ($value.tupleValue)[1..^1]
    s[0] = '('
    s[^1] = ')'
    s
  of vEffect: "Effect(" & $value.effectValue.unref & ")"
  of vBoxed: $value.boxedValue.value
  of vInt64: $value.int64Value.value
  of vUint64: $value.uint64Value.value
  of vFloat64: $value.float64Value.value
  of vList: ($value.listValue.value.unref)[1..^1]
  of vString: value.stringValue.value.unref
  of vType: $value.typeValue.type
  of vFunction: "<function>"
  of vLinearFunction: "<linear function>"
  of vNativeFunction: "<native function>"
  of vSet: $value.setValue.value
  of vTable: $value.tableValue.value
  of vExpression: $value.expressionValue[]
  of vStatement: $value.statementValue[]
  of vContext: $value.contextValue.value
  of vModule: $value.moduleValue

proc `$`*(p: TypeBase): string {.inline.} = p.name

proc `$`*(tb: TypeBound): string

proc `$`*(t: Type): string =
  proc `$`(s: seq[Type]): string =
    for t in s:
      if result.len != 0:
        result.add(", ")
      result.add($t)
  result = case t.kind
  of tyNoType: "<none>"
  of tyInstance: t.instanceBase.name & "(" & $t.instanceArgs & ")"
  of tyAny: "Any"
  of tyAll: "All"
  of tyTuple: "Tuple(" & $t.elements & (if t.varargs.isNoType: ")" else: ", " & $t.varargs & "...)")
  of tyUnion: "Union(" & $t.operands & ")"
  of tyIntersection: "Intersection(" & $t.operands & ")"
  of tyNot: "Not " & $t.notType
  of tyBase: "Base(" & $t.typeBase & ")"
  of tyNativeBase: "Base(" & $t.nativeBase & ")"
  of tySomeValue: "SomeValue(" & $t.someValueType & ")"
  of tyParameter: "Parameter(" & $t.parameter.name & ")"
  of tyValue: "Value(" & $t.value & ": " & $t.valueType & ")"
  of noArgNativeTypes: $t.kind
  of argNativeTypes: $t.kind & "(" & $t.nativeArgs & ")"
  if t.properties.len != 0:
    result.add(" {") 
    var afterFirst = false
    for tag, arg in t.properties:
      if afterFirst: result.add(", ")
      else: afterFirst = true
      result.add($arg)
    result.add('}')

proc `$`*(tb: TypeBound): string =
  (case tb.variance
  of Covariant: '+'
  of Contravariant: '-'
  of Invariant: '~'
  of Ultravariant: '*') & $tb.boundType

proc `$`*(variable: Variable): string =
  variable.name & ": " & $variable.knownType

proc `$`*(scope: Scope): string

proc `$`*(module: Module): string =
  result = "module"
  if module.name.len != 0:
    result.add ' '
    result.add module.name
  result.add '\n'
  for v in module.stackSlots:
    let prefix =
      case v.kind
      of Capture:
        "  capture "
      of Constant: # not used
        "  constant "
      of Argument:
        "  argument "
      of Local:
        "  "
    result.add(prefix & $v.variable & "\n")
  result.add("parent\n")
  for line in splitLines($module.origin):
    result.add("  " & line & "\n")

proc `$`*(scope: Scope): string =
  result = "scope\n"
  for v in scope.variables:
    result.add("  " & $v & "\n")
  if not scope.parent.isNil:
    result.add("parent ")
    for line in splitLines($scope.parent):
      result.add("  " & line & "\n")
  if scope.imports.len != 0:
    result.add("imports\n")
    for c in scope.imports:
      for line in splitLines($c):
        result.add("  " & line & "\n")

when false:
  proc `$`*(st: Statement): string =
    result = ""
    for a, b in fieldPairs(st[]):
      when a == "kind":
        result.add(($b)[2..^1])
        result.add("(")
      else:
        result.add(a & ": ")
        result.add($b)
        result.add(", ")
    result.add(")")
