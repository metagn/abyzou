import std/tables, ./[primitives, ids]

template NoType*: untyped = Type(kind: tyNoType)
template AnyTy*: untyped = Type(kind: tyAny)
template AllTy*: untyped = Type(kind: tyAll)

proc `+`*(t: Type): TypeBound {.inline.} = TypeBound(boundType: t, variance: Covariant)
proc `-`*(t: Type): TypeBound {.inline.} = TypeBound(boundType: t, variance: Contravariant)
proc `~`*(t: Type): TypeBound {.inline.} = TypeBound(boundType: t, variance: Invariant)
proc `*`*(t: Type): TypeBound {.inline.} = TypeBound(boundType: t, variance: Ultravariant)
proc `*`*(t: Type, variance: Variance): TypeBound {.inline.} = TypeBound(boundType: t, variance: variance)

proc newTypeParameter*(name: string, bound: TypeBound = +AnyTy): TypeParameter =
  TypeParameter(id: newTypeParameterId(), name: name, bound: bound)

when defined(gcDestructors):
  template defineTypeBase*(name, value): untyped {.dirty.} =
    bind newTypeBaseId
    let `name`* = block: # !global
      var `name` {.inject.}: TypeBase
      `name` = value
      `name`.id = newTypeBaseId()
      `name`
else:
  template defineTypeBase*(name, value): untyped =
    bind newTypeBaseId
    proc getTypeBase: TypeBase {.gensym.} =
      var `name` {.global, inject.}: TypeBase
      if `name`.isNil:
        `name` = value
        `name`.id = newTypeBaseId()
      result = `name`
    template `name`*: TypeBase {.inject.} = getTypeBase()

proc toTypeParams(args: varargs[TypeBound]): seq[TypeParameter] =
  result.newSeq(args.len)
  for i in 0 ..< args.len:
    result[i] = newTypeParameter("", args[i])

template nativeType(n: untyped, typename: static string, nt: NativeType, args: varargs[TypeBound]) =
  defineTypeBase n, TypeBase(name: typename,
    nativeType: nt,
    arguments: toTypeParams(args))

template nativeType(n: untyped, args: varargs[TypeBound]) =
  nativeType(`n Ty`, astToStr(n), `ty n`, args)

template nativeAtomicType(n: untyped) =
  nativeType(`n TyBase`, astToStr(n), `ty n`)
  template `n Ty`*: untyped = Type(kind: `ty n`)#Type(kind: tyInstance, base: `n TyBase`)

nativeType TupleTy, "Tuple", tyTuple, [] # not used for tuple type construction

proc nativeBase*(kind: NativeType): Type {.inline.} =
  Type(kind: tyNativeBase, nativeBase: kind)

proc baseType*(base: TypeBase): Type {.inline.} =
  if base.nativeType != tyNoType:
    Type(kind: tyNativeBase, nativeBase: base.nativeType)
  else:
    Type(kind: tyBase, typeBase: base)

let nativeTypeArgs*: array[NativeType, seq[TypeBound]] = [
  tyNoType: @[],
  # weird concrete
  tyInstance: @[], tyTuple: @[], # - not native
  # concrete
  tyNoneValue: @[],
  tyInt32: @[], tyUint32: @[], tyFloat32: @[], tyBool: @[],
  tyInt64: @[], tyUint64: @[], tyFloat64: @[],
  tyReference: @[+AnyTy],
  tyFunction: @[+baseType(TupleTy), -AllTy],
  tyList: @[+AnyTy],
  tyString: @[],
  tySet: @[+AnyTy],
  tyTable: @[+AnyTy, +AnyTy],
  tyExpression: @[], tyStatement: @[], tyContext: @[], tyModule: @[],
  tyType: @[+AnyTy],
  # typeclass
  tyAny: @[], tyAll: @[], # - not native
  tyUnion: @[], tyIntersection: @[], tyNot: @[], # - not native
  tyBase: @[], tyNativeBase: @[], # - not native
  tyTupleConstructor: @[+baseType(TupleTy)],
  tySomeValue: @[+AnyTy], # - not native
  # generic parameter
  tyParameter: @[], # - not native
  # value container
  tyValue: @[] # - not native
]

nativeAtomicType NoneValue
nativeAtomicType Int32
nativeAtomicType Uint32
nativeAtomicType Float32
nativeAtomicType Bool
nativeAtomicType Int64
nativeAtomicType Uint64
nativeAtomicType Float64
nativeAtomicType String
nativeAtomicType Expression
nativeAtomicType Statement
nativeAtomicType Context
nativeAtomicType Module
nativeType Reference, [+AnyTy]
nativeType List, [+AnyTy]
nativeType Set, [+AnyTy]
nativeType Table, [+AnyTy, +AnyTy]
nativeType Function, [+baseType(TupleTy), -AllTy]
nativeType Type, [+AnyTy]

nativeType TupleConstructor, [+baseType(TupleTy)]

proc instance*(tag: TypeBase, args: varargs[Type]): Type {.inline.} =
  let tnt = tag.nativeType
  case tnt
  of noArgNativeTypes:
    Type(kind: tnt)
  of argNativeTypes:
    Type(kind: tnt, nativeArgs: @args)
  else:
    Type(kind: tyInstance, instanceBase: tag, instanceArgs: @args)

template `!`*(tag: TypeBase): Type = instance(tag)
template `[]`*(tag: TypeBase, args: varargs[Type]): Type = instance(tag, args)

proc property*(tag: TypeBase, args: varargs[Type]): Type {.inline.} =
  instance(tag, args)

proc property*(prop: Type): Type {.inline.} =
  assert prop.kind == tyInstance
  prop

proc properties*(ps: varargs[Type, property]): Table[TypeBase, Type] =
  result = initTable[TypeBase, Type](ps.len)
  for p in ps:
    result[p.instanceBase] = p

proc withProperties*(ty: sink Type, ps: varargs[Type, property]): Type {.inline.} =
  ty.properties = properties(ps)
  ty

proc hasProperty*(t: Type, tag: TypeBase): bool =
  t.properties.hasKey(tag)

proc property*(t: Type, tag: TypeBase): Type =
  t.properties[tag]

proc tupleType*(s: varargs[Type]): Type =
  Type(kind: tyTuple, elements: @s)

proc funcType*(returnType: Type, arguments: varargs[Type]): Type {.inline.} =
  FunctionTy[tupleType(arguments), returnType]

proc tupleTypeWithVarargs*(s: varargs[Type], varargs: Type): Type =
  Type(kind: tyTuple, elements: @s, varargs: varargs.box)

proc funcTypeWithVarargs*(returnType: Type, arguments: varargs[Type], varargs: Type): Type {.inline.} =
  FunctionTy[tupleTypeWithVarargs(arguments, varargs), returnType]

proc union*(s: varargs[Type]): Type =
  Type(kind: tyUnion, operands: @s)

proc unwrapTypeType*(t: Type): Type {.inline.} =
  result = t
  # XXX no native type normalization here
  if t.kind == tyType:#t.kind == tyInstance and t.base.nativeType == tyType:
    result = t.nativeArgs[0]

const definiteTypeLengths*: array[TypeKind, int] = [
  tyNoType: 0,
  # weird concrete
  tyInstance: -1,
  tyTuple: -1,
  # concrete
  tyNoneValue: 0,
  tyInt32: 0, tyUint32: 0, tyFloat32: 0, tyBool: 0,
  tyInt64: 0, tyUint64: 0, tyFloat64: 0,
  tyReference: 1,
  tyFunction: 2,
  tyList: 1,
  tyString: 0,
  tySet: 1,
  tyTable: 2,
  tyExpression: 0, tyStatement: 0, tyContext: 0, tyModule: 0,
  tyType: 1,
  # typeclass
  tyAny: 0, tyAll: 0,
  tyUnion: -1, tyIntersection: -1, tyNot: 1,
  tyBase: 0,
  tyNativeBase: 0,
  tyTupleConstructor: 1,
  tySomeValue: 1,
  # generic parameter
  tyParameter: -1,
  # value container
  tyValue: -1
]

proc len*(t: Type): int =
  result = definiteTypeLengths[t.kind]
  if result < 0:
    case t.kind
    of tyTuple:
      if t.varargs.isNoType:
        result = t.elements.len
    of tyInstance:
      result = t.instanceArgs.len
    of tyUnion, tyIntersection:
      result = t.operands.len
    else: discard

proc hasNth*(t: Type, i: int): bool {.inline.} =
  i < t.len or (t.kind == tyTuple and not t.varargs.isNoType)

proc nth*(t: Type, i: int): Type =
  case t.kind
  of tyNoType, tyAny, tyAll, noArgNativeTypes:
    discard # inapplicable
  of tyBase, tyNativeBase:
    discard # inapplicable
  of tyInstance:
    result = t.instanceArgs[i]
  of tyTuple:
    if i < t.elements.len or t.varargs.isNoType:
      result = t.elements[i]
    else:
      result = t.varargs.unbox
  of argNativeTypes:
    result = t.nativeArgs[i]
  of tyUnion, tyIntersection:
    # this is actually not supposed to happen
    result = t.operands[i]
  of tyNot:
    result = t.notType.unbox
  of tySomeValue:
    result = t.someValueType.unbox
  of tyParameter, tyValue:
    discard # what

proc param*(t: Type, i: int): Type {.inline.} =
  # XXX no native type normalization here
  assert t.kind == tyFunction#t.kind == tyInstance and t.base.nativeType == tyFunction
  t.nativeArgs[0].nth(i)

proc fillParameters*(pattern: var Type, table: ParameterInstantiation) =
  template fill(a: var Type) = fillParameters(a, table)
  template fill(a: var Box[Type]) =
    if not a.isNil:
      var newType: Type = a.unbox
      fillParameters(newType, table)
      a = newType.box
  case pattern.kind
  of tyParameter:
    pattern = table.table[pattern.parameter]
  of tyNoType, tyAny, tyAll, tyBase, tyNativeBase, noArgNativeTypes:
    discard
  of tyInstance:
    # XXX [types] check argument bounds
    if unlikely(not pattern.instanceBase.paramFiller.isNil):
      pattern.instanceBase.paramFiller(pattern, table)
    else:
      for t in pattern.instanceArgs.mitems:
        fill(t)
  of tyTuple:
    for e in pattern.elements.mitems:
      fill(e)
    fill(pattern.varargs)
  of argNativeTypes:
    for t in pattern.nativeArgs.mitems:
      fill(t)
  of tyUnion, tyIntersection:
    for o in pattern.operands.mitems:
      fill(o)
  of tyNot:
    fill(pattern.notType)
  of tyValue:
    fill(pattern.valueType)
  of tySomeValue:
    fill(pattern.someValueType)
  for a, v in pattern.properties.mpairs:
    fill(v)
