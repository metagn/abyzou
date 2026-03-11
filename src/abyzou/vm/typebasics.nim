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
  nativeType(`n Ty`, astToStr(n), `nty n`, args)

template nativeAtomicType(n: untyped) =
  nativeType(`n TyBase`, astToStr(n), `nty n`)
  template `n Ty`*: untyped = Type(kind: tyInstance, base: `n TyBase`)

nativeType TupleTy, "Tuple", ntyTuple, [] # not used for tuple type construction

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
nativeType Reference, [+AnyTy]
nativeType List, [+AnyTy]
nativeType Set, [+AnyTy]
nativeType Table, [+AnyTy, +AnyTy]
nativeType Function, [+Type(kind: tyBase, typeBase: TupleTy), -AllTy]
nativeType Type, [+AnyTy]

nativeType TupleConstructor, [+Type(kind: tyBase, typeBase: TupleTy)]

proc instance*(tag: TypeBase, args: varargs[Type]): Type {.inline.} =
  Type(kind: tyInstance, base: tag, baseArguments: @args)

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
    result[p.base] = p

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
  if t.kind == tyInstance and t.base.nativeType == ntyType:
    result = t.baseArguments[0]

const definiteTypeLengths*: array[TypeKind, int] = [
  tyNoType: 0,
  tyInstance: -1,
  tyTuple: -1,
  tyAny: 0,
  tyAll: 0,
  tyUnion: -1,
  tyIntersection: -1,
  tyNot: 1,
  tyBase: 0,
  tySomeValue: 1,
  tyParameter: -1,
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
      result = t.baseArguments.len
    of tyUnion, tyIntersection:
      result = t.operands.len
    else: discard

proc hasNth*(t: Type, i: int): bool {.inline.} =
  i < t.len or (t.kind == tyTuple and not t.varargs.isNoType)

proc nth*(t: Type, i: int): Type =
  case t.kind
  of tyNoType, tyAny, tyAll:
    discard # inapplicable
  of tyTuple:
    if i < t.elements.len or t.varargs.isNoType:
      result = t.elements[i]
    else:
      result = t.varargs.unbox
  of tyInstance:
    result = t.baseArguments[i]
  of tyUnion, tyIntersection:
    # this is actually not supposed to happen
    result = t.operands[i]
  of tyNot:
    result = t.notType.unbox
  of tyBase:
    discard # inapplicable
  of tySomeValue:
    result = t.someValueType.unbox
  of tyParameter, tyValue:
    discard # what

proc param*(t: Type, i: int): Type {.inline.} =
  assert t.kind == tyInstance and t.base.nativeType == ntyFunction
  t.baseArguments[0].nth(i)

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
  of tyNoType, tyAny, tyAll, tyBase:
    discard
  of tyInstance:
    # XXX (2) check argument bounds
    if unlikely(not pattern.base.paramFiller.isNil):
      pattern.base.paramFiller(pattern, table)
    else:
      for t in pattern.baseArguments.mitems:
        fill(t)
  of tyTuple:
    for e in pattern.elements.mitems:
      fill(e)
    fill(pattern.varargs)
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
