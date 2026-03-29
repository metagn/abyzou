import
  std/[tables, sets, hashes],
  ../defines,
  ../util/box,
  ./[arrays, pointertag, ids],
  ../lang/expressions

export largeValue
export box, unbox
template toRef*[T](x: T): ref T =
  var res: ref T
  new(res)
  res[] = x
  res
type Reference*[T] = distinct ref T
proc `==`*[T](a, b: Reference[T]): bool = system.`==`((ref T)(a), (ref T)(b))
proc hash*[T](a: Reference[T]): Hash =
  result = result !& hash(cast[pointer]((ref T)(a)))
  result = !$ result
template unref*[T](x: ref T): untyped = x[]
template unref*[T](x: Box[T]): untyped = x.unbox
template unref*[T](x: Reference[T]): untyped = (ref T)(x)[]
template unref*[T](x: T): untyped = x
template realRef*[T](x: Reference[T]): ref T = (ref T)(x)

# type system exists for both static and runtime dispatch
# runtime-only types should only be subtypes of static-only types

type
  ValueKind* = enum
    vNone
      ## singleton null value
    vInt32, vUint32, vFloat32, vBool
      ## unboxed numbers
    # XXX 48 bit ints, probably expanded to 64 bit then capped off again, but can keep 32 bit for maybe faster operations
    vEffect
      ## embedded effect value for exceptions/return/yield/whatever
    #vShortestString
    #  ## word size string
    vReference
      ## reference value, can be mutable
      ## only value kind with reference semantics
      # XXX [memory] ^ this should be wrong
    vArray
      ## like java array but typed like TS, implementation of tuples
    vFunction
      ## treewalk function
    vLinearFunction
      ## linearized (bytecode) function
    vNativeFunction
      ## Nim function that takes values as argument
    # could be pointers or serialized but for now this is more efficient:
    vExpression
    vStatement
    vModule
    vMemory
      ## memory pointer of a module or function
      # XXX [memory] maybe replace vReference, vArray, maybe more with this
    vBoxed
      ## boxed version of unboxed values, used for type info
    vInt64, vUint64, vFloat64
    vType
      ## type value
    vString
      ## general byte sequence type
      # XXX [memory] maybe split into vByteList (mutable), vByteArray (immutable/ungrowable), vShortByteArray, then strings can abstract over these
    vList
      ## both seq and string are references to save memory
    vSet
    vTable
    vContext
    # bigints can be added
    # native types in general can be BoxedValue[pointer]
    # XXX ^ no, use an inheritable NativeValue, maybe use it for sets and tables

  TypeKind* = enum
    # maybe add unknown type for values with unknown type at runtime
    tyNoType = "<none>",
    # weird concrete
    tyInstance = "<instance>",
    tyTuple = "Tuple", # XXX [tuple] make into tyComposite, tuple, named tuple, array (i.e. int^20) all at once
    # concrete
    tyNoneValue = "NoneValue",
    tyInt32 = "Int32", tyUint32 = "Uint32", tyFloat32 = "Float32", tyBool = "Bool",
    tyInt64 = "Int64", tyUint64 = "Uint64", tyFloat64 = "Float64",
    tyReference = "Reference",
    tyFunction = "Function",
    tyList = "List",
    tyString = "String",
    tySet = "Set",
    tyTable = "Table",
    tyExpression = "Expression", tyStatement = "Statement", tyContext = "Context", tyModule = "Module", tyMemory = "Memory"
    tyType = "Type",
    # typeclass
    tyAny = "Any", tyAll = "All", ## top and bottom types
    tyUnion = "Union", tyIntersection = "Intersection", tyNot = "Not"
    tyBase = "<base>",
    tyNativeBase = "<native base>",
    tyTupleConstructor = "TupleConstructor"
    tySomeValue = "SomeValue"
    # generic parameter
    tyParameter = "Parameter",
    # value container
    tyValue = "Value"
      # XXX [types] maybe only makes sense in type arg context and could go in separate TypeArg type?

const
  allValueKinds* = {low(ValueKind)..high(ValueKind)}
  largeValueKinds* = {vInt64..vFloat64}
  boxedValueKinds* = {vBoxed..high(ValueKind)} -
    (when largeValue: largeValueKinds else: {})
  functionValueKinds* = {vFunction..vNativeFunction}
  typedValueKinds* = boxedValueKinds + functionValueKinds - {vNativeFunction}
  untypedValueKinds* = allValueKinds - typedValueKinds

const
  allTypeKinds* = {low(TypeKind)..high(TypeKind)}
  concreteTypeKinds* = {tyTuple, #[tyInstance,]# tyNoneValue..tyType}
  typeclassTypeKinds* = {tyAny..tySomeValue}
  nativeTypes* = {tyNoneValue..tyType, tyTupleConstructor}
    # XXX [types] to consider later: tuple, any all, union intersection not, somevalue
    # typeclasses look a little annoying with normalization
  noArgNativeTypes* = {tyNoneValue..tyFloat64, tyString, tyExpression, tyStatement, tyContext, tyModule, tyMemory}
  argNativeTypes* = nativeTypes - noArgNativeTypes

type NativeType* = TypeKind # since it can't be a range

type
  BoxedValueObj*[T] = object
    # value first might be useful
    when T isnot Type:
      value*: T
    `type`*: Type
  BoxedValue*[T] = ref BoxedValueObj[T]

  ValueObj* = object
    # entire thing can be pointer tagged, but would need GC hooks - implemented in external library froth
    # probably use exboxing, high exponents get boxed
    # maybe interning for some pointer types
    case kind*: ValueKind
    of vNone: discard
    of vBool:
      boolValue*: bool
    of vInt32:
      int32Value*: int32
    of vUint32:
      uint32Value*: uint32
    of vFloat32:
      float32Value*: float32
    of vEffect:
      effectValue*: Box[Value]
    of vReference:
      # XXX [memory] figure out how to optimize this for mutable collections - probably wont and just have the collections act like references
      referenceValue*: Reference[Value]
    of vArray:
      # XXX [memory] maybe match pointer field location with vList, vString
      arrayValue*: RefArray[Value]
    of vBoxed:
      boxedValue*: BoxedValue[Value]
    of vInt64:
      int64Value*: (when largeValue: int64 else: BoxedValue[int64])
    of vUint64:
      uint64Value*: (when largeValue: uint64 else: BoxedValue[uint64])
    of vFloat64:
      float64Value*: (when largeValue: float64 else: BoxedValue[float64])
    of vType:
      typeValue*: BoxedValue[Type]
    of vString:
      # XXX [memory] maybe match pointer field location with vArray, vList
      stringValue*: BoxedValue[string]
    of vList:
      # XXX [memory] maybe match pointer field location with vArray, vString
      listValue*: BoxedValue[seq[Value]]
    of vSet:
      setValue*: BoxedValue[HashSet[Value]]
    of vTable:
      tableValue*: BoxedValue[Table[Value, Value]]
    of vFunction:
      functionValue*: TreeWalkFunction
    of vLinearFunction:
      linearFunctionValue*: LinearFunction
    of vNativeFunction:
      nativeFunctionValue*: NativeFunction
    of vExpression:
      expressionValue*: Expression
    of vStatement:
      statementValue*: Statement
    of vContext:
      contextValue*: BoxedValue[Context]
    of vModule:
      moduleValue*: Module
    of vMemory:
      memoryValue*: Memory
  
  PointerTaggedValue* = distinct (
    when pointerTaggable:
      TaggedPointer
    else:
      Value
  )
  
  Value* = ValueObj

  MatchLevel* = enum
    # in order of strength
    tmUnknown, tmNone,
    tmFiniteFalse, tmFalse, tmUniversalFalse,
    tmUniversalTrue, tmTrue, tmFiniteTrue,
    tmSimilar, tmGeneric,
    tmAlmostEqual, tmEqual
  
  TypeMatch* = object
    level*: MatchLevel
    case deep*: bool
    of false: discard
    of true:
      children*: seq[TypeMatch]

  Variance* = enum
    Covariant
    Contravariant
    Invariant
    Ultravariant
  
  ParameterInstantiation* = object
    strict*: bool
    table*: Table[TypeParameter, Type]

  TypeBase* = ref object
    # XXX [types] check arguments at generic fill time
    # XXX [types, modules] relate this to modules and memory etc somehow
    id*: TypeBaseId
    name*: string
    nativeType*: NativeType
    arguments*: seq[TypeParameter]
    typeMatcher*: proc (pattern, t: Type, inst: var ParameterInstantiation): TypeMatch
    valueMatcher*: proc (v: Value, thisType: Type): bool
    paramFiller*: proc (pattern: var Type, table: ParameterInstantiation)

  TypeParameter* = ref object
    id*: TypeParameterId # this needs to be assigned
    name*: string
    bound*: TypeBound

  Properties* = ref object
    leaves*: array[4, (TypeBase, Type)]
    rest*: Properties

  Type* = object
    # XXX [types] 90 bytes
      # - change these tables out for something smaller
      # - array instead of seq
      # - maybe pointer tag TypeBase with the type kind
    properties*: Table[TypeBase, Type]
      # XXX [types] redo these
      # can be a multitable later on
    case kind*: TypeKind
    of tyNoType: discard
    of tyInstance:
      instanceBase*: TypeBase
      instanceArgs*: seq[Type]
    of tyTuple:
      elements*: seq[Type]
      varargs*: Box[Type] # for now only trailing
        # XXX [tuple] either move to property, or allow non-trailing
        # XXX [tuple] definite length varargs? i.e. array[3, int]
      elementNames*: Table[string, int]
      # XXX [functions, tuple] also Defaults purely for initialization/conversion?
      # meaning only considered in function type relation
      # - maybe have as property on functions then
    of noArgNativeTypes: discard
    of argNativeTypes:
      nativeArgs*: seq[Type]
    of tyBase:
      typeBase*: TypeBase
    of tyNativeBase:
      nativeBase*: NativeType
    of tyAny, tyAll: discard
    of tyUnion, tyIntersection:
      operands*: seq[Type]
    of tyNot:
      notType*: Box[Type]
    of tySomeValue:
      someValueType*: Box[Type]
    of tyParameter:
      parameter*: TypeParameter
    of tyValue:
      valueType*: BoxedValue[Value]

  TypeBound* = object
    boundType*: Type
    variance*: Variance

  MemoryArray* = RefArray[Value]
  Memory* = object
    stack*: MemoryArray
  #MemoryImplDistinct* = distinct MemoryArray
  #Memory* = (
  #  when defined(gcDestructors):
  #    MemoryImplObj
  #  else:
  #    MemoryImplDistinct
  #)

  NativeFunction* = #[ref ]#object
    # value first just to copy BoxedValue
    callback*: proc (args: openarray[Value]): Value {.nimcall.}
    #`type`*: Type

  TreeWalkProgram* = object
    memory*: Memory
      ## persistent stack
      ## gets shallow copied when function is run
    instruction*: Statement
    thisIndex*: int

  # XXX [functions] add function names to objects but then native function is unnamed

  TreeWalkFunction* = ref object
    # value first just to copy BoxedValue
    program*: TreeWalkProgram
    `type`*: Type

  LinearProgram* = object
    registerCount*: int
    heapSize*: int
    thisIndex*: int
    argPositions*: Array[int] ## last is result
    constants*: Array[Value] # XXX [serialization] serialize values
    jumpLocations*: Array[int]
    instructions*: seq[byte]

  LinearFunction* = ref object
    # value first just to copy BoxedValue
    program*: LinearProgram
    `type`*: Type

  BinaryInstructionKind* = enum
    AddInt, SubInt, MulInt, DivInt
    AddFloat, SubFloat, MulFloat, DivFloat
    CheckType

  UnaryInstructionKind* = enum
    NegInt, NegFloat

  StatementKind* = enum
    skNone
    skConstant
    skFunctionCall, skDispatch
    skSequence
    # stack
    skVariableGet, skVariableSet
    skAddressGet, skAddressSet
    skPrepareSubmodule
    # goto
    skIf, skWhile, skDoUntil
    # effect, can emulate goto
    skEmitEffect, skHandleEffect
    # collections
    skTuple, skList, skSet, skTable
    skGetIndex, skSetIndex
    # custom instructions
    skUnaryInstruction, skBinaryInstruction

  StatementObj* = object
    ## typed/compiled expression
    # XXX [macros] differentiate between validated and unvalidated,
    # maybe allow things like skFromExpression for metas
    knownType*: Type
    case kind*: StatementKind
    of skNone: discard
    of skConstant:
      constant*: Value
    of skFunctionCall:
      callee*: Statement
      arguments*: seq[Statement]
    of skDispatch:
      # XXX [typematch] generalize dispatch result - ??? what does this mean
      dispatchees*: seq[(seq[Type], Statement)]
      dispatchArguments*: seq[Statement]
    of skSequence:
      sequence*: seq[Statement]
    of skVariableGet:
      variableGetIndex*: StackIndex
    of skVariableSet:
      variableSetIndex*: StackIndex
      variableSetValue*: Statement
    of skAddressGet:
      addressGetMemory*: Statement
      addressGetIndex*: StackIndex
    of skAddressSet:
      addressSetMemory*: Statement
      addressSetIndex*: StackIndex
      addressSetValue*: Statement
    of skPrepareSubmodule:
      ## arms a function with captures etc
      submodule*: Submodule
        ## ref object, `captures` field is only set after the module is fully compiled if the submodule is lazy compiled
    of skIf:
      ifCond*, ifTrue*, ifFalse*: Statement
    of skWhile:
      whileCond*, whileBody*: Statement
    of skDoUntil:
      doUntilCond*, doUntilBody*: Statement
    of skEmitEffect:
      effect*: Statement
    of skHandleEffect:
      effectHandler*, effectBody*: Statement
    of skTuple, skList, skSet:
      elements*: seq[Statement]
    of skTable:
      entries*: seq[tuple[key, value: Statement]]
    of skGetIndex:
      getIndexAddress*: Statement
      getIndex*: int
    of skSetIndex:
      setIndexAddress*: Statement
      setIndex*: int
      setIndexValue*: Statement
    of skUnaryInstruction:
      unaryInstructionKind*: UnaryInstructionKind
      unary*: Statement
    of skBinaryInstruction:
      binaryInstructionKind*: BinaryInstructionKind
      binary1*, binary2*: Statement
  Statement* = ref StatementObj

  StackIndex* = int
    ## index of variable in module variable list,
    ## currently also used for variable addresses (i.e. variable registers cannot overlap)

  Variable* = ref object
    id*: VariableId
    name*: string
    nameHash*: Hash
    hidden*: bool # unable to look up
    knownType*: Type
    stackIndex*: StackIndex
    scope* {.cursor.}: Scope
    genericParams*: seq[TypeParameter]
      # XXX [types] maybe make this a tuple type too with signature for named and default generic params
    isSubmodule*: bool # maybe use variable kind
    evaluated*: bool # currently just a fast check for if submodule was compiled

  StackSlot* = object
    kind*: VariableReferenceKind
    variable*: Variable

  ModuleState* = enum
    Created
    Queued ## submodules marked as either this or `Created` will be lazy compiled
    Compiling
    Compiled
  
  SubmoduleKind* = enum
    SubmoduleLinearFunction
    SubmoduleTreeWalkFunction
  
  Submodule* = ref object
    ## ref so the captures can be updated for codegen after a statement with this is generated
    value*: Module
      ## can compile after the main module is compiled
    stackIndex*: StackIndex
    captures*: seq[tuple[index, valueIndex: StackIndex]]
      ## list of (variable in submodule stack, variable in local stack)
      ## only used for passing captures so the value is just a variable index
      ## is filled after the submodule is compiled
    case kind*: SubmoduleKind
    of SubmoduleLinearFunction, SubmoduleTreeWalkFunction:
      bodyBound*: TypeBound
      inferReturnType*: bool

  Module* = ref object
    ## current module or function
    ## should not contain any "temporary" compilation constructs but it works out that everything can stay saved
    id*: ModuleId
    name*: string
    state*: ModuleState
    source*: Expression
    origin*: Scope
      ## context closure is defined in
    captures*: Table[Variable, StackIndex]
    moduleCaptures*: Table[Module, StackIndex]
    submodules*: OrderedTable[Variable, Submodule] ## should not shrink
    top*: Scope
    memorySlots*: seq[StackSlot] ## should not shrink
    memory*: Memory
    runtimeBody*: Statement ## nil until fully compiled

  Scope* = ref object
    ## restricted subset of variables in a context
    parent*: Scope
    module*: Module
    imports*: seq[Scope]
    variables*: seq[Variable] ## should not shrink

  VariableReferenceKind* = enum
    Local
    Argument # slot for function argument
    Constant
    StaticCapture # captured value loaded into function stack once when function is created
    ThisMemory
    Pinned # i.e. exported, pinned to the stack in the module object

  VariableReference* = object
    variable*: Variable
    `type`*: Type ## must have a known type
    case kind*: VariableReferenceKind
    of Local, Argument, Constant: discard
    of ThisMemory, Pinned: discard
    of StaticCapture:
      captureIndex*: int

  Context* = object
    ## statement compilation context
    scope*: Scope
    bound*: TypeBound

static:
  doAssert sizeof(Value) <= 2 * sizeof(int)

when false: {.hint: $(sizeof(Context), sizeof(TypeBound), sizeof(Variance), sizeof(Type)).}

proc isNoType*(t: Type): bool = t.kind == tyNoType
proc isNoType*(vt: Box[Type]): bool = vt.isNil or vt.unbox.isNoType
template tupleValue*(v: Value): untyped =
  v.arrayValue

# for now clashes with `module` macro for libraries
#proc module*(c: Context): Module {.inline.} = c.scope.module

import ./primitiveprocs
export primitiveprocs
