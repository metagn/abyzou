import ./[primitives, arrays, valueconstr, typebasics], std/tables

# XXX [bytecode] do some kind of register last use analysis to merge some registers
# XXX [serialization] constant pool can be long string of serialized values,
# then they are deserialized and cached into registers when loaded

type
  Register* = distinct uint16 # 32 bit would be nice
  JumpLocation* = distinct uint16
    # can rename to just Location or Position
  Constant* = distinct uint16

  LinearInstructionKind* = enum
    NoOp
    LoadConstant
      ## shallow copies element from constant pool
    SetRegisterRegister # mov
    NullaryCall, UnaryCall, BinaryCall, TernaryCall
    TupleCall
    TryDispatch, ArmType
    ArmStack, RefreshStack
    JumpPoint
    IfTrueJump, IfFalseJump
    Jump
    # effect, can emulate goto
    EmitEffect
    PushEffectHandler, PopEffectHandler
    # collection
    InitTuple, InitList, InitSet, InitTable
    GetIndex, SetIndex
    GetConstIndex, SetConstIndex
    # binary
    AddInt32, SubInt32, MulInt32, DivInt32
    AddFloat32, SubFloat32, MulFloat32, DivFloat32, CheckType
    # unary
    NegInt32, NegFloat32
  
  LinearInstruction* = object
    # cannot recurse
    case kind*: LinearInstructionKind
    of NoOp: discard
    of LoadConstant:
      lc*: tuple[res: Register, constant: Constant]
    of SetRegisterRegister:
      srr*: tuple[dest, src: Register]
    of NullaryCall:
      ncall*: tuple[res, callee: Register]
    of UnaryCall:
      ucall*: tuple[res, callee, arg1: Register]
    of BinaryCall:
      bcall*: tuple[res, callee, arg1, arg2: Register]
    of TernaryCall:
      tcall*: tuple[res, callee, arg1, arg2, arg3: Register]
    of TupleCall:
      tupcall*: tuple[res, callee, args: Register]
    of TryDispatch:
      tdisp*: tuple[res, callee, args: Register, successPos: JumpLocation]
    of ArmType:
      armt*: tuple[val, typ: Register]
    of ArmStack:
      arm*: tuple[fun: Register, ind: int32, val: Register]
    of RefreshStack:
      rfs*: tuple[fun: Register]
    of JumpPoint:
      jpt*: tuple[loc: JumpLocation]
    of IfTrueJump:
      iftj*: tuple[cond: Register, truePos: JumpLocation]
    of IfFalseJump:
      iffj*: tuple[cond: Register, falsePos: JumpLocation]
    of Jump:
      jmp*: tuple[pos: JumpLocation]
    of EmitEffect:
      emit*: tuple[effect: Register]
    of PushEffectHandler:
      pueh*: tuple[handler: Register]
    of PopEffectHandler:
      poeh*: tuple[]
    of InitTuple, InitSet, InitList, InitTable:
      coll*: tuple[res: Register, siz: int32]
    of GetConstIndex:
      gci*: tuple[res, coll: Register, ind: int32]
    of SetConstIndex:
      sci*: tuple[coll: Register, ind: int32, val: Register]
    of GetIndex:
      gri*: tuple[res, coll, ind: Register]
    of SetIndex:
      sri*: tuple[coll, ind, val: Register]
    of AddInt32, SubInt32, MulInt32, DivInt32,
      AddFloat32, SubFloat32, MulFloat32, DivFloat32, CheckType:
      binary*: tuple[res, arg1, arg2: Register]
    of NegInt32, NegFloat32:
      unary*: tuple[res, arg: Register]
  
  SpecialRegister = enum
    Void

  LinearContext* = ref object
    instructions*: seq[LinearInstruction]
    byteCount*: int
    registerCount*: int
    jumpLocationCount*: int
    jumpLocationByteIndex*: seq[int]
    constants*: seq[Value] # first are always variable default values
    cachedConstants*: Table[Value, Constant]
    variableRegisters*, argRegisters*: seq[Register]
    usedSpecialRegisters: set[SpecialRegister]
    specialRegisters: array[SpecialRegister, Register]
  
  ResultKind = enum
    Value
    Statement
    SetRegister
  
  Result = object
    case kind: ResultKind
    of Value:
      value: Register
    of Statement: discard
    of SetRegister:
      register: Register

const
  lowBinary = AddInt32
  highBinary = CheckType
  lowUnary = NegInt32
  highUnary = NegFloat32
  binaryInstructions: array[BinaryInstructionKind, range[lowBinary .. highBinary]] = [
    AddInt: range[lowBinary .. highBinary] AddInt32, SubInt: SubInt32, MulInt: MulInt32, DivInt: DivInt32,
    AddFloat: AddFloat32, SubFloat: SubFloat32, MulFloat: MulFloat32, DivFloat: DivFloat32,
    CheckType: CheckType
  ]
  unaryInstructions: array[UnaryInstructionKind, range[lowUnary .. highUnary]] = [
    NegInt: range[lowUnary .. highUnary] NegInt32, NegFloat: NegFloat32
  ]

when false:
  proc `$`*(x: Register | Constant | JumpLocation): string = $x.uint16

proc byteCount*(atom: Register | int32 | JumpLocation | Constant): int =
  result = sizeof(atom)

proc byteCount*[T: tuple](tup: T): int =
  for a in fields(tup):
    result += sizeof(a)

proc byteCount*(atom: Array[int32]): int =
  result = sizeof(int32(atom.len)) + atom.len * sizeof(int32)

proc byteCount*(instr: LinearInstruction): int =
  result = sizeof(instr.kind)
  for a in instr.fields:
    when a is tuple:
      result += byteCount(a)

proc addBytes*(bytes: var openarray[byte], i: var int, instr: LinearInstruction) =
  template add(b: byte) =
    bytes[i] = b
    inc i
  template add(r: Register | JumpLocation | Constant) =
    let u = r.uint16
    add(byte((u shr 8) and 0xFF))
    add(byte(u and 0xFF))
  template add(ii: int32) =
    let u = cast[uint32](ii)
    add(byte((u shr 24) and 0xFF))
    add(byte((u shr 16) and 0xFF))
    add(byte((u shr 8) and 0xFF))
    add(byte(u and 0xFF))
  template add(ia: Array[int32]) =
    add(int32(ia.len))
    for x in ia:
      add(x)
  template add(tup: tuple) =
    for a in tup.fields:
      add(a)
  add instr.kind.byte
  case instr.kind
  of NoOp: discard
  of LoadConstant:
    add instr.lc
  of SetRegisterRegister:
    add instr.srr
  of NullaryCall:
    add instr.ncall
  of UnaryCall:
    add instr.ucall
  of BinaryCall:
    add instr.bcall
  of TernaryCall:
    add instr.tcall
  of TupleCall:
    add instr.tupcall
  of TryDispatch:
    add instr.tdisp
  of ArmType:
    add instr.armt
  of ArmStack:
    add instr.arm
  of RefreshStack:
    add instr.rfs
  of JumpPoint:
    add instr.jpt
  of IfTrueJump:
    add instr.iftj
  of IfFalseJump:
    add instr.iffj
  of Jump:
    add instr.jmp
  of EmitEffect:
    add instr.emit
  of PushEffectHandler:
    add instr.pueh
  of PopEffectHandler:
    add instr.poeh
  of InitTuple, InitList, InitSet, InitTable:
    add instr.coll
  of GetConstIndex:
    add instr.gci
  of SetConstIndex:
    add instr.sci
  of GetIndex:
    add instr.gri
  of SetIndex:
    add instr.sri
  of AddInt32, SubInt32, MulInt32, DivInt32,
    AddFloat32, SubFloat32, MulFloat32, DivFloat32, CheckType:
    add instr.binary
  of NegInt32, NegFloat32:
    add instr.unary

proc toBytes*(fn: LinearContext): seq[byte] =
  result = newSeq[byte](fn.byteCount)
  var i = 0
  for instr in fn.instructions:
    addBytes(result, i, instr)

proc add(fn: LinearContext, instr: LinearInstruction) =
  fn.instructions.add(instr)
  fn.byteCount += instr.byteCount
  if instr.kind == JumpPoint:
    fn.jumpLocationByteIndex.setLen(fn.jumpLocationCount)
    fn.jumpLocationByteIndex[instr.jpt.loc.int] = fn.byteCount

proc newRegister(fn: LinearContext): Register =
  result = fn.registerCount.Register
  inc fn.registerCount

proc getRegister(fn: LinearContext, sr: SpecialRegister): Register =
  if sr in fn.usedSpecialRegisters:
    result = fn.specialRegisters[sr]
  else:
    result = fn.newRegister()
    fn.specialRegisters[sr] = result
    fn.usedSpecialRegisters.incl(sr)

proc newJumpLocation(fn: LinearContext): JumpLocation =
  result = fn.jumpLocationCount.JumpLocation
  inc fn.jumpLocationCount

proc jumpPoint(fn: LinearContext, loc: JumpLocation) =
  fn.add(LinearInstruction(kind: JumpPoint, jpt: (loc: loc)))

proc getConstant(fn: LinearContext, constant: Value): Constant =
  let cacheLen = fn.cachedConstants.len
  result = fn.cachedConstants.mgetOrPut(constant, Constant(fn.constants.len))
  if cacheLen != fn.cachedConstants.len:
    fn.constants.add(constant)

proc resultRegister(fn: LinearContext, res: var Result): Register =
  case res.kind
  of SetRegister: result = res.register
  of Value:
    result = fn.newRegister()
    res.value = result
  of Statement: result = fn.getRegister(Void)

proc linearize*(module: Module, fn: LinearContext, result: var Result, s: Statement) =
  type Instr = LinearInstruction
  template value(s: Statement): Register {.callsite.} =
    var res = Result(kind: Value)
    linearize(module, fn, res, s)
    res.value
  var statementResult = Result(kind: Statement)
  template statement(s: Statement) {.callsite.} =
    linearize(module, fn, statementResult, s)
  let resultKind = result.kind
  case s.kind
  of skNone:
    case resultKind
    of SetRegister:
      fn.add(Instr(kind: LoadConstant, lc:
        (res: result.register, constant: fn.getConstant(Value(kind: vNone)))))
    of Value:
      result.value = fn.newRegister()
      fn.add(Instr(kind: LoadConstant, lc:
        (res: result.value, constant: fn.getConstant(Value(kind: vNone)))))
    of Statement: discard # nothing
  of skConstant:
    fn.add(Instr(kind: LoadConstant, lc: (res: resultRegister(fn, result),
      constant: fn.getConstant(s.constant))))
  of skFunctionCall:
    let f = value(s.callee)
    let res = resultRegister(fn, result)
    case s.arguments.len
    of 0:
      fn.add(Instr(kind: NullaryCall, ncall: (res: res, callee: f)))
    of 1:
      fn.add(Instr(kind: UnaryCall, ucall:
        (res: res, callee: f, arg1: value(s.arguments[0]))))
    of 2:
      fn.add(Instr(kind: BinaryCall, bcall:
        (res: res, callee: f, arg1: value(s.arguments[0]),
          arg2: value(s.arguments[1]))))
    of 3:
      fn.add(Instr(kind: TernaryCall, tcall:
        (res: res, callee: f, arg1: value(s.arguments[0]),
          arg2: value(s.arguments[1]), arg3: value(s.arguments[2]))))
    else:
      let args = fn.newRegister()
      fn.add(Instr(kind: InitTuple, coll: (res: args, siz: s.arguments.len.int32)))
      for i, a in s.arguments:
        fn.add(Instr(kind: SetConstIndex, sci: (coll: args, ind: i.int32, val: value(a))))
      fn.add(Instr(kind: TupleCall, tupcall: (res: res, callee: f, args: args)))
  of skDispatch:
    let res = resultRegister(fn, result)
    let successPos = fn.newJumpLocation()
    let args = fn.newRegister()
    fn.add(Instr(kind: InitTuple, coll:
      (res: args, siz: s.dispatchArguments.len.int32)))
    for i, a in s.dispatchArguments:
      fn.add(Instr(kind: SetConstIndex, sci:
        (coll: args, ind: i.int32, val: value(a))))
    let tReg = fn.newRegister()
    for t, d in s.dispatchees.items:
      # XXX [type-arming] make sure this type arming works
      let ty = funcType(AnyTy, t)
      fn.add(Instr(kind: LoadConstant, lc:
        (res: tReg, constant: fn.getConstant(toValue(ty)))))
      let fun = value(d)
      fn.add(Instr(kind: ArmType, armt:
        (val: fun, typ: tReg)))
      fn.add(Instr(kind: TryDispatch, tdisp:
        (res: res, callee: fun, args: args, successPos: successPos)))
    fn.jumpPoint(successPos)
  of skSequence:
    let h = s.sequence.len - 1
    for i in 0 ..< h:
      statement(s.sequence[i])
    linearize(module, fn, result, s.sequence[h])
  of skVariableGet:
    case result.kind
    of SetRegister:
      fn.add(Instr(kind: SetRegisterRegister, srr:
        (dest: result.register,
          src: fn.variableRegisters[s.variableGetIndex])))
    of Value:
      result.value = fn.variableRegisters[s.variableGetIndex]
    of Statement: discard
  of skVariableSet:
    let val = value(s.variableSetValue)
    fn.add(Instr(kind: SetRegisterRegister, srr:
      (dest: fn.variableRegisters[s.variableSetIndex], src: val)))
    case resultKind
    of SetRegister:
      fn.add(Instr(kind: SetRegisterRegister, srr: (dest: result.register, src: val)))
    of Value:
      result.value = val
    of Statement: discard
  of skArmStack:
    let fun = value(s.armStackFunction)
    # XXX [function-arm] comment needs to be correct
    #fn.add(Instr(kind: RefreshStack, rfs: (fun: fun)))
    for a, b in s.armStackCaptures.items:
      fn.add(Instr(kind: ArmStack, arm:
        (fun: fun, ind: a.int32, val: fn.variableRegisters[b])))
    fn.add(Instr(kind: RefreshStack, rfs: (fun: fun)))
    case result.kind
    of SetRegister:
      fn.add(Instr(kind: SetRegisterRegister, srr: (dest: result.register, src: fun)))
    of Value:
      result.value = fun
    of Statement: discard
  of skIf:
    # the true location is immediately afterward so we don't really need it
    var branchRes =
      if result.kind == Statement: result
      else: Result(kind: SetRegister, register: fn.resultRegister(result))
    let falseLoc = fn.newJumpLocation()
    fn.add(Instr(kind: IfFalseJump, iffj:
      (cond: value(s.ifCond), falsePos: falseLoc)))
    linearize(module, fn, branchRes, s.ifTrue)
    let endLoc = fn.newJumpLocation()
    fn.add(Instr(kind: Jump, jmp: (pos: endLoc)))
    fn.jumpPoint(falseLoc)
    linearize(module, fn, branchRes, s.ifFalse)
    fn.jumpPoint(endLoc)
    # XXX [bytecode] maybe later optimize consecutive jump points to 1 jump point
    # like if s.ifFalse is a skNone statement
  of skWhile:
    let startLoc = fn.newJumpLocation()
    let endLoc = fn.newJumpLocation()
    fn.jumpPoint(startLoc)
    fn.add(Instr(kind: IfFalseJump, iffj:
      (cond: value(s.whileCond), falsePos: endLoc)))
    linearize(module, fn, result, s.whileBody)
    fn.add(Instr(kind: Jump, jmp: (pos: startLoc)))
    fn.jumpPoint(endLoc)
  of skDoUntil:
    let startLoc = fn.newJumpLocation()
    let endLoc = fn.newJumpLocation()
    fn.jumpPoint(startLoc)
    linearize(module, fn, result, s.doUntilBody)
    fn.add(Instr(kind: IfTrueJump, iftj:
      (cond: value(s.doUntilCond), truePos: endLoc)))
    fn.jumpPoint(endLoc)
  of skEmitEffect:
    fn.add(Instr(kind: EmitEffect, emit: (effect: value(s.effect))))
  of skHandleEffect:
    fn.add(Instr(kind: PushEffectHandler, pueh:
      (handler: value(s.effectHandler))))
    linearize(module, fn, result, s.effectBody)
    fn.add(Instr(kind: PopEffectHandler))
  of skTuple:
    # XXX [bytecode] statement shouldn't build collection
    let res = resultRegister(fn, result)
    fn.add(Instr(kind: InitTuple, coll:
      (res: res, siz: s.elements.len.int32)))
    for i, a in s.elements:
      fn.add(Instr(kind: SetConstIndex, sci:
        (coll: res, ind: i.int32, val: value(a))))
  of skList:
    # XXX [bytecode] statement shouldn't build collection
    let res = resultRegister(fn, result)
    fn.add(Instr(kind: InitList, coll:
      (res: res, siz: s.elements.len.int32)))
    for i, a in s.elements:
      # XXX [memory, references] SetIndex for lists and strings should only work if their pointer is
      # in the same location in memory as arrays
      fn.add(Instr(kind: SetConstIndex, sci:
        (coll: res, ind: i.int32, val: value(a))))
  of skSet:
    # XXX [bytecode] statement shouldn't build collection
    let res = resultRegister(fn, result)
    fn.add(Instr(kind: InitSet, coll:
      (res: res, siz: s.elements.len.int32)))
    for a in s.elements:
      # XXX [memory, references] no SetIndex for sets
      fn.add(Instr(kind: SetIndex, sri:
        (coll: res, ind: value(a), val: value(a))))
  of skTable:
    # XXX [bytecode] statement shouldn't build collection
    let res = resultRegister(fn, result)
    fn.add(Instr(kind: InitTable, coll:
      (res: res, siz: s.elements.len.int32)))
    for k, v in s.entries.items:
      # XXX [memory, references] probably no SetIndex for tables
      fn.add(Instr(kind: SetIndex, sri:
        (coll: res, ind: value(k), val: value(v))))
  of skGetIndex:
    fn.add(Instr(kind: GetConstIndex, gci:
      (res: resultRegister(fn, result),
        coll: value(s.getIndexAddress),
        ind: s.getIndex.int32)))
  of skSetIndex:
    let val = value(s.setIndexValue)
    fn.add(Instr(kind: SetConstIndex, sci:
      (coll: value(s.setIndexAddress), ind: s.setIndex.int32, val: val)))
    case resultKind
    of SetRegister:
      fn.add(Instr(kind: SetRegisterRegister, srr:
        (dest: result.register, src: val)))
    of Value:
      result.value = val
    of Statement: discard
  of skUnaryInstruction:
    let res =
      case resultKind
      of SetRegister: result.register
      of Value:
        result.value = fn.newRegister()
        result.value
      of Statement: fn.getRegister(Void)
    fn.add(Instr(kind: unaryInstructions[s.unaryInstructionKind], unary:
      (res: res, arg: value(s.unary))))
  of skBinaryInstruction:
    let res =
      case resultKind
      of SetRegister: result.register
      of Value:
        result.value = fn.newRegister()
        result.value
      of Statement: fn.getRegister(Void)
    fn.add(Instr(kind: binaryInstructions[s.binaryInstructionKind], binary:
      (res: res, arg1: value(s.binary1), arg2: value(s.binary2))))

proc createLinearContext*(module: Module): LinearContext =
  result = LinearContext()
  result.variableRegisters.newSeq(module.stackSlots.len + 1)
  result.constants.newSeq(module.stackSlots.len)
  for i in 0 ..< module.stackSlots.len:
    let reg = result.newRegister()
    result.variableRegisters[i] = reg
    if module.stackSlots[i].kind == Local:
      # enforce this so that other modules can easily access it:
      doAssert reg.int == module.stackSlots[i].variable.stackIndex, $(i, reg.int, module.stackSlots[i].variable.stackIndex)
    if module.stackSlots[i].kind == Argument:
      result.argRegisters.add(reg)
    # this might lose performance but is needed for capture arming
    let defaultValue = module.stackSlots[i].value
    if defaultValue.kind != vNone or module.stackSlots[i].kind == Capture:
      result.constants[i] = defaultValue
      result.add(LinearInstruction(kind: LoadConstant, lc:
        (res: reg, constant: Constant(i))))
  result.argRegisters.add(result.newRegister()) # result value

proc linear*(module: Module, body: Statement): LinearContext =
  result = createLinearContext(module)
  var res = Result(kind: SetRegister, register: result.argRegisters[^1])
  linearize(module, result, res, body)

proc toFunction*(lc: LinearContext): LinearProgram =
  var ap = initArray[int](lc.argRegisters.len)
  for i in 0 ..< lc.argRegisters.len:
    ap[i] = lc.argRegisters[i].int
  result = LinearProgram(
    registerCount: lc.registerCount,
    argPositions: ap,
    constants: toArray(lc.constants),
    jumpLocations: toArray(lc.jumpLocationByteIndex),
    instructions: lc.toBytes())
