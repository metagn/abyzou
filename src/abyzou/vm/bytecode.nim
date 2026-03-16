# bytecode interpreter

{.push hint[DuplicateModuleImport]: off.}
import
  ../repr/[primitives, arrays, guesstype, valueconstr, typebasics, memory],
  ./[linearizer, checktype],
  std/[sets, tables]

proc shallowRefresh*(fun: LinearFunction): LinearFunction {.inline.} =
  let prev {.cursor.} = fun.program.constants
  new(result)
  result[] = fun[]
  result.program.constants = toArray(prev.toOpenArray(0, prev.len - 1))

proc call*(lf: LinearProgram, args: openarray[Value]): Value

when not declared(EffectHandler):
  import ./treewalk
{.pop.}

proc runOnStack*(lf: LinearProgram, stack: var Array[Value], effectPos: int) =
  var registers = move stack
  defer: stack = move registers
  template put(reg: Register, val: Value) =
    registers[reg.int32] = val
  template get(reg: Register): Value =
    registers[reg.int32]
  template getMut(reg: Register): var Value =
    registers[reg.int32]
  template mov(src, dest: Register) =
    registers[dest.int32] = registers[src.int32]

  var
    effectHandlers: seq[EffectHandler]
    effectHandler: EffectHandler
    unhandledEffect = false

  # remove these cursor annotations if needed
  let instructions {.cursor.} = lf.instructions
  var i = 0
  template read(b: var byte) =
    assert i < instructions.len
    b = instructions[i]
    inc i
  template read(b: var uint16) =
    assert i + 1 < instructions.len
    b = (instructions[i].uint16 shl 8) or
      instructions[i + 1].uint16
    inc i, 2
  template read(b: var uint32) =
    assert i + 3 < instructions.len
    b = (instructions[i].uint32 shl 24) or
      (instructions[i + 1].uint32 shl 16) or
      (instructions[i + 2].uint32 shl 8) or
      instructions[i + 3].uint32
    inc i, 4
  template read(r: var (Register | JumpLocation | Constant)) =
    var u: uint16
    read(u)
    r = typeof(r)(u)
  template read(ii: var int32) =
    var u: uint32
    read(u)
    ii = int32(u)
  template read(ia: var Array[int32]) =
    var len: int32
    read(len)
    ia = initArray[int32](len)
    for x in ia.mitems:
      read(x)
  template read[T: tuple](tup: var T) =
    for a in tup.fields:
      read(a)
  
  template jump(p: JumpLocation) =
    i = lf.jumpLocations[p.int]

  template checkEffect(val: Value): untyped =
    if val.kind == vEffect:
      let eff = val.effectValue.unref
      if effectHandler.isNil or not effectHandler(eff):
        registers[effectPos] = val
        unhandledEffect = true

  while i < instructions.len:
    var opcode: byte
    read(opcode)
    var instr = LinearInstruction(kind: LinearInstructionKind(opcode))
    if unhandledEffect and instr.kind != PopEffectHandler:
      continue
    {.computedGoto.}
    case instr.kind
    of NoOp: discard
    of LoadConstant:
      read instr.lc
      # XXX shallow copy here (not really needed but still)
      put instr.lc.res, lf.constants[instr.lc.constant.int32]
    of SetRegisterRegister:
      read instr.srr
      mov instr.srr.src, instr.srr.dest
    of LoadAddress:
      read instr.la
      let heap = unboxStripType get instr.la.heap
      assert heap.kind == vMemory
      put instr.la.res, heap.memoryValue.get(instr.la.ind)
    of SetAddress:
      read instr.sa
      let heap = unboxStripType get instr.sa.heap
      assert heap.kind == vMemory, $heap
      heap.memoryValue.set(instr.sa.ind, get instr.sa.val)
    of NullaryCall:
      read instr.ncall
      let fn {.cursor.} = unboxStripType get instr.ncall.callee
      let val =
        case fn.kind
        of vNativeFunction:
          fn.nativeFunctionValue.callback([])
        of vFunction:
          fn.functionValue.program.call(
            default(Array[Value]),
            effectHandler)
        of vLinearFunction:
          fn.linearFunctionValue.program.call([])
        else: raiseAssert("cannot call " & $fn)
      checkEffect val
      put instr.ncall.res, val
    of UnaryCall:
      read instr.ucall
      let fn {.cursor.} = unboxStripType get instr.ucall.callee
      let val =
        case fn.kind
        of vNativeFunction:
          fn.nativeFunctionValue.callback(
            [get instr.ucall.arg1])
        of vFunction:
          fn.functionValue.program.call(
            toArray([get instr.ucall.arg1]),
            effectHandler)
        of vLinearFunction:
          fn.linearFunctionValue.program.call([get instr.ucall.arg1])
        else: raiseAssert("cannot call " & $fn)
      checkEffect val
      put instr.ucall.res, val
    of BinaryCall:
      read instr.bcall
      let fn {.cursor.} = unboxStripType get instr.bcall.callee
      let args = [get instr.bcall.arg1, get instr.bcall.arg2]
      let val =
        case fn.kind
        of vNativeFunction:
          fn.nativeFunctionValue.callback(args)
        of vFunction:
          fn.functionValue.program.call(toArray(args), effectHandler)
        of vLinearFunction:
          fn.linearFunctionValue.program.call(args)
        else: raiseAssert("cannot call " & $fn)
      checkEffect val
      put instr.bcall.res, val
    of TernaryCall:
      read instr.tcall
      let fn {.cursor.} = unboxStripType get instr.tcall.callee
      let args = [get instr.tcall.arg1, get instr.tcall.arg2, get instr.tcall.arg3]
      let val =
        case fn.kind
        of vNativeFunction:
          fn.nativeFunctionValue.callback(args)
        of vFunction:
          fn.functionValue.program.call(toArray(args), effectHandler)
        of vLinearFunction:
          fn.linearFunctionValue.program.call(args)
        else: raiseAssert("cannot call " & $fn)
      checkEffect val
      put instr.tcall.res, val
    of TupleCall:
      read instr.tupcall
      let fn {.cursor.} = unboxStripType get instr.tupcall.callee
      let args = (get instr.tupcall.args).tupleValue.unref # maybe move
      let val =
        case fn.kind
        of vNativeFunction:
          fn.nativeFunctionValue.callback(args.toOpenArray(0, args.len - 1))
        of vFunction:
          fn.functionValue.program.call(args, effectHandler)
        of vLinearFunction:
          fn.linearFunctionValue.program.call(args.toOpenArray(0, args.len - 1))
        else: raiseAssert("cannot call " & $fn)
      checkEffect val
      put instr.tupcall.res, val
    of TryDispatch:
      read instr.tdisp
      let fn {.cursor.} = get instr.tdisp.callee
      let argsVal = get instr.tdisp.args
      let t = fn.getType
      # XXX no native type normalization here
      assert t.kind == tyFunction, $t#t.kind == tyInstance and t.base.nativeType == tyFunction, $t
      let argt = t.nativeArgs[0]
      if argsVal.checkType(argt):
        let args = argsVal.tupleValue.unref
        let fn = unboxStripType fn
        let val =
          case fn.kind
          of vNativeFunction:
            fn.nativeFunctionValue.callback(args.toOpenArray(0, args.len - 1))
          of vFunction:
            fn.functionValue.program.call(args, effectHandler)
          of vLinearFunction:
            fn.linearFunctionValue.program.call(args.toOpenArray(0, args.len - 1))
          else: raiseAssert("cannot call " & $fn)
        checkEffect val
        put instr.tdisp.res, val
        jump instr.tdisp.successPos
    of ArmType:
      read instr.armt
      let tVal = get(instr.armt.typ)
      assert tVal.kind == vType
      let t = tVal.typeValue.type.unwrapTypeType
      makeTyped(getMut(instr.armt.val), t)
    of CheckType:
      read instr.binary
      let val = get(instr.binary.arg1)
      let tVal = get(instr.binary.arg2)
      assert tVal.kind == vType
      let t = tVal.typeValue.type.unwrapTypeType
      put instr.binary.res, toValue val.checkType(t)
    of ArmStack:
      read instr.arm
      let fn = get(instr.arm.fun)
      case fn.kind
      of vFunction:
        fn.functionValue.program.memory.set(instr.arm.ind, get(instr.arm.val))
      of vLinearFunction:
        fn.linearFunctionValue.program.constants[instr.arm.ind] = get instr.arm.val
      else: raiseAssert("cannot arm stack of " & $fn)
    of RefreshStack:
      read instr.rfs
      let fn = get(instr.rfs.fun)
      case fn.kind
      of vFunction:
        # XXX [function-arm, needs-testing] ??? uncommented should be correct but not tested
        #fn.functionValue.program.stack = fn.functionValue.program.stack.shallowRefresh()
        let oldFn = fn.functionValue
        getMut(instr.rfs.fun).functionValue = oldFn.shallowRefresh()
      of vLinearFunction:
        let oldFn = fn.linearFunctionValue
        getMut(instr.rfs.fun).linearFunctionValue = oldFn.shallowRefresh()
      else: raiseAssert("cannot refresh stack of " & $fn)
    of JumpPoint:
      read instr.jpt
      assert i == lf.jumpLocations[instr.jpt.loc.int]
    of IfTrueJump:
      read instr.iftj
      let cond = get(instr.iftj.cond)
      assert cond.kind == vBool
      if cond.boolValue:
        jump instr.iftj.truePos
    of IfFalseJump:
      read instr.iffj
      let cond = get(instr.iffj.cond)
      assert cond.kind == vBool
      if not cond.boolValue:
        jump instr.iffj.falsePos
    of Jump:
      read instr.jmp
      jump instr.jmp.pos
    of EmitEffect:
      read instr.emit
      var eff = Value(kind: vEffect)
      eff.effectValue.store get(instr.emit.effect)
      checkEffect eff
    of PushEffectHandler:
      read instr.pueh
      let h = unboxStripType get instr.pueh.handler
      var handler: proc (effect: Value): bool
      case h.kind
      of vNativeFunction:
        let f = h.nativeFunctionValue.callback
        handler = proc (effect: Value): bool =
          f([effect]).toBool
      of vFunction:
        let f = h.functionValue.program
        handler = proc (effect: Value): bool =
          let val = f.call([effect].toArray)
          if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val)):
            return false
          val.toBool
      of vLinearFunction:
        let f = h.linearFunctionValue.program
        handler = proc (effect: Value): bool =
          let val = f.call([effect])
          if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val)):
            return false
          val.toBool
      else: raiseAssert("cannot make " & $h & " into effect handler")
      effectHandlers.add(handler)
    of PopEffectHandler:
      read instr.poeh
      let handler = effectHandlers.pop()
      if unhandledEffect and handler(registers[effectPos]):
        reset(registers[effectPos])
        unhandledEffect = false
    of InitTuple:
      read instr.coll
      put instr.coll.res, toValue initArray[Value](instr.coll.siz)
    of InitList:
      read instr.coll
      put instr.coll.res, toValue newSeq[Value](instr.coll.siz)
    of InitSet:
      read instr.coll
      put instr.coll.res, toValue initHashSet[Value](instr.coll.siz)
    of InitTable:
      read instr.coll
      put instr.coll.res, toValue initTable[Value, Value](instr.coll.siz)
    of GetConstIndex:
      read instr.gci
      let coll = get(instr.gci.coll)
      case coll.kind
      of vArray:
        put instr.gci.res, coll.tupleValue[instr.gci.ind.int]
      of vList:
        put instr.gci.res, coll.listValue.value[instr.gci.ind.int]
      of vString:
        put instr.gci.res, toValue(coll.stringValue.value[instr.gci.ind.int].int)
      else: discard # error
    of SetConstIndex:
      read instr.sci
      let coll = get(instr.sci.coll)
      case coll.kind
      of vArray:
        coll.tupleValue[instr.sci.ind.int] = get(instr.sci.val)
      of vList:
        coll.listValue.value[instr.sci.ind.int] = get(instr.sci.val)
      of vString:
        coll.stringValue.value[instr.sci.ind.int] = get(instr.sci.val).int32Value.char
      else: discard # error
    of GetIndex:
      read instr.gri
      let coll = get instr.gri.coll
      let ind = get instr.gri.ind
      # XXX [memory] maybe prevent dispatch here
      case coll.kind
      of vList:
        put instr.gri.res, coll.listValue.value.unref[ind.unboxStripType.int32Value]
      of vArray:
        put instr.gri.res, coll.tupleValue[ind.unboxStripType.int32Value]
      of vString:
        put instr.gri.res, toValue(coll.stringValue.value.unref[ind.unboxStripType.int32Value].int)
      of vTable:
        put instr.gri.res, coll.tableValue.value[ind]
      else: discard # error
    of SetIndex:
      read instr.sri
      let coll = get instr.sri.coll
      let ind = get instr.sri.ind
      let val = get instr.sri.val
      # XXX [memory] maybe prevent dispatch here
      case coll.kind
      of vList:
        coll.listValue.value.unref[ind.unboxStripType.int32Value] = val
      of vArray:
        coll.tupleValue[ind.unboxStripType.int32Value] = val
      of vString:
        coll.stringValue.value.unref[ind.unboxStripType.int32Value] = val.int32Value.char
      of vTable:
        coll.tableValue.value[ind] = val
      of vSet:
        coll.setValue.value.incl(ind)
      else: discard # error
    of AddInt32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.int32Value
      let b = get(instr.binary.arg2).unboxStripType.int32Value
      put instr.binary.res, toValue(a + b)
    of SubInt32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.int32Value
      let b = get(instr.binary.arg2).unboxStripType.int32Value
      put instr.binary.res, toValue(a - b)
    of MulInt32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.int32Value
      let b = get(instr.binary.arg2).unboxStripType.int32Value
      put instr.binary.res, toValue(a * b)
    of DivInt32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.int32Value
      let b = get(instr.binary.arg2).unboxStripType.int32Value
      put instr.binary.res, toValue(a div b)
    of AddFloat32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.float32Value
      let b = get(instr.binary.arg2).unboxStripType.float32Value
      put instr.binary.res, toValue(a + b)
    of SubFloat32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.float32Value
      let b = get(instr.binary.arg2).unboxStripType.float32Value
      put instr.binary.res, toValue(a - b)
    of MulFloat32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.float32Value
      let b = get(instr.binary.arg2).unboxStripType.float32Value
      put instr.binary.res, toValue(a * b)
    of DivFloat32:
      read instr.binary
      let a = get(instr.binary.arg1).unboxStripType.float32Value
      let b = get(instr.binary.arg2).unboxStripType.float32Value
      put instr.binary.res, toValue(a / b)
    of NegInt32:
      read instr.unary
      let a = get(instr.unary.arg).unboxStripType.int32Value
      put instr.unary.res, toValue(-a)
    of NegFloat32:
      read instr.unary
      let a = get(instr.unary.arg).unboxStripType.float32Value
      put instr.unary.res, toValue(-a)

proc call*(lf: LinearProgram, args: openarray[Value]): Value =
  var registers = initArray[Value](lf.registerCount)
  
  assert lf.argPositions.len == args.len + 1, $(lf.argPositions, args.len)
  for i in 0 ..< args.len:
    registers[lf.argPositions[i]] = args[i]
  let resultPos = lf.argPositions[args.len]

  if lf.heapSize > 0 or lf.thisIndex >= 0:
    assert lf.heapSize > 0 and lf.thisIndex >= 0, $(lf.heapSize, lf.thisIndex)
    let heap = newMemory(lf.heapSize)
    registers[lf.thisIndex] = toValue(heap)
  
  runOnStack(lf, registers, resultPos)

  result = registers[resultPos]
