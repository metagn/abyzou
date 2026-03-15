import
  std/[sets, tables],
  ../repr/[primitives, arrays, valueconstr, typebasics],
  ./checktype

proc shallowRefresh*(stack: ModuleStack): ModuleStack {.inline.} =
  result = stack

proc shallowRefresh*(fun: TreeWalkFunction): TreeWalkFunction {.inline.} =
  new(result)
  result[] = fun[]
  result.program.stack = result.program.stack.shallowRefresh()

type EffectHandler* = proc (effect: Value): bool
  ## returns true to continue execution

template toNegatedBool*(val: Value): bool =
  not val.boolValue

template toBool*(val: Value): bool =
  val.boolValue

proc evaluate*(stack: var ModuleStack, ins: Statement, effectHandler: EffectHandler = nil): Value

template runCheckEffect(instr: Statement, stack, effectHandler): Value =
  let val = evaluate(stack, instr, effectHandler)
  if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val.effectValue.unref)):
    return val
  val

proc call*(fun: TreeWalkProgram, args: sink Array[Value], effectHandler: EffectHandler = nil): Value {.inline.} =
  var newStack = fun.stack.shallowRefresh()
  for i in 0 ..< args.len:
    newStack.set(i, args[i])
  #if fun.thisIndex >= 0:
  #  newStack.set(fun.thisIndex, fun)
  result = runCheckEffect(fun.instruction, newStack, effectHandler)

proc run*(fun: TreeWalkProgram, effectHandler: EffectHandler = nil): Value {.inline.} =
  var newStack = fun.stack.shallowRefresh()
  #if fun.thisIndex >= 0:
  #  newStack.set(fun.thisIndex, fun)
  result = runCheckEffect(fun.instruction, newStack, effectHandler)

import ./bytecode

proc call*(fun: Value, args: sink Array[Value], effectHandler: EffectHandler = nil): Value {.inline.} =
  case fun.kind
  of vNativeFunction:
    result = fun.nativeFunctionValue.callback(args.toOpenArray(0, args.len - 1))
  of vFunction:
    result = fun.functionValue.program.call(args, effectHandler)
  of vLinearFunction:
    result = fun.linearFunctionValue.program.call(args.toOpenArray(0, args.len - 1))
  else: raiseAssert("cannot call " & $fun)

proc evaluate*(stack: var ModuleStack, ins: Statement, effectHandler: EffectHandler = nil): Value =
  template run(instr; stack = stack; effectHandler = effectHandler): untyped =
    runCheckEffect(instr, stack, effectHandler)
  let ins = ins[]
  case ins.kind
  of skNone:
    result = Value(kind: vNone)
  of skConstant:
    result = ins.constant
  of skFunctionCall:
    let fn = unboxStripType run ins.callee
    var args = initArray[Value](ins.arguments.len)
    for i in 0 ..< args.len:
      args[i] = run ins.arguments[i]
    result = fn.call(args, effectHandler)
  of skDispatch:
    var args = initArray[Value](ins.dispatchArguments.len)
    for i in 0 ..< args.len:
      args[i] = run ins.dispatchArguments[i]
    block dispatch:
      for ts, fnInstr in ins.dispatchees.items:
        block accepted:
          for i in 0 ..< args.len:
            if not args[i].checkType(ts[i]):
              break accepted
          let fn = unboxStripType run fnInstr
          result = fn.call(args, effectHandler)
          break dispatch
  of skSequence:
    for instr in ins.sequence:
      result = run instr
  of skVariableGet:
    result = stack.get(ins.variableGetIndex)
  of skVariableSet:
    result = run ins.variableSetValue
    stack.set(ins.variableSetIndex, result)
  of skAddressGet:
    let m = unboxStripType run ins.addressGetModule
    assert m.kind == vModule
    result = m.moduleValue.stack.get(ins.addressGetIndex)
  of skAddressSet:
    let m = unboxStripType run ins.addressSetModule
    assert m.kind == vModule
    result = run ins.addressSetValue
    m.moduleValue.stack.set(ins.addressSetIndex, result)
  of skArmStack:
    result = stack.get(ins.armStackFunctionVariable)
    # XXX [function-arm] missing impl for linear function?
    let oldFn = result.functionValue
    let newFn = oldFn.shallowRefresh()
    result = toValue newFn
    # XXX [function-arm, needs-testing] the following should let it arm itself
    stack.set(ins.armStackFunctionVariable, result)
    for a, b in ins.armStackCaptures.items:
      newFn.program.stack.set(a, stack.get(b))
  of skIf:
    let cond = run ins.ifCond
    if cond.toBool:
      result = run ins.ifTrue
    else:
      result = run ins.ifFalse
  of skWhile:
    while (let cond = run ins.whileCond; cond.toBool):
      result = run ins.whileBody
  of skDoUntil:
    while true:
      result = run ins.doUntilBody
      let cond = run ins.doUntilCond
      if cond.toBool:
        break
  of skEmitEffect:
    result = Value(kind: vEffect)
    result.effectValue.store(run ins.effect)
  of skHandleEffect:
    let h = unboxStripType run ins.effectHandler
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
    result = run(ins.effectBody, stack, handler)
  of skTuple:
    if ins.elements.len <= 255:
      var arr = initArray[Value](ins.elements.len)
      for i in 0 ..< arr.len:
        arr[i] = run ins.elements[i]
      result = toValue(arr)
    else:
      var arr = initArray[Value](ins.elements.len)
      for i in 0 ..< arr.len:
        arr[i] = run ins.elements[i]
      result = toValue(arr)
  of skList:
    var arr = newSeq[Value](ins.elements.len)
    for i in 0 ..< arr.len:
      arr[i] = run ins.elements[i]
    result = toValue(arr)
  of skSet:
    var arr = initHashSet[Value](ins.elements.len)
    for e in ins.elements:
      arr.incl(run e)
    result = toValue(arr)
  of skTable:
    var arr = initTable[Value, Value](ins.entries.len)
    for k, v in ins.entries.items:
      arr[run k] = run v
    result = toValue(arr)
  of skGetIndex:
    let x = run ins.getIndexAddress
    case x.kind
    of vList:
      result = x.listValue.value.unref[ins.getIndex]
    of vArray:
      result = x.tupleValue[ins.getIndex]
    of vString:
      result = toValue(x.stringValue.value.unref[ins.getIndex].int)
    else: discard # error
  of skSetIndex:
    let x = run ins.setIndexAddress
    result = run ins.setIndexValue
    case x.kind
    of vList:
      x.listValue.value.unref[ins.setIndex] = result
    of vArray:
      x.tupleValue[ins.setIndex] = result
    of vString:
      assert result.kind == vInt32 and result.int32Value >= 0 and result.int32Value <= 255
      x.stringValue.value.unref[ins.setIndex] = result.int32Value.char
    else: discard # error
  of skBinaryInstruction:
    case ins.binaryInstructionKind
    of AddInt:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.int32Value + b.int32Value)
    of SubInt:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.int32Value - b.int32Value)
    of MulInt:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.int32Value * b.int32Value)
    of DivInt:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.int32Value div b.int32Value)
    of AddFloat:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.float32Value + b.float32Value)
    of SubFloat:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.float32Value - b.float32Value)
    of MulFloat:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.float32Value * b.float32Value)
    of DivFloat:
      let a = unboxStripType run ins.binary1
      let b = unboxStripType run ins.binary2
      result = toValue(a.float32Value / b.float32Value)
    of CheckType:
      let val = run ins.binary1
      let tVal = run ins.binary2
      assert tVal.kind == vType
      let t = tVal.typeValue.type.unwrapTypeType
      result = toValue val.checkType(t)
  of skUnaryInstruction:
    case ins.unaryInstructionKind
    of NegInt:
      let a = unboxStripType run ins.unary
      result = toValue(-a.int32Value)
    of NegFloat:
      let a = unboxStripType run ins.unary
      result = toValue(-a.float32Value)
