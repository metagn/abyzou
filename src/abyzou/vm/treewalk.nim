import
  std/[sets, tables],
  ./[primitives, arrays, valueconstr, checktype, typebasics]

proc get*(stack: Stack, index: int): lent Value {.inline.} =
  stack.stack[index]
proc set*(stack: Stack, index: int, value: sink Value) {.inline.} =
  stack.stack[index] = value

proc shallowRefresh*(stack: Stack): Stack =
  result = Stack(stack: initArray[Value](stack.stack.len))
  for i in 0 ..< stack.stack.len:
    result.stack[i] = stack.stack[i]

type EffectHandler* = proc (effect: Value): bool
  ## returns true to continue execution

template toNegatedBool*(val: Value): bool =
  not val.boolValue

template toBool*(val: Value): bool =
  val.boolValue

proc evaluate*(ins: Instruction, stack: Stack, effectHandler: EffectHandler = nil): Value

template runCheckEffect(instr: Instruction, stack, effectHandler): Value =
  let val = evaluate(instr, stack, effectHandler)
  if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val.effectValue.unref)):
    return val
  val

proc call*(fun: TreeWalkFunction, args: sink Array[Value], effectHandler: EffectHandler = nil): Value {.inline.} =
  var newStack = fun.stack.shallowRefresh()
  for i in 0 ..< args.len:
    newStack.set(i, args[i])
  result = runCheckEffect(fun.instruction, newStack, effectHandler)

import ./bytecode

proc call*(fun: Value, args: sink Array[Value], effectHandler: EffectHandler = nil): Value {.inline.} =
  case fun.kind
  of vNativeFunction:
    result = fun.nativeFunctionValue(args.toOpenArray(0, args.len - 1))
  of vFunction:
    result = fun.functionValue.value.call(args, effectHandler)
  of vLinearFunction:
    result = fun.linearFunctionValue.value.call(args.toOpenArray(0, args.len - 1))
  else: raiseAssert("cannot call " & $fun)

proc evaluate*(ins: Instruction, stack: Stack, effectHandler: EffectHandler = nil): Value =
  template run(instr; stack = stack; effectHandler = effectHandler): untyped =
    runCheckEffect(instr, stack, effectHandler)
  let ins = ins[]
  case ins.kind
  of NoOp:
    result = Value(kind: vNone)
  of Constant:
    result = ins.constantValue
  of FunctionCall:
    let fn = unboxStripType run ins.function
    var args = initArray[Value](ins.arguments.len)
    for i in 0 ..< args.len:
      args[i] = run ins.arguments[i]
    result = fn.call(args, effectHandler)
  of Dispatch:
    var args = initArray[Value](ins.dispatchArguments.len)
    for i in 0 ..< args.len:
      args[i] = run ins.dispatchArguments[i]
    block dispatch:
      for ts, fnInstr in ins.dispatchFunctions.items:
        block accepted:
          for i in 0 ..< args.len:
            if not args[i].checkType(ts[i]):
              break accepted
          let fn = unboxStripType run fnInstr
          result = fn.call(args, effectHandler)
          break dispatch
  of CheckType:
    let val = run ins.binary1
    let tVal = run ins.binary2
    assert tVal.kind == vType
    let t = tVal.typeValue.type.unwrapTypeType
    result = toValue val.checkType(t)
  of Sequence:
    for instr in ins.sequence:
      result = run instr
  of VariableGet:
    result = stack.get(ins.variableGetIndex)
  of VariableSet:
    result = run ins.variableSetValue
    stack.set(ins.variableSetIndex, result)
  of ArmStack:
    result = run ins.armStackFunction
    var fun = result.functionValue.value
    for a, b in ins.armStackCaptures.items:
      fun.stack.set(a, stack.get(b))
    fun.stack = fun.stack.shallowRefresh()
    result = toValue fun
  of If:
    let cond = run ins.ifCondition
    if cond.toBool:
      result = run ins.ifTrue
    else:
      result = run ins.ifFalse
  of While:
    while (let cond = run ins.whileCondition; cond.toBool):
      result = run ins.whileTrue
  of DoUntil:
    while true:
      result = run ins.doUntilTrue
      let cond = run ins.doUntilCondition
      if cond.toBool:
        break
  of EmitEffect:
    result = Value(kind: vEffect)
    result.effectValue.store(run ins.effect)
  of HandleEffect:
    let h = unboxStripType run ins.effectHandler
    var handler: proc (effect: Value): bool
    case h.kind
    of vNativeFunction:
      let f = h.nativeFunctionValue
      handler = proc (effect: Value): bool =
        f([effect]).toBool
    of vFunction:
      let f = h.functionValue.value
      handler = proc (effect: Value): bool =
        let val = f.call([effect].toArray)
        if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val)):
          return false
        val.toBool
    of vLinearFunction:
      let f = h.linearFunctionValue.value
      handler = proc (effect: Value): bool =
        let val = f.call([effect])
        if val.kind == vEffect and (effectHandler.isNil or not effectHandler(val)):
          return false
        val.toBool
    else: raiseAssert("cannot make " & $h & " into effect handler")
    result = run(ins.effectEmitter, stack, handler)
  of BuildTuple:
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
  of BuildList:
    var arr = newSeq[Value](ins.elements.len)
    for i in 0 ..< arr.len:
      arr[i] = run ins.elements[i]
    result = toValue(arr)
  of BuildSet:
    var arr = initHashSet[Value](ins.elements.len)
    for e in ins.elements:
      arr.incl(run e)
    result = toValue(arr)
  of BuildTable:
    var arr = initTable[Value, Value](ins.entries.len)
    for k, v in ins.entries.items:
      arr[run k] = run v
    result = toValue(arr)
  of GetIndex:
    let x = run ins.getIndexAddress
    case x.kind
    of vList:
      result = x.listValue.value.unref[ins.getIndex]
    of vArray:
      result = x.tupleValue[ins.getIndex]
    of vString:
      result = toValue(x.stringValue.value.unref[ins.getIndex].int)
    else: discard # error
  of SetIndex:
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
  of NegInt:
    let a = unboxStripType run ins.unary
    result = toValue(-a.int32Value)
  of NegFloat:
    let a = unboxStripType run ins.unary
    result = toValue(-a.float32Value)
