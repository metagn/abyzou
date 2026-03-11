import ./[primitives, arrays, treewalk, bytecode]

type
  FunctionKind* = enum Linear, TreeWalk
  Function* = object
    case kind*: FunctionKind
    of Linear: linear*: LinearFunction
    of TreeWalk: tw*: TreeWalkFunction

proc call*(function: Function, args: openarray[Value], effectHandler: EffectHandler = nil): Value =
  case function.kind
  of TreeWalk: call(function.tw, toArray(args), effectHandler)
  of Linear: call(function.linear, args)

proc run*(function: Function, effectHandler: EffectHandler = nil): Value =
  case function.kind
  of TreeWalk: evaluate(function.tw.instruction, function.tw.stack, effectHandler)
  of Linear: call(function.linear, [])
