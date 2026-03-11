import ./[primitives, arrays, treewalk, bytecode]

type
  ProgramKind* = enum Linear, TreeWalk
  Program* = object
    case kind*: ProgramKind
    of Linear: linear*: LinearProgram
    of TreeWalk: tw*: TreeWalkProgram

proc call*(function: Program, args: openarray[Value], effectHandler: EffectHandler = nil): Value =
  case function.kind
  of TreeWalk: call(function.tw, toArray(args), effectHandler)
  # XXX push initial effect handler?
  of Linear: call(function.linear, args)

proc run*(program: Program, effectHandler: EffectHandler = nil): Value =
  case program.kind
  of TreeWalk: evaluate(program.tw.instruction, program.tw.stack, effectHandler)
  # XXX push initial effect handler?
  of Linear: call(program.linear, [])
