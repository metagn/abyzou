import std/[algorithm, hashes, tables],
  ../lang/[expressions],
  ../repr/[primitives, ids, typebasics],
  ./[typematch, treewalk]

proc newVariable*(name: string, knownType: Type = NoType): Variable =
  Variable(id: newVariableId(), name: name, nameHash: name.hash, knownType: knownType)

proc newModule*(parent: Scope = nil, imports: seq[Scope] = @[]): Module =
  # XXX [modules] use module registry
  result = Module(id: newModuleId(), origin: parent)
  result.top = Scope(module: result, imports: imports)

proc childModule*(scope: Scope): Module =
  result = newModule(parent = scope)

proc childScope*(scope: Scope): Scope =
  result = Scope(parent: scope, module: scope.module)

proc get*(module: Module, variable: Variable): Value {.inline.} =
  assert variable.scope.module == module
  module.stack.get(variable.stackIndex)

proc getMut*(module: Module, variable: Variable): var Value {.inline.} =
  assert variable.scope.module == module
  module.stack.getMut(variable.stackIndex)

proc set*(module: Module, variable: Variable, value: sink Value) {.inline.} =
  assert variable.scope.module == module
  module.stack.set(variable.stackIndex, value)

proc evaluateStatic*(module: Module, st: Statement): Value =
  result = module.stack.evaluate(st)

proc addStackSlot*(module: Module, kind: VariableReferenceKind, v: Variable) =
  module.stackSlots.add(StackSlot(kind: kind, variable: v))
  if module.stack.stack.len < module.stackSlots.len:
    module.stack.stack.setLen(module.stackSlots.len)

proc addStackSlot*(module: Module, kind: VariableReferenceKind, v: Variable, value: Value) =
  let i = module.stackSlots.len
  module.addStackSlot(kind, v)
  module.stack.set(i, value)

proc define*(scope: Scope, variable: Variable, kind = Local) =
  variable.scope = scope
  variable.stackIndex = scope.module.stackSlots.len
  scope.module.addStackSlot(kind, variable)
  scope.variables.add(variable)

proc evaluateStatic*(scope: Scope, ex: Expression, bound: TypeBound = +AnyTy): Value

proc setStatic*(variable: Variable, expression: Expression)

proc getType*(variable: Variable): Type =
  if variable.knownType.isNoType and not variable.lazyExpression.isNil and not variable.evaluated:
    variable.setStatic(variable.lazyExpression)
  variable.knownType

proc shallowReference*(v: Variable, `type`: Type = v.getType): VariableReference {.inline.} =
  VariableReference(variable: v, type: `type`, kind: Local)

proc capture*(c: Module, v: Variable): int =
  if v.scope.module == c:
    result = v.stackIndex
  else:
    if not c.origin.isNil:
      discard c.origin.module.capture(v)
    result = c.captures.mgetOrPut(v, c.stackSlots.len)
    c.addStackSlot(StaticCapture, v, v.scope.module.get(v))

proc symbols*(scope: Scope, name: string, bound: TypeBound,
  nameHash = name.hash): seq[VariableReference] =
  if scope.isNil: return
  if not scope.parent.isNil:
    result.add(symbols(scope.parent, name, bound, nameHash = nameHash))
  elif not scope.module.origin.isNil:
    for a in symbols(scope.module.origin, name, bound, nameHash = nameHash):
      let b =
        if a.kind == VariableReferenceKind.Constant:
          a
        else:
          VariableReference(variable: a.variable, type: a.type,
            kind: StaticCapture, captureIndex: -1)
      result.add(b)
  for i, im in scope.imports:
    let addrs = symbols(im, name, bound, nameHash = nameHash)
    for a in addrs:
      result.add(VariableReference(variable: a.variable, type: a.type,
        kind: Constant))
  for i, v in scope.variables:
    if (v.nameHash == 0 or v.nameHash == nameHash) and name == v.name and not v.hidden:
      var t = v.getType
      if v.genericParams.len != 0:
        var matches = ParameterInstantiation(strict: true,
          table: initTable[TypeParameter, Type](v.genericParams.len))
        try:
          discard match(t, bound.boundType, matches)
        except ParameterMatchError:
          matches.table.clear()
        if matches.table.len != 0:
          fillParameters(t, matches)
      if bound.matchBound(t):
        result.add(v.shallowReference(t))

proc variableGet*(c: Module, r: VariableReference): Statement

proc variableSet*(c: Module, r: VariableReference, value: Statement, source: Expression = nil): Statement

proc overloads*(scope: Scope, name: string, bound: TypeBound): seq[VariableReference] =
  result = symbols(scope, name, bound)
  # sort must be stable to preserve definition/import order
  result.sort(
    cmp = proc (a, b: VariableReference): int =
      compare(a.type, b.type),
    order = if bound.variance == Covariant: Ascending else: Descending)
  result.reverse()

proc resolve*(scope: Scope, ex: Expression, name: string, bound: TypeBound): VariableReference

import ./compilation

proc evaluateStatic*(scope: Scope, ex: Expression, bound: TypeBound = +AnyTy): Value =
  scope.module.evaluateStatic(scope.compile(ex, bound))

proc setStatic*(variable: Variable, expression: Expression) =
  let value = variable.scope.compile(expression, +variable.knownType)
  variable.knownType = value.knownType
  let val = variable.scope.module.stack.evaluate(value)
  variable.scope.module.stack.set(variable.stackIndex, val)
  variable.evaluated = true

proc variableGet*(c: Module, r: VariableReference): Statement =
  let t = r.type
  case r.kind
  of Constant:
    result = Statement(kind: skConstant,
      constant: r.variable.scope.module.get(r.variable),
      knownType: t)
  of Local, Argument:
    result = Statement(kind: skVariableGet,
      variableGetIndex: r.variable.stackIndex,
      knownType: t)
  of StaticCapture:
    result = Statement(kind: skVariableGet,
      variableGetIndex: c.capture(r.variable),
      knownType: t)

proc variableSet*(c: Module, r: VariableReference, value: Statement, source: Expression = nil): Statement =
  let t = r.type
  case r.kind
  of Local, Argument:
    result = Statement(kind: skVariableSet,
      variableSetIndex: r.variable.stackIndex,
      variableSetValue: value,
      knownType: t)
  of Constant, StaticCapture:
    raise (ref OutOfScopeModifyError)(expression: source,
      variable: r.variable, referenceKind: r.kind,
      msg: "cannot modify " &
        (if r.kind == StaticCapture: "captured " else: "constant ") &
        r.variable.name & ", use a reference instead")

proc resolve*(scope: Scope, ex: Expression, name: string, bound: TypeBound): VariableReference =
  let overloads = overloads(scope, name, bound)
  if overloads.len == 0:
    raise (ref NoOverloadFoundError)(
      expression: ex,
      bound: bound,
      scope: scope,
      msg: "no overloads with bound " & $bound & " for " & $ex)
  result = overloads[0]
  when false:
    # xxx can implement generic evaluation here
    # maybe lazyExpression compiled with a new scope with the type variables
    # but then we would need to save every version
    # can generate new variables but that would fill up scope
    if result.variable.genericParams.len != 0:
      var matches: ParameterInstantiation = initTable[TypeParameter, Type](result.variable.genericParams.len)
      try:
        matchParameters(result.type, bound.boundType, matches)
      except GenericMatchError as e:
        e.expression = ex
        raise e
      block:
        var unmatchedParams: seq[TypeParameter]
        for p in result.variable.genericParams:
          if p notin matches:
            unmatchedParams.add(p)
        if unmatchedParams.len != 0:
          raise (ref GenericUnmatchedError)(
            expression: ex,
            allParameters: result.variable.genericParams,
            matchedParameters: matches)
  if not bound.matchBound(result.type):
    raise (ref TypeBoundMatchError)(
      expression: ex,
      bound: bound,
      type: result.type,
      msg: "bound " & $bound & " does not match type " & $result.type &
       " in expression " & $ex)
