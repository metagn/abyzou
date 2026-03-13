import std/[algorithm, hashes, tables],
  ../lang/[expressions],
  ../repr/[primitives, ids, typebasics, arrays],
  ./[typematch, treewalk, compilation]

proc newVariable*(name: string, knownType: Type = NoType): Variable =
  Variable(id: newVariableId(), name: name, nameHash: name.hash, knownType: knownType)

proc newModule*(parent: Scope = nil, imports: seq[Scope] = @[]): Module =
  result = Module(id: newModuleId(), origin: parent)
  result.top = Scope(module: result, imports: imports)

proc childModule*(scope: Scope): Module =
  result = newModule(parent = scope)

proc childScope*(scope: Scope): Scope =
  result = Scope(parent: scope, module: scope.module)

proc makeStack*(module: Module): Stack =
  result = Stack(stack: initArray[Value](module.stackSlots.len))
  for i in 0 ..< module.stackSlots.len:
    result.stack[i] = module.stackSlots[i].value

proc fillStack(module: Module, stack: Stack) =
  for i in 0 ..< stack.stack.len:
    module.stackSlots[i].value = stack.stack[i]

template withStack*(module: Module, body) =
  let stack {.inject.} = makeStack(module)
  body
  fillStack(module, stack)

proc evaluateStatic*(module: Module, st: Statement): Value =
  module.withStack:
    result = st.evaluate(stack)

proc define*(scope: Scope, variable: Variable, kind = Local) =
  variable.scope = scope
  variable.stackIndex = scope.module.stackSlots.len
  scope.module.stackSlots.add(
    StackSlot(kind: kind, variable: variable))
  scope.variables.add(variable)

proc set*(module: Module, variable: Variable, value: sink Value) =
  assert variable.scope.module == module
  module.stackSlots[variable.stackIndex].value = value

proc evaluateStatic*(scope: Scope, ex: Expression, bound: TypeBound = +AnyTy): Value =
  scope.module.evaluateStatic(scope.compile(ex, bound))

proc setStatic*(variable: Variable, expression: Expression) =
  let value = variable.scope.compile(expression, +variable.knownType)
  variable.knownType = value.knownType
  variable.scope.module.withStack:
    stack.set(variable.stackIndex, value.evaluate(stack))
  variable.evaluated = true

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
    c.stackSlots.add(
      StackSlot(kind: Capture, variable: v,
        value: v.scope.module.stackSlots[v.stackIndex].value))

proc variableGet*(c: Module, r: VariableReference): Statement =
  let t = r.type
  case r.kind
  of Constant:
    result = Statement(kind: skConstant,
      constant: r.variable.scope.module.stackSlots[r.variable.stackIndex].value,
      knownType: t)
  of Local, Argument:
    result = Statement(kind: skVariableGet,
      variableGetIndex: r.variable.stackIndex,
      knownType: t)
  of Capture:
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
  of Constant, Capture:
    raise (ref OutOfScopeModifyError)(expression: source,
      variable: r.variable, referenceKind: r.kind,
      msg: "cannot modify " &
        (if r.kind == Capture: "captured " else: "constant ") &
        r.variable.name & ", use a reference instead")

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
            kind: Capture, captureIndex: -1)
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

proc overloads*(scope: Scope, name: string, bound: TypeBound): seq[VariableReference] =
  result = symbols(scope, name, bound)
  # sort must be stable to preserve definition/import order
  result.sort(
    cmp = proc (a, b: VariableReference): int =
      compare(a.type, b.type),
    order = if bound.variance == Covariant: Ascending else: Descending)
  result.reverse()

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
