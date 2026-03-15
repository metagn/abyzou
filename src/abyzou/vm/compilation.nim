import
  std/[hashes, tables, sets, strutils, algorithm],
  ../defines,
  ../lang/[expressions, number, shortstring],
  ../repr/[ids, primitives, arrays, typebasics, valueconstr, guesstype],
  ./[typematch, linearizer, programs, treewalk]

type
  CompileError* = object of CatchableError
    expression*: Expression

  TypeBoundMatchError* = object of CompileError
    bound*: TypeBound
    `type`*: Type
  
  NoOverloadFoundError* = object of CompileError
    bound*: TypeBound
    scope*: Scope
  
  CannotCallError* = object of NoOverloadFoundError
    `type`*: Type
    argumentTypes*: seq[Type]
  
  OutOfScopeModifyError* = object of CompileError
    variable*: Variable
    referenceKind*: VariableReferenceKind
  
  OutOfScopeAddressError* = object of CompileError
    innerModule*, outerModule*: Module

proc compile*(scope: Scope, ex: Expression, bound: TypeBound): Statement

template constant*(value: Value, ty: Type): Statement =
  Statement(kind: skConstant, constant: value, knownType: ty)
template constant*(value: untyped, ty: Type): Statement =
  constant(toValue(value), ty)
template constant*(value: string): Statement = constant(value, StringTy)
template constant*(value: int32): Statement = constant(value, Int32Ty)
template constant*(value: uint32): Statement = constant(value, Uint32Ty)
template constant*(value: float32): Statement = constant(value, Float32Ty)

import ./modules
export modules

defineTypeBase Meta, TypeBase(name: "Meta",
  arguments: @[newTypeParameter("", +baseType(FunctionTy))])

proc isNative(bound: TypeBound, nt: NativeType): bool {.inline.} =
  # XXX no native type normalization here
  bound.boundType.kind == nt#bound.boundType.kind == tyInstance and bound.boundType.base.nativeType == nt

proc compileNumber*(ex: Expression, bound: TypeBound): Statement =
  let s = $ex.number
  result = Statement(kind: skConstant)
  case ex.number.kind
  of Integer:
    let val = parseInt(s)
    if isNative(bound, tyFloat32):
      result = constant(val.float32)
    elif val >= 0 and isNative(bound, tyUint32):
      result = constant(val.uint32)
    else:
      result = constant(val.int32)
  of Floating:
    result = constant(parseFloat(s).float32)
  of Unsigned:
    result = constant(parseUInt(s).uint32)

template defaultBound: untyped = +AnyTy
template map(ex: Expression, bound = defaultBound): Statement =
  compile(scope, ex, bound)
template forward(ex: Expression): Statement =
  compile(scope, ex, bound)
proc isSingleColon(e: Expression): bool =
  e.kind == Symbol and e.symbol == short":"

proc compileCall*(scope: Scope, ex: Expression, bound: TypeBound,
  argumentStatements: sink seq[Statement] = newSeq[Statement](ex.arguments.len)): Statement

template same(a, b: Expression): bool = system.`==`(a, b)

proc compileProperty*(scope: Scope, ex: Expression, lhs: Statement, name: string, bound: TypeBound): Statement =
  result = nil
  if lhs.knownType.kind == tyTuple and lhs.knownType.elementNames.contains(name):
    let ind = lhs.knownType.elementNames[name]
    result = Statement(kind: skGetIndex,
      knownType: lhs.knownType.nth(ind),
      getIndexAddress: lhs,
      getIndex: ind)
  else:
    let ident = Expression(kind: Name, identifier: "." & name)
    try:
      result = forward(
        Expression(kind: PathCall,
          address: ident,
          arguments: @[ex.left]))
    except NoOverloadFoundError as e:
      if not same(ident, e.expression):
        raise

proc compileMetaCall*(scope: Scope, name: string, ex: Expression, bound: TypeBound, argumentStatements: var seq[Statement]): Statement =
  result = nil
  var argumentTypes = newSeq[Type](ex.arguments.len)
  for t in argumentTypes.mitems: t = AnyTy
  # XXX [macros] validate output statement
  var realArgumentTypes = newSeq[Type](ex.arguments.len + 1)
  realArgumentTypes[0] = ContextTy
  for i in 1 ..< realArgumentTypes.len:
    realArgumentTypes[i] = union(ExpressionTy, StatementTy)
  # get all metas first and type statements accordingly
  let funcTy = funcType(if bound.variance == Covariant: AnyTy else: bound.boundType, argumentTypes)
  var allMetas = overloads(scope, name,
    *funcType(StatementTy, realArgumentTypes).withProperties(
      property(Meta, funcTy)))
  if allMetas.len != 0:
    var makeStatement = newSeq[bool](ex.arguments.len)
    var metaTypes = newSeq[Type](allMetas.len)
    for i, v in allMetas:
      let ty = v.type
      let metaTy = v.type.properties[Meta].instanceArgs[0]
      metaTypes[i] = metaTy
      for i in 0 ..< ex.arguments.len:
        if matchBound(+StatementTy, ty.param(i + 1)):
          makeStatement[i] = true
          # this should be correct but it was commonSubType before
          argumentTypes[i] = commonSuperType(argumentTypes[i], metaTy.param(i))
    for i, x in makeStatement:
      if x:
        try:
          argumentStatements[i] = map(ex.arguments[i], +argumentTypes[i])
        except NoOverloadFoundError as e:
          if same(e.expression, ex.arguments[i]):
            reset(allMetas)
            break
          continue
        except TypeBoundMatchError as e:
          if same(e.expression, ex.arguments[i]):
            reset(allMetas)
            break
          continue
        argumentTypes[i] = commonSubType(argumentTypes[i], argumentStatements[i].knownType)
    var superMetas, subMetas: typeof(allMetas)
    for i, m in allMetas:
      let mt = metaTypes[i]
      if matchBound(+mt,
        funcType(if bound.variance == Contravariant: AnyTy else: bound.boundType, argumentTypes)):
        superMetas.add(m)
      if matchBound(
        +funcType(if bound.variance == Covariant: AllTy else: bound.boundType, argumentTypes),
        mt):
        subMetas.add(m)
    superMetas.sort(
      cmp = proc (a, b: VariableReference): int =
        compare(a.type, b.type),
      order = Descending)
    subMetas.sort(
      cmp = proc (a, b: VariableReference): int =
        compare(a.type, b.type),
      order = Ascending)
    if superMetas.len != 0:
      let meta = superMetas[0]
      let ty = meta.type
      var arguments = newSeq[Statement](ex.arguments.len + 1)
      arguments[0] = constant(Context(scope: scope, bound: bound), ContextTy)
      for i in 0 ..< ex.arguments.len:
        if matchBound(+StatementTy, ty.param(i + 1)):
          arguments[i + 1] = constant(argumentStatements[i], StatementTy)
        else:
          arguments[i + 1] = constant(copy ex.arguments[i], ExpressionTy)
      let call = Statement(kind: skFunctionCall,
        callee: variableGet(scope.module, meta),
        arguments: arguments)
      result = scope.module.evaluateStatic(call).statementValue
    elif subMetas.len != 0:
      # XXX [typematch, macros] sub meta dispatch, needs better output and described semantics
      var argumentValues = newSeq[Variable](ex.arguments.len)
      var dispatches: seq[tuple[condition, body: Statement]]
      for d in subMetas:
        var arguments = initArray[Value](ex.arguments.len + 1)
        arguments[0] = toValue Context(scope: scope, bound: bound)
        var variableCheckTypes = newSeq[Type](ex.arguments.len)
        var noMatch = false
        let metaTy = d.type.properties[Meta].instanceArgs[0].nativeArgs[0]
        var newVariables: seq[(Statement, Variable)]
        for i in 0 ..< ex.arguments.len:
          if matchBound(+StatementTy, d.type.param(i + 1)):
            let st = argumentStatements[i]
            let matchTy = metaTy.nth(i)
            if st.isNil or not match(matchTy, st.knownType).matches:
              noMatch = true
              break
            var v = argumentValues[i]
            if v.isNil:
              v = newVariable("arg" & $i, st.knownType)
              v.hidden = true
              newVariables.add((st, v))
              argumentValues[i] = v
            variableCheckTypes[i] = matchTy
        if noMatch: continue
        var variableAssignments = newSeqOfCap[Statement](newVariables.len + 1)
        for st, v in newVariables.items:
          scope.define(v)
          variableAssignments.add(Statement(kind: skVariableSet,
            variableSetIndex: v.stackIndex,
            variableSetValue: st,
            knownType: v.knownType))
        for i in 0 ..< ex.arguments.len:
          if not variableCheckTypes[i].isNoType:
            arguments[i + 1] = toValue Statement(kind: skVariableGet,
              variableGetIndex: argumentValues[i].stackIndex,
              knownType: argumentValues[i].knownType)
          else:
            arguments[i + 1] = toValue copy ex.arguments[i]
        var argumentStatement = newSeq[Statement](arguments.len)
        for i, a in arguments: argumentStatement[i] = constant(a, a.getType)
        let call = Statement(kind: skFunctionCall,
          callee: variableGet(scope.module, d),
          arguments: argumentStatement)
        let body = scope.module.evaluateStatic(call).statementValue
        var operands: seq[Statement]
        for i, checkType in variableCheckTypes:
          if not checkType.isNoType:
            operands.add(Statement(kind: skBinaryInstruction, binaryInstructionKind: CheckType,
              binary1: arguments[i + 1].statementValue,
              binary2: constant(toValue(checkType), TypeTy[checkType]),
              knownType: BoolTy))
        var cond = if operands.len == 0: constant(toValue true, BoolTy) else: operands[^1]
        if operands.len > 1:
          for i in countdown(operands.len - 2, 0):
            cond = Statement(kind: skIf,
              ifCond: operands[i],
              ifTrue: cond,
              ifFalse: constant(false, BoolTy),
              knownType: BoolTy)
        if variableAssignments.len != 0:
          variableAssignments.add(cond)
          cond = Statement(kind: skSequence,
            sequence: variableAssignments,
            knownType: BoolTy)
        dispatches.add((cond, body))
      if dispatches.len != 0:
        result = Statement(kind: skNone, knownType: AllTy) # should be error 
        for i in countdown(dispatches.len - 1, 0):
          let (cond, body) = dispatches[i]
          result = Statement(kind: skIf,
            ifCond: cond,
            ifTrue: body,
            ifFalse: result,
            knownType: commonSuperType(result.knownType, body.knownType))

proc compileRuntimeCall*(scope: Scope, ex: Expression, bound: TypeBound,
  argumentStatements: var seq[Statement],
  argumentTypes: var seq[Type], 
  functionType: var Type): Statement =
  result = nil
  for i in 0 ..< ex.arguments.len:
    if argumentStatements[i].isNil:
      argumentStatements[i] = map(ex.arguments[i])
    argumentTypes[i] = argumentStatements[i].knownType
  functionType = funcType(if bound.variance == Contravariant: AnyTy else: bound.boundType, argumentTypes)
  # lowest supertype function:
  try:
    # XXX [tuple, functions] named arguments
    var withConstructor = functionType
    withConstructor.nativeArgs[0] = TupleConstructorTy[withConstructor.nativeArgs[0]]
    let callee = map(ex.address, -withConstructor)
    reorderTupleConstructor(withConstructor.nativeArgs[0].nativeArgs[0],
      callee.knownType.nativeArgs[0],
      argumentStatements)
    result = Statement(kind: skFunctionCall,
      knownType: callee.knownType.nativeArgs[1],
      callee: callee,
      arguments: argumentStatements)
  except NoOverloadFoundError as e:
    # dispatch lowest subtype functions in order:
    if same(e.expression, ex.address) and ex.address.isIdentifier(name):
      functionType.nativeArgs[1] =
        if bound.variance == Covariant:
          AllTy
        else:
          bound.boundType
      let subs = overloads(scope, name, +functionType)
      if subs.len != 0:
        # structured like this to make refc work
        result = Statement(kind: skDispatch,
          knownType: AllTy,
          dispatchees: newSeq[(seq[Type], Statement)](subs.len),
          dispatchArguments: argumentStatements)
        for i in 0 ..< result.dispatchees.len:
          let t = subs[i].type
          var argTypes = newSeq[Type](argumentStatements.len)
          for j in 0 ..< argumentStatements.len:
            let pt = t.param(j)
            let m = match(-argumentTypes[j], pt)
            if m.matches:
              # optimize checking types we know match
              # XXX [typematch, type-arming] do this recursively using deep matches for some types
              argTypes[j] = AnyTy
            else:
              argTypes[j] = pt
          result.dispatchees[i] = (argTypes, variableGet(scope.module, subs[i]))
          result.knownType = commonSuperType(result.knownType, t.nativeArgs[1])
            # could allow union here

proc compileCall*(scope: Scope, ex: Expression, bound: TypeBound,
  argumentStatements: sink seq[Statement] = newSeq[Statement](ex.arguments.len)): Statement =
  if ex.address.isIdentifier(name):
    # meta calls take evaluation priority in overloading with runtime calls
    result = compileMetaCall(scope, name, ex, bound, argumentStatements)
  if result.isNil:
    var argumentTypes = newSeq[Type](ex.arguments.len)
    var functionType: Type
    result = compileRuntimeCall(scope, ex, bound, argumentStatements, argumentTypes, functionType)
    assert not functionType.isNoType
    # .call, should recurse but compiled arguments should be reused:
    if result.isNil:
      let callee = map ex.address
      argumentStatements.insert(callee, 0)
      argumentTypes.insert(callee.knownType, 0)
      functionType = funcType(if bound.variance == Contravariant: AnyTy else: bound.boundType, argumentTypes)
      let overs = overloads(scope, ".call", -functionType)
      if overs.len != 0:
        let dotCall = variableGet(scope.module, overs[0])
        result = Statement(kind: skFunctionCall,
          knownType: dotCall.knownType.nativeArgs[1],
          callee: callee,
          arguments: argumentStatements)
      else:
        raise (ref CannotCallError)(
          expression: ex.address,
          bound: bound,
          scope: scope,
          argumentTypes: argumentTypes,
          type: callee.knownType,
          msg: "no way to call " & $ex.address & " of type " & $callee.knownType &
            " found for argument types " & $argumentTypes)

proc compileTupleExpression*(scope: Scope, ex: Expression, bound: TypeBound): Statement =
  # XXX [tuple] tuple type sugar?
  if bound.boundType.kind == tyTuple:
    assert bound.boundType.elements.len == ex.elements.len, "tuple bound type lengths do not match"
  result = Statement(kind: skTuple, knownType: Type(kind: tyTuple, elements: newSeqOfCap[Type](ex.elements.len)))
  for i, e in ex.elements:
    var val: Expression
    if e.kind == Colon:
      assert e.left.kind == Name, "tuple field has non-name left hand side on colon expression"
      let name = e.left.identifier
      result.knownType.elementNames[name] = i
      val = e.right
    else:
      val = e
    let element = if bound.boundType.kind == tyTuple:
      map(val, bound.boundType.elements[i] * bound.variance)
    else:
      map val
    result.elements.add(element)
    result.knownType.elements.add(element.knownType)

proc compileArrayExpression*(scope: Scope, ex: Expression, bound: TypeBound): Statement =
  result = Statement(kind: skList, knownType: ListTy[AnyTy])
  var boundSet = isNative(bound, tyList)
  var b =
    if boundSet:
      bound.boundType.nativeArgs[0] * bound.variance
    else:
      defaultBound
  for e in ex.elements:
    let element = map(e, b)
    result.elements.add(element)
    if result.knownType.nativeArgs[0].isNoType or result.knownType.nativeArgs[0] < element.knownType:
      result.knownType.nativeArgs[0] = element.knownType
    if not boundSet:
      b = +element.knownType
      boundSet = true

proc compileSetExpression*(scope: Scope, ex: Expression, bound: TypeBound): Statement =
  if ex.elements.len != 0 and (ex.elements[0].kind == Colon or
    ex.elements[0].isSingleColon):
    result = Statement(kind: skTable, knownType: TableTy[AnyTy, AnyTy])
    var boundSet = isNative(bound, tyTable)
    var (bk, bv) =
      if boundSet:
        (bound.boundType.nativeArgs[0] * bound.variance,
          bound.boundType.nativeArgs[1] * bound.variance)
      else:
        (defaultBound, defaultBound)
    for e in ex.elements:
      if e.isSingleColon: continue
      assert e.kind == Colon, "table literal must only have colon expressions"
      let k = map(e.left, bk)
      let v = map(e.right, bv)
      result.entries.add((key: k, value: v))
      if result.knownType.nativeArgs[0].isNoType or result.knownType.nativeArgs[0] < k.knownType:
        result.knownType.nativeArgs[0] = k.knownType
      if result.knownType.nativeArgs[1].isNoType or result.knownType.nativeArgs[1] < v.knownType:
        result.knownType.nativeArgs[1] = v.knownType
      if not boundSet:
        bk = +k.knownType
        bv = +v.knownType
        boundSet = true
  else:
    result = Statement(kind: skSet, knownType: SetTy[AnyTy])
    var boundSet = isNative(bound, tySet) 
    var b =
      if boundSet:
        bound.boundType.nativeArgs[0] * bound.variance
      else:
        defaultBound
    for e in ex.elements:
      let element = map(e, b)
      result.elements.add(element)
      if result.knownType.nativeArgs[0].isNoType or result.knownType.nativeArgs[0] < element.knownType:
        result.knownType.nativeArgs[0] = element.knownType
      if not boundSet:
        b = +element.knownType
        boundSet = true

proc compileBlock*(scope: Scope, ex: Expression, bound: TypeBound): Statement =
  result = Statement(kind: skSequence)
  for i, e in ex.statements:
    let b =
      if i == ex.statements.high:
        bound
      else:
        -AllTy # like void
    let element = map(e, bound = b)
    result.sequence.add(element)
    if i == ex.statements.high:
      result.knownType = element.knownType

proc compile*(scope: Scope, ex: Expression, bound: TypeBound): Statement =
  case ex.kind
  of None: result = Statement(kind: skNone, knownType: NoType)
  of Number: result = compileNumber(ex, bound)
  of String, SingleQuoteString: result = constant(ex.str)
  of Wrapped: result = forward(ex.wrapped)
  of Name, Symbol:
    # XXX [modules] warn on ambiguity, thankfully recency is accounted for
    let name = if ex.kind == Symbol: $ex.symbol else: ex.identifier
    result = variableGet(scope.module, resolve(scope, ex, name, bound))
  of Dot:
    if ex.right.kind == Name:
      let lhs = map ex.left
      let name = ex.right.identifier
      result = compileProperty(scope, ex, lhs, name, bound)
    if result.isNil:
      result = forward(
        Expression(kind: PathCall,
          address: Expression(kind: Name, identifier: "."),
          arguments: @[ex.left, ex.right]))
  of CallKinds: result = compileCall(scope, ex, bound)
  of Subscript:
    # XXX [types] specialize for generics
    result = forward(Expression(kind: PathCall,
      address: newSymbolExpression(short".[]"),
      arguments: @[ex.address] & ex.arguments))
  of CurlySubscript:
    result = forward(Expression(kind: PathCall,
      address: newSymbolExpression(short".{}"),
      arguments: @[ex.address] & ex.arguments))
  of Colon:
    assert false, "cannot compile lone colon expression " & $ex
  of Comma, Tuple:
    result = compileTupleExpression(scope, ex, bound)
  of ExpressionKind.Array:
    result = compileArrayExpression(scope, ex, bound)
  of Set:
    result = compileSetExpression(scope, ex, bound)
  of Block, SemicolonBlock:
    result = compileBlock(scope, ex, bound)
  if not bound.matchBound(result.knownType):
    raise (ref TypeBoundMatchError)(
      expression: ex,
      bound: bound,
      type: result.knownType,
      msg: "bound " & $bound & " does not match type " & $result.knownType &
        " in expression " & $ex)

proc compile*(context: Context, ex: Expression): Statement {.inline.} =
  # context object is huge so dont use it yet
  result = compile(context.scope, ex, context.bound)

proc compile*(ex: Expression, imports: seq[Scope], bound: TypeBound = +AnyTy): Program =
  var module = newModule(imports = imports)
  let body = compile(module.top, ex, bound)
  if useBytecode:
    let lc = linear(module, body)
    result = Program(kind: Linear, linear: lc.toFunction())
  else:
    result = Program(kind: TreeWalk, tw: TreeWalkProgram(
      instruction: body,#copy(body),
      memory: module.memory.shallowRefresh(),
      thisIndex: module.moduleCaptures.getOrDefault(module, -1)))
