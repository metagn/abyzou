import
  std/tables,
  ../defines,
  ../lang/[expressions, shortstring],
  ../repr/[primitives, typebasics, valueconstr],
  ../vm/[compilation, linearizer]

import common

module syntax:
  templ "block", 1:
    let sc = context.scope.childScope()
    result = toValue sc.compile(args[0], +AnyTy)
  templ "static", 1:
    let st = context.scope.compile(args[0], +AnyTy)
    result = toValue constant(context.scope.module.evaluateStatic(st), st.knownType)

  # XXX [types, macros, functions] add syntax for generic assignments or functions
  proc makeFn(scope: Scope, arguments: seq[Expression], body: Expression,
    name: string, returnBound: TypeBound, returnBoundSet: bool): Statement =
    let bodyModule = scope.childModule()
    let bodyScope = bodyModule.top
    var fnTypeArguments = Type(kind: tyTuple, elements: newSeq[Type](arguments.len))
    for i in 0 ..< arguments.len:
      var arg = arguments[i]
      if arg.kind == Colon:
        fnTypeArguments.elements[i] = scope.evaluateStatic(arg.right, +TypeTy[AnyTy]).typeValue.type.unwrapTypeType
        arg = arg.left
      else:
        fnTypeArguments.elements[i] = AnyTy
      let name = $arg
      if name.len != 0 and name[0] != '_':
        fnTypeArguments.elementNames[name] = i
      let argVar = newVariable(name, fnTypeArguments.elements[i])
      bodyScope.define(argVar, Argument)
    let fnType = FunctionTy[fnTypeArguments, returnBound.boundType]
    var v: Variable
    if name.len != 0:
      v = scope.define(name, fnType)
    else:
      # required for arming stack
      v = newVariable("_lambda", fnType)
      v.hidden = true
      scope.define(v)
    let body = bodyScope.compile(body, returnBound)
    if not v.isNil and not returnBoundSet:
      v.knownType.nativeArgs[1] = body.knownType
    var fun: Value
    if useBytecode:
      let lc = linear(bodyScope.module, body)
      fun = toValue(LinearFunction(
        program: lc.toFunction(),
        type: fnType))
    else:
      let body2 = [body][0]#copy(body) # weird orc bug workaround
      let tw = TreeWalkProgram(
        stack: bodyScope.module.makeStack(),
        instruction: body2)
      fun = toValue(TreeWalkFunction(
        program: tw,
        type: fnType))
    setTypeIfBoxed(fun, fnType)
    var captures: seq[tuple[index, valueIndex: int]]
    for c, ci in bodyModule.captures:
      captures.add((ci, bodyModule.origin.module.capture(c)))
    result = constant(fun, fnType)
    if not v.isNil:
      if captures.len == 0:
        scope.module.set(v, fun)
      # required so that recursive functions can capture themselves in next statement:
      result = variableSet(scope.module, v.shallowReference, result) # , source = lhs
    if captures.len != 0:
      result = Statement(kind: skSequence, knownType: fnType, sequence: @[
        result, 
        Statement(kind: skArmStack,
          knownType: fnType,
          armStackFunctionVariable: v.stackIndex,
          armStackCaptures: captures)])

  templ "=>", 2:
    let scope = context.scope
    var lhs = args[0]
    var body = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +TypeTy[AnyTy]).typeValue.type.unwrapTypeType
        lhs = lhs.left
        (+t, true)
      else:
        (+AnyTy, false)
    let (name, arguments) =
      if lhs.kind in CallKinds:
        ($lhs.address, lhs.arguments)
      elif lhs.kind == Wrapped:
        ("", @[lhs.wrapped])
      else:
        ("", lhs.elements)
    result = toValue makeFn(scope, arguments, body, name, bound, typeSet)
  templ ":=", 2:
    # generics?
    let scope = context.scope
    var lhs = args[0]
    let rhs = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +TypeTy[AnyTy]).typeValue.type.unwrapTypeType
        lhs = lhs.left
        (+t, true)
      else:
        (+AnyTy, false)
    case lhs.kind
    of Name, Symbol:
      let name = $lhs
      let value = compile(scope, rhs, bound)
      let v = scope.define(name, if typeSet: bound.boundType else: value.knownType)
      result = toValue variableSet(scope.module, v.shallowReference, value, source = lhs)
    of CallKinds:
      result = toValue makeFn(scope, lhs.arguments, rhs, $lhs.address, bound, typeSet)
    else: assert false, $lhs
  templ "=", 2:
    let scope = context.scope
    var lhs = args[0]
    let rhs = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +TypeTy[AnyTy]).typeValue.type.unwrapTypeType
        lhs = lhs.left
        (+t, true)
      else:
        (+AnyTy, false)
    case lhs.kind
    of Name, Symbol:
      let name = $lhs
      if (let a = scope.overloads(name, bound); a.len != 0):
        let v = a[0]
        let value = compile(scope, rhs, +v.type)
        result = toValue variableSet(scope.module, v, value, source = lhs)
      else:
        let value = compile(scope, rhs, bound)
        let v = scope.define(name, value.knownType)
        result = toValue variableSet(scope.module, v.shallowReference, value, source = lhs)
    of CallKinds:
      result = toValue makeFn(scope, lhs.arguments, rhs, $lhs.address, bound, typeSet)
    of Subscript:
      result = toValue compile(scope, Expression(kind: PathCall,
        address: newSymbolExpression(short".[]="),
        arguments: @[lhs.address] & lhs.arguments & rhs), bound)
    of CurlySubscript:
      result = toValue compile(scope, Expression(kind: PathCall,
        address: newSymbolExpression(short".{}="),
        arguments: @[lhs.address] & lhs.arguments & rhs), bound)
    else: assert false, $lhs
  # todo: let/for
