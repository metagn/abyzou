import ".."/[primitives, compilation, types, values], ../../language/[expressions, shortstring]

import common

module syntax:
  templ "block", 1:
    let sc = scope.childScope()
    result = toValue sc.compile(args[0], +Ty(Any))
  templ "static", 1:
    let st = scope.compile(args[0], +Ty(Any))
    result = toValue constant(scope.context.evaluateStatic(st.toInstruction), st.knownType)
  
  proc makeFn(scope: Scope, arguments: seq[Expression], body: Expression,
    name: string, returnBound: TypeBound, returnBoundSet: bool): Statement =
    let context = scope.context.childContext()
    let bodyScope = context.top
    var argTypes = newSeq[Type](arguments.len)
    for i in 0 ..< arguments.len:
      var arg = arguments[i]
      if arg.kind == Colon:
        argTypes[i] = scope.evaluateStatic(arg.right, +Type(kind: tyType, typeValue: box Ty(Any))).boxedValue.typeValue
        arg = arg.left
      else:
        argTypes[i] = Ty(Any)
      discard bodyScope.define($arg, argTypes[i])
    var fnType = funcType(returnBound.boundType, argTypes)
    var v: Variable
    if name.len != 0:
      v = scope.define(name, fnType)
    let body = bodyScope.compile(body, returnBound)
    if not v.isNil and not returnBoundSet:
      v.knownType.returnType = body.knownType.box
    bodyScope.context.refreshStack()
    let fun = toValue(
      Function(stack: bodyScope.context.stack.shallowRefresh(), instruction: body.toInstruction))
    if not v.isNil:
      context.refreshStack()
      scope.context.stack.set(v.stackIndex, fun)
    result = Statement(kind: skArmStack,
      knownType: fnType,
      armStackFunction: constant(fun, fnType))

  templ "=>", 2:
    var lhs = args[0]
    var body = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +Type(kind: tyType, typeValue: Ty(Any).box)).boxedValue.typeValue
        lhs = lhs.left
        (+t, true)
      else:
        (+Ty(Any), false)
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
    var lhs = args[0]
    let rhs = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +Type(kind: tyType, typeValue: Ty(Any).box)).boxedValue.typeValue
        lhs = lhs.left
        (+t, true)
      else:
        (+Ty(Any), false)
    case lhs.kind
    of Name, Symbol:
      let name = $lhs
      let value = compile(scope, rhs, bound)
      let v = scope.define(name, if typeSet: bound.boundType else: value.knownType)
      result = toValue variableSet(v.shallowReference, value)
    of CallKinds:
      result = toValue makeFn(scope, lhs.arguments, rhs, $lhs.address, bound, typeSet)
    else: assert false, $lhs
  templ "=", 2:
    var lhs = args[0]
    let rhs = args[1]
    let (bound, typeSet) =
      if lhs.kind == Colon:
        let t = scope.evaluateStatic(lhs.right, +Type(kind: tyType, typeValue: Ty(Any).box)).boxedValue.typeValue
        lhs = lhs.left
        (+t, true)
      else:
        (+Ty(Any), false)
    case lhs.kind
    of Name, Symbol:
      let name = $lhs
      if (let a = scope.overloads(name, bound); a.len != 0):
        let v = a[0]
        let value = compile(scope, rhs, +v.type)
        result = toValue variableSet(v, value)
      else:
        let value = compile(scope, rhs, bound)
        let v = scope.define(name, value.knownType)
        result = toValue variableSet(v.shallowReference, value)
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
  define "if", funcType(Ty(Statement), [Ty(Scope), Ty(Statement), Ty(Expression)]).withProperties(
    property(Meta, toValue funcType(Ty(Any), [Ty(Bool), Ty(Any)]))
  ), toValue proc (valueArgs: openarray[Value]): Value = 
    let sc = valueArgs[0].boxedValue.scopeValue.childScope()
    result = toValue Statement(kind: skIf,
      ifCond: valueArgs[1].boxedValue.statementValue,
      ifTrue: sc.compile(valueArgs[2].boxedValue.expressionValue, +Ty(Any)),
      ifFalse: Statement(kind: skNone))
  define "if", funcType(Ty(Statement), [Ty(Scope), Ty(Statement), Ty(Expression), Ty(Expression)]).withProperties(
    property(Meta, toValue funcType(Ty(Any), [Ty(Bool), Ty(Any), Ty(Any)]))
  ), toValue proc (valueArgs: openarray[Value]): Value = 
    var els = valueArgs[3].boxedValue.expressionValue
    if els.kind == Colon and els.left.isIdentifier(ident) and ident == "else":
      els = els.right
    let scope = valueArgs[0].boxedValue.scopeValue
    let sc = scope.childScope()
    let elsesc = scope.childScope()
    var res = Statement(kind: skIf,
      ifCond: valueArgs[1].boxedValue.statementValue,
      ifTrue: sc.compile(valueArgs[2].boxedValue.expressionValue, +Ty(Any)),
      ifFalse: elsesc.compile(els, +Ty(Any)))
    res.knownType = commonSuperType(res.ifTrue.knownType, res.ifFalse.knownType)
    result = toValue(res)
  define "while", funcType(Ty(Statement), [Ty(Scope), Ty(Statement), Ty(Expression)]).withProperties(
    property(Meta, toValue funcType(union(), [Ty(Bool), union()]))
  ), toValue proc (valueArgs: openarray[Value]): Value = 
    let sc = valueArgs[0].boxedValue.scopeValue.childScope()
    result = toValue Statement(kind: skWhile,
      whileCond: valueArgs[1].boxedValue.statementValue,
      whileBody: sc.compile(valueArgs[2].boxedValue.expressionValue, -union()))
  # todo: let/for
