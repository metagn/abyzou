import
  std/tables,
  ../language/expressions,
  ../vm/[primitives, compilation, typebasics, guesstype, valueconstr]

proc define*(scope: Scope, n: string, typ: Type): Variable =
  result = newVariable(n, typ)
  scope.define(result)

proc define*(scope: Scope, n: string, typ: Type, x: sink Value) =
  let variable = define(scope, n, typ)
  setTypeIfBoxed(x, typ)
  scope.module.set(variable, x)

proc define*(module: Module, n: string, typ: Type): Variable {.inline.} =
  module.top.define(n, typ)

proc define*(module: Module, n: string, typ: Type, x: sink Value) =
  let variable = define(module, n, typ)
  setTypeIfBoxed(x, typ)
  module.set(variable, x)

proc templType*(arity: int): Type {.inline.} =
  var args = newSeq[Type](arity + 1)
  var bArgs = newSeq[Type](arity)
  args[0] = ScopeTy
  for i in 0 ..< arity:
    args[i + 1] = ExpressionTy
    bArgs[i] = AnyTy
  result = funcType(StatementTy, args)
  result.properties = properties(property(Meta, funcType(AnyTy, bArgs)))

template doTempl*(body): untyped =
  (proc (valueArgs: openarray[Value]): Value {.nimcall.} =
    let scope {.inject, used.} = valueArgs[0].scopeValue
    var args {.inject.} = newSeq[Expression](valueArgs.len - 1)
    for i in 0 ..< args.len:
      args[i] = valueArgs[i + 1].expressionValue
    body)

proc typedTemplType*(arity: int): Type {.inline.} =
  var args = newSeq[Type](arity + 1)
  var bArgs = newSeq[Type](arity)
  args[0] = ScopeTy
  for i in 0 ..< arity:
    args[i + 1] = StatementTy
    bArgs[i] = AnyTy
  result = funcType(StatementTy, args)
  result.properties = properties(property(Meta, funcType(AnyTy, bArgs)))

proc typedTemplType*(realArgs: openarray[Type], returnType: Type): Type {.inline.} =
  var args = newSeq[Type](realArgs.len + 1)
  args[0] = ScopeTy
  for i in 0 ..< realArgs.len:
    args[i + 1] = StatementTy
  result = funcType(StatementTy, args)
  result.properties = properties(property(Meta, funcType(returnType, realArgs)))

template doTypedTempl*(body): untyped =
  (proc (valueArgs: openarray[Value]): Value {.nimcall.} =
    let scope {.inject, used.} = valueArgs[0].scopeValue
    var args {.inject.} = newSeq[Statement](valueArgs.len - 1)
    for i in 0 ..< args.len:
      args[i] = valueArgs[i + 1].statementValue
    body)

template doFn*(body): untyped =
  (proc (args {.inject.}: openarray[Value]): Value {.nimcall.} =
    body)

template module*(moduleName, definitions): untyped {.dirty.} =
  proc `moduleName`*: Scope =
    result = newModule().top
    template define(n: string, typ: Type, x: Value) {.used.} =
      define(result, n, typ, x)
    template define(n: string, x: Value) {.used.} =
      bind getType
      let value = x
      define(n, getType(value), value)
    template define(n: string, typ: Type, x) {.used.} =
      define(n, typ, toValue(x))
    template define(n: string, x) {.used.} =
      define(n, toValue(x))
    template templ(n: string, arity: int, body: untyped) {.used.} =
      define n, templType(arity), doTempl(body)
    template typedTempl(n: string, arity: int, body: untyped) {.used.} =
      define n, typedTemplType(arity), doTypedTempl(body)
    template typedTempl(n: string, realArgs: openarray[Type], returnType: Type, body: untyped) {.used.} =
      define n, typedTemplType(realArgs, returnType), doTypedTempl(body)
    template fn(n: string, arguments: openarray[Type], returnType: Type, body: untyped) {.used.} =
      bind funcType
      define n, funcType(returnType, arguments), doFn(body)
    definitions
