import ../vm/[primitives, compilation, valueconstr, typebasics]

import common

module types:
  define "Any", AnyTy
  define "All", AllTy
  define "None", NoneValueTy
  define "none", NoneValueTy, Value(kind: vNone)
  typedTempl "type_of", [AnyTy], TypeTy[AnyTy]:
    let t = args[0].knownType
    result = toValue constant(t, TypeTy[t])
  {.push hints: off.}
  typedTempl "cast", [AnyTy, TypeTy[AnyTy]], AnyTy:
    let newStmt = new(Statement)
    newStmt[] = args[0][]
    newStmt.knownType = context.scope.module.evaluateStatic(args[1].toInstruction).typeValue.type.unwrapTypeType
    result = toValue newStmt
  {.pop.}
  when false:
    let anyType = Type(kind: tyType, typeValue: AnyTy)
    fn "functionType", [anyType], anyType:
      result = toValue Type(kind: tyFunction, arguments: seq[Type] @[], returnType: args[0].typeValue)
    fn "functionType", [anyType, anyType], anyType:
      result = toValue Type(kind: tyFunction, arguments: @[args[0].typeValue], returnType: args[1].typeValue)
  # XXX (types) .call / .[] for type arguments, and generics in general
