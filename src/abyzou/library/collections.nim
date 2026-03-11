import
  ../vm/[primitives, compilation, valueconstr, typebasics]

import common

module collections:
  block reference:
    # todo: better names (maybe just copy nim)
    let T = Type(kind: tyParameter, parameter: newTypeParameter("T"))
    let rf = define(result, "ref", funcType(ReferenceTy[T], [T]))
    rf.genericParams = @[T.parameter]
    result.define(rf)
    let urf = define(result, "unref", funcType(T, [ReferenceTy[T]]))
    urf.genericParams = @[T.parameter]
    result.define(urf)
    let upd = define(result, "update", funcType(NoneValueTy, [ReferenceTy[T], T]))
    upd.genericParams = @[T.parameter]
    result.define(upd)
    result.module.set rf, toValue proc (args: openarray[Value]): Value =
      result = Value(kind: vReference)
      new(result.referenceValue.realRef)
      result.referenceValue.realRef[] = args[0]
    result.module.set urf, toValue proc (args: openarray[Value]): Value =
      args[0].referenceValue.unref
    result.module.set upd, toValue proc (args: openarray[Value]): Value =
      args[0].referenceValue.realRef[] = args[1]
  # XXX (8) maybe move this to compilation, or allow dynamic dispatch of .[] some other way
  define ".[]", funcType(StatementTy, [ScopeTy, StatementTy, StatementTy]).withProperties(
    property(Meta, funcType(AnyTy, [Type(kind: tyBase, typeBase: TupleTy), Int32Ty]))
  ), toValue proc (valueArgs: openarray[Value]): Value =
    let scope = valueArgs[0].scopeValue
    let index = scope.module.evaluateStatic(valueArgs[2].statementValue.toInstruction)
    let nthType = valueArgs[1].statementValue.knownType.nth(index.int32Value)
    result = toValue Statement(kind: skGetIndex,
      knownType: nthType,
      getIndexAddress: valueArgs[1].statementValue,
      getIndex: index.int32Value)
  block list:
    let T = Type(kind: tyParameter, parameter: newTypeParameter("T"))
    let get = define(result, ".[]", funcType(T, [ListTy[T], Int32Ty]))
    get.genericParams = @[T.parameter]
    result.define(get)
    let size = define(result, "size", funcType(Int32Ty, [ListTy[T]]))
    size.genericParams = @[T.parameter]
    result.define(size)
    result.module.set get, toValue proc (args: openarray[Value]): Value =
      args[0].listValue.value[args[1].int32Value]
    result.module.set size, toValue proc (args: openarray[Value]): Value =
      args[0].listValue.value.len.int32.toValue
