when (compiles do: import nimbleutils/bridge):
  import nimbleutils/bridge
else:
  import unittest

import abyzou,
  abyzou/repr/[primitives, valueconstr, typebasics, arrays],
  abyzou/vm/[typematch, compilation, programs]

test "type relation":
  check {Int32Ty.match(Float32Ty).level, Float32Ty.match(Int32Ty).level} == {tmNone}
  let a1 = Type(kind: tyTuple, elements: @[ContextTy], varargs: box ExpressionTy)
  let a2 = Type(kind: tyTuple, elements: @[ContextTy, ExpressionTy, ExpressionTy])
  check {a1.match(a2).level, a2.match(a1).level} == {tmAlmostEqual}
  let a3 = Type(kind: tyTuple, elements: @[ContextTy], varargs: box AnyTy)
  let a4 = Type(kind: tyTuple, elements: @[ContextTy])
  check a1.match(a3).level == tmUniversalFalse
  check a3.match(a1).level == tmUniversalTrue
  check {a1.match(a4).level, a4.match(a1).level, a3.match(a4).level, a4.match(a3).level} == {tmAlmostEqual}
  check a1 < a3

test "compile success":
  template working(a) =
    discard compile(a)
  template failing(a) =
    check (
      try:
        discard compile(a)
        false
      except CompileError:
        true)
  working "1 + 1"
  failing "1 + 1.0"
  working "while true, ()"
  failing "while 1.0, ()"

test "eval values":
  var tests = {
    "a = \"abcd\"; a": toValue("abcd"), # breaks arc
    "a = (b = do c = 1); [a, 2, b,  3, c]":
      toValue(@[toValue(1), toValue(2), toValue(1), toValue(3), toValue(1)]),
    "a = (b = do c = 1); (a, 2, b,  3, c, \"ab\")":
      toValue(toArray([toValue(1), toValue(2), toValue(1), toValue(3), toValue(1), toValue("ab")])),
    "a = (b = do c = 1); a + (b + 3) + c": toValue(6),
    "9 * (1 + 4) / 2 - 3f": toValue(19.5),
    "9 * (1 + 4) div 2 - 3": toValue(19),

    # functions:
    "foo(x) = x + 1; foo(3)": toValue(4),
    "a = 1; foo(x) = x + a; foo(3)": toValue(4),
    """
gcd(a: Int, b: Int): Int =
  if b == 0
    a
  else
    gcd(b, a mod b)
gcd(12, 42)
""": toValue(6),
    "foo(x) = x + 1; foo(x: Float) = x - 1.0; foo(3)": toValue(4),
    "foo(x) = x + 1; foo(x: Int) = x - 1; foo(3)": toValue(2),
    "foo(x: Float) = x - 1.0; foo(x) = x + 1; foo(3)": toValue(4),
    "foo(x: Int) = x - 1; foo(x) = x + 1; foo(3)": toValue(2),
    "foo(x) = x + 1; foo(x) = x - 1; foo(3)": toValue(2),
    "foo(x: Int) = if(x == 0, (), (x, foo(x - 1))); foo(5)":
      toValue(toArray([toValue 5,
        toValue(toArray([toValue 4,
          toValue(toArray([toValue 3,
            toValue(toArray([toValue 2,
              toValue(toArray([toValue 1,
                toValue(toArray[Value]([]))]))]))]))]))])),
    """
foo(i: Int) =
  if i == 1
    "a"
  else if i == 2
    "b"
  else
    "c"
[foo(0), foo(1), foo(2), foo(3)]
""": toValue(@[toValue("c"), toValue("a"), toValue("b"), toValue("c")]),
    """
fibo(i: Int): Int =
  if i == 1
    1
  else if i == 2
    1
  else
    fibo(i - 1) + fibo(i - 2)

[fibo(3), fibo(4), fibo(5)]""": toValue(@[toValue(2), toValue(3), toValue(5)]),

    # closures, mutation only through references
    "a = 1; foo() = a; foo()": toValue(1),
    "a = 1; foo() = (b = 2; bar() = (c = 3; (a, b, c)); bar()); foo()": toValue(toArray([toValue(1), toValue(2), toValue(3)])),

    "(true and false, true and true, false and true, false and false)": toValue(toArray([toValue(false), toValue(true), toValue(false), toValue(false)])),
    """
a = 0
(true and (a = a + 1; false), true and (a = a + 1; true), false and (a = a + 1; true), false and (a = a + 1; false), a)""": toValue(toArray([toValue(false), toValue(true), toValue(false), toValue(false), toValue(2)])),
    "i = 5; while(i > 0, i = i - 1); i": toValue(0),
    "1 + 1 == 1 or false": toValue(false),
    "(1, (2, 3), 4)[1][0]": toValue(2),
    "a = (1, (2, 3), 4); a[0] == 1 and a[1][1] == 3": toValue(true),
    "`.[]=`(a: Int, b: Int, c: Int) = a * b + c; 3[4] = 5": toValue(17),
    # also tests generics:
    "a = ref 1; update a, 1 + unref a; unref a": toValue(2),

    # misc
    "[1, 2, 3][0]": toValue(1),
    "x = 1; [1, 2, 3][x]": toValue(2),

    # closures with references (mutable):
    "a = ref 1; foo() = unref a; [foo(), (update(a, 2); foo()), foo()]": toValue(@[toValue(1), toValue(2), toValue(2)]),
    "a = 1; foo() = (b = 2; bar() = (c = 3; (a, b, c)); bar()); foo()": toValue(toArray([toValue(1), toValue(2), toValue(3)])),
    """
foo() =
  x = ref 1
  (getter: (() => unref x),
  setter: ((y: Int) => update(x, y))) 
a = foo()
_ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  x = ref 1
  (getter: (() => unref x),
  setter: ((y: Int) => update(x, y))) 
a = foo()
_ = a.setter.(3)
b = foo()
[a.getter.(), b.getter.()]""": toValue(@[toValue(3), toValue(1)]),
    """
foo() =
  x = ref 1
  (getter: (
    () => unref x),
  setter: (
    (y: Int) => update(x, y))) 
static a = foo()
_ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  x = ref 1
  (getter: (() => unref x),
  setter: ((y: Int) => update(x, y))) 
static
  a = foo()
  _ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  x = ref 1
  (getter: (
    () => unref x),
  setter: (
    (y: Int) => update(x, y))) 
static a = foo()
_ = a.setter.(3)
static b = foo()
c = foo()
[a.getter.(), b.getter.(), c.getter.()]""": toValue(@[toValue(3), toValue(1), toValue(1)]),
    """
foo() =
  x = ref 1
  (getter: (() => unref x),
  setter: ((y: Int) => update(x, y))) 
static
  a = foo()
  _ = a.setter.(3)
  b = foo()
c = foo()
[a.getter.(), b.getter.(), c.getter.()]""": toValue(@[toValue(3), toValue(1), toValue(1)]),

    # closures with pinned captures (mutable):
    "@a = 1; foo() = a; [foo(), (a = 2; foo()), foo()]": toValue(@[toValue(1), toValue(2), toValue(2)]),
    "@a = 1; foo() = (@b = 2; bar() = (@c = 3; (a, b, c)); bar()); foo()": toValue(toArray([toValue(1), toValue(2), toValue(3)])),
    """
foo() =
  @x = 1
  (getter: (() => x),
  setter: ((y: Int) => x = y)) 
a = foo()
_ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  @x = 1
  (getter: (() => x),
  setter: ((y: Int) => x = y)) 
a = foo()
_ = a.setter.(3)
b = foo()
[a.getter.(), b.getter.()]""": toValue(@[toValue(3), toValue(1)]),
    """
foo() =
  @x = 1
  (getter: (
    () => x),
  setter: (
    (y: Int) => x = y)) 
static a = foo()
_ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  @x = 1
  (getter: (() => x),
  setter: ((y: Int) => x = y)) 
static
  a = foo()
  _ = a.setter.(3)
a.getter.()""": toValue(3),
    """
foo() =
  @x = 1
  (getter: (
    () => x),
  setter: (
    (y: Int) => x = y)) 
static a = foo()
_ = a.setter.(3)
static b = foo()
c = foo()
[a.getter.(), b.getter.(), c.getter.()]""": toValue(@[toValue(3), toValue(1), toValue(1)]),
    """
foo() =
  @x = 1
  (getter: (() => x),
  setter: ((y: Int) => x = y)) 
static
  a = foo()
  _ = a.setter.(3)
  b = foo()
c = foo()
[a.getter.(), b.getter.(), c.getter.()]""": toValue(@[toValue(3), toValue(1), toValue(1)]),
  }

  for inp, outp in tests.items:
    {.push warning[BareExcept]: off.}
    try:
      checkpoint inp
      check evaluate(inp) == outp
    except:
      echo "fail: ", (input: inp)
      let ex = parse(inp)
      echo ex
      when false:
        var module = newModule(imports = @[Prelude])
        let body = compile(module.top, ex, +AnyTy)
        echo body
      if getCurrentException() of ref NoOverloadFoundError:
        echo (ref NoOverloadFoundError)(getCurrentException()).scope.variables
      raise
    {.pop.}

import abyzou/library/common

module withVarargsFn:
  define "max", funcTypeWithVarargs(Int32Ty, [], Int32Ty), (doFn do:
    var res = args[0].int32Value
    for i in 1 ..< args.len:
      let el = args[i].int32Value
      if el > res: res = el
    toValue(res))

test "varargs function":
  let libraries = @[Prelude, withVarargsFn()]
  let compiled = compile("""
max(3, 7, 4, 5)
""", libraries)
  check compiled.run() == toValue(7)
  check:
    try:
      discard compile("max(3.0, 4.0, 5.0)", libraries)
      false
    except NoOverloadFoundError:
      true

module withGeneric:
  let T = Type(kind: tyParameter, parameter: newTypeParameter("T"))
  let f = define(result, "foo", funcType(ListTy[T], [T]))
  f.genericParams = @[T.parameter]
  result.define(f)
  let f2 = define(result, "foo", funcType(ListTy[Int32Ty], [Int32Ty]))
  result.define(f2)
  result.module.set f, toValue proc (args: openarray[Value]): Value =
    result = toValue(@[args[0]])
  result.module.set f2, toValue proc (args: openarray[Value]): Value =
    result = toValue(@[toValue(-args[0].int32Value)])

test "generic":
  let libraries = @[Prelude, withGeneric()]
  let compiled = compile("""
(foo(123), foo("abc"))
""", libraries)
  check compiled.run() == toValue(toArray([toValue(@[toValue(-123)]), toValue(@[toValue("abc")])]))

module withGenericMeta:
  let T = Type(kind: tyParameter, parameter: newTypeParameter("T"))
  let f = define(result, "foo", funcType(StatementTy, [ContextTy, ExpressionTy]).withProperties(
    property(Meta, funcType(ListTy[T], [T]))
  ))
  f.genericParams = @[T.parameter]
  result.define(f)
  let f2 = define(result, "foo", funcType(StatementTy, [ContextTy, StatementTy]).withProperties(
    property(Meta, funcType(ListTy[Int32Ty], [Int32Ty]))
  ))
  result.define(f2)
  result.module.set f, toValue proc (args: openarray[Value]): Value =
    let context = args[0].contextValue.value
    result = toValue compile(context.scope, Expression(kind: Array,
      elements: @[args[1].expressionValue]), +AnyTy)
  result.module.set f2, toValue proc (args: openarray[Value]): Value =
    result = toValue Statement(kind: skList,
      knownType: ListTy[Int32Ty],
      elements: @[Statement(kind: skUnaryInstruction,
        knownType: Int32Ty,
        unaryInstructionKind: NegInt,
        unary: args[1].statementValue)])

test "generic meta":
  let libraries = @[Prelude, withGenericMeta()]
  let compiled = compile("""
(foo(123), foo("abc"))
""", libraries)
  check compiled.run() == toValue(toArray([toValue(@[toValue(-123)]), toValue(@[toValue("abc")])]))

module checks:
  fn "assert", [BoolTy], NoneValueTy:
    # could use more info
    if not args[0].boolValue:
      raise newException(AssertionDefect, "assertion failed")

test "examples":
  let libraries = @[Prelude, checks()]
  for f in [
    "examples/binary_search.byz"
  ]:
    let s = when declared(read): read(f) else: readFile(f)
    checkpoint s
    let compiled = compile(s, libraries)
    discard compiled.run() 

