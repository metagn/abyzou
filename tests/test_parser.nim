when (compiles do: import nimbleutils/bridge):
  import nimbleutils/bridge
else:
  import unittest

import abyzou

test "simple code":
  let tests = {
    "a": "a",
    "a.b": "a.b",
    "a+b": "(a + b)",
    "a + b": "(a + b)",
    "a +b": "a((+ b))",
    "a+ b": "(a +)(b)",
    "a.b+c/2": "((a.b + c) / 2)",
    "a(b, c)": "a(b, c)",
    "a + b - c": "((a + b) - c)",
    "a * b / c ^ d ^ e << f | g + h < i as j":
      "((((a * b) / (c ^ (d ^ e))) << ((f | g) + h)) < (i as j))",
    "a\nb": """(
  a;
  b
)""",
    "a\nb\nc": """(
  a;
  b;
  c
)""",
    "a do\n  b": "a(b)",
    "a\n  b\n  c\nd\ne\n  f\n    g\nh": """(
  a((
    b;
    c
  ));
  d;
  e(f(g));
  h
)""",
    "a b, c": "a(b, c)",
    "a b c, d e, f": "a(b(c), d(e), f)",
    "a b\n\\c\n  d\n  e": """a(b, c((
  d;
  e
)))""",
#    "a = \\b c\na = \\b c\n  a = \\b c\na = \\b c": """(
#  (a = b(c));
#  (a = b(c, (a = b(c))));
#  (a = b(c))
#)""",
    #"""
    #a = (b = \c d
    #  e = \f g
    #h = \i j)""": "(a = ((b = c(d((e = f(g((h = i(j))))))))))",
    """
a = do b c
a = do b c
  a = do b c
a = do b c""": """(
  (a = b(c));
  (a = b(c, (a = b(c))));
  (a = b(c))
)""",
    """
    a = (do
      b = do c d
        e = do f g
      h = do i j)""": """(a = ((
  (b = c(d, (e = f(g))));
  (h = i(j))
)))""",
    "\"abc\"": "\"abc\"",
    "1..20": "(1 .. 20)",
    "1a": "(1 a)",
    "1ea": "(1 ea)",
    "+3.0 / -2.0": "(3.0 / -2.0)",
    "3e-2000 / 2e1400": "(3e-2000 / 2e1400)",
    "+3.1419e2 / -27.828e-1": "(314.19 / -2.7828)",
    "0.03": "0.03",
    "0.00042e-4": "0.00042e-4",
    "a + b c + d e": "(a + b((c + d(e))))",
    "a+b c+d e": "(a + b)((c + d)(e))",
    "a + b c, d e + f g": "((a + b(c)), d((e + f(g))))",
    "a do(b) do(c)": "a((b)((c)))",
#    """
#a = \b
#  c = \d
#    e = \f
#      g = \h
#  i = \j
#k""": """(
#  (a = b((
#    (c = d((e = f((g = h)))));
#    (i = j)
#  )));
#  k
#)""",
    """
a = do b
  c = do d
    e = do f
      g = do h
  i = do j
k""": """(
  (a = b((
    (c = d((e = f((g = h)))));
    (i = j)
  )));
  k
)""",
    """
a do b do (c)
d""": """(
  a(b((c)));
  d
)""",
    """if a, b,
else: (do
  c
  d)""": """if(a, b, else: ((
  c;
  d
)))""",
    "permutation(n: Int, r: Int) = product n - r + 1 .. n":
      # command syntax with infixes
      "(permutation(n: Int, r: Int) = product((((n - r) + 1) .. n)))",
    "factorial(n: Int) = permutation n, n":
      # consequence
      "((factorial(n: Int) = permutation(n)), n)",
    "a =\n  b": "(a = b)", # postfix expansion
    "\\(foo a, b)": "foo(a, b)",
    """
if (a
  b)
  c
""": "if((a(b)), c)",
    """
if (a
    b
      c)
  c
""": "if((a(b(c))), c)",
    "a: b = c": "(a: b = c)",
    "a(b): c = d": "(a(b): c = d)",
    "a(b): c =\n  d": "(a(b): c = d)",
    """
if a
  if b
    c
  else do
    d
else do
  e
""": "if(a, if(b, c, else: d), else: e)",
    """
if a
  if b
    c
  else do
    d
    e
else do
  f
""": """if(a, if(b, c, else: (
  d;
  e
)), else: f)""",
    """
if a
  if b
    c
  else
    d
else
  e
""": "if(a, if(b, c, else: d), else: e)",
    """
if a
  if b
    c
  \else
    d
\else
  e
""": "if(a, if(b, c, else(d)), else(e))",
    """
if a
  if b
    c
  \else:
    d
\else:
  e
""": "if(a, if(b, c, else: d), else: e)",
    """
if a
  if b
    c
  else
    d
    e
else
  f
""": """if(a, if(b, c, else: (
  d;
  e
)), else: f)""",
    "foo(a \"a\" \"abcd\")": "foo(a(\"a\"(\"abcd\")))",
    "a(b, c) -> d = e; a(b, c) -> d => e = f(g, h) -> i => j":
      "(((a(b, c) -> d) = e); ((a(b, c) -> d) => (e = ((f(g, h) -> i) => j))))"
  }

  for inp, outp in tests.items:
    let parsed = parse(inp)
    let a = $parsed
    let b = outp
    checkpoint "parsed: " & a
    checkpoint "expected: " & b
    check a == b

import abyzou/language/shortstring

test "equivalent syntax":
  let equivalents = {
    "combination(n: Int, r: Int) = do for result x = 1, each i in 0..<r do " &
      "while i < r do x = x * (n - i) / (r - i)":
        "combination(n: Int, r: Int) = for(result x = 1, each i in 0..<r) do " &
          "while i < r, x = x * (n - i) / (r - i)"
  }

  proc reduced(a: Expression): Expression

  proc reduced(a: seq[Expression]): seq[Expression] =
    result.newSeq(a.len)
    for i in 0 ..< a.len:
      result[i] = a[i].reduced

  proc reduced(a: Expression): Expression =
    const equivalentKinds = [
      {Name, Symbol},
      {OpenCall, Infix, Prefix, Postfix,
        PathCall, PathInfix, PathPrefix, PathPostfix},
      {Block, SemicolonBlock}
    ]

    result = a
    while result.kind == Wrapped: result = result.wrapped

    for ek in equivalentKinds:
      if result.kind in ek:
        if OpenCall in ek:
          result = Expression(kind: PathCall, address: result.address.reduced,
            arguments: result.arguments.reduced)
        elif Name in ek:
          result = Expression(kind: Name, identifier: (if result.kind == Symbol: $result.symbol else: result.identifier))
        elif Block in ek:
          result = Expression(kind: Block, statements: result.statements.reduced)
        else:
          echo "weird equivalent kinds set ", ek
        return

  for a, b in equivalents.items:
    let a = reduced(parse(a))
    let b = reduced(parse(b))
    let aRepr = a.repr
    let bRepr = b.repr
    checkpoint "a: " & aRepr
    checkpoint "b: " & bRepr
    checkpoint "a: " & $a
    checkpoint "b: " & $b
    when defined(js):
      check aRepr == bRepr
    else:
      check a == b

when not defined(nimscript) and defined(testsBenchmark):
  import std/monotimes, strutils
  template bench(name, body) =
    checkpoint name
    let a = getMonoTime()
    body
    let b = getMonoTime()
    let time = formatFloat((b.ticks - a.ticks).float / 1_000_000, precision = 2)
    echo name, " took ", time, " ms"
else:
  # nimscript is actually really slow here
  template bench(name, body) =
    checkpoint name
    body

test "parse files without crashing":
  for f in [
    "concepts/arguments.byz",
    "concepts/badspec.byz",
    "concepts/tag.byz",
    "concepts/test.byz"
  ]:
    when defined(testsBenchmark): echo "file ", f
    bench("loading file"):
      let s = when declared(read): read(f) else: readFile(f)
    bench("tokenizing"):
      let ts = tokenize(s)
    proc collated(s: string, n: int): proc(): string =
      var i = 0
      result = proc(): string =
        if i < s.len:
          let j = min(s.len, i + n)
          result = s[i ..< j]
          i = j
        else:
          result = ""
    bench("tokenizing with buffer loader of 4"):
      block:
        var tz = newTokenizer(collated(s, 4))
        let ts2 = tokenize(tz)
        check ts == ts2
    bench("tokenizing with char buffer loader"):
      block:
        var tz = newTokenizer(collated(s, 1))
        let ts2 = tokenize(tz)
        check ts == ts2
    bench("parsing"):
      let p {.used.} = parse(ts)

when defined(testsBenchmark):
  test "200x size file":
    let f = "concepts/badspec.byz"
    bench("loading file"):
      let s = repeat(when declared(read): read(f) else: readFile(f), 200)
    bench("tokenizing"):
      let ts = tokenize(s)
    bench("parsing"):
      let _ = parse(ts)
