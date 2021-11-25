import unittest

import bazy/[parser, expressions]

test "simple code":
  let tests = {
    "a": "a",
    "a.b": "a.b",
    "a+b": "(a + b)",
    "a + b": "(a + b)",
    "a +b": "(a (+ b))",
    "a+ b": "((a +) b)",
    "a.b+c/2": "((a.b + c) / 2)",
    "a(b, c)": "a(b, c)",
    "a * b / c ^ d ^ e << f | g + h < i as j":
      "((((a * b) / (c ^ (d ^ e))) << ((f | g) + h)) < (i as j))",
    "a do\n  b": "(a b)",
    "a\n  b\n  c\nd\ne\n  f\n    g\nh": """(
  (a (
    b;
    c
  ));
  d;
  (e (f g));
  h
)""",
    "a b, c": "(a b, c)",
    "a b c, d e, f": "(a (b c), (d e), f)",
    "a b\n\\c\n  d\n  e": """(a b, c: (
  d;
  e
))""",
    "a = \\b c\na = \\b c\n  a = \\b c\na = \\b c": """(
  (a = (b c));
  (a = (b c, (a = (b c))));
  (a = (b c))
)""",
    """
    a = (b = \c d
      e = \f g
    h = \i j)""": "(a = ((b = (c (d (e = (f (g (h = (i j))))))))))",
    "\"abc\"": "\"abc\"",
    "1..20": "(1 .. 20)",
    "1a": "(1 a)",
    "1ea": "(1 ea)",
    "+3.0 / -2.0": "(3.0 / -2.0)",
    "3e-2000 / 2e1400": "(3e-2000 / 2e1400)",
    "+3.1419e2 / -27.828e-1": "(314.19 / -2.7828)",
    "0.03": "0.03",
    "0.00042e-4": "0.00042e-4"
  }

  for inp, outp in tests.items:
    check $parse(inp) == outp
