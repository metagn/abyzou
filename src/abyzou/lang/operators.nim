import shortstring

type
  Precedence* = enum
    Access # dot operators
    Colon
    Exponent
    Shift
    Multiplication, Addition
    Range
    Conversion # as etc
    Comparison, Not, And, Or
    Misc
    Accusative # ? @ etc
    Separation # , maybe
    Assignment
    Lambda # should not be different from Assignment, i.e.
    # (a, b) => c = (d, e) => f
    # should be (a, b) => ((c = (d, e) => f))
    # not (a, b) => ((c = (d, e)) => f)
    Statement # postfix if/for, nonexistent
    None
  
  Associativity* = enum Left, Right, Unary

const Associativities*: array[Precedence, Associativity] = [
  Access: Left,
  Colon: Right,
  Exponent: Right,
  Shift: Left,
  Multiplication: Left,
  Addition: Left,
  Range: Left,
  Conversion: Left,
  Comparison: Left,
  Not: Unary,
  And: Left,
  Or: Left,
  Misc: Left,
  Accusative: Right,
  Separation: Right,
  Assignment: Right,
  Lambda: Right,
  Statement: Left,
  None: Left
]

when shortStringIsArray:
  {.experimental: "caseStmtMacros".}

proc precedence*(symbol: ShortString): Precedence =
  var L: int
  case symbol
  of short"": None
  of short"=": Assignment
  of short":": Colon
  of short"**", short"pow": Exponent # not keyword
  of short"shl", short"shr": Shift # not keywords
  of short"div", short"mod", short"rem": Multiplication # rem not a keyword
  of short"as", short"from": Conversion
  of short"is", short"in", short"of": Comparison # maybe not of
  of short"not", short"!": Not
  of short"and", short"&&": And
  of short"or", short"||": Or
  of short"for", short"if", short"while", short"unless", short"until", short"do": Statement # not sure if these can be keywords
  elif (L = symbol.len; L > 1 and symbol[L - 2 .. L - 1] == short"=>"):
    Assignment
  elif L > 1 and symbol[L - 2 .. L - 1] == short"->":
    Separation
  else:
    case symbol[0]
    of '^': Exponent
    of '*', '%', '/', '&', '\\': Multiplication
    of '+', '-', '~', '|': Addition
    of '.':
      if L > 1 and symbol[1] == '.':
        Range
      else:
        Access
    of '<', '>', '!', '=': Comparison
    of '@', '?', ':': Accusative
    of ',', ';': Separation
    elif symbol[L - 1] == '=': Assignment
    else: Misc
