import shortstring, number, operators, skinsuit/equals, ../defines, info

type
  ExpressionKind* = enum
    None
    Number, String, SingleQuoteString
    Name, Symbol
    Wrapped
    OpenCall, Infix, Prefix, Postfix
    PathCall, PathInfix, PathPrefix, PathPostfix
    Subscript, CurlySubscript
    Dot, Colon, Comma
    Tuple, Array, Set
    Block, SemicolonBlock
  Expression* {.acyclic.} = ref object
    when doLineColumn:
      info*: Info
    case kind*: ExpressionKind
    of None: discard
    of Number:
      number*: NumberRepr
    of String, SingleQuoteString:
      str*: string
    of Name:
      identifier*: string
    of Symbol:
      symbol*: ShortString
      precedence*: Precedence ## calculated based on the symbol, but cached
    of Wrapped:
      wrapped*: Expression
    of OpenCall, Infix, Prefix, Postfix,
      PathCall, PathInfix, PathPrefix, PathPostfix,
      Subscript, CurlySubscript:
      address*: Expression
      arguments*: seq[Expression]
    of Dot, Colon:
      left*, right*: Expression
    of Comma, Tuple, Array, Set:
      # these can be colon expressions
      elements*: seq[Expression]
    of Block, SemicolonBlock:
      statements*: seq[Expression]

equals *Expression
equals *typeof(Expression()[])

proc len*(ex: Expression): int =
  case ex.kind
  of Wrapped: 1
  of Dot, Colon: 2
  of OpenCall, Infix, Prefix, Postfix,
    PathCall, PathInfix, PathPrefix, PathPostfix,
    Subscript, CurlySubscript: ex.arguments.len + 1
  of Comma, Tuple, Array, Set: ex.elements.len
  of Block, SemicolonBlock: ex.statements.len
  else: -1

proc `[]`*(ex: Expression, i: int): Expression =
  rangeCheck i >= 0 and i < ex.len
  case ex.kind
  of Wrapped: ex.wrapped
  of Dot, Colon:
    if i == 0: ex.left else: ex.right
  of OpenCall, Infix, Prefix, Postfix,
    PathCall, PathInfix, PathPrefix, PathPostfix,
    Subscript, CurlySubscript:
    if i == 0: ex.address else: ex.arguments[i - 1]
  of Comma, Tuple, Array, Set: ex.elements[i]
  of Block, SemicolonBlock: ex.statements[i]
  else: assert false; nil # invalid

proc withInfo*(ex: sink Expression, info: Info): Expression {.inline.} =
  result = ex
  when doLineColumn:
    result.info = info

proc inferInfo*(ex: sink Expression): Expression {.inline.} = ex.withInfo(ex[0].info)

proc copy*(ex: Expression): Expression =
  result = Expression(kind: ex.kind)
  case ex.kind
  of None: discard
  of Number: result.number = ex.number
  of String, SingleQuoteString: result.str = ex.str
  of Name: result.identifier = ex.identifier
  of Symbol: result.symbol = ex.symbol
  of Wrapped: result.wrapped = copy ex.wrapped
  of OpenCall, Infix, Prefix, Postfix,
    PathCall, PathInfix, PathPrefix, PathPostfix,
    Subscript, CurlySubscript:
    result.address = copy ex.address
    result.arguments = newSeq[Expression](ex.arguments.len)
    for i in 0 ..< result.arguments.len:
      result.arguments[i] = copy ex.arguments[i]
  of Dot, Colon:
    result.left = copy ex.left
    result.right = copy ex.right
  of Comma, Tuple, Array, Set:
    result.elements = newSeq[Expression](ex.elements.len)
    for i in 0 ..< result.elements.len:
      result.elements[i] = copy ex.elements[i]
  of Block, SemicolonBlock:
    result.statements = newSeq[Expression](ex.statements.len)
    for i in 0 ..< result.statements.len:
      result.statements[i] = copy ex.statements[i]

const
  OpenCallKinds* = {OpenCall, Infix, Prefix, Postfix}
  PathCallKinds* = {PathCall, PathInfix, PathPrefix, PathPostfix}
  CallKinds* = OpenCallKinds + PathCallKinds
  IndentableCallKinds* = OpenCallKinds + {PathCall}

proc makeInfix*(op, a, b: sink Expression): Expression =
  if op.kind == Symbol and op.symbol == short":":
    Expression(kind: Colon, left: a, right: b, info: op.info)
  else:
    Expression(kind: Infix, address: op, arguments: @[a, b], info: op.info)

proc newSymbolExpression*(s: ShortString): Expression {.inline.} =
  Expression(kind: Symbol, symbol: s, precedence: s.precedence)

template newSymbolExpression*(s: static string): Expression =
  newSymbolExpression(short(s))

template isIdentifier*(ex: Expression, name: untyped): bool =
  var `name` {.inject.}: string
  (ex.kind == Name and (`name` = ex.identifier; true)) or (ex.kind == Symbol and (`name` = $ex.symbol; true))

import strutils

proc `$`*(ex: Expression): string {.noSideEffect.}  =
  if ex.isNil: return "nil"
  case ex.kind
  of None: "()"
  of Number: $ex.number
  of String: "\"" & ex.str & "\""
  of SingleQuoteString: "'" & ex.str & "'"
  of Name: ex.identifier
  of Symbol: $ex.symbol
  of Wrapped: "(" & $ex.wrapped & ")"
  of Infix, PathInfix:
    "(" & $ex.arguments[0] & " " & $ex.address & " " & $ex.arguments[1] & ")" &
      (if ex.arguments.len > 2: " {" & ex.arguments[2..^1].join(", ") & "}" else: "")
  of Postfix, PathPostfix:
    "(" & $ex.arguments[0] & " " & $ex.address & ")" &
      (if ex.arguments.len > 1: " {" & ex.arguments[1..^1].join(", ") & "}" else: "")
  of Prefix, PathPrefix:
    "(" & $ex.address & " " & $ex.arguments[0] & ")" &
      (if ex.arguments.len > 1: " {" & ex.arguments[1..^1].join(", ") & "}" else: "")
  of OpenCall, PathCall: $ex.address & "(" & ex.arguments.join(", ") & ")"
  of Subscript: $ex.address & "[" & ex.arguments.join(", ") & "]"
  of CurlySubscript: $ex.address & "{" & ex.arguments.join(", ") & "}"
  of Dot: $ex.left & "." & $ex.right
  of Colon: $ex.left & ": " & $ex.right
  of Comma, Tuple: "(" & ex.elements.join(", ") & ")"
  of Array: "[" & ex.elements.join(", ") & "]"
  of Set: "{" & ex.elements.join(", ") & "}"
  of Block:
    var s = "(\n"
    for i in 0 ..< ex.statements.len:
      let ss = $ex.statements[i]
      for sl in ss.splitLines:
        s.add("  " & sl & "\n")
      if i < ex.statements.len - 1:
        s[^1 .. ^1] = ";\n"
    s.add(")")
    s
  of SemicolonBlock: "(" & ex.statements.join("; ") & ")"

proc repr*(ex: Expression): string {.noSideEffect.}  =
  if ex.isNil: return "nil"
  proc joinRepr(exs: seq[Expression]): string =
    for e in exs:
      if result.len != 0:
        result.add(", ")
      result.add(e.repr)
  case ex.kind
  of None: "None"
  of Number: "Number " & $ex.number
  of String: "String \"" & ex.str & "\""
  of SingleQuoteString: "String \'" & ex.str & "\'"
  of Name: $ex.kind & " " & ex.identifier
  of Symbol: $ex.kind & " " & $ex.symbol
  of Wrapped: "Wrapped(" & ex.wrapped.repr & ")"
  of Infix, PathInfix, Postfix, PathPostfix, Prefix, PathPrefix,
    OpenCall, PathCall, Subscript, CurlySubscript:
    $ex.kind & "(" & ex.address.repr & ", " & ex.arguments.joinRepr & ")"
  of Dot, Colon: $ex.kind & "(" & ex.left.repr & ", " & ex.right.repr & ")"
  of Comma, Tuple, Array, Set: $ex.kind & "(" & ex.elements.joinRepr & ")"
  of Block, SemicolonBlock:
    $ex.kind & "(" & ex.statements.joinRepr & ")"

import unicode

proc unescape*(s: string): string =
  # result.len <= s.len
  # if result.len == s.len, result == s
  var
    escaped, everEscaped = false
    uBase: int
    uNum = 0
    startedU = -1
  result = s
  var i = 0
  while i < s.len:
    template addEscaped(term) =
      if not everEscaped:
        everEscaped = true
        result.setLen(i)
      result.add(term)
    let c = s[i]
    if startedU != -1:
      case c
      of '_': discard
      # could change these to revert if digits don't match base
      of '0'..'9': uNum = uNum * uBase + int(c.byte - '0'.byte)
      of 'a'..'f': uNum = uNum * uBase + 10 + int(c.byte - 'a'.byte)
      of 'A'..'F': uNum = uNum * uBase + 10 + int(c.byte - 'A'.byte)
      else:
        if c == '}':
          addEscaped($Rune(uNum))
        elif everEscaped:
          result.add(s[startedU..i])
        uNum = 0
        startedU = -1
    elif escaped:
      if c in {'u', 'U'}:
        if i + 1 < s.len and s[i + 1] == '{':
          uBase = 16
          startedU = i - 1
        elif i + 2 < s.len and s[i + 1] in {'x', 'o', 'd', 'b',
          'X', 'O', 'D', 'B'} and s[i + 2] == '{':
          uBase = case s[i + 1]
          of 'x', 'X': 16
          of 'o', 'O': 8
          of 'd', 'D': 10
          of 'b', 'B': 2
          else: -1 # unreachable
          startedU = i - 1
          inc i, 2
          continue
        elif i + 4 < s.len and {s[i + 1], s[i + 2],
          s[i + 3], s[i + 4]} <= HexDigits:
          # can change parseHexInt to something more optimized but doesnt matter
          addEscaped($Rune(parseHexInt(s[i + 1 .. i + 4])))
          inc i, 5
          continue
        elif everEscaped:
          result.add('\\')
          result.add(c)
      elif c in {'x', 'X'} and {s[i + 1], s[i + 2]} <= HexDigits:
        result.add(char(parseHexInt(s[i + 1 .. i + 2])))
      else:
        let ch = case c
        of 't': '\t'
        of '\'': '\''
        of '\\': '\\'
        of 'r': '\r'
        of 'n': '\n'
        of 'f': '\f'
        of 'v': '\v'
        of 'a': '\a'
        of 'b': '\b'
        of 'e': '\e'
        else:
          if everEscaped:
            result.add('\\')
            result.add(c)
          inc i
          continue
        addEscaped(ch)
      escaped = false
    elif c == '\\':
      escaped = true
    elif everEscaped:
      result.add(c)
    inc i

proc binary*(ex: Expression): string =
  result.add(ex.kind.char)
  case ex.kind
  of None: discard
  of Number:
    result.add(ex.number.kind.char)
    result.add(ex.number.bits.char)
    let str = $ex.number
    result.add(str.len.char)
    result.add(str)
  of String, SingleQuoteString:
    let s = ex.str
    result.add(char (s.len shr 24) and 0xFF)
    result.add(char (s.len shr 16) and 0xFF)
    result.add(char (s.len shr 8) and 0xFF)
    result.add(char s.len and 0xFF)
    result.add(s)
  of Name:
    let s = ex.identifier
    result.add(char (s.len shr 8) and 0xFF)
    result.add(char s.len and 0xFF)
    result.add(s)
  of Symbol:
    let s = $ex.symbol
    result.add(char s.len and 0xFF)
    result.add(s)
  of Wrapped:
    result.add(binary(ex.wrapped))
  of Dot, Colon:
    result.add(binary(ex.left))
    result.add(binary(ex.right))
  of OpenCall, Infix, Prefix, Postfix,
      PathCall, PathInfix, PathPrefix, PathPostfix,
      Subscript, CurlySubscript,
      Comma, Tuple, Array, Set, Block, SemicolonBlock:
    let exprs =
      case ex.kind
      of OpenCall, Infix, Prefix, Postfix,
          PathCall, PathInfix, PathPrefix, PathPostfix,
          Subscript, CurlySubscript:
        let args = ex.arguments
        @[ex.address] & args
      of Dot, Colon: @[ex.left, ex.right]
      of Comma, Tuple, Array, Set: ex.elements
      of Block: ex.statements
      else: @[]
    result.add(char (exprs.len shr 24) and 0xFF)
    result.add(char (exprs.len shr 16) and 0xFF)
    result.add(char (exprs.len shr 8) and 0xFF)
    result.add(char exprs.len and 0xFF)
    for e in exprs: result.add(binary(e))
