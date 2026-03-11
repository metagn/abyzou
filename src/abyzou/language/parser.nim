import shortstring, tokens, tokenizer, expressions, operators, info

#[

notes:

* probably (not) a lot of indent bugs when you indent in parentheses (delegated to tokenizer) or with variable spaces
* some kind of delimiter counter/stack on parser object would stop infinite loops from errors
* keep track of indents with a counter (maybe not)
* maybe make distinction between indent and normal argument, or `do` and indent, no idea
* maybe make commas and semicolons operators, this would depend on
  command-after-operator transformation for `a b, c d`
  these would not be infixes, they would be one list of expressions
* maybe command-after-operator also works with commas

]#

type
  ParserOptions* = object
    curlyBlocks*,
      pathOperators*,
      operatorIndentMakesBlock*,
      backslashLine*,
      backslashPostArgument*,
      colonPostArgument*,
      weirdOperatorIndentUnwrap*,
      makeOperatorInfixOnIndent*,
      backslashParenLine*
    : bool
    postArgumentColonKeywords*: seq[ShortString] # performance hazard
    postArgumentCallKeywords*: seq[ShortString]
    precedence*: proc (symbol: ShortString): Precedence

  Parser* = ref object
    tokenizer*: Tokenizer
    currentToken*: Token
    keepToken*: bool
    tokenQueue*: seq[Token]
    tokenQueuePos*: int
    options*: ParserOptions

proc defaultOptions*(): ParserOptions =
  result = ParserOptions(
    curlyBlocks: false,
    pathOperators: true,
    operatorIndentMakesBlock: true,
    backslashLine: false,
    backslashPostArgument: true,
    colonPostArgument: false,
    weirdOperatorIndentUnwrap: true,
    makeOperatorInfixOnIndent: true,
    backslashParenLine: true)
  result.postArgumentColonKeywords.add(short"else")

proc newSymbolExpression*(p: Parser, s: ShortString): Expression {.inline.} =
  let prec = if p.options.precedence.isNil: s.precedence else: p.options.precedence(s)
  Expression(kind: Symbol, symbol: s, precedence: prec)

proc nextToken*(p: var Parser) =
  #inc p.pos
  if p.tokenQueuePos < p.tokenQueue.len:
    p.currentToken = p.tokenQueue[p.tokenQueuePos]
    inc p.tokenQueuePos
    return
  elif p.tokenQueue.len != 0:
    p.tokenQueue = @[]
    p.tokenQueuePos = 0
  
  if not p.tokenizer.isNil:
    p.currentToken = p.tokenizer.nextToken()
  else:
    p.currentToken = Token(kind: tkNone)

iterator nextTokens*(p: var Parser): Token =
  while p.currentToken.kind != tkNone:
    yield p.currentToken
    if p.keepToken:
      p.keepToken = false
    else:
      p.nextToken()
  
proc info*(p: var Parser): Info {.inline.} =
  p.currentToken.info

template conservePosNextIteration(p: var Parser) =
  #dec p.pos
  p.keepToken = true

proc newParser*(tokens: sink seq[Token] = @[], options = defaultOptions()): Parser {.inline.} =
  result = Parser(tokenQueue: tokens, options: options)
  result.nextToken()

proc newParser*(tokenizer: Tokenizer, options = defaultOptions()): Parser {.inline.} =
  result = Parser(tokenizer: tokenizer, options: options)
  result.nextToken()

proc recordLineLevel*(parser: var Parser, info: Info, closed = false): Expression

proc recordWideLine*(parser: var Parser, info: Info, closed = false): Expression =
  var s: seq[Expression]
  var semicoloned = false
  for t in parser.nextTokens:
    case t.kind
    of tkSemicolon:
      semicoloned = true
    of tkComma, tkCloseParen, tkCloseBrack, tkCloseCurly,
      tkIndentBack, tkNewline: # newline could be delegated to line
      break
    elif s.len == 0 or semicoloned:
      s.add(parser.recordLineLevel(t.info, closed))
      parser.conservePosNextIteration()
    else:
      break
  if semicoloned: Expression(kind: SemicolonBlock, statements: s, info: info)
  elif s.len == 0: Expression(kind: ExpressionKind.None, info: info)
  else: s[0]

proc recordBlockLevel*(parser: var Parser, indented = false): Expression =
  result = Expression(kind: Block, info: parser.info)
  defer:
    if result.statements.len == 1: result = result.statements[0]
  var backslashNames: seq[string]
  for token in parser.nextTokens:
    case token.kind
    of tkNone, tkWhitespace, tkNewline: continue
    of tkSemicolon: discard
    of tkIndentBack:
      if indented:
        parser.nextToken()
        break
      else:
        echo "warning extra indentback at " & $token.info
        continue
    of tkComma, tkCloseBrack, tkCloseCurly, tkCloseParen:
      assert indented, "extra delim " & $token.kind
      break
    elif token.kind == tkColon and 
      parser.options.colonPostArgument and
      result.statements.len > 0 and
      result.statements[^1].kind in IndentableCallKinds:
      parser.nextToken()
      result.statements[^1].arguments.add(parser.recordWideLine(parser.info))
      parser.conservePosNextIteration()
    else:
      result.statements.add(parser.recordWideLine(token.info))
      parser.conservePosNextIteration()
    reset backslashNames

proc recordBrack*(parser: var Parser, info: Info): Expression =
  var s: seq[Expression]
  var ended = false
  for t in parser.nextTokens:
    case t.kind
    of tkNone, tkWhitespace, tkIndent, tkIndentBack, tkNewline, tkComma: discard
    of tkCloseBrack:
      parser.nextToken()
      ended = true
      break
    of tkCloseCurly, tkCloseParen:
      assert false, "wrong delim for brack"
    else:
      s.add(parser.recordWideLine(t.info, closed = true))
      parser.conservePosNextIteration()
  assert ended, "missing ending brack"
  Expression(kind: Array, elements: s, info: info)

proc recordParen*(parser: var Parser, info: Info): Expression =
  var commad = false
  var s: seq[Expression]
  var ended = false
  for t in parser.nextTokens:
    case t.kind
    of tkNone, tkWhitespace, tkIndent, tkIndentBack, tkNewline: discard
    of tkComma: commad = true
    of tkCloseParen:
      parser.nextToken()
      ended = true
      break
    of tkCloseCurly, tkCloseBrack:
      assert false, "wrong delim for paren"
    elif s.len == 0 or commad:
      s.add(parser.recordWideLine(t.info, closed = true))
      parser.conservePosNextIteration()
    else:
      break
  assert ended, "missing ending paren"
  if not commad and s.len == 1: Expression(kind: Wrapped, wrapped: s[0], info: info)
  #elif not commad and s.len == 0: Expression(kind: ExpressionKind.None)
  else: Expression(kind: Tuple, elements: s, info: info)

proc recordCurly*(parser: var Parser, info: Info): Expression =
  var s: seq[Expression]
  var commad = false
  var ended = false
  for t in parser.nextTokens:
    case t.kind
    of tkNone, tkWhitespace, tkIndent, tkIndentBack, tkNewline: discard
    of tkComma: commad = true
    of tkCloseCurly:
      parser.nextToken()
      ended = true
      break
    of tkCloseBrack, tkCloseParen:
      assert false, "wrong delim for curly"
    elif s.len == 0 or commad or parser.options.curlyBlocks:
      s.add(parser.recordWideLine(t.info, closed = not parser.options.curlyBlocks or commad))
      parser.conservePosNextIteration()
  assert ended, "missing ending curly"
  if not parser.options.curlyBlocks or commad: Expression(kind: Set, elements: s, info: info)
  else: Expression(kind: Block, statements: s, info: info)

proc recordSingle*(parser: var Parser, info: Info): Expression =
  # +a is a path
  # a.b[c] is a path
  # a+b/c is a path and implies (a + b) / c
  var
    precedingSymbol, currentSymbol: Expression = nil
    precedingDot, lastWhitespace, lastDot = false
  defer:
    # paths will never terminate with delimiter
    let resultWasNil = result.isNil
    if not currentSymbol.isNil:
      if not parser.options.pathOperators:
        assert false, "currentSymbol should not exist when path operators are off"
      if resultWasNil:
        result = currentSymbol
      else:
        result = Expression(kind: PathPostfix, address: currentSymbol, arguments: @[result], info: info)
    if not precedingSymbol.isNil and not resultWasNil:
      if not parser.options.pathOperators:
        assert false, "precedingSymbol should not exist when path operators are off"
      result = Expression(kind: PathPrefix, address: precedingSymbol, arguments: @[result], info: info)
    if precedingDot:
      result = Expression(kind: PathPrefix,
        address: parser.newSymbolExpression(short".").withInfo(info),
        arguments: @[result], info: info)
  template finish = return
  for token in parser.nextTokens:
    case token.kind
    of tkNone: discard
    of tkWhitespace:
      if not currentSymbol.isNil:
        finish()
      lastWhitespace = true
      continue
    of tkIndent, tkIndentBack, tkNewLine,
       tkComma, tkSemicolon, tkCloseParen,
       tkCloseCurly, tkCloseBrack, tkColon:
      finish()
    of tkString, tkSingleQuoteString, tkNumber, tkWord, tkQuotedWord:
      if lastWhitespace and not lastDot:
        finish()
      let ex = case token.kind
        of tkString, tkSingleQuoteString:
          let str = if result.isNil or lastDot: unescape(token.content) else: token.content
          if token.kind == tkSingleQuoteString:
            Expression(kind: SingleQuoteString, str: str, info: token.info)
          else:
            Expression(kind: String, str: str, info: token.info)
        of tkNumber: Expression(kind: Number, number: token.num, info: token.info)
        of tkWord, tkQuotedWord: Expression(kind: Name, identifier: token.raw, info: token.info)
        else: nil
      if result.isNil:
        result = ex
        if lastDot:
          precedingDot = true
        if not currentSymbol.isNil:
          precedingSymbol = currentSymbol
          currentSymbol = nil
      elif lastDot:
        result = Expression(kind: Dot, left: result, right: ex, info: result.info)
      elif not currentSymbol.isNil:
        result = Expression(kind: PathInfix, address: currentSymbol, arguments: @[result, ex], info: result.info)
        currentSymbol = nil
      else:
        result = Expression(kind: PathPrefix, address: result, arguments: @[ex], info: result.info)
    of tkOpenBrack, tkOpenCurly, tkOpenParen:
      if lastWhitespace and not lastDot:
        finish()
      parser.nextToken()
      let inf = token.info
      let ex = case token.kind
        of tkOpenBrack: parser.recordBrack(inf)
        of tkOpenParen: parser.recordParen(inf)
        of tkOpenCurly: parser.recordCurly(inf)
        else: nil
      if result.isNil:
        result = ex
        if lastDot: precedingDot = true
      elif not currentSymbol.isNil:
        result = Expression(kind: PathInfix, address: currentSymbol, arguments: @[result, ex], info: inf)
        currentSymbol = nil
      else:
        result = (case ex.kind
        of Tuple:
          if result.kind == Dot and not lastDot:
            Expression(kind: PathCall, address: result.right, arguments: @[result.left] & ex.elements)
          else:
            Expression(kind: PathCall, address: result, arguments: ex.elements)
        of Array: Expression(kind: Subscript, address: result, arguments: ex.elements)
        of Set: Expression(kind: CurlySubscript, address: result, arguments: ex.elements)
        of Wrapped: # single expression
          if result.kind == Dot and not lastDot:
            Expression(kind: PathCall, address: result.right, arguments: @[result.left, ex.wrapped])
          else:
            Expression(kind: PathCall, address: result, arguments: @[ex.wrapped])
        of ExpressionKind.None:
          Expression(kind: PathCall, address: result, arguments: @[])
        else:
          assert false, "should return one of tuple, array, set, wrapped"
          nil).withInfo(token.info)
      parser.conservePosNextIteration()
    of tkDot:
      lastDot = true
      lastWhitespace = false
      continue
    of tkSymbol, tkBackslash:
      if lastWhitespace and not lastDot:
        finish()
      let ex = parser.newSymbolExpression(
        if token.kind == tkSymbol: token.short
        else: short"\\").withInfo(token.info)
      if result.isNil:
        if lastDot: precedingDot = true
        if parser.options.pathOperators:
          currentSymbol = ex
          precedingSymbol = currentSymbol
        else:
          result = ex
      elif lastDot:
        result = Expression(kind: Dot, left: result, right: ex, info: token.info)
      else:
        if parser.options.pathOperators:
          currentSymbol = ex
        else:
          finish()
    lastDot = false
    lastWhitespace = false

proc reduceOperators*(exprs: sink seq[Expression], lowestKind = low(Precedence)): seq[Expression] =
  # use nils to delete expressions instead of reordering the seq
  if exprs.len <= 1: return exprs
  var prec = lowestKind
  var deleted = 0
  template delete(foo) =
    when defined(c): # fast to use swap, doesn't evaluate foo twice
      var old: Expression
      swap old, foo
      if not old.isNil:
        inc deleted
    else:
      if not foo.isNil:
        inc deleted
      foo = nil
  while prec != Precedence.None:
    proc isOperator(e: Expression, precedence = prec): bool {.inline, nimcall.} =
      e.kind == Symbol and e.precedence == precedence
    let assoc = Associativities[prec]
    var mustPrefix = true
    var
      prefixStack: seq[Expression]
      prefixStackLast = -1
    var i = 0
    while i < exprs.len:
      var e = exprs[i]
      if e.isNil: discard
      elif e.isOperator:
        if mustPrefix:
          prefixStackLast = i
          prefixStack.add(e)
        mustPrefix = true
      else:
        for j in countdown(prefixStackLast, 0):
          if not exprs[j].isNil:
            e = Expression(kind: Prefix, address: move exprs[j], arguments: @[e]).inferInfo()
            delete exprs[j]
        exprs[i] = e
        mustPrefix = false
        prefixStack = @[]
      inc i
    if mustPrefix:
      let startIndex = max(0, exprs.len - prefixStack.len - 2)
      var e = exprs[startIndex]
      for j in startIndex + 1 ..< exprs.len:
        e = Expression(kind: Postfix, address: move exprs[j], arguments: @[e]).inferInfo()
        delete exprs[j]
      exprs[startIndex] = e
    case assoc
    of Left:
      var lhsStart, i = 0
      var lhs, op: Expression
      while i < exprs.len:
        let e = exprs[i]
        if e.isNil: discard
        elif e.isOperator:
          op = e
        elif op.isNil:
          lhs = e
          lhsStart = i
        else:
          lhs = makeInfix(op, lhs, e)
          for j in lhsStart ..< i:
            delete exprs[j]
          exprs[i] = lhs
          discard lhs # arc destroys lhs here otherwise
          op = nil
        inc i
    of Right:
      var rhsStart, i = exprs.high
      var rhs, op: Expression
      while i >= 0:
        let e = exprs[i]
        if e.isNil: discard
        elif e.isOperator:
          op = e
        elif op.isNil:
          rhs = e
          rhsStart = i
        else:
          rhs = makeInfix(op, e, rhs)
          for j in i ..< rhsStart:
            delete exprs[j]
          exprs[rhsStart] = rhs
          discard rhs # arc deletes rhs otherwise
          op = nil
        dec i
    of Unary:
      var stack: seq[Expression]
      var i = 0
      while i < exprs.len:
        var e = exprs[i]
        if e.isNil: discard
        elif e.isOperator:
          stack.add(e)
        else:
          let sl = stack.len
          while stack.len != 0:
            e = Expression(kind: Prefix, address: stack.pop, arguments: @[e]).inferInfo()
          for j in i - sl ..< i:
            delete exprs[j]
          exprs[i] = e
        inc i
    inc prec
  result = newSeqOfCap[Expression](exprs.len - deleted)
  for e in exprs:
    if not e.isNil:
      result.add(e)

proc collectLineExpression*(exprs: sink seq[Expression], info: Info): Expression =
  if exprs.len == 0: return Expression(kind: ExpressionKind.None, info: info)
  var terms = reduceOperators(exprs)
  result = terms.pop
  while terms.len != 0:
    let callee = terms.pop
    if callee.kind in {Prefix, Infix, ExpressionKind.Colon}: # postfix should not be possible
      # command-after-operator support
      var deepest = callee
      proc last(ex: var Expression): var Expression =
        if ex.kind == ExpressionKind.Colon:
          result = ex.right
        else:
          result = ex.arguments[^1]
      while (let last = deepest.last; last.kind in {Prefix, Infix, ExpressionKind.Colon}):
        deepest = last
      (deepest.last) = Expression(kind: OpenCall, address: deepest.last, arguments: @[result]).inferInfo()
      result = callee
    else:
      result = Expression(kind: OpenCall, address: callee, arguments: @[result], info: callee.info)

type
  CommaKind = enum
    NoComma, CommaCall, CommaList
  LineRecording = object
    lineExprs: seq[Expression]
    comma: CommaKind
    singleExprs: seq[Expression]
    indent: Expression
    indentIsDo: bool
    postArg: Expression

proc recordLineLevelUnfinished*(parser: var Parser, info: Info, closed = false): LineRecording =
  var waiting = false
  template finish = return
  for token in parser.nextTokens:
    case token.kind
    of tkNone, tkWhitespace: discard
    of tkComma:
      if closed:
        # outside line scope
        finish()
      waiting = true
      if result.singleExprs.len != 0: # consider ,, typo as ,
        let ex = collectLineExpression(move result.singleExprs, info)
        when defined(nimscript): result.singleExprs = @[]
        if not closed and result.comma == NoComma and (ex.kind == OpenCall or
          (ex.kind == Prefix and ex.address.kind == Symbol and ex.address.precedence == Statement)):
          assert ex.arguments.len == 1, "opencall with more than 1 argument should be impossible before comma"
          result.comma = CommaCall
          result.lineExprs.add(ex.address)
          result.lineExprs.add(ex.arguments)
        else:
          if result.comma == NoComma: result.comma = CommaList
          result.lineExprs.add(ex)
    of tkNewline, tkIndent:
      if waiting or (token.kind == tkNewline and closed):
        if token.kind == tkNewline:
          for tok in parser.nextTokens:
            if tok.kind notin {tkNone, tkWhitespace, tkNewline, tkIndent, tkIndentBack}:
              parser.conservePosNextIteration()
              break
      else:
        # there was a rollback here, but it seemed to just produce whitespace
        # that would normally be ignored, so disabling it seems to be fine
        #var lastPos = parser.pos
        var indentRecorded = false
        for tok in parser.nextTokens:
          case tok.kind
          of tkNone, tkWhitespace, tkNewline: discard
          elif tok.kind == tkIndent and not indentRecorded:
            parser.nextToken()
            result.indent = parser.recordBlockLevel(indented = true)
            indentRecorded = true
            #lastPos = parser.pos
            parser.conservePosNextIteration()
          else:
            type PostArgumentKind = enum backslash, colon, call
            let postArgKind =
              if parser.options.backslashPostArgument and tok.kind == tkBackslash:
                backslash
              elif parser.options.postArgumentColonKeywords.len != 0 and tok.kind == tkSymbol and
                tok.short in parser.options.postArgumentColonKeywords:
                colon
              elif parser.options.postArgumentCallKeywords.len != 0 and tok.kind == tkSymbol and
                tok.short in parser.options.postArgumentCallKeywords:
                call
              else:
                break
            let name =
              if postArgKind == colon:
                Expression(kind: Name, identifier: $tok.short, info: tok.info)
              else:
                nil
            if postArgKind == call:
              parser.currentToken = Token(kind: tkQuotedWord, raw: $tok.short, info: tok.info)
            else:
              parser.nextToken()
              for tok in parser.nextTokens:
                case tok.kind
                of tkNone, tkWhitespace, tkNewline: discard
                else: break
            let value = parser.recordLineLevel(tok.info, closed) # closed is clearly false here
            if postArgKind == colon:
              result.postArg = Expression(kind: ExpressionKind.Colon, left: name, right: value, info: tok.info)
            else:
              result.postArg = value
            #lastPos = parser.pos
            parser.conservePosNextIteration()
        #parser.pos = lastPos
        finish()
      waiting = false
    of tkIndentBack:
      if not waiting:
        # outside line scope
        finish()
    of tkSemicolon, tkCloseBrack, tkCloseCurly, tkCloseParen:
      # outside line scope
      finish()
    of tkColon:
      result.singleExprs.add(parser.newSymbolExpression(short":").withInfo(token.info))
    elif token.kind == tkBackslash and parser.options.backslashParenLine and
      (block:
        parser.nextToken() # temporarily skip backslash
        let tok2 = parser.currentToken
        let passed = tok2.kind == tkOpenParen
        if not passed:
          # unskip backslash
          parser.currentToken = token
          parser.tokenQueue.insert(tok2, parser.tokenQueuePos)
        passed):
      parser.nextToken() # backslash is skipped, skip open paren
      result.singleExprs.add(parser.recordLineLevel(token.info, closed = false))
      assert parser.currentToken.kind == tkCloseParen, "wrong delimiter for backslash paren line"
      parser.nextToken() # skip closing paren
    elif token.kind == tkBackslash and parser.options.backslashLine:
      parser.nextToken() # skip backslash
      result.singleExprs.add(parser.recordLineLevel(token.info, closed))
      finish()
    elif token.kind == tkSymbol and token.short == short"do":
      waiting = false
      parser.nextToken() # skip do
      while parser.currentToken.kind in {tkNewline, tkWhitespace}:
        # skip newlines to not confuse line recorder
        parser.nextToken()
      result.indent = parser.recordWideLine(token.info)
      result.indentIsDo = true
      finish()
    else:
      let ex = parser.recordSingle(token.info)
      waiting = false # symbols do not bypass this
      result.singleExprs.add(ex)
      parser.conservePosNextIteration()
  finish()

proc finishLineRecording*(parser: var Parser, info: Info, recording: sink LineRecording): Expression =
  if recording.singleExprs.len != 0:
    recording.lineExprs.add(collectLineExpression(move recording.singleExprs, info))
    when defined(nimscript): recording.singleExprs = @[]
  if not recording.indent.isNil:
    if (parser.options.operatorIndentMakesBlock or recording.indentIsDo) and
      recording.lineExprs.len == 1 and recording.lineExprs[0].kind in IndentableCallKinds:
      if parser.options.weirdOperatorIndentUnwrap and
        (let expandKinds =
          if recording.indentIsDo: {Prefix, Infix, ExpressionKind.Colon}
          else: {Infix, ExpressionKind.Colon};
          recording.lineExprs[0].kind in expandKinds):
        proc last(ex: var Expression): var Expression =
          if ex.kind == ExpressionKind.Colon:
            result = ex.right
          else:
            result = ex.arguments[^1]
        var ex = recording.lineExprs[0]
        while (let last = ex.last; last.kind in expandKinds):
          ex = last
        if ex.last.kind in IndentableCallKinds:
          ex.last.arguments.add(recording.indent)
        else:
          (ex.last) = Expression(kind: OpenCall,
            address: ex.last, arguments: @[recording.indent]).inferInfo()
      elif parser.options.makeOperatorInfixOnIndent and
        (let ex = recording.lineExprs[0]; ex.kind in {Postfix, Prefix}):
        if ex.arguments.len == 1:
          recording.lineExprs[0] = makeInfix(ex.address, ex.arguments[0], recording.indent)
        else:
          recording.lineExprs[0] = Expression(kind: Infix,
            address: ex.address,
            arguments: ex.arguments & recording.indent).inferInfo()
      else:
        recording.lineExprs[0].arguments.add(recording.indent)
    else:
      recording.lineExprs.add(recording.indent)
  if not recording.postArg.isNil:
    if recording.lineExprs[0].kind in IndentableCallKinds:
      recording.lineExprs[0].arguments.add(recording.postArg)
    else:
      recording.lineExprs.add(recording.postArg)
  if recording.lineExprs.len == 0:
    result = Expression(kind: ExpressionKind.None, info: info)
  elif recording.comma == CommaList:
    result = Expression(kind: Comma, elements: recording.lineExprs, info: info)
  elif recording.lineExprs.len == 1:
    result = recording.lineExprs[0]
  else:
    result = Expression(kind: OpenCall, address: recording.lineExprs[0], arguments: recording.lineExprs[1..^1], info: info)

proc recordLineLevel*(parser: var Parser, info: Info, closed = false): Expression =
  var recording = recordLineLevelUnfinished(parser, info, closed)
  result = finishLineRecording(parser, info, recording)

proc parse*(tokens: sink seq[Token]): Expression =
  var parser = newParser(tokens)
  result = copy parser.recordBlockLevel()

proc parse*(tokenizer: Tokenizer): Expression =
  var parser = newParser(tokenizer)
  result = copy parser.recordBlockLevel()

when isMainModule:
  #import tokenizer
  when false:
    var t = newTokenizer("var a = b, c = d\n  e")
    t.options.symbolWords.add(short"var")
    var p = newParser(t.tokenize)
    p.options.precedence = proc (s: ShortString): Precedence =
      if s == short"var":
        Statement
      else:
        s.precedence
    echo p.recordBlockLevel.repr

  when false:
    let tests = [
      readFile("concepts/test.byz"),
      #readFile("concepts/tag.byz"),
      readFile("concepts/arguments.byz"),
      readFile("concepts/badspec.byz")
    ]

    for t in tests:
      echo "input: ", t
      echo "output: ", parse(tokenize(t))

  template tp(ss: string) =
    let s = ss
    let t = tokenize(s)
    echo t
    let p = parse(t)
    echo p
    echo p.repr

  when true:
    tp "a"
  else:
    tp """
  a = \b
    c = \d
      e = \f
        g = \h
    i = \j
  k
  """
    tp """
  a do b do (c)
  d
  """
    tp """
do
  if a,
    b,
        c,
  d

  if a,
    do
      b
  else c
"""
    tp "combination(n: Int, r: Int) = \\for result x = 1, each i in 0..<r do while i < r do x = x * (n - i) / (r - i)"
    tp "`for` a = b, c = d do e = f"
    tp "a := b + c * 4"
    tp "a:b:c + 1"
    tp "{:}"
    tp "a + b - c"
    tp """
try (do
  a
  b),
(catch c do
  d
  e),
(catch f do
  g),
(finally do
  e)
"""
    tp """
if (a, \
  b)
  c
"""
    tp """
if (a
  b)
  c
"""
    tp """
if (a
    b
      c)
  c
"""
    tp """
a
  b
    c
d
"""
    tp """
if a
  if b
    c
  \else
    d
\else
  e
"""
    tp """
if a
  if b
    c
    c2
  \else:
    d
    d2
\else:
  e
  f
"""
    tp """
if a
  if b
    c
    c2
  else
    d
    d2
else
  e
  f
"""
    tp """
try do
  a
  b; ,
catch c do
  d
  e; ,
catch f do
  g; ,
finally do
  e
"""
    discard

  when false:
    import os

    for (k, p) in walkDir("concepts"):
      if k == pcFile:
        echo "file: ", p
        let e = parse(readFile(p))
        echo "expr: ", e
