import
  std/strutils,
  fleu/load_buffer,
  ../defines,
  ./[number, shortstring, tokens, info]

when useUnicode:
  import std/unicode

  template asChar(r: Rune): char =
    char(r.int and 0xFF)
  
  template isChar(r: Rune): bool =
    r.int32 < 128i32

  proc contains(s: set[char], r: Rune): bool {.inline.} =
    r.isChar and r.char in s

  proc `==`(s: char, r: Rune): bool {.inline.} =
    r.isChar and r.char == s

  template `==`(r: Rune, s: char): bool = s == r
else:
  type Rune = char
  
  template asChar(r: Rune): char = r

  template isChar(r: Rune): bool = true

  template isAlpha(r: Rune): bool = r.isAlphaAscii

  template isWhitespace(r: Rune): bool = r in Whitespace

type
  TokenizerOptions* = object
    symbolWords*: seq[ShortString]
    stringBackslashEscape*, stringQuoteEscape*: bool
    backslashBreakNewline*, commaIgnoreIndent*: bool
    file*: CachedFile
  
  IndentContext* = object
    levels*: seq[int]
    level*: int

  QueueMode* = enum
    ClearQueue, NewlineQueue

  Tokenizer* = ref object
    options*: TokenizerOptions
    buffer*: LoadBuffer
    indentContexts*: seq[IndentContext]
    lastKind*: TokenKind
    queueMode*: QueueMode
    recordingIndent*, comment*: bool
    currentRune*: Rune
    queue*: seq[Token]
    queuePos*: int
    indent*: int
    pos*, previousPos*: int
    when doLineColumn:
      ln*, cl*, previousCol*: int

proc defaultOptions*(): TokenizerOptions =
  result = TokenizerOptions(
    stringBackslashEscape: true,
    stringQuoteEscape: true,
    backslashBreakNewline: true,
    commaIgnoreIndent: true)
  for it in ["do", "else",
    "is", "as", "in", 
    "not", "and", "or",
    "div", "mod", "xor"]:
    result.symbolWords.add(it.toShortString)

proc resetTokenizer*(tz: var Tokenizer) =
  tz.indentContexts = @[IndentContext()]

proc newTokenizer*(str: sink string = "", options = defaultOptions()): Tokenizer =
  result = Tokenizer(buffer: initLoadBuffer(str), options: options)
  result.resetTokenizer()

proc newTokenizer*(loader: proc(): string, options = defaultOptions()): Tokenizer =
  result = Tokenizer(buffer: initLoadBuffer(loader), options: options)
  result.resetTokenizer()

proc loadBufferOne(tz: var Tokenizer) =
  let remove = tz.buffer.loadOnce()
  tz.pos -= remove
  tz.previousPos -= remove

proc peekCharOrZero(tz: var Tokenizer): char =
  if tz.pos < tz.buffer.data.len:
    result = tz.buffer.data[tz.pos]
  else:
    tz.loadBufferOne()
    if tz.pos < tz.buffer.data.len:
      result = tz.buffer.data[tz.pos]
    else:
      result = '\0'

proc resetPos*(tz: var Tokenizer) =
  assert tz.previousPos != -1, "no previous position to reset to"
  tz.pos = tz.previousPos
  tz.previousPos = -1
  when doLineColumn:
    tz.cl = tz.previousCol
    if tz.currentRune == '\n':
      dec tz.ln

proc nextRune*(tz: var Tokenizer): bool =
  ## converts \r\n to \n and updates line and column
  tz.previousPos = tz.pos
  when doLineColumn:
    tz.previousCol = tz.cl
  let c =
    if tz.pos < tz.buffer.data.len:
      tz.buffer.data[tz.pos]
    else:
      tz.loadBufferOne()
      if tz.pos < tz.buffer.data.len:
        tz.buffer.data[tz.pos]
      else:
        return false
  if c == '\r' and (inc tz.pos;
      tz.peekCharOrZero() == '\n' or
        (dec tz.pos; false)):
    tz.currentRune = Rune '\n'
    inc tz.pos
    when doLineColumn:
      tz.ln += 1
      tz.cl = 0
  else:
    when useUnicode:
      let b = c.byte
      var n = 0
      if b shr 5 == 0b110:
        n = 1
      elif b shr 4 == 0b1110:
        n = 2
      elif b shr 3 == 0b11110:
        n = 3
      elif b shr 2 == 0b111110:
        n = 4
      elif b shr 1 == 0b1111110:
        n = 5
      let remove = tz.buffer.loadBy(n)
      tz.pos -= remove
      tz.previousPos -= remove
      fastRuneAt(tz.buffer.data, tz.pos, tz.currentRune, true)
    else:
      tz.currentRune = c
      inc tz.pos
    when doLineColumn:
      if tz.currentRune == '\n':
        tz.ln += 1
        tz.cl = 0
      else:
        tz.cl += 1
  tz.buffer.freeBefore = tz.previousPos
  result = true

iterator runes*(tz: var Tokenizer): Rune =
  while tz.nextRune():
    yield tz.currentRune

proc recordString*(tz: var Tokenizer, quote: char): string =
  var escaped = false
  for c in tz.runes:
    if escaped:
      if c != '\\' and c != quote:
        result.add('\\')
      result.add(c)
      escaped = false
    elif tz.options.stringBackslashEscape and c == '\\':
      escaped = true
    elif c == quote:
      if tz.options.stringQuoteEscape and tz.peekCharOrZero() == quote:
        let gotNext = tz.nextRune()
        assert gotNext
        result.add(c)
      else:
        return
    else:
      result.add(c)

proc recordNumber*(tz: var Tokenizer, negative = false): NumberRepr =
  type Stage = enum
    inBase, inDecimalStart, inDecimal, inExpStart, inExp, inExpNeg, inBits

  result = NumberRepr(negative: negative)

  var
    stage = inBase
    digits: seq[byte]
    lastZeros = 0 # Natural
    recordedExp: int16 = 0
  
  var
    prevPosSet = false
    prevPos2: int
  when doLineColumn:
    var prevCol2: int
  
  defer:
    result.exp += recordedExp
    if result.kind != Floating:
      if lastZeros < -result.exp:
        result.kind = Floating
      elif result.exp < 0 and -result.exp < digits.len:
        # remove excessive zeros, ie 10000e-3 is simplified to 10
        result.exp = 0
        digits.setLen(digits.len + result.exp)
    result.digits = toDigitSequence(digits)

  for c in tz.runes:
    if prevPosSet:
      # would be prevPos2, but we can't keep track of how much the buffer shifts left
      # (unless we move this logic inside the tokenizer)
      tz.buffer.freeBefore = 0
    case stage
    of inBase:
      let ch = c.asChar
      case ch
      of '0'..'9':
        if c == '0':
          inc lastZeros
        else:
          lastZeros = 0
        digits.add(ch.byte - '0'.byte)
      of '.':
        result.kind = Floating
        stage = inDecimalStart
        prevPos2 = tz.previousPos
        when doLineColumn:
          prevCol2 = tz.previousCol
        prevPosSet = true
        tz.buffer.freeBefore = 0
      of 'e', 'E':
        stage = inExpStart
        prevPos2 = tz.previousPos
        when doLineColumn:
          prevCol2 = tz.previousCol
        prevPosSet = true
        tz.buffer.freeBefore = 0
      of 'i', 'I':
        result.kind = Integer
        stage = inBits
      of 'u', 'U':
        result.kind = Unsigned
        stage = inBits
      of 'f', 'F':
        result.kind = Floating
        stage = inBits
      else:
        tz.resetPos()
        return
    of inDecimalStart:
      tz.resetPos()
      case c.asChar
      of '0'..'9':
        stage = inDecimal
      else:
        result.kind = Integer
        tz.pos = prevPos2
        when doLineColumn:
          tz.cl = prevCol2
        prevPosSet = false
        return
    of inDecimal:
      let ch = c.asChar
      case ch
      of '0'..'9':
        if c == '0':
          inc lastZeros
        else:
          lastZeros = 0
        digits.add(ch.byte - '0'.byte)
        dec result.exp
      of 'e', 'E':
        stage = inExpStart
        prevPos2 = tz.previousPos
        when doLineColumn:
          prevCol2 = tz.previousCol
        prevPosSet = true
        tz.buffer.freeBefore = 0
      else:
        tz.resetPos()
        return
    of inExpStart:
      case c.asChar
      of '+':
        stage = inExp
      of '-':
        stage = inExpNeg
      of '0'..'9':
        stage = inExp
        tz.resetPos()
      else:
        tz.resetPos()
        tz.pos = prevPos2
        when doLineColumn:
          tz.cl = prevCol2
        prevPosSet = false
        return
    of inExp, inExpNeg:
      let ch = c.asChar
      case ch
      of '0'..'9':
        var val = (ch.byte - '0'.byte).int16
        if stage == inExpNeg: val = -val
        recordedExp = recordedExp * 10 + val
      of 'i', 'I':
        result.kind = Integer
        stage = inBits
      of 'u', 'U':
        result.kind = Unsigned
        stage = inBits
      of 'f', 'F':
        result.kind = Floating
        stage = inBits
      else:
        tz.resetPos()
        return
    of inBits:
      let ch = c.asChar
      case ch
      of '0'..'9':
        result.bits = (result.bits * 10) + (ch.byte - '0'.byte)
      else:
        tz.resetPos()
        return

proc recordWord*(tz: var Tokenizer): string =
  for c in tz.runes:
    if c == Rune('_') or (c.isChar and c.char.isDigit) or c.isAlpha:
      result.add(c)
    else:
      tz.resetPos()
      return

const NonSymbolChars = Whitespace + Digits + CharacterTokenSet + {'_', '\'', '"', '`', '#'}

proc recordSymbol*(tz: var Tokenizer): string =
  result = newStringOfCap(sizeof(ShortString))
  for c in tz.runes:
    if c notin NonSymbolChars and not c.isAlpha:
      result.add(c)
      if result.len == shortStringMaxSize:
        return
    else:
      tz.resetPos()
      return

proc recordSymbolPlus*(tz: var Tokenizer, extra: char): string =
  result = newStringOfCap(sizeof(ShortString))
  result.add(extra)
  for c in tz.runes:
    if c == extra or (c notin NonSymbolChars and not c.isAlpha):
      result.add(c)
      if result.len == shortStringMaxSize:
        return
    else:
      tz.resetPos()
      return

template clampType[T](val: T, newType: type): untyped =
  newType(min(val, T(high(newType))))

when defined(js):
  template clampType[T: SomeInteger](val: T, newType: type uint32): untyped =
    newType(val)

proc nextToken*(tz: var Tokenizer): Token =
  result = Token(kind: tkNone)
  template fill(t: Token): Token =
    var tok = t
    when doLineColumn:
      tok.info = Info(
        file: tz.options.file,
        line: clampType(ln, typeof(tok.info.line)),
        column: clampType(cl, typeof(tok.info.column)))
    tz.lastKind = tok.kind
    tok

  template add(t: Token) =
    return fill(t)

  template add(tt: TokenKind) =
    add Token(kind: tt)

  template queue(tt: TokenKind, mode: QueueMode = ClearQueue) =
    tz.queueMode = mode
    tz.queue.add(fill(Token(kind: tt)))

  for c in tz.runes:
    when doLineColumn:
      let (ln, cl) = (tz.ln, tz.cl)
    if tz.comment:
      if c == '\n':
        tz.comment = false
      else: continue

    let w = c.isWhitespace

    if tz.recordingIndent and c != '\n':
      case c.asChar
      of '\t':
        inc tz.indent, 4
        continue
      of '#':
        tz.indent = 0
        # recordingIndent still true
        tz.comment = true
        continue
      elif w:
        inc tz.indent
        continue
      else:
        template indentLevels: untyped = tz.indentContexts[^1].levels
        template indentLevel: untyped = tz.indentContexts[^1].level
        let diff = tz.indent - indentLevel
        if diff < 0:
          var d = -diff
          var i = indentLevels.len
          while i > 0:
            dec i
            let indt = indentLevels[i]
            dec d, indt
            dec indentLevel, indt
            queue tkIndentBack
            if d < 0:
              dec indentLevel, d
              indentLevels[^1] = -d
              queue tkIndent
              break
            indentLevels.setLen(indentLevels.high)
            if d == 0: break
        elif diff > 0:
          indentLevels.add(diff)
          inc indentLevel, diff
          queue tkIndent
        tz.indent = 0
        tz.recordingIndent = false

    if tz.queue.len != 0:
      case tz.queueMode
      of ClearQueue:
        tz.resetPos()
        result = tz.queue[tz.queuePos]
        inc tz.queuePos
        if tz.queuePos >= tz.queue.len:
          tz.queuePos = 0
          reset(tz.queue)
        return result
      of NewlineQueue:
        if c == '\n':
          var breakIndent = false
          var breakNewline = false
          case tz.queue[0].kind
          of tkBackslash:
            if tz.options.backslashBreakNewline:
              tz.queue.delete(0)
              breakNewline = true
              breakIndent = true
          of tkComma:
            if tz.options.commaIgnoreIndent:
              breakIndent = true
          else: discard # impossible
          if not breakNewline:
            queue(tkNewline)
          tz.queueMode = ClearQueue
        elif w:
          if tz.lastKind != tkWhitespace:
            queue(tkWhitespace, NewlineQueue)
        else:
          tz.resetPos()
          tz.queueMode = ClearQueue
    elif w:
      if c == '\n':
        tz.recordingIndent = true
        add(tkNewLine)
      elif tz.lastKind != tkWhitespace:
        add(tkWhitespace)
    elif c.isAlpha or c == '_':
      # identifier start
      tz.resetPos()
      let word = recordWord(tz)
      if word.len < shortStringMaxSize and
        (let ss = word.toShortString; ss in tz.options.symbolWords):
        add Token(kind: tkSymbol, short: ss)
      else:
        add Token(kind: tkWord, raw: word)
    elif c.int32 > 127:
      # non-space and non-alpha unicode char, so symbol start
      tz.resetPos()
      add Token(kind: tkSymbol, short: recordSymbol(tz).toShortString)
    else:
      let ch = c.char
      template dotColon(k: TokenKind, startChar: char) =
        let s = recordSymbolPlus(tz, ch)
        if s.len == 1:
          add Token(kind: k)
        else:
          add Token(kind: tkSymbol, short: s.toShortString)
      template openDelim(kind: TokenKind) =
        tz.indentContexts.add(IndentContext())
        add kind
      template closeDelim(kind: TokenKind) =
        if tz.indentContexts.len > 1:
          tz.indentContexts.setLen(tz.indentContexts.high)
        add kind
      case ch
      of '#': tz.comment = true
      of '\\': queue(tkBackslash, NewlineQueue)
      of ',': queue(tkComma, NewlineQueue)
      of '.': dotColon tkDot, '.'
      of ':': dotColon tkColon, ':'
      of ';': add tkSemicolon
      of '(': openDelim tkOpenParen
      of '[': openDelim tkOpenBrack
      of '{': openDelim tkOpenCurly
      of ')': closeDelim tkCloseParen
      of ']': closeDelim tkCloseBrack
      of '}': closeDelim tkCloseCurly
      of '\'', '"', '`':
        let s = recordString(tz, ch)
        case c.asChar
        of '`':
          add Token(kind: tkQuotedWord, raw: s)
        of '\'':
          add Token(kind: tkSingleQuoteString, content: s)
        else:
          add Token(kind: tkString, content: s)
      of '0'..'9':
        tz.resetPos()
        let n = recordNumber(tz)
        add Token(kind: tkNumber, num: n)
      of '+', '-':
        if tz.peekCharOrZero() in {'0'..'9'}:
          add Token(kind: tkNumber, num: recordNumber(tz, ch == '-'))
        else:
          tz.resetPos()
          add Token(kind: tkSymbol, short: recordSymbol(tz).toShortString)
      else:
        # non-alpha, so symbol start
        tz.resetPos()
        add Token(kind: tkSymbol, short: recordSymbol(tz).toShortString)

proc tokenize*(tz: var Tokenizer): seq[Token] =
  tz.resetTokenizer()
  while (let tok = tz.nextToken(); tok.kind != tkNone):
    result.add(tok)

proc tokenize*(str: string): seq[Token] =
  var tokenizer = newTokenizer(str)
  tokenize(tokenizer)

when isMainModule:
  import times, sequtils
  template bench*(body) =
    let a = cpuTime()
    for i in 1..10000000: body
    let b = cpuTime()
    echo "took ", b - a
  let s = "foo(\"a\" \"abcd\")"
  echo system.`$`(tokenize(s))
  echo $tokenize(s).mapIt(it.kind)
