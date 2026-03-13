type
  DigitSequence* = object
    pairs: seq[byte]
    last: byte

  NumberKind* = enum Integer, Floating, Unsigned

  NumberReprObj* = object
    digits*: DigitSequence
    kind*: NumberKind
    negative*: bool
    exp*: int16
    bits*: uint8

when defined(js):
  import skinsuit/equals
  type NumberRepr* = ref NumberReprObj
  equals *NumberRepr
else:
  type NumberRepr* = NumberReprObj

when false: {.hint: $sizeof(NumberRepr).}

proc odd(ds: DigitSequence): bool {.inline.} =
  ds.last shr 4 == 0

proc len*(ds: DigitSequence): int {.inline.} =
  (ds.pairs.len * 2) or ord(ds.odd)

iterator items*(ds: DigitSequence): byte =
  for p in ds.pairs:
    yield p shr 4
    yield p and 0xF
  if ds.odd:
    yield ds.last and 0xF

iterator pairs*(ds: DigitSequence): (int, byte) =
  var i = 0
  for p in ds.pairs:
    yield (i, p shr 4)
    yield (i + 1, p and 0xF)
    i += 2
  if ds.odd:
    yield (i, ds.last and 0xF)

proc toDigitSequence*[T](s: seq[T]): DigitSequence =
  let nl = s.len div 2
  result.pairs.newSeq(nl)
  for i in 0 ..< nl:
    result.pairs[i] =
      ((s[2 * i] and 0xF) shl 4) or
        (s[2 * i + 1] and 0xF)
  if s.len mod 2 != 0:
    result.last = s[^1] and 0xF
  else:
    result.last = 0xFF

proc `$`*(number: NumberRepr): string =
  var exponent: string
  let dotIndex =
    if number.kind == Floating and number.exp < 0 and -number.exp < number.digits.len:
      number.digits.len + number.exp - 1
    elif number.exp != 0:
      exponent = $(number.exp + number.digits.len - 1)
      if number.digits.len > 1:
        0
      else:
        -1
    else:
      -2
  let exactLen = number.negative.ord +
    number.digits.len +
    (dotIndex >= 0).ord +
    (if exponent.len != 0: exponent.len + 1 else: 0)
  result = newStringOfCap(exactLen)
  if number.negative:
    result.add('-')
  for i, d in number.digits:
    result.add(char('0'.byte + d))
    if i == dotIndex: result.add('.') 
  if exponent.len != 0:
    result.add('e')
    result.add(exponent)
  assert exactLen == result.len
