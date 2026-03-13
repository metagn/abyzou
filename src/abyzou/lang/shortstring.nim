runnableExamples:
  block:
    for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
      block:
        let ss = s.toShortString
        doAssert $ss == s, $(ss, s)
        for i in 0 ..< s.len:
          doAssert s[i] == ss[i]
      block:
        let ss = s.toShortString(optimized = false)
        doAssert $ss == s, $(ss, s)
        for i in 0 ..< s.len:
          doAssert s[i] == ss[i]
    doAssert short"ab" < short"abc"
    doAssert short"ab" < short"ac"
    doAssert short"ab" < short"bb"
    doAssert toShortString"ab" < toShortString"abc"
    doAssert toShortString"ab" < toShortString"ac"
    doAssert toShortString"ab" < toShortString"bb"

when sizeof(uint) == 8:
  type ShortString* = distinct uint
  template impl(ss: ShortString): uint = uint(ss)
  const shortStringIsArray* = false

  proc `==`*(a, b: ShortString): bool {.borrow.}
  proc `<`*(a, b: ShortString): bool {.borrow.}
else:
  type ShortString* = distinct array[2, uint32]
  template impl(ss: ShortString): array[2, uint32] = array[2, uint32](ss)
  const shortStringIsArray* = true

  proc `==`*(a, b: ShortString): bool =
    (a.impl[0] == b.impl[0]) and (a.impl[1] == b.impl[1])
  proc `<`*(a, b: ShortString): bool =
    (a.impl[0] < b.impl[0]) or (a.impl[0] == b.impl[0] and a.impl[1] < b.impl[1])

  import macros

  macro `case`*(ss: ShortString): untyped =
    result = newNimNode(nnkCaseStmt, ss)
    result.add(newCall(ident"$", ss[0]))
    for i in 1 ..< ss.len:
      let n = ss[i]
      if n.kind == nnkOfBranch:
        var b = newNimNode(nnkOfBranch, n)
        for i in 0 ..< n.len - 1:
          b.add(newCall(ident"$", n[i]))
        b.add(n[^1])
        result.add(b)
      else:
        result.add(n)

const shortStringMaxSize* = sizeof(ShortString) div sizeof(char)
const charBits = sizeof(char) * 8

template get(ss: ShortString, i: int): char =
  when shortStringIsArray:
    char(
      (ss.impl[i shr 2] shr ((i and 0b11) * charBits)) and
        high(char).uint32)
  else:
    char(
      (ss.uint shr (i * charBits)) and
        high(char).uint)

template set(ss: var ShortString, i: int, c: char) =
  when shortStringIsArray:
    let idx = i shr 2
    ss.impl[idx] = ss.impl[idx] or (c.uint32 shl ((i and 0b11) * charBits))
  else:
    ss = ShortString(ss.uint or
      (c.uint shl (i * charBits)))

proc `[]`*(ss: ShortString, i: int): char {.inline.} =
  rangeCheck i >= 0 and i < shortStringMaxSize
  {.push checks: off.}
  result = get(ss, i)
  {.pop.}

proc `[]=`*(ss: var ShortString, i: int, c: char) {.inline.} =
  rangeCheck i >= 0 and i < shortStringMaxSize
  {.push checks: off.}
  set(ss, i, c)
  {.pop.}

proc len*(ss: ShortString): int =
  # unrolled loop
  {.push checks: off.}
  template doIndex(i: int) =
    if get(ss, i) == char(0):
      return i
  doIndex 0
  doIndex 1
  doIndex 2
  doIndex 3
  doIndex 4
  doIndex 5
  doIndex 6
  doIndex 7
  return 8
  {.pop.}

template `[]`*(ss: ShortString, i: BackwardsIndex): char =
  ss[ss.len - i.int]

template `[]=`*(ss: var ShortString, i: BackwardsIndex, c: char) =
  ss[ss.len - i.int] = c

proc `[]`*(ss: ShortString, sl: Slice[int]): ShortString {.inline.} =
  rangeCheck sl.a >= 0 and sl.a < shortStringMaxSize and sl.b >= 0 and sl.b < shortStringMaxSize
  when shortStringIsArray:
    {.push checks: off.}
    for i in sl.a .. sl.b:
      set(result, i - sl.a, get(ss, i))
    {.pop.}
  else:
    ShortString((ss.uint shl (sl.a * charBits)) shr ((sl.len - sl.b + sl.a - 1) * charBits))

proc `[]=`*(ss: var ShortString, sl: Slice[int], ss2: ShortString) {.inline.} =
  rangeCheck sl.a >= 0 and sl.a < shortStringMaxSize and sl.b >= 0 and sl.b < shortStringMaxSize
  {.push checks: off.}
  for i in sl:
    set(ss, i, get(ss2, i - sl.a))
  {.pop.}

iterator items*(ss: ShortString): char =
  # not unrolled because nim doesnt allow return
  {.push checks: off.}
  var i = 0
  while i < shortStringMaxSize:
    let c = get(ss, i)
    if c == char(0):
      break
    yield c
    inc i
  {.pop.}

when not defined(js) and not defined(nimscript):
  when defined(gcc) or defined(llvm_gcc) or defined(clang):
    when shortStringMaxSize == 2:
      proc swapEndian(a: uint): uint {.
          importc: "__builtin_bswap16", nodecl, noSideEffect.}
    elif shortStringMaxSize == 4:
      proc swapEndian(a: uint): uint {.
          importc: "__builtin_bswap32", nodecl, noSideEffect.}
    elif shortStringMaxSize == 8:
      proc swapEndian(a: uint): uint {.
          importc: "__builtin_bswap64", nodecl, noSideEffect.}
  elif defined(icc):
    when shortStringMaxSize == 2:
      proc swapEndian(a: uint): uint {.
          importc: "_bswap16", nodecl, noSideEffect.}
    elif shortStringMaxSize == 4:
      proc swapEndian(a: uint): uint {.
          importc: "_bswap", nodecl, noSideEffect.}
    elif shortStringMaxSize == 8:
      proc swapEndian(a: uint): uint {.
          importc: "_bswap64", nodecl, noSideEffect.}
  elif defined(vcc):
    when shortStringMaxSize == 2:
      proc swapEndian(a: uint): uint {.
          importc: "_byteswap_ushort", nodecl, header: "<intrin.h>", noSideEffect.}
    elif shortStringMaxSize == 4:
      proc swapEndian(a: uint): uint {.
          importc: "_byteswap_ulong", nodecl, header: "<intrin.h>", noSideEffect.}
    elif shortStringMaxSize == 8:
      proc swapEndian(a: uint): uint {.
          importc: "_byteswap_uint64", nodecl, header: "<intrin.h>", noSideEffect.}
  when declared(swapEndian):
    template toLittleEndian(x: uint): uint =
      when cpuEndian == bigEndian:
        swapEndian(x)
      else:
        x

proc `$`*(ss: ShortString, optimized: static bool = true): string =
  {.push checks: off.}
  when nimvm:
    result = newStringOfCap(sizeof(ShortString))
    for c in ss.items:
      result.add(c)
  else:
    when defined(js) or defined(nimscript) or not optimized or (cpuEndian == bigEndian and not declared(swapEndian)):
      result = newStringOfCap(sizeof(ShortString))
      for c in ss.items:
        result.add(c)
    else:
      # this should be faster than adding one at a time, but we still have to calculate length
      if ss.uint == 0:
        result = ""
      else:
        result = newString(ss.len)
        cast[ptr uint](addr result[0])[] = toLittleEndian(ss.uint)
  {.pop.}

iterator mitems*(ss: var ShortString): var char =
  {.push checks: off.}
  var i = 0
  while i < shortStringMaxSize:
    var c = get(ss, i)
    if c == char(0):
      break
    yield addr(c)[]
    ss[i] = c
    inc i
  {.pop.}

proc add*(ss: var ShortString, c: char) =
  {.push checks: off.}
  var i = 0
  while i < shortStringMaxSize:
    let c = get(ss, i)
    if c == char(0):
      set(ss, i, c)
      return
    inc i
  {.pop.}
  assert false, "string " & $ss & " is full"

proc toShortString*(s: openarray[char], optimized: static bool = true): ShortString =
  rangeCheck s.len <= shortStringMaxSize
  {.push checks: off.}
  when nimvm:
    for i, c in s:
      result[i] = c
  else:
    when defined(js) or defined(nimscript) or not optimized or (cpuEndian == bigEndian and not declared(swapEndian)):
      for i, c in s:
        result[i] = c
    else:
      let L = s.len
      if L == 0:
        # bypass nil
        result = ShortString(0)
      else:
        let offset = shortStringMaxSize - L
        result = ShortString(
          (cast[ptr uint](unsafeAddr s[0])[].toLittleEndian shl
            (offset * charBits)) shr
              (offset * charBits))
  {.pop.}

template short*(s: static string): ShortString =
  toShortString(s)

when isMainModule:
  import times
  template bench(body) =
    let a = cpuTime()
    body
    let b = cpuTime()
    echo "took ", b - a
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString.len
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString(false).len
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString.len
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString(false).len
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString.len
  bench:
    for i in 1..50000000:
      for s in ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh"]:
        discard s.toShortString(false).len
