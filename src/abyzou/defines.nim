## options for tuning

const
  # if using unicode in JS, turn bound checks off
  useUnicode* {.booldefine: "abyzou.unicode".} = true
    ## treat unicode alpha and whitespace characters accordingly in tokenizer
  doLineColumn* {.booldefine: "abyzou.lineColumn".} = true
  refToken* {.booldefine: "abyzou.refToken".} = defined(js)
    ## make token type a reference rather than a value type
  arrayImpl* {.strdefine: "abyzou.arrayImpl".} =
    when (NimMajor, NimMinor) >= (2, 2):
      "mantavalue"
    else:
      "manta"
  useBytecode* {.booldefine: "abyzou.bytecode".} = true
  largeValue* {.booldefine: "abyzou.largeValue".} = true
    ## whether or not to fully embrace values that only fit in 64 bits
    ## in the future can be used to disable pointer tagging
