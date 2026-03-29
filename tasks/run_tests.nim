when (compiles do: import nimbleutils):
  import nimbleutils

when not declared(runTests):
  {.fatal: "tests task not implemented, need nimbleutils".}

var comboMatrix = [
  @["--mm:orc", "-mm:refc"],
  @["-d:abyzou.bytecode=true", "-d:abyzou.bytecode=false"],
  @["-d:abyzou.largeValue=true", "-d:abyzou.largeValue=false"]
  #"--gc:orc -d:useMalloc",
  #"--gc:orc -d:danger",
  #"-d:abyzou.unicode=false",
  #"-d:abyzou.lineColumn=false"
]

var combos = comboMatrix[0]
for rowI in 1 ..< comboMatrix.len:
  var nextCombos: seq[string] = @[]
  for a in combos:
    for b in comboMatrix[rowI]:
      var s = a
      s.add ' '
      s.add b
      nextCombos.add s
  combos = nextCombos

runTests(@["tests/test_vm.nim"], optionCombos = combos)
runTests(@["tests/test_parser.nim"], backends = {c, js, nims})
