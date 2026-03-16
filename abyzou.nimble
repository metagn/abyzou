# Package

version       = "0.1.0"
author        = "metagn"
description   = "bagy"
license       = "MIT"
srcDir        = "src"
installExt    = @["nim"]
skipDirs      = @["src/abyzou/disabled"]


# Dependencies

requires "nim >= 1.6.14"
requires "skinsuit >= 0.2.3"
requires "manta"
requires "https://github.com/metagn/hemodyne"

when (compiles do: import nimbleutils):
  import nimbleutils

task docs, "build docs for all modules":
  when declared(buildDocs):
    buildDocs(gitUrl = "https://github.com/metagn/abyzou")
  else:
    echo "docs task not implemented, need nimbleutils"

task tests, "run tests for multiple backends":
  when declared(runTests):
    runTests(@["tests/test_vm.nim"], optionCombos = @[
      "--mm:refc -d:abyzouUseBytecode=true",
      "--mm:refc -d:abyzouUseBytecode=false",
      "--mm:orc -d:abyzouUseBytecode=true",
      "--mm:orc -d:abyzouUseBytecode=false",
      #"--gc:orc -d:useMalloc",
      #"--gc:orc -d:danger",
      #"-d:abyzouUseUnicode=false",
      #"-d:abyzouDoLineColumn=false"
    ])
    runTests(@["tests/test_parser.nim"], backends = {c, js, nims})
  else:
    echo "tests task not implemented, need nimbleutils"

task buildall, "builds library and exe":
  echo "building all"
  exec "nim c -d:release --gc:orc --d:useMalloc --outdir:bin src/abyzou"
  exec "nim c --app:lib -d:release --gc:orc --d:useMalloc --outdir:bin src/abyzou"
  echo "done building"
