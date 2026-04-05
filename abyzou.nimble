# Package

version       = "0.1.0"
author        = "metagn"
description   = "scripting language"
license       = "MIT"
srcDir        = "src"
installExt    = @["nim"]
skipDirs      = @["src/abyzou/disabled"]


# Dependencies

requires "nim >= 2.0.0"
requires "skinsuit >= 0.2.3"
requires "manta"
requires "https://github.com/holo-nim/fleu"


task docs, "build docs for all modules":
  exec "nim r tasks/build_docs.nim"

task tests, "run tests for multiple backends":
  exec "nim r tasks/run_tests.nim"

task buildall, "builds library and exe":
  exec "nim r tasks/build.nim"
