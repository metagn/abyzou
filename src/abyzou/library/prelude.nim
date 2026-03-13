import ../repr/primitives, ../vm/compilation

import ./[syntax, numbers, logic, types, collections]

proc prelude*: Scope =
  result = newModule(imports = @[syntax(), numbers(), logic(), types(), collections()]).top
  # todo:
  # modules & module system
  # reflection, metas
  # errors
  # iterators
  # functional stuff
  # comparisons, hashes
  # strings
  # random, json, times, io
