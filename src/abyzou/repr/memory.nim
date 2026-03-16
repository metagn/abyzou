import ./[primitives, arrays]

proc get*(stack: Memory, index: int): lent Value {.inline.} =
  stack.stack[index]
proc getMut*(stack: Memory, index: int): var Value {.inline.} =
  (addr stack.stack[index])[]
proc set*(stack: Memory, index: int, value: sink Value) {.inline.} =
  stack.stack[index] = value

proc newMemory*(initialSize = 4): Memory =
  let arr = newArray[Value](initialSize)
  result = Memory(stack: arr)

proc grow*(memory: var Memory, minLen: int) =
  if minLen > memory.stack.len:
    # double memory i guess:
    var newMem = newMemory(memory.stack.len + memory.stack.len)
    for i in 0 ..< memory.stack.len:
      let val = memory.get(i)
      newMem.set(i, val)
    memory = move newMem

proc shallowRefresh*(stack: Memory): Memory {.inline.} =
  result = newMemory(stack.stack.len)
  for i in 0 ..< stack.stack.len:
    let val = stack.get(i)
    result.set(i, val)
