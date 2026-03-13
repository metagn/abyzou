import ../defines

when arrayImpl == "seq":
  template distinctSeq(name) {.dirty.} =
    type `name`*[T] = distinct seq[T]

    proc `new name`*[T](len: int): `name`[T] =
      `name`[T](newSeq[T](len))

    template `to name`*[T](x: openarray[T]): `name`[T] =
      `name`[T](@x)

    template toSeq*[T](arr: `name`[T]): seq[T] = seq[T](arr)
    converter toSeqConverter*[T](arr: `name`[T]): seq[T] = toSeq(arr)

    template len*[T](arr: `name`[T]): int =
      toSeq(arr).len

    template `[]`*[T](arr: `name`[T], index): untyped =
      `[]`(toSeq(arr), index)

    template `[]=`*[T](arr: `name`[T], index, value) =
      `[]=`(toSeq(arr), index, value)

    template hash*[T](arr: `name`[T]): untyped =
      mixin hash
      hash(toSeq(arr))

    template `==`*[T](a, b: `name`[T]): untyped =
      mixin `==`
      `==`(toSeq(a), toSeq(b))
    
    template `$`*[T](a: `name`[T]): string =
      `$`(toSeq(a))[1..^1]

  distinctSeq Array
elif arrayImpl == "hybrid":
  import ../disabled/hybridarrays
  export hybridarrays
elif arrayImpl == "manta":
  import manta/refarray
  export refarray
  type Array*[T] = RefArray[T]
  template toArray*[T](foo: openarray[T]): RefArray =
    toRefArray[T](foo)
  template initArray*[T](foo): RefArray[T] =
    newArray[T](foo)
  template unref*[T](arr: RefArray[T]): Array[T] =
    arr
elif arrayImpl == "mantavalue":
  # needs https://github.com/nim-lang/Nim/pull/24194
  import manta
  export manta
  proc unref*[T](arr: RefArray[T]): Array[T] {.inline.} =
    toArray(arr.toOpenArray(0, arr.len - 1))

when not declared(RefArray):
  type RefArray*[T] = ref Array[T]
  template toRefArray*(foo): RefArray =
    var res = new(typeof(toArray(foo)))
    res[] = toArray(foo)
    res

  proc len*[T](arr: RefArray[T]): int =
    if arr.isNil: 0 else: arr[].len

  template `[]`*[T](arr: RefArray[T], index): untyped =
    arr[][index]

  template `[]=`*[T](arr: RefArray[T], index, value) =
    arr[][index] = value
  
  iterator items*[T](arr: RefArray[T]): T =
    if not arr.isNil:
      for a in arr[]:
        yield a
  
  proc `$`*[T](a: RefArray[T]): string {.inline.} =
    if a.isNil: "" else: $a[]

  proc `==`*[T](a, b: RefArray[T]): bool {.inline.} =
    mixin `==`
    system.`==`(a, b) or (not a.isNil and not b.isNil and a[] == b[])

  import hashes

  proc hash*[T](x: RefArray[T]): Hash =
    mixin hash
    if x.isNil:
      hash(pointer nil)
    else:
      hash(x[])
