const pointerTaggable* = sizeof(pointer) == 8

when pointerTaggable:
  type TaggedPointer* = uint64

  proc untagPointer*(x: TaggedPointer): pointer =
    if bool((x shr 47) and 1):
      cast[pointer]((x or 0xFFFF_0000_0000_0000'u64) and 0xFFFF_FFFF_FFFF_FFF8'u64)
    else:
      cast[pointer](x and 0x0000_FFFF_FFFF_FFF8'u64)

  proc tagPointer*(p: pointer, first2Bytes: uint16, last3Bits: range[0..7] = 0): TaggedPointer =
    ((cast[uint64](p) or last3Bits.TaggedPointer) and 0x0000_FFFF_FFFF_FFFF'u64) or
      (first2Bytes.uint64 shl 48)
