import tables, hashes

type
  CachedFile* = distinct uint32
  
  Info* = object
    file*: CachedFile
    line*, column*: uint16

proc `==`*(a, b: CachedFile): bool {.borrow.}
template hash*(a: CachedFile): Hash = hash(uint32(a))

when defined(nimscript):
  {.pragma: notCompileTime, compileTime.}
else:
  {.pragma: notCompileTime.}

var
  fileCacheVar {.notCompileTime.}: Table[CachedFile, tuple[filename: string, filenameHash: Hash]] # !global

proc getCachedFile*(filename: string): CachedFile =
  let hash = hash(filename)
  for id, (fn, h) in fileCacheVar:
    if hash == h and filename == fn:
      return id
  result = CachedFile(fileCacheVar.len)
  fileCacheVar[result] = (filename, hash)

proc `$`*(a: CachedFile): string =
  fileCacheVar.getOrDefault(a, (filename: "<unknown file>", filenameHash: 0)).filename

proc `$`*(info: Info): string =
  result = $info.file & "(" & $info.line & ", " & $info.column & ")"
