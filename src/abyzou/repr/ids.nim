import std/hashes

type
  IdImpl = uint64

template id(kind) {.dirty.} =
  type `kind Id`* = distinct IdImpl
  proc `==`*(a, b: `kind Id`): bool {.borrow.}
  proc hash*(a: `kind Id`): Hash {.borrow.}
  # 0 reserved for none values
  # can change with something else later
  var `counter kind`: IdImpl = 0 # !global
  proc `new kind Id`*(): `kind Id` =
    inc `counter kind`
    `kind Id`(`counter kind`)

id(TypeBase)
id(TypeParameter)
id(Variable)
id(Module)

# XXX maybe intern identifiers or strings? - registry idea:
# StringRegistry library type, `id "abc"` returns a StringId mapped to "abc", then stringifying it looks up the id from the string registry and gives back "abc"
# could also make registries a generic thing and allow users to define their own, i guess as a sort of enum 
