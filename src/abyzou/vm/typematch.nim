import
  std/tables,
  ./[primitives, typebasics]

type
  TypeMatchError* = object of CatchableError
  ParameterMatchError* = object of TypeMatchError
    parameter*: TypeParameter
    presumed*: Type
    conflicting*: Type

const
  highestNonMatching* = tmUniversalFalse
  lowestMatching* = tmUniversalTrue

proc matches*(tm: MatchLevel): bool {.inline.} =
  tm >= lowestMatching

proc matches*(tm: TypeMatch): bool {.inline.} =
  matches(tm.level)

proc atomicMatch*(tm: MatchLevel): TypeMatch {.inline.} =
  TypeMatch(level: tm, deep: false)

proc boolMatch*(b: bool): TypeMatch {.inline.} =
  atomicMatch(if b: tmTrue else: tmFalse)

proc compare*(m1, m2: MatchLevel): int {.inline.} =
  ord(m1) - ord(m2)

proc compare*(a, b: TypeMatch): int =
  template propagate(x, y, comparer): untyped =
    let c = comparer(x, y)
    if c != 0: return c
  propagate a.level, b.level, compare
  # weird:
  propagate a.deep, b.deep, cmp
  if a.deep:
    propagate a.children.len, b.children.len, cmp
    for i in 0 ..< a.children.len:
      propagate a.children[i], b.children[i], compare
  0 # equal

proc `<`*(a, b: TypeMatch): bool = compare(a, b) < 0
proc `<=`*(a, b: TypeMatch): bool = compare(a, b) <= 0

proc min*(a, b: MatchLevel): MatchLevel {.inline.} =
  if a == tmNone: a
  else: system.min(a, b)

proc min*(a, b: TypeMatch): TypeMatch {.inline.} =
  if a.level == tmNone: a
  else: system.min(a, b)

proc minLevel*(lv: MatchLevel, m: TypeMatch): TypeMatch {.inline.} =
  result = m
  if result.level > lv: result.level = lv

proc converse*(tm: MatchLevel): MatchLevel =
  case tm
  of tmEqual, tmNone, tmSimilar, tmAlmostEqual, tmUnknown: tm
  of tmTrue: tmFalse
  of tmFalse: tmTrue
  of tmFiniteTrue, tmGeneric: tmFiniteFalse
  of tmFiniteFalse: tmFiniteTrue
  of tmUniversalFalse: tmUniversalTrue
  of tmUniversalTrue: tmUniversalFalse

proc converse*(tm: TypeMatch): TypeMatch =
  result = tm
  result.level = converse(result.level)
  if result.deep:
    for c in result.children.mitems:
      c = converse(c)

proc reorderTupleConstructor*(ct: var Type, t: Type, argumentStatements: var seq[Statement]) =
  assert ct.kind == tyTuple
  assert t.kind == tyTuple
  var newElems = newSeq[Type](ct.elements.len)
  var oldStmts, newStmts: seq[Statement]
  let doStmts = argumentStatements.len != 0
  if doStmts:
    assert ct.elements.len == argumentStatements.len
    oldStmts = argumentStatements
    newStmts = newSeq[Statement](oldStmts.len)
  for f, newI in t.elementNames:
    if f in ct.elementNames:
      let oldI = ct.elementNames[f]
      swap ct.elements[oldI], newElems[newI]
      if doStmts:
        swap oldStmts[oldI], newStmts[newI]
  var oldI = 0
  for i, newE in newElems.mpairs:
    if newE.isNoType:
      var
        oldE: Type
        oldStmt: Statement
      while oldE.isNoType and oldI < ct.elements.len:
        oldE = ct.elements[oldI]
        if doStmts: oldStmt = oldStmts[oldI]
        inc oldI
      newE = oldE
      if doStmts:
        assert not oldStmt.isNil
        newStmts[i] = oldStmt
    elif doStmts:
      assert not newStmts[i].isNil
  if doStmts:
    argumentStatements = newStmts

proc match*(matcher, t: Type, inst: var ParameterInstantiation): TypeMatch

proc match*(matcher, t: Type): TypeMatch {.inline.} =
  var dummy = ParameterInstantiation(strict: false)
  result = match(matcher, t, dummy)

proc match*(b: TypeBound, t: Type): TypeMatch =
  case b.variance
  of Covariant:
    result = b.boundType.match(t)
    if result.level == tmUnknown:
      result = converse t.match(b.boundType)
  of Contravariant:
    result = t.match(b.boundType)
    if result.level == tmUnknown:
      result = converse b.boundType.match(t)
  of Invariant:
    result = min(b.boundType.match(t), converse t.match(b.boundType))
  of Ultravariant:
    result = b.boundType.match(t)
    if result.level != tmNone:
      result = max(result, converse t.match(b.boundType))

proc matchBound*(b: TypeBound, t: Type): bool {.inline.} =
  b.match(t).matches

proc commonSubType*(a, b: Type, doUnion = true, variance = Covariant): Type =
  let m1 = (a * variance).match(b)
  let m2 = (b * variance).match(a)
  let cmp = compare(m1, m2)
  if cmp > 0:
    b
  elif cmp < 0:
    a
  elif m1.level in {tmEqual, tmAlmostEqual}:
    a
  elif doUnion: # union here meaning either
    union(a, b)
  else:
    NoType

proc commonSuperType*(a, b: Type, doUnion = true, variance = Covariant): Type =
  let m1 = (a * variance).match(b)
  let m2 = (b * variance).match(a)
  let cmp = compare(m1, m2)
  if cmp > 0:
    a
  elif cmp < 0:
    b
  elif m1.level in {tmEqual, tmAlmostEqual}:
    a
  elif doUnion:
    union(a, b)
  else:
    NoType

proc match*(matcher, t: Type, inst: var ParameterInstantiation): TypeMatch =
  # commutativity rules:
  # must be commutative when equal
  # otherwise either order can give none, in which the non-none result matters
  # otherwise generally should be anticommutative, but this is not necessary
  # properties do not have effect on default types besides dropping equal to almost equal
  if matcher == t: return atomicMatch(tmEqual)
  result = case matcher.kind
  of tyNoType: atomicMatch(tmUnknown)
  of tyInstance:
    if unlikely(not matcher.instanceBase.typeMatcher.isNil):
      matcher.instanceBase.typeMatcher(matcher, t, inst)
    else:
      # XXX native type normalization here
      let mnt = matcher.instanceBase.nativeType
      let tnt =
        case t.kind
        of tyInstance: t.instanceBase.nativeType
        #of tyBase: t.typeBase.nativeType
        #of tyNativeBase: t.nativeBase
        else: t.kind
      if mnt != tnt:
        return if {mnt, tnt} <= concreteTypeKinds:
          atomicMatch(tmNone)
        else:
          atomicMatch(tmUnknown)
      if t.kind == tyInstance and matcher.instanceBase != t.instanceBase: return atomicMatch(tmUnknown)
      let margBounds {.cursor.} = matcher.instanceBase.arguments
      let targs {.cursor.} =
        case t.kind
        of tyInstance: t.instanceArgs
        #of tyBase, tyNativeBase: @[]
        else: t.nativeArgs
      var res = atomicMatch(tmAlmostEqual)
      let len = margBounds.len
      if len > 0:
        res = TypeMatch(level: tmAlmostEqual, deep: true)
        res.children.newSeq(len)
        for i in 0 ..< len:
          let v = margBounds[i].bound.variance
          let m = match(matcher.instanceArgs[i] * v, targs[i])
          res.children[i] = m
          if m.level < res.level: res.level = m.level
          if res.level <= tmNone: return res
      res
  of nativeTypes * concreteTypeKinds:
    # XXX native type normalization here
    let tnt =
      case t.kind
      of tyInstance: t.instanceBase.nativeType
      #of tyBase: t.typeBase.nativeType
      #of tyNativeBase: t.nativeBase
      else: t.kind
    if matcher.kind != tnt:
      return if tnt in concreteTypeKinds:
        atomicMatch(tmNone)
      else:
        atomicMatch(tmUnknown)
    let margBounds {.cursor.} = nativeTypeArgs[matcher.kind]
    let targs {.cursor.} =
      case t.kind
      of tyInstance: t.instanceArgs
      #of tyBase, tyNativeBase: @[]
      else: t.nativeArgs
    var res = atomicMatch(tmAlmostEqual)
    let len = margBounds.len#matcher.instanceBase.arguments.len
    if len > 0:
      res = TypeMatch(level: tmAlmostEqual, deep: true)
      res.children.newSeq(len)
      for i in 0 ..< len:
        let v = margBounds[i].variance
        let m = match(matcher.nativeArgs[i] * v, targs[i])
        res.children[i] = m
        if m.level < res.level: res.level = m.level
        if res.level <= tmNone: return res
    res
  of tyTuple:
    # XXX no native type normalization here
    if matcher.kind != t.kind:
      return if t.kind in concreteTypeKinds:
        atomicMatch(tmNone)
      else:
        atomicMatch(tmUnknown)
    if matcher.elements.len != t.elements.len and matcher.varargs.isNoType and t.varargs.isNoType:
      return atomicMatch(tmNone)
    var max = t.elements.len
    if matcher.elements.len > t.elements.len and (max = matcher.elements.len; t.varargs.isNoType):
      return atomicMatch(tmNone)
    var res = atomicMatch(tmAlmostEqual)
    if max > 0:
      res = TypeMatch(level: tmAlmostEqual, deep: true)
      res.children.newSeq(max)
      for i in 0 ..< max:
        let m = match(+matcher.nth(i), t.nth(i))
        res.children[i] = m
        if m.level < res.level: res.level = m.level
        if res.level <= tmNone: return res
    if not matcher.varargs.isNoType and not t.varargs.isNoType:
      let vm = match(+matcher.varargs.unbox, t.varargs.unbox)
      if vm.level < res.level: res.level = vm.level
    res
  of tyAny: atomicMatch(tmUniversalTrue)
  of tyAll: atomicMatch(tmUniversalFalse)
  of tyUnion:
    var max = TypeMatch(level: tmFiniteFalse, deep: true, children: @[atomicMatch(tmUnknown)])
    for a in matcher.operands:
      let m = match(+a, t)
      if m > max.children[0]:
        max.children[0] = m
        if m.level >= tmFiniteTrue:
          max.level = tmFiniteTrue
          break
    max
  of tyIntersection:
    var min = TypeMatch(level: tmFiniteTrue, deep: true, children: @[atomicMatch(tmAlmostEqual)])
    for a in matcher.operands:
      let m = match(+a, t)
      if m < min.children[0]:
        min.children[0] = m
        if m.level <= tmFiniteFalse:
          min.level = tmFiniteFalse
          break
    min
  of tyNot:
    boolMatch not match(matcher.notType.unbox, t).matches
  of tyNativeBase:
    # XXX native type normalization here
    let mnt = matcher.nativeBase
    case t.kind
    of tyBase:
      if mnt == t.typeBase.nativeType: atomicMatch(tmAlmostEqual)
      else: atomicMatch(tmNone)
    of tyNativeBase:
      if mnt == t.nativeBase: atomicMatch(tmAlmostEqual)
      else: atomicMatch(tmNone)
    of tyInstance:
      boolMatch mnt == t.instanceBase.nativeType
    elif t.kind == mnt: atomicMatch(tmTrue)
    else: atomicMatch(tmNone)
    # XXX [typematch] use unknown?
  of tyBase:
    # XXX native type normalization here
    let mnt = matcher.typeBase.nativeType
    # in nim a dummy instance type is created from the base and compared
    if mnt != tyNoType:
      case t.kind
      of tyBase:
        if matcher.typeBase == t.typeBase or mnt == t.typeBase.nativeType: atomicMatch(tmAlmostEqual)
        else: atomicMatch(tmNone)
      of tyNativeBase:
        if mnt == t.nativeBase: atomicMatch(tmAlmostEqual)
        else: atomicMatch(tmNone)
      of tyInstance:
        boolMatch matcher.typeBase == t.instanceBase or mnt == t.instanceBase.nativeType
      elif t.kind == mnt: atomicMatch(tmTrue)
      else: atomicMatch(tmNone)
    else:
      case t.kind
      of tyBase:
        if matcher.typeBase == t.typeBase: atomicMatch(tmAlmostEqual)
        else: atomicMatch(tmNone)
      of tyInstance:
        boolMatch matcher.typeBase == t.instanceBase
      else: atomicMatch(tmNone)
    # XXX [typematch] use unknown?
  of tyTupleConstructor:
    # XXX native type normalization here???
    case t.kind
    of tyInstance:
      if t.instanceBase.nativeType == tyTupleConstructor:
        match(matcher.nativeArgs[0], t.instanceArgs[0])
      # XXX [typematch, tuple] no tuple support here
      else: atomicMatch(tmUnknown)
    of tyTuple:
      var mr = matcher.nativeArgs[0]
      var dummy: seq[Statement]
      reorderTupleConstructor(mr, t, dummy)
      match(mr, t)
    else: atomicMatch(tmUnknown)
  of tySomeValue:
    case t.kind
    of tySomeValue:
      minLevel(
        tmAlmostEqual,
        match(+matcher.someValueType.unbox, t.someValueType.unbox))
    of tyValue:
      minLevel(
        tmSimilar,
        match(+matcher.someValueType.unbox, t.valueType.unbox))
    else: atomicMatch(tmNone)
  of tyParameter:
    let param = matcher.parameter
    let boundMatch = match(param.bound, t)
    if not boundMatch.matches:
      return boundMatch
    var newType = t
    if param in inst.table:
      let oldType = inst.table[param]
      newType = commonSuperType(oldType, newType, doUnion = false, variance = param.bound.variance)
      if newType.isNoType and inst.strict:
        raise (ref ParameterMatchError)(
          msg: "param " & $param & " had type " & $newType & " but got " & $t,
          parameter: param,
          presumed: oldType,
          conflicting: t)
    inst.table[param] = newType
    minLevel(
      tmGeneric,
      match(newType, t))
  of tyValue:
    case t.kind
    of tyValue:
      let tm = match(matcher.valueType.unbox, t.valueType.unbox)
      if not tm.matches or matcher.value != t.value:
        atomicMatch(tmNone)
      else: tm
    of tySomeValue: atomicMatch(tmUnknown)
    else: atomicMatch(tmNone)
  if result.level > tmAlmostEqual:
    result.level = tmAlmostEqual
  if result.matches:
    for p, args in matcher.properties:
      if not p.typeMatcher.isNil:
        result = min(result, p.typeMatcher(t, args, inst))
        if result.level <= tmNone: return result

proc compare*(t1, t2: Type): int =
  ## t1 < t2 mirrors being a subtype
  let
    m1 = t1.match(t2)
    m2 = t2.match(t1)
  assert not (m1.level == tmEqual and m1 != m2), "equal match must be commutative"
  compare(m1, m2)

proc `<`*(a, b: Type): bool {.inline.} = compare(a, b) < 0
proc `<=`*(a, b: Type): bool {.inline.} = compare(a, b) <= 0
proc `>`*(a, b: Type): bool {.inline.} = compare(a, b) > 0
proc `>=`*(a, b: Type): bool {.inline.} = compare(a, b) >= 0
