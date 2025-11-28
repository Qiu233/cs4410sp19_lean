import Cs4410sp19.MIR.Basic
import Cs4410sp19.MIR.MData

namespace Cs4410sp19
namespace MIR

structure Segment where
  start_inc : Nat
  end_inc : Nat
  used_pos : List Nat
deriving Inhabited, Repr, BEq, Hashable

structure Interval where
  segs : Array Segment
deriving Inhabited, Repr

instance : ToString Interval where
  toString x :=
    s!"[{String.intercalate ", " (x.segs.toList.map fun s => s!"[{s.start_inc}-{s.end_inc}]")}]"

def Interval.merge (x y : Interval) : Interval := Id.run do
  let mut res : Array Segment := #[]
  let mut i := 0
  let mut j := 0
  while i < x.segs.size || j < y.segs.size do
    let next ←
      if i < x.segs.size && (j ≥ y.segs.size || x.segs[i]!.start_inc ≤ y.segs[j]!.start_inc) then
        let curr := x.segs[i]!
        i := i + 1
        pure curr
      else
        let curr := y.segs[j]!
        j := j + 1
        pure curr
    if res.isEmpty then
      res := res.push next
    else
      let last := res.back!
      if last.end_inc + 1 ≥ next.start_inc then
        let used := (last.used_pos ++ next.used_pos).mergeSort.eraseDups
        res := res.pop.push ⟨last.start_inc, Nat.max last.end_inc next.end_inc, used⟩
      else
        res := res.push next
  return ⟨res⟩

structure ValDef where
  d : DefUse
  def_pos : Nat
deriving Inhabited, Repr, Hashable, BEq

def BasicBlock.lineno_start (b : BasicBlock InstMData String AbsLoc) : Nat :=
  b.insts[0]?.map Inst.tag |>.getD b.terminal.tag |>.lineno

def BasicBlock.lineno_end (b : BasicBlock InstMData String AbsLoc) : Nat :=
  b.insts.back?.map Inst.tag |>.getD b.terminal.tag |>.lineno

structure LivenessMaps where
  liveIn : Std.HashMap String Bool
  liveOut : Std.HashMap String Bool
deriving Inhabited

structure LivenessCache where
  data : Std.HashMap DefUse LivenessMaps := {}
deriving Inhabited

abbrev LivenessM := StateM LivenessCache

private def blockLiveIn (v : DefUse) (block : BasicBlock InstMData String AbsLoc) (outVal : Bool) :
    Bool := Id.run do
  let tags := block.insts.map Inst.tag |>.push block.terminal.tag
  let mut defined := false
  for tag in tags do
    if tag.is_used v then
      if defined then
        return false
      else
        return true
    if tag.is_def v then
      defined := true
  return outVal

private def computeLiveness (cfg : CFG' InstMData String AbsLoc) (v : DefUse) : LivenessMaps :=
  Id.run do
    let mut liveIn : Std.HashMap String Bool := {}
    let mut liveOut : Std.HashMap String Bool := {}
    for block in cfg.blocks do
      liveIn := liveIn.insert block.id false
      liveOut := liveOut.insert block.id false
    let mut changed := true
    while changed do
      changed := false
      for block in cfg.blocks do
        let succs := cfg.succ block.id
        let outVal :=
          if succs.isEmpty then
            false
          else
            succs.any fun s => liveIn[s]?.getD false
        let inVal := blockLiveIn v block outVal
        let oldOut := liveOut[block.id]?.getD false
        if outVal ≠ oldOut then
          liveOut := liveOut.insert block.id outVal
          changed := true
        let oldIn := liveIn[block.id]?.getD false
        if inVal ≠ oldIn then
          liveIn := liveIn.insert block.id inVal
          changed := true
    { liveIn, liveOut }

private def getLivenessMaps (cfg : CFG' InstMData String AbsLoc) (v : DefUse) :
    LivenessM LivenessMaps := do
  let cache ← get
  match cache.data[v]? with
  | some maps => pure maps
  | none =>
      let maps := computeLiveness cfg v
      modify fun s => { s with data := s.data.insert v maps }
      pure maps

private def liveInBlock (maps : LivenessMaps) (b : String) : Bool :=
  maps.liveIn[b]?.getD false

private def liveOutBlock (maps : LivenessMaps) (b : String) : Bool :=
  maps.liveOut[b]?.getD false

mutual
  partial def propagateInterval
      (cfg : CFG' InstMData String AbsLoc) (maps : LivenessMaps)
      (v : DefUse) (b : String) : Interval := Id.run do
    let some block := cfg.get? b | unreachable!
    let start := block.lineno_start * 2
    let mut uses := #[]
    let tags := block.insts.map Inst.tag |>.push block.terminal.tag
    for tag in tags do
      if tag.is_used v then
        uses := uses.push (tag.lineno * 2)
      if tag.is_def v then
        return ⟨#[⟨start, tag.lineno * 2, uses.toList⟩]⟩
    if ¬ liveOutBlock maps block.id then
      assert! !uses.isEmpty
      let lastUsed := uses.map (· + 1) |>.foldl (init := start) max
      return ⟨#[⟨start, lastUsed, uses.toList⟩]⟩
    let mut itv : Interval := ⟨#[⟨start, block.lineno_end * 2 + 1, uses.toList⟩]⟩
    for s in cfg.succ block.id do
      if liveInBlock maps s then
        itv := itv.merge (propagateInterval cfg maps v s)
    return itv

  partial def livenessOfDefWithMaps
      (cfg : CFG' InstMData String AbsLoc) (maps : LivenessMaps)
      (v : DefUse) (def_pos : Nat) : Interval := Id.run do
    assert! def_pos % 2 == 1
    let def_lineno := def_pos / 2
    let some block := cfg.blocks.find? (fun b => b.lineno_start ≤ def_lineno && def_lineno ≤ b.lineno_end)
      | unreachable!
    if block.insts.isEmpty then
      unreachable!
    let instIdx := def_lineno - block.lineno_start
    let inst := block.insts[instIdx]!
    assert! inst.tag.is_def v
    let mut uses := #[]
    let tags := block.insts[instIdx + 1:].toArray.map Inst.tag |>.push block.terminal.tag
    for tag in tags do
      if tag.is_used v then
        uses := uses.push (tag.lineno * 2)
      if tag.is_def v then
        return ⟨#[⟨def_pos, tag.lineno * 2, uses.toList⟩]⟩
    if ¬ liveOutBlock maps block.id then
      let ending := uses.map (· + 1) |>.foldl (init := def_pos) max
      return ⟨#[⟨def_pos, ending, uses.toList⟩]⟩
    let mut itv : Interval := ⟨#[⟨def_pos, block.lineno_end * 2 + 1, uses.toList⟩]⟩
    for s in cfg.succ block.id do
      if liveInBlock maps s then
        itv := itv.merge (propagateInterval cfg maps v s)
    return itv
end

def liveness_of_def (cfg : CFG' InstMData String AbsLoc) (v : DefUse) (def_pos : Nat) :
    LivenessM Interval := do
  let maps ← getLivenessMaps cfg v
  pure (livenessOfDefWithMaps cfg maps v def_pos)

def build_live_intervals (cfg : CFG' InstMData String AbsLoc) : Std.HashMap ValDef Interval :=
  Id.run do
    let work : LivenessM (Std.HashMap ValDef Interval) := do
      let mut intervals : Std.HashMap ValDef Interval := {}
      let defs := cfg.blocks.flatMap fun b => b.insts.flatMap fun i => i.tag.defs.map fun d => (d, i.tag.lineno * 2 + 1)
      for (d, pos) in defs do
        let itv ← liveness_of_def cfg d pos
        intervals := intervals.insert ⟨d, pos⟩ itv
      return intervals
    let (result, _) := work.run {}
    return result

def collect_reg_constraints (cfg : CFG' InstMData String AbsLoc) : Std.HashMap DefUse (List Nat) :=
  Id.run do
    let mut req : Std.HashMap DefUse (List Nat) := {}
    for block in cfg.blocks do
      for inst in block.insts do
        match inst with
        | .cmp tag (.vreg v) _ | .test tag (.vreg v) _ | .push tag (.vreg v) =>
          let key := DefUse.vreg v
          let positions := req[key]?.getD []
          req := req.insert key ((tag.lineno * 2) :: positions)
        | .pop tag (.vreg v) | .mov tag (.vreg v) (.arg _) =>
          let key := DefUse.vreg v
          let positions := req[key]?.getD []
          req := req.insert key ((tag.lineno * 2 + 1) :: positions)
        | .mul tag (.vreg v) _ _ | .add tag (.vreg v) _ _ | .sub tag (.vreg v) _ _
        | .band tag (.vreg v) _ _ | .bor tag (.vreg v) _ _ | .xor tag (.vreg v) _ _
        | .shl tag (.vreg v) _ _ | .shr tag (.vreg v) _ _ | .sar tag (.vreg v) _ _
          =>
          let key := DefUse.vreg v
          let positions := req[key]?.getD []
          req := req.insert key ((tag.lineno * 2 + 1) :: positions)
        | _ => ()
    return req

structure LiveSegment where
  owner : ValDef
  start : Nat
  stop : Nat
deriving Inhabited

private def LiveSegment.lt (x y : LiveSegment) : Bool :=
  if x.start == y.start then
    if x.owner.def_pos == y.owner.def_pos then
      x.stop < y.stop
    else
      x.owner.def_pos < y.owner.def_pos
  else
    x.start < y.start

structure ActiveSegment where
  owner : ValDef
  stop  : Nat
  reg   : GPR32
  pinned : Bool
deriving Inhabited

structure SegAssignment where
  owner : ValDef
  start : Nat
  stop  : Nat
  reg? : Option GPR32
  pinned : Bool
deriving Inhabited, Repr, BEq

structure RAState where
  freeRegs : List GPR32
  active : List ActiveSegment
  varLoc : Std.HashMap DefUse AbsLoc
  nextSlot : Nat
  regRequired : Std.HashMap DefUse (List Nat)
  assignments : Array SegAssignment
deriving Inhabited

private def listContains [BEq α] (xs : List α) (x : α) : Bool :=
  xs.any fun y => y == x

private def addReg [BEq α] (regs : List α) (r : α) : List α :=
  if listContains regs r then regs else r :: regs

private def removeReg [BEq α] : List α → α → List α
  | [], _ => []
  | x :: xs, r =>
      if x == r then xs else x :: removeReg xs r

private def expireSegments (active : List ActiveSegment) (pos : Nat) :
    (List ActiveSegment × List GPR32) :=
  match active with
  | [] => ([], [])
  | x :: xs =>
      if x.stop < pos then
        let (rest, freed) := expireSegments xs pos
        (rest, x.reg :: freed)
      else
        (active, [])

private def insertActive (entry : ActiveSegment) : List ActiveSegment → List ActiveSegment
  | [] => [entry]
  | x :: xs =>
      if entry.stop ≤ x.stop then
        entry :: x :: xs
      else
        x :: insertActive entry xs

private def removeActiveByReg (active : List ActiveSegment) (r : GPR32) :
    (List ActiveSegment × Option ActiveSegment) :=
  match active with
  | [] => ([], none)
  | x :: xs =>
      if x.reg == r then
        (xs, some x)
      else
        let (rest, found) := removeActiveByReg xs r
        (x :: rest, found)

private def removeActiveByOwner (active : List ActiveSegment) (owner : ValDef) :
    (List ActiveSegment × Option ActiveSegment) :=
  match active with
  | [] => ([], none)
  | x :: xs =>
      if x.owner == owner then
        (xs, some x)
      else
        let (rest, found) := removeActiveByOwner xs owner
        (x :: rest, found)

private def lastNonPinned? : List ActiveSegment → Option ActiveSegment
  | [] => none
  | x :: xs =>
      match lastNonPinned? xs with
      | some y => some y
      | none =>
          if x.pinned then none else some x

private def ensureFrame (varLoc : Std.HashMap DefUse AbsLoc) (d : DefUse) (nextSlot : Nat) :
    (AbsLoc × Std.HashMap DefUse AbsLoc × Nat) :=
  match varLoc[d]? with
  | some (.frame idx) => (.frame idx, varLoc, nextSlot)
  | _ =>
      let loc := AbsLoc.frame nextSlot
      (loc, varLoc.insert d loc, nextSlot + 1)

private def spillIfAllowed (regRequired : Std.HashMap DefUse (List Nat))
    (varLoc : Std.HashMap DefUse AbsLoc) (d : DefUse) (nextSlot : Nat) :
    Std.HashMap DefUse AbsLoc × Nat :=
  if (regRequired[d]?.getD []).isEmpty then
    let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
    (varLoc', nextSlot')
  else
    panic! "linear_scan: cannot spill register constrained value"

private def extractRequired (req : Std.HashMap DefUse (List Nat)) (d : DefUse) (start stop : Nat) :
    Bool × Std.HashMap DefUse (List Nat) := Id.run do
  let positions := req[d]?.getD []
  let rec loop
    | [], found, rest => (found, rest)
    | x :: xs, found, rest =>
        if start ≤ x ∧ x ≤ stop then
          loop xs true rest
        else
          loop xs found (x :: rest)
  let (found, remaining) := loop positions false []
  let req' :=
    if remaining.isEmpty then
      req.erase d
    else
      req.insert d remaining
  (found, req')

private def occupyRegister (active : List ActiveSegment) (freeRegs : List GPR32)
    (varLoc : Std.HashMap DefUse AbsLoc) (nextSlot : Nat)
    (owner : ValDef) (stop : Nat) (reg : GPR32) (pinned : Bool) :
    Option (List ActiveSegment × List GPR32 × Std.HashMap DefUse AbsLoc × Nat) := Id.run do
  let (active, stolen?) := removeActiveByReg active reg
  let (varLoc, nextSlot, freeRegs) ←
    match stolen? with
    | none => (varLoc, nextSlot, freeRegs)
    | some victim =>
        if victim.pinned then
          if pinned then
            panic! "linear_scan: overlapping pinned registers"
          else
            return none
        else
          let (_, varLoc, nextSlot) := ensureFrame varLoc victim.owner.d nextSlot
          pure (varLoc, nextSlot, freeRegs)
  let freeRegs := removeReg freeRegs reg
  let active := insertActive { owner, stop, reg, pinned } active
  some (active, freeRegs, varLoc, nextSlot)

abbrev RAM := StateM RAState

def expireAt (pos : Nat) : RAM Unit := do
  let st ← get
  let (active', freed) := expireSegments st.active pos
  let free := freed.foldl (init := st.freeRegs) fun acc r => addReg acc r
  set { st with active := active', freeRegs := free }

def consumeRequirement (d : DefUse) (start stop : Nat) : RAM Bool := do
  let st ← get
  let (need, req') := extractRequired st.regRequired d start stop
  set { st with regRequired := req' }
  pure need

def hasFutureRequirement (d : DefUse) : RAM Bool := do
  let st ← get
  pure !((st.regRequired[d]?.getD []).isEmpty)

def spillCurrent (d : DefUse) : RAM Unit := do
  let st ← get
  let (varLoc', nextSlot') := spillIfAllowed st.regRequired st.varLoc d st.nextSlot
  set { st with varLoc := varLoc', nextSlot := nextSlot' }

def replaceExisting (seg : LiveSegment) (pinned : Bool) : RAM (Option GPR32) := do
  let st ← get
  let (active', existing?) := removeActiveByOwner st.active seg.owner
  set { st with active := active' }
  match existing? with
  | some prev =>
      let extended := { owner := seg.owner, stop := Nat.max prev.stop seg.stop, reg := prev.reg, pinned := prev.pinned || pinned }
      modify fun s => { s with active := insertActive extended s.active }
      pure (some prev.reg)
  | none =>
      pure none

def assignRegister (seg : LiveSegment) (reg : GPR32) (pinned : Bool) : RAM Bool := do
  let st ← get
  match occupyRegister st.active st.freeRegs st.varLoc st.nextSlot seg.owner seg.stop reg pinned with
  | some (active', free', loc', next') =>
      set { st with active := active', freeRegs := free', varLoc := loc', nextSlot := next' }
      pure true
  | none =>
      pure false

def spillAndForget (d : DefUse) (pinned : Bool) : RAM Unit := do
  if pinned then
    panic! "linear_scan: cannot satisfy register constraint"
  spillCurrent d

def recordAssignment (seg : LiveSegment) (reg? : Option GPR32) (pinned : Bool) : RAM Unit := do
  modify fun s => { s with assignments := s.assignments.push { owner := seg.owner, start := seg.start, stop := seg.stop, reg? := reg?, pinned := pinned } }

def evictVictim (victim : ActiveSegment) : RAM GPR32 := do
  let st ← get
  let (active', removed?) := removeActiveByOwner st.active victim.owner
  let some removed := removed? | unreachable!
  let (varLoc', nextSlot') := spillIfAllowed st.regRequired st.varLoc removed.owner.d st.nextSlot
  set { st with active := active', varLoc := varLoc', nextSlot := nextSlot' }
  pure removed.reg

def allocateForVReg (seg : LiveSegment) (pinned : Bool) : RAM (Option GPR32) := do
  let st ← get
  match st.freeRegs with
  | [] =>
      match lastNonPinned? st.active with
      | some victim =>
          if victim.stop > seg.stop then
            let reg ← evictVictim victim
            let ok ← assignRegister seg reg pinned
            if ok then
              -- keep existing home if already spilled
              modify fun s =>
                let v := s.varLoc[seg.owner.d]?
                let varLoc :=
                  match v with
                  | some (.frame _) => s.varLoc
                  | _ => s.varLoc.insert seg.owner.d (.preg reg)
                { s with varLoc }
              return some reg
            else
              spillAndForget seg.owner.d pinned
              return none
          else
            spillAndForget seg.owner.d pinned
            return none
      | none =>
          spillAndForget seg.owner.d pinned
          return none
  | r :: _ =>
      let ok ← assignRegister seg r pinned
      if ok then
        modify fun s =>
          let v := s.varLoc[seg.owner.d]?
          let varLoc :=
            match v with
            | some (.frame _) => s.varLoc
            | _ => s.varLoc.insert seg.owner.d (.preg r)
          { s with varLoc }
        return some r
      else
        spillAndForget seg.owner.d pinned
        return none

def processNew (seg : LiveSegment) (pinned : Bool) : RAM (Option GPR32) := do
  let _ ← hasFutureRequirement seg.owner.d
  let loc? := (← get).varLoc[seg.owner.d]?
  match loc? with
  | some (.frame _) =>
      if pinned then
        allocateForVReg seg pinned
      else
        return none
  | some (.preg r) =>
      let ok ← assignRegister seg r pinned
      if ok then
        return some r
      else
        -- fall back to any available register, even if original home was a preg
        spillCurrent seg.owner.d
        allocateForVReg seg pinned
  | some _ =>
      unreachable!
  | none =>
      match seg.owner.d with
      | .flags => unreachable!
      | .greg r =>
          modify fun s => { s with varLoc := s.varLoc.insert seg.owner.d (.preg r) }
          let ok ← assignRegister seg r true
          if ok then
            return some r
          else
            panic! "linear_scan: failed to assign precolored register"
      | .vreg _ =>
          allocateForVReg seg pinned

def processSegment (seg : LiveSegment) : RAM Unit := do
  expireAt seg.start
  let needsReg ← consumeRequirement seg.owner.d seg.start seg.stop
  let pinned :=
    match seg.owner.d with
    | .greg _ => true
    | _ => needsReg
  let reused? ← replaceExisting seg pinned
  let reg? ←
    match reused? with
    | some r => pure (some r)
    | none => processNew seg pinned
  recordAssignment seg reg? pinned

partial def processSegments : List LiveSegment → RAM Unit := fun ss => ss.forM processSegment

structure LoadedInfo where
  reg : GPR32
  stop : Nat
deriving Inhabited

structure RewriteState where
  loaded : Std.HashMap DefUse LoadedInfo := {}
  homes : Std.HashMap DefUse AbsLoc
  nextSlot : Nat
deriving Inhabited

private abbrev RewriteM := StateM RewriteState

private def groupAssignments (assignments : Array SegAssignment) :
    Std.HashMap DefUse (List SegAssignment) := Id.run do
  let mut grouped : Std.HashMap DefUse (List SegAssignment) := {}
  for a in assignments do
    match a.owner.d with
    | .greg _ => continue
    | .flags => continue
    | _ => ()
    let xs := grouped[a.owner.d]?.getD []
    grouped := grouped.insert a.owner.d (a :: xs)
  let mut sorted : Std.HashMap DefUse (List SegAssignment) := {}
  for (owner, segs) in grouped.toList do
    sorted := sorted.insert owner (segs.mergeSort (fun x y => x.start < y.start))
  return sorted

private def findSegment (byOwner : Std.HashMap DefUse (List SegAssignment))
    (owner : DefUse) (pos : Nat) : Option SegAssignment :=
  match byOwner[owner]? with
  | none => none
  | some segs => segs.find? (fun s => s.start ≤ pos ∧ pos ≤ s.stop)

private def hasFutureSegment (byOwner : Std.HashMap DefUse (List SegAssignment))
    (owner : DefUse) (pos : Nat) : Bool :=
  match byOwner[owner]? with
  | none => false
  | some segs => segs.any (fun s => pos < s.start)

private def ensureHome (d : DefUse) : RewriteM AbsLoc := do
  let st ← get
  match d with
  | .vreg _ =>
      match st.homes[d]? with
      | some (.frame idx) => pure (.frame idx)
      | _ =>
          let slot := st.nextSlot
          set { st with homes := st.homes.insert d (.frame slot), nextSlot := slot + 1 }
          pure (.frame slot)
  | .greg r =>
      match st.homes[d]? with
      | some loc => pure loc
      | none =>
          set { st with homes := st.homes.insert d (.preg r) }
          pure (.preg r)
  | .flags =>
      match st.homes[d]? with
      | some loc => pure loc
      | none =>
          let slot := st.nextSlot
          set { st with homes := st.homes.insert d (.frame slot), nextSlot := slot + 1 }
          pure (.frame slot)

private def expireLoaded (pos : Nat) (tag : InstMData)
    (byOwner : Std.HashMap DefUse (List SegAssignment)) :
    RewriteM (Array (Inst InstMData String AbsLoc)) := do
  let st ← get
  let mut emitted : Array (Inst InstMData String AbsLoc) := #[]
  for (d, info) in st.loaded.toList do
    if info.stop < pos then
      if hasFutureSegment byOwner d pos then
        let home ← ensureHome d
        let _ ← match home with
          | .frame _ =>
              emitted := emitted.push (.mov tag home (.preg info.reg))
              pure ()
          | _ => pure ()
      modify fun s => { s with loaded := s.loaded.erase d }
  return emitted

private def clobberDefinedRegs (defs : Array DefUse) (pos : Nat) (tag : InstMData)
    (byOwner : Std.HashMap DefUse (List SegAssignment)) :
    RewriteM (Array (Inst InstMData String AbsLoc)) := do
  let st ← get
  let clobbers := defs.toList.filterMap (fun
    | .greg r => some r
    | _ => none)
  if clobbers.isEmpty then
    return #[]
  let mut emitted : Array (Inst InstMData String AbsLoc) := #[]
  let mut loaded := st.loaded
  for (d, info) in st.loaded.toList do
    if clobbers.any (· == info.reg) then
      if info.stop > pos && hasFutureSegment byOwner d pos then
        let home ← ensureHome d
        if home != AbsLoc.preg info.reg then
          emitted := emitted.push (.mov tag home (.preg info.reg))
      loaded := loaded.erase d
  set { st with loaded := loaded }
  return emitted

private def borrowScratch (pos : Nat) (tag : InstMData)
    (byOwner : Std.HashMap DefUse (List SegAssignment)) :
    RewriteM (Array (Inst InstMData String AbsLoc) × GPR32) := do
  let candidates := [GPR32.eax, GPR32.ebx, GPR32.ecx, GPR32.edx]
  let st ← get
  for r in candidates do
    match st.loaded.toList.find? (fun (_, info) => info.reg == r) with
    | none =>
        return (#[], r)
    | some (d, info) =>
        if info.stop > pos && hasFutureSegment byOwner d pos then
          let home ← ensureHome d
          if home == AbsLoc.preg r then
            continue
          let spill := #[.mov tag home (.preg r)]
          modify fun s => { s with loaded := s.loaded.erase d }
          return (spill, r)
        else
          modify fun s => { s with loaded := s.loaded.erase d }
          return (#[], r)
  panic! "linear_scan: no scratch register available"

private def ensureUseLoc
    (byOwner : Std.HashMap DefUse (List SegAssignment))
    (loc : AbsLoc) (pos : Nat) (tag : InstMData) :
    RewriteM (Array (Inst InstMData String AbsLoc) × AbsLoc) := do
  match loc.toDefUse? with
  | none => return (#[], loc)
  | some d =>
      let some seg := findSegment byOwner d pos
        | do
            let home ← ensureHome d
            modify fun s => { s with loaded := s.loaded.erase d }
            return (#[], home)
      match seg.reg? with
      | some r =>
          let st ← get
          let needLoad ←
            match st.loaded[d]? with
            | some info =>
                if info.reg == r then
                  let stop' := Nat.max info.stop seg.stop
                  modify fun s => { s with loaded := s.loaded.insert d { reg := r, stop := stop' } }
                  pure false
                else
                  modify fun s => { s with loaded := s.loaded.erase d }
                  pure true
            | none => pure true
          if !needLoad then
            return (#[], AbsLoc.preg r)
          let home ← ensureHome d
          if home == AbsLoc.preg r then
            panic! "linear_scan: register-resident value spanned a clobber"
          let extra : Array (Inst InstMData String AbsLoc) :=
            if home == AbsLoc.preg r then
              #[]
            else
              #[.mov tag (AbsLoc.preg r) home]
          modify fun s => { s with loaded := s.loaded.insert d { reg := r, stop := seg.stop } }
          return (extra, AbsLoc.preg r)
      | none =>
          let home ← ensureHome d
          modify fun s => { s with loaded := s.loaded.erase d }
          return (#[], home)

private def rewriteDefLoc
    (byOwner : Std.HashMap DefUse (List SegAssignment))
    (loc : AbsLoc) (pos : Nat) :
    RewriteM AbsLoc := do
  match loc.toDefUse? with
  | none => pure loc
  | some d =>
      let some seg := findSegment byOwner d pos
        | do
            let home ← ensureHome d
            modify fun s => { s with loaded := s.loaded.erase d }
            return home
      match seg.reg? with
      | some r =>
          modify fun s => { s with loaded := s.loaded.insert d { reg := r, stop := seg.stop } }
          pure (AbsLoc.preg r)
      | none =>
          let home ← ensureHome d
          modify fun s => { s with loaded := s.loaded.erase d }
          pure home

private def isMemLoc : AbsLoc → Bool
  | .frame _ | .arg _ => true
  | _ => false

private def rewriteInst
    (byOwner : Std.HashMap DefUse (List SegAssignment))
    (inst : Inst InstMData String AbsLoc) :
    RewriteM (Array (Inst InstMData String AbsLoc)) := do
  let pos := inst.tag.lineno * 2
  let expired ← expireLoaded pos inst.tag byOwner
  let clobbered ← clobberDefinedRegs inst.tag.defs pos inst.tag byOwner
  let mut insts := expired.append clobbered
  match inst with
  | .mov tag dst src =>
      let (extra, src') ← ensureUseLoc byOwner src pos tag
      insts := insts.append extra
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      if (isMemLoc dst') && (isMemLoc src') then
        let (spill, scratch) ← borrowScratch pos tag byOwner
        insts := insts.append spill
        insts := insts.push (.mov tag (AbsLoc.preg scratch) src')
        insts := insts.push (.mov tag dst' (AbsLoc.preg scratch))
      else
        insts := insts.push (.mov tag dst' src')
      pure insts
  | .add tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.add tag dst' x' y')
      pure insts
  | .sub tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.sub tag dst' x' y')
      pure insts
  | .mul tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.mul tag dst' x' y')
      pure insts
  | .band tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.band tag dst' x' y')
      pure insts
  | .bor tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.bor tag dst' x' y')
      pure insts
  | .xor tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.xor tag dst' x' y')
      pure insts
  | .push tag x =>
      let (extra, x') ← ensureUseLoc byOwner x pos tag
      insts := insts.append extra
      insts := insts.push (.push tag x')
      pure insts
  | .pop tag dst =>
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.pop tag dst')
      pure insts
  | .pop' tag =>
      insts := insts.push (.pop' tag)
      pure insts
  | .cmp tag x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      insts := insts.push (.cmp tag x' y')
      pure insts
  | .test tag x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      insts := insts.push (.test tag x' y')
      pure insts
  | .shl tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.shl tag dst' x' y')
      pure insts
  | .shr tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.shr tag dst' x' y')
      pure insts
  | .sar tag dst x y =>
      let (extraX, x') ← ensureUseLoc byOwner x pos tag
      let (extraY, y') ← ensureUseLoc byOwner y pos tag
      insts := insts.append extraX
      insts := insts.append extraY
      let dst' ← rewriteDefLoc byOwner dst (pos + 1)
      insts := insts.push (.sar tag dst' x' y')
      pure insts
  | .call' tag target =>
      insts := insts.push (.call' tag target)
      pure insts
  | inst =>
      panic! s!"rewriteInst: unexpected instruction after lowering: {inst}"

private def rewriteTerminal
    (byOwner : Std.HashMap DefUse (List SegAssignment))
    (term : Terminal InstMData String AbsLoc) :
    RewriteM (Array (Inst InstMData String AbsLoc) × Terminal InstMData String AbsLoc) := do
  let pos := term.tag.lineno * 2
  let expired ← expireLoaded pos term.tag byOwner
  match term with
  | .ret tag v =>
      let (extra, v') ← ensureUseLoc byOwner v pos tag
      return (expired.append extra, .ret tag v')
  | .br tag cond lt lf =>
      let (extra, cond') ← ensureUseLoc byOwner cond pos tag
      return (expired.append extra, .br tag cond' lt lf)
  | .jmp tag lbl =>
      return (expired, .jmp tag lbl)
  | .jl tag lbl =>
      return (expired, .jl tag lbl)
  | .jle tag lbl =>
      return (expired, .jle tag lbl)
  | .jg tag lbl =>
      return (expired, .jg tag lbl)
  | .jge tag lbl =>
      return (expired, .jge tag lbl)
  | .jz tag lbl =>
      return (expired, .jz tag lbl)
  | .jnz tag lbl =>
      return (expired, .jnz tag lbl)

private def rewriteCFG (cfg : CFG' InstMData String AbsLoc) (finalState : RAState) :
    CFG' InstMData String AbsLoc := Id.run do
  let byOwner := groupAssignments finalState.assignments
  let initial : RewriteState := { loaded := {}, homes := finalState.varLoc, nextSlot := finalState.nextSlot }
  let work : RewriteM (Array (BasicBlock InstMData String AbsLoc)) := do
    let mut blocks : Array (BasicBlock InstMData String AbsLoc) := #[]
    for block in cfg.blocks do
      let mut insts : Array (Inst InstMData String AbsLoc) := #[]
      for inst in block.insts do
        let rewritten ← rewriteInst byOwner inst
        insts := insts.append rewritten
      let (extraTermInsts, term') ← rewriteTerminal byOwner block.terminal
      insts := insts.append extraTermInsts
      blocks := blocks.push { block with insts := insts, terminal := term' }
    pure blocks
  let (blocks, _) := (work.run initial)
  { name := cfg.name, blocks := blocks : CFG' InstMData String AbsLoc }

def linear_scan_register_allocation (cfg : CFG' InstMData String AbsLoc)
    (intervals : Std.HashMap ValDef Interval) : CFG' InstMData String AbsLoc := Id.run do
  let availableRegs : List GPR32 := [GPR32.eax, GPR32.ebx, GPR32.ecx, GPR32.edx]
  let regRequired := collect_reg_constraints cfg
  let mut segments : Array LiveSegment := #[]
  for (vd, itv) in intervals.toList do
    if vd.d == DefUse.flags then
      continue
    for seg in itv.segs do
      -- ignore zero-length, unused segments (e.g., pure clobbers)
      if seg.start_inc == seg.end_inc && seg.used_pos.isEmpty then
        continue
      segments := segments.push { owner := vd, start := seg.start_inc, stop := seg.end_inc }
  let ordered := segments.toList.mergeSort LiveSegment.lt
  let initState : RAState :=
    { freeRegs := availableRegs, active := [], varLoc := {}, nextSlot := 0, regRequired, assignments := #[] }
  let (_, finalState) := processSegments ordered |>.run initState
  rewriteCFG cfg finalState
