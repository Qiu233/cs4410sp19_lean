import Cs4410sp19.MIR.Basic
import Cs4410sp19.MIR.MData

namespace Cs4410sp19
namespace MIR

structure Segment where
  start_inc : Nat
  end_inc : Nat
  used_pos : List Nat
deriving Inhabited, Repr

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
            succs.any fun s => (liveIn[s]? ).getD false
        let inVal := blockLiveIn v block outVal
        let oldOut := (liveOut[block.id]? ).getD false
        if outVal ≠ oldOut then
          liveOut := liveOut.insert block.id outVal
          changed := true
        let oldIn := (liveIn[block.id]? ).getD false
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
  (maps.liveIn[b]? ).getD false

private def liveOutBlock (maps : LivenessMaps) (b : String) : Bool :=
  (maps.liveOut[b]? ).getD false

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
        | .cmp tag lhs _ | .test tag lhs _ | .push tag lhs | .pop tag lhs =>
            match lhs with
            | .vreg v =>
                let key := DefUse.vreg v
                let positions := (req[key]? ).getD []
                req := req.insert key ((tag.lineno * 2) :: positions)
            | _ => ()
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

structure RAState where
  freeRegs : List GPR32
  active : List ActiveSegment
  varLoc : Std.HashMap DefUse AbsLoc
  nextSlot : Nat
  regRequired : Std.HashMap DefUse (List Nat)
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
  if ((regRequired[d]? ).getD []).isEmpty then
    let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
    (varLoc', nextSlot')
  else
    panic! "linear_scan: cannot spill register constrained value"

private def extractRequired (req : Std.HashMap DefUse (List Nat)) (d : DefUse) (start stop : Nat) :
    Bool × Std.HashMap DefUse (List Nat) := Id.run do
  let positions := (req[d]? ).getD []
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
  pure !(((st.regRequired[d]? ).getD []).isEmpty)

def spillCurrent (d : DefUse) : RAM Unit := do
  let st ← get
  let (varLoc', nextSlot') := spillIfAllowed st.regRequired st.varLoc d st.nextSlot
  set { st with varLoc := varLoc', nextSlot := nextSlot' }

def replaceExisting (seg : LiveSegment) (pinned : Bool) : RAM Bool := do
  let st ← get
  let (active', existing?) := removeActiveByOwner st.active seg.owner
  set { st with active := active' }
  match existing? with
  | some prev =>
      let extended := { owner := seg.owner, stop := Nat.max prev.stop seg.stop, reg := prev.reg, pinned := prev.pinned || pinned }
      modify fun s => { s with active := insertActive extended s.active }
      pure true
  | none =>
      pure false

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

def evictVictim (victim : ActiveSegment) : RAM GPR32 := do
  let st ← get
  let (active', removed?) := removeActiveByOwner st.active victim.owner
  let some removed := removed? | unreachable!
  let (varLoc', nextSlot') := spillIfAllowed st.regRequired st.varLoc removed.owner.d st.nextSlot
  set { st with active := active', varLoc := varLoc', nextSlot := nextSlot' }
  pure removed.reg

def allocateForVReg (seg : LiveSegment) (pinned : Bool) : RAM Unit := do
  let st ← get
  match st.freeRegs with
  | [] =>
      match lastNonPinned? st.active with
      | some victim =>
          if victim.stop > seg.stop then
            let reg ← evictVictim victim
            modify fun s => { s with varLoc := s.varLoc.insert seg.owner.d (.preg reg) }
            let ok ← assignRegister seg reg pinned
            unless ok do spillAndForget seg.owner.d pinned
          else
            spillAndForget seg.owner.d pinned
      | none =>
          spillAndForget seg.owner.d pinned
  | r :: _ =>
      modify fun s => { s with varLoc := s.varLoc.insert seg.owner.d (.preg r) }
      let ok ← assignRegister seg r pinned
      unless ok do spillAndForget seg.owner.d pinned

def processNew (seg : LiveSegment) (pinned : Bool) : RAM Unit := do
  let future ← hasFutureRequirement seg.owner.d
  let loc? := (← get).varLoc[seg.owner.d]?
  match loc? with
  | some (.frame _) =>
      if pinned || future then
        panic! "linear_scan: register constrained value spilled"
      else
        pure ()
  | some (.preg r) =>
      let ok ← assignRegister seg r pinned
      unless ok do spillAndForget seg.owner.d pinned
  | some _ =>
      unreachable!
  | none =>
      match seg.owner.d with
      | .flags => unreachable!
      | .greg r =>
          modify fun s => { s with varLoc := s.varLoc.insert seg.owner.d (.preg r) }
          let ok ← assignRegister seg r true
          unless ok do panic! "linear_scan: failed to assign precolored register"
      | .vreg _ =>
          allocateForVReg seg pinned

def processSegment (seg : LiveSegment) : RAM Unit := do
  expireAt seg.start
  let needsReg ← consumeRequirement seg.owner.d seg.start seg.stop
  let pinned :=
    match seg.owner.d with
    | .greg _ => true
    | _ => needsReg
  let replaced ← replaceExisting seg pinned
  if replaced then
    pure ()
  else
    processNew seg pinned

partial def processSegments : List LiveSegment → RAM Unit
  | [] => pure ()
  | seg :: rest => do
      processSegment seg
      processSegments rest

def linear_scan_register_allocation (cfg : CFG' InstMData String AbsLoc)
    (intervals : Std.HashMap ValDef Interval) : CFG' InstMData String AbsLoc := Id.run do
  let availableRegs : List GPR32 := [GPR32.eax, GPR32.ebx, GPR32.ecx, GPR32.edx]
  let regRequired := collect_reg_constraints cfg
  let mut segments : Array LiveSegment := #[]
  for (vd, itv) in intervals.toList do
    if vd.d == DefUse.flags then
      continue
    for seg in itv.segs do
      segments := segments.push { owner := vd, start := seg.start_inc, stop := seg.end_inc }
  let ordered := segments.toList.mergeSort LiveSegment.lt
  let initState : RAState :=
    { freeRegs := availableRegs, active := [], varLoc := {}, nextSlot := 0, regRequired := regRequired }
  let (_, finalState) := processSegments ordered |>.run initState
  let rewriteLoc := fun
    | AbsLoc.vreg v =>
        let key := DefUse.vreg v
        match finalState.varLoc[key]? with
        | some (.preg r) => AbsLoc.preg r
        | some (.frame idx) => AbsLoc.frame idx
        | _ => AbsLoc.vreg v
    | loc => loc
  let blocks := cfg.blocks.map fun b =>
    let insts := b.insts.map fun inst => inst.mapM_loc (m := Id) rewriteLoc
    let terminal := b.terminal.mapM_loc (m := Id) rewriteLoc
    { b with insts, terminal }
  { name := cfg.name, blocks := blocks : CFG' InstMData String AbsLoc }
