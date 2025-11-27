import Cs4410sp19.MIR.Basic
import Cs4410sp19.MIR.Construct
import Cs4410sp19.MIR.MData

namespace Cs4410sp19
namespace MIR

-- structure Def where
--   P : String
--   defPos : Nat
-- deriving Inhabited, Repr, BEq

-- instance : ToString Def where
--   toString x := s!"⟨{x.P}, {x.defPos}⟩"

variable (cfg : CFG' InstMData String AbsLoc) (v : DefUse) in
mutual

partial def defs_in (b : String) : Array (String × Nat) :=
  if cfg.isEntryBlock b then
    #[]
  else
    Array.flatten ((cfg.pred b).map defs_out)

partial def defs_out (b : String) : Array (String × Nat) := Id.run do
  let some block := cfg.get? b | unreachable!
  for (inst, idx) in block.insts.zipIdx.reverse do
    if inst.tag.is_def v then
      return #[⟨b, idx⟩]
  defs_in b

end

variable (cfg : CFG' InstMData String AbsLoc) (v : DefUse) in
mutual

partial def live_in (b : String) : Bool := Id.run do
  let mut defined := false
  let some block := cfg.get? b | unreachable!
  let tags := block.insts.map Inst.tag |>.push block.terminal.tag
  for tag in tags do
    if tag.is_used v then
      if defined then
        return false
      else
        return true
    if tag.is_def v then
      defined := true
  return live_out b

partial def live_out (b : String) : Bool :=
  if cfg.succ b |>.isEmpty then
    false
  else
    (cfg.succ b).any fun s => live_in s

end


/-- [start_inc, end_exc] -/
structure Segment where
  start_inc : Nat
  end_inc : Nat
  used_pos : List Nat
deriving Inhabited, Repr

/-- non-overlapping sorted segments -/
structure Interval where
  segs : Array Segment
deriving Inhabited, Repr

instance : ToString Interval where
  toString x := s!"[{String.intercalate ", " (x.segs.toList.map fun x => s!"[{x.start_inc}-{x.end_inc}]")}]"

def Interval.empty : Interval := ⟨#[]⟩

def Interval.merge : Interval → Interval → Interval := fun x y => Id.run do
  -- merge the overlapping segments
  let mut res : Array Segment := #[]
  let mut i := 0
  let mut j := 0
  while i < x.segs.size || j < y.segs.size do
    let next ←
      if i < x.segs.size && (j >= y.segs.size || x.segs[i]!.start_inc <= y.segs[j]!.start_inc) then
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
      if last.end_inc + 1 >= next.start_inc then
        let used := last.used_pos ++ next.used_pos
        let used := used.mergeSort
        let used := used.eraseDups
        res := res.pop.push ⟨last.start_inc, Nat.max last.end_inc next.end_inc, used⟩
      else
        res := res.push next
  return ⟨res⟩

def Interval.addRange : Interval → Nat → Nat → List Nat → Interval := fun l x y used => Interval.merge l ⟨#[⟨x, y, used⟩]⟩

def Interval.setFrom : Interval → Nat → Interval := fun l f => Id.run do
  let mut is := l.segs.toList
  while is.length != 0 do
    let i :: is' := is | unreachable!
    if i.end_inc > f then
      break
    is := is'
  if is.isEmpty then
    return ⟨#[⟨f, f, []⟩]⟩ -- at least live for one instruction
  let i :: is' := is | unreachable!
  return ⟨({i with start_inc := f} :: is').toArray⟩

private def Interval.start (it : Interval) : Nat :=
  it.segs[0]!.start_inc

private def Interval.end (it : Interval) : Nat :=
  it.segs.back!.end_inc

def BasicBlock.lineno_start : BasicBlock InstMData String AbsLoc → Nat := fun b =>
  b.insts[0]?.map Inst.tag |>.getD b.terminal.tag |>.lineno

def BasicBlock.lineno_end : BasicBlock InstMData String AbsLoc → Nat := fun b => b.terminal.tag |>.lineno

partial def f (cfg : CFG' InstMData String AbsLoc) (v : DefUse) (b : String)
    (_ : live_in cfg v b) : Interval := Id.run do
  let some block := cfg.get? b | unreachable!
  let start := block.lineno_start * 2
  let mut uses := #[]
  let tags := block.insts.map Inst.tag |>.push block.terminal.tag
  for tag in tags do
    if tag.is_used v then
      uses := uses.push (tag.lineno * 2)
    if tag.is_def v then
      return ⟨#[ { start_inc := start, end_inc := tag.lineno * 2, used_pos := uses.toList } ]⟩
  if not <| live_out cfg v block.id then
    assert! !uses.isEmpty
    let last_used := uses.map (· + 1) |>.foldl (init := 0) max
    return ⟨#[ ⟨start, last_used, uses.toList⟩ ]⟩
  let mut itv : Interval := ⟨#[{ start_inc := start, end_inc := block.lineno_end * 2 + 1, used_pos := uses.toList }]⟩
  for s in cfg.succ block.id do
    if h : live_in cfg v s then
      let t := f cfg v s h
      itv := itv.merge t
  return itv

def liveness_of_def (cfg : CFG' InstMData String AbsLoc) (v : DefUse) (def_pos : Nat) : Interval := Id.run do
  assert! def_pos % 2 == 1
  let def_lineno := def_pos / 2
  let block? := cfg.blocks.find? (fun b => b.lineno_start ≤ def_lineno && def_lineno ≤ b.lineno_end)
  let some block := block? | unreachable!
  if block.insts.isEmpty then -- def cannot be terminal
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
      return ⟨#[ ⟨def_pos, tag.lineno * 2, uses.toList⟩ ]⟩
  if not <| live_out cfg v block.id then
    let ending := uses.map (· + 1) |>.foldl (init := def_pos) max
    return ⟨#[ ⟨def_pos, ending, uses.toList⟩ ]⟩
  let mut itv : Interval := ⟨#[ ⟨def_pos, block.lineno_end * 2 + 1, uses.toList⟩ ]⟩
  for s in cfg.succ block.id do
    if h : live_in cfg v s then
      let t := f cfg v s h
      itv := itv.merge t
  return itv

structure ValDef where
  d : DefUse
  def_pos : Nat
deriving Inhabited, Repr, Hashable, BEq

def build_live_intervals (cfg : CFG' InstMData String AbsLoc) : Std.HashMap ValDef Interval := Id.run do
  let mut r := #[]
  let ds := cfg.blocks.flatMap fun b => b.insts.flatMap fun i => i.tag.defs.map fun d => (d, i.tag.lineno * 2 + 1)
  for (d, i) in ds do
    r := r.push (⟨d, i⟩, liveness_of_def cfg d i)
  return Std.HashMap.ofList r.toList

private structure LiveSegment where
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

private structure ActiveSegment where
  owner : ValDef
  stop  : Nat
  reg   : GPR32
  pinned : Bool
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
      if entry.stop <= x.stop then
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
          if x.pinned then
            none
          else
            some x

private def ensureFrame (varLoc : Std.HashMap DefUse AbsLoc) (d : DefUse) (nextSlot : Nat) :
    (AbsLoc × Std.HashMap DefUse AbsLoc × Nat) :=
  match varLoc[d]? with
  | some (.frame idx) => (.frame idx, varLoc, nextSlot)
  | _ =>
      let loc := AbsLoc.frame nextSlot
      (loc, varLoc.insert d loc, nextSlot + 1)

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
            -- let active := insertActive victim active
            -- we drop the victim entirely on failure
            return none
        else
          let (_, varLoc, nextSlot) := ensureFrame varLoc victim.owner.d nextSlot
          pure (varLoc, nextSlot, freeRegs)
  let freeRegs := removeReg freeRegs reg
  let active := insertActive { owner, stop, reg, pinned } active
  some (active, freeRegs, varLoc, nextSlot)

def linear_scan_register_allocation (cfg : CFG' InstMData String AbsLoc) (intervals : Std.HashMap ValDef Interval) : CFG' InstMData String AbsLoc := Id.run do
  let availableRegs : List GPR32 := [GPR32.eax, GPR32.ebx, GPR32.ecx, GPR32.edx]
  let mut segments : Array LiveSegment := #[]
  for (vd, itv) in intervals.toList do
    if vd.d == DefUse.flags then
      continue
    for seg in itv.segs do
      segments := segments.push { owner := vd, start := seg.start_inc, stop := seg.end_inc }
  let ordered := segments.toList.mergeSort LiveSegment.lt
  let mut freeRegs := availableRegs
  let mut active : List ActiveSegment := []
  let mut varLoc : Std.HashMap DefUse AbsLoc := {}
  let mut nextSlot : Nat := 0
  for seg in ordered do
    let d := seg.owner.d
    if d == DefUse.flags then
      continue
    let (active', freed) := expireSegments active seg.start
    active := active'
    for r in freed do
      freeRegs := addReg freeRegs r
    let pinned :=
      match d with
      | .greg _ => true
      | _ => false
    match varLoc[d]? with
    | some (.frame _) =>
        continue
    | some (.preg r) =>
        match occupyRegister active freeRegs varLoc nextSlot seg.owner seg.stop r pinned with
        | some (active', freeRegs', varLoc', nextSlot') =>
            active := active'
            freeRegs := freeRegs'
            varLoc := varLoc'
            nextSlot := nextSlot'
        | none =>
            let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
            varLoc := varLoc'
            nextSlot := nextSlot'
    | some _ => unreachable!
    | none =>
        match d with
        | .flags => unreachable!
        | .greg r =>
            varLoc := varLoc.insert d (.preg r)
            match occupyRegister active freeRegs varLoc nextSlot seg.owner seg.stop r true with
            | some (active', freeRegs', varLoc', nextSlot') =>
                active := active'
                freeRegs := freeRegs'
                varLoc := varLoc'
                nextSlot := nextSlot'
            | none =>
                panic! "linear_scan: failed to assign precolored register"
        | .vreg _ =>
            match freeRegs with
            | [] =>
                match lastNonPinned? active with
                | some victim =>
                    if victim.stop > seg.stop then
                      let (active', removed?) := removeActiveByOwner active victim.owner
                      let some removed := removed? | unreachable!
                      let (_, varLoc', nextSlot') := ensureFrame varLoc removed.owner.d nextSlot
                      varLoc := varLoc'
                      nextSlot := nextSlot'
                      active := active'
                      let reg := removed.reg
                      varLoc := varLoc.insert d (.preg reg)
                      match occupyRegister active freeRegs varLoc nextSlot seg.owner seg.stop reg false with
                      | some (active', freeRegs', varLoc', nextSlot') =>
                          active := active'
                          freeRegs := freeRegs'
                          varLoc := varLoc'
                          nextSlot := nextSlot'
                      | none =>
                          let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
                          varLoc := varLoc'
                          nextSlot := nextSlot'
                    else
                      let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
                      varLoc := varLoc'
                      nextSlot := nextSlot'
                | none =>
                    let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
                    varLoc := varLoc'
                    nextSlot := nextSlot'
            | r :: _ =>
                varLoc := varLoc.insert d (.preg r)
                match occupyRegister active freeRegs varLoc nextSlot seg.owner seg.stop r false with
                | some (active', freeRegs', varLoc', nextSlot') =>
                    active := active'
                    freeRegs := freeRegs'
                    varLoc := varLoc'
                    nextSlot := nextSlot'
                | none =>
                    let (_, varLoc', nextSlot') := ensureFrame varLoc d nextSlot
                    varLoc := varLoc'
                    nextSlot := nextSlot'
  let rewriteLoc := fun
    | AbsLoc.vreg v =>
        let key := DefUse.vreg v
        match varLoc[key]? with
        | some (.preg r) => AbsLoc.preg r
        | some (.frame idx) => AbsLoc.frame idx
        | _ => AbsLoc.vreg v
    | loc => loc
  let blocks := cfg.blocks.map fun b =>
    let insts := b.insts.map fun inst => inst.mapM_loc (m := Id) rewriteLoc
    let terminal := b.terminal.mapM_loc (m := Id) rewriteLoc
    { b with insts, terminal }
  { name := cfg.name, blocks := blocks : CFG' InstMData String AbsLoc }

def src := "def f(x, y):
  let t = 7 in
  let x = 5 in
  (if x == 0: 0 else: if x == 1: 1 + 4 else: 2) + (if y == 1: 2 else: 3) + x + t + g(1) + g(2)
"

-- #exit

#eval do
  let e ← match (parse_function_decl <* Std.Internal.Parsec.String.ws <* Std.Internal.Parsec.eof).run src with
    | .error e => println! s!"failed to parse expression due to: {e}"; return
    | .ok r => pure r
  let s := ContT.run (m := SSA.M) (do
    let a ← anf_decl e.decls[0]!
    let t := (match a with | ADecl.function _ f => f)
    let r ← liftM <| SSA.cfg_of_function_def t
    let r : SSA.CFG' Unit String SSA.VarName SSA.Operand := { r with }
    return r
    ) (fun n => pure n) |>.run {} |>.run' {}
  let (r, s) := s.run {}
  println! "converted:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.reduce_assign r
  println! "unary assignment reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.eliminate_trivial_blocks r
  println! "trivial blocks reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, _) := FreshM.run (SSA.eliminate_block_args r) s
  println! "block args eliminated:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.construct r.toCFG |>.run' {}) {}
  println! "MIR constructed:"
  println! "{MIR.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.reduce_lop r.toCFG) s
  println! "logical operators reduced:"
  println! "{MIR.pp_cfg' r}\n"

  let r := MIR.to_c_call r
  println! "call unfolded:"
  println! "{MIR.pp_cfg' r}\n"

  let (r, s) := FreshM.run (MIR.form r) s
  println! "two address formation:"
  println! "{MIR.pp_cfg' r}\n"

  let r := MIR.compute_mdata r
  println! "mdata:"
  println! "{MIR.pp_cfg r}\n"

  -- let ds := defs_in {r with}
  -- println! "{ds (.vreg ⟨"x.8"⟩) ".join.2"}"

  -- println! "{live_in {r with } (.vreg ⟨"x.8"⟩) ".join.2"}"
  -- println! "{defs_out {r with } (.greg .eax) ".join.2"}"

  -- let t := liveness_of_def {r with} (.greg .eax) 95
  -- println! "{t}"
  let intervals := build_live_intervals {r with}
  -- let itvs := sorry
  let itvs := intervals.toList.mergeSort fun x y => x.fst.def_pos < y.fst.def_pos
  println! "intervals (sorted by def_pos):"
  for (i, t) in itvs do
    println! "{i.d}, {i.def_pos}: {t}"
  let r := linear_scan_register_allocation {r with} intervals

  println! "\nregister allocated:"
  println! "{MIR.pp_cfg' r.unsetTag.toCFG}\n"

  -- let (li, lo) := MIR.liveness { r with }
  -- println! "{li[".split_.join.0_.join.2_1.0"]!.toArray}"

  -- let itvs := MIR.build_live_intervals { r with }
  -- println! "{itvs.toArray}"
