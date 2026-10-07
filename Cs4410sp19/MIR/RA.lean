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

structure StackSpan where
  owner : ValDef
  start : Nat
  stop  : Nat
deriving Inhabited

private def spanStart (itv : Interval) (fallback : Nat) : Nat :=
  match itv.segs[0]? with
  | some seg => seg.start_inc
  | none => fallback

private def spanStop (itv : Interval) (fallback : Nat) : Nat :=
  match itv.segs.back? with
  | some seg => seg.end_inc
  | none => fallback

private def collectSpans (intervals : Std.HashMap ValDef Interval) : List StackSpan :=
  let spans := Id.run do
    let mut acc : Array StackSpan := #[]
    for (vd, itv) in intervals.toList do
      match vd.d with
      | .vreg _ =>
          let start := spanStart itv vd.def_pos
          let stop := spanStop itv vd.def_pos
          acc := acc.push { owner := vd, start, stop }
      | _ => ()
    return acc
  spans.toList.mergeSort fun a b =>
    if a.start == b.start then
      a.owner.def_pos < b.owner.def_pos
    else
      a.start < b.start

private def expireStack (active : List (Nat × Nat)) (pos : Nat) :
    (List (Nat × Nat) × List Nat) :=
  match active with
  | [] => ([], [])
  | (stop, slot) :: rest =>
      if stop < pos then
        let (rest', freed) := expireStack rest pos
        (rest', slot :: freed)
      else
        (active, [])

private def insertActiveSpan (stop slot : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(stop, slot)]
  | x :: xs =>
      if stop ≤ x.fst then
        (stop, slot) :: x :: xs
      else
        x :: insertActiveSpan stop slot xs

private def assignStackHomes (intervals : Std.HashMap ValDef Interval) :
    Std.HashMap DefUse AbsLoc × Nat :=
  Id.run do
    let spans := collectSpans intervals
    let mut homes : Std.HashMap DefUse AbsLoc := {}
    let mut nextSlot := 0
    let mut freeSlots : List Nat := []
    let mut active : List (Nat × Nat) := []
    for span in spans do
      let (active', freed) := expireStack active span.start
      let freeSlotsNew := freed.foldl (init := freeSlots) fun acc slot => slot :: acc
      let (slot, freeSlots', nextSlot') :=
        match freeSlotsNew with
        | s :: rest => (s, rest, nextSlot)
        | [] => (nextSlot, [], nextSlot + 1)
      active := insertActiveSpan span.stop slot active'
      homes := homes.insert span.owner.d (.frame slot)
      freeSlots := freeSlots'
      nextSlot := nextSlot'
    return (homes, nextSlot)

structure RewriteState where
  homes : Std.HashMap DefUse AbsLoc
  nextSlot : Nat
deriving Inhabited

abbrev RewriteM := StateM RewriteState

private def resolveHome (d : DefUse) : RewriteM AbsLoc := do
  match d with
  | .vreg v =>
      let key := DefUse.vreg v
      let st ← get
      match st.homes[key]? with
      | some loc => pure loc
      | none =>
          let slot := st.nextSlot
          let loc := AbsLoc.frame slot
          set { st with homes := st.homes.insert key loc, nextSlot := slot + 1 }
          pure loc
  | .greg r => pure (.preg r)
  | .flags =>
      let st ← get
      match st.homes[d]? with
      | some loc => pure loc
      | none =>
          let slot := st.nextSlot
          let loc := AbsLoc.frame slot
          set { st with homes := st.homes.insert d loc, nextSlot := slot + 1 }
          pure loc

private def resolveLoc (loc : AbsLoc) : RewriteM AbsLoc :=
  match loc with
  | .vreg v => resolveHome (DefUse.vreg v)
  | _ => pure loc

private def isMemLoc : AbsLoc → Bool
  | .frame _ | .arg _ => true
  | _ => false

private def isRegLoc : AbsLoc → Bool
  | .preg _ => true
  | _ => false

private def isImmLoc : AbsLoc → Bool
  | .imm _ => true
  | _ => false

private def regsInLoc : AbsLoc → List GPR32
  | .preg r => [r]
  | _ => []

private def regsInList (locs : List AbsLoc) : List GPR32 :=
  locs.foldl (fun acc loc => regsInLoc loc ++ acc) []

private def scratchOrder : List GPR32 := [GPR32.eax, GPR32.ebx, GPR32.ecx, GPR32.edx]

private def borrowScratch (used : List GPR32) : GPR32 × List GPR32 :=
  match scratchOrder.find? (fun r => !(used.contains r)) with
  | some r => (r, r :: used)
  | none => panic! "register allocation: no scratch registers available for lowering"

private def lowerMov (tag : InstMData) (dst src : AbsLoc) : Array (Inst InstMData String AbsLoc) :=
  if isImmLoc dst then
    panic! s!"register allocation: mov destination cannot be immediate ({dst})"
  else if isMemLoc dst && isMemLoc src then
    let used := regsInList [dst, src]
    let (scratch, _) := borrowScratch used
    let reg := AbsLoc.preg scratch
    #[
      .mov tag reg src,
      .mov tag dst reg
    ]
  else
    #[.mov tag dst src]

private def lowerTwoAddr
    (build : InstMData → AbsLoc → AbsLoc → AbsLoc → Inst InstMData String AbsLoc)
    (tag : InstMData) (dst x y : AbsLoc) : Array (Inst InstMData String AbsLoc) :=
  if dst != x then
    panic! s!"register allocation: expected two-address form (dst={dst}, x={x})"
  else if isImmLoc dst then
    panic! s!"register allocation: destination cannot be immediate ({dst})"
  else if isMemLoc dst && isMemLoc y then
    let used := regsInList [dst, y]
    let (scratch, _) := borrowScratch used
    let reg := AbsLoc.preg scratch
    #[
      .mov tag reg y,
      build tag dst dst reg
    ]
  else
    #[build tag dst dst y]

private def lowerMul (tag : InstMData) (dst x y : AbsLoc) :
    Array (Inst InstMData String AbsLoc) :=
  if dst != x then
    panic! s!"register allocation: imul requires dst == x ({dst}, {x})"
  else if isImmLoc dst then
    panic! s!"register allocation: imul destination cannot be immediate"
  else
    Id.run do
      let mut insts : Array (Inst InstMData String AbsLoc) := #[]
      let used := regsInList [dst, y]
      let (regDst, needsStore, loadInsts) :=
        if isRegLoc dst then
          (dst, false, #[])
        else
          let (scratch, _) := borrowScratch used
          let reg := AbsLoc.preg scratch
          (reg, true, #[
            .mov tag reg dst
          ])
      insts := insts.append loadInsts
      insts := insts.push (.mul tag regDst regDst y)
      if needsStore then
        insts := insts.push (.mov tag dst regDst)
      return insts

private def lowerCmpLike
    (ctor : InstMData → AbsLoc → AbsLoc → Inst InstMData String AbsLoc)
    (tag : InstMData) (lhs rhs : AbsLoc) : Array (Inst InstMData String AbsLoc) :=
  Id.run do
    let mut insts : Array (Inst InstMData String AbsLoc) := #[]
    let mut lhs := lhs
    let mut rhs := rhs
    let mut used := regsInList [lhs, rhs]
    if isImmLoc lhs then
      let (scratch, used') := borrowScratch used
      used := used'
      let reg := AbsLoc.preg scratch
      insts := insts.push (.mov tag reg lhs)
      lhs := reg
    if isMemLoc rhs then
      let (scratch, _) := borrowScratch used
      let reg := AbsLoc.preg scratch
      insts := insts.push (.mov tag reg rhs)
      rhs := reg
    insts := insts.push (ctor tag lhs rhs)
    return insts

private def lowerShift
    (ctor : InstMData → AbsLoc → AbsLoc → AbsLoc → Inst InstMData String AbsLoc)
    (tag : InstMData) (dst x amount : AbsLoc) :
    Array (Inst InstMData String AbsLoc) :=
  if dst != x then
    panic! s!"register allocation: shift requires dst == x ({dst}, {x})"
  else if isImmLoc dst then
    panic! "register allocation: shift destination cannot be immediate"
  else
    Id.run do
      let mut insts : Array (Inst InstMData String AbsLoc) := #[]
      let mut used := regsInList [dst, amount]
      let mut regDst := dst
      let mut needsStore := false
      if ¬ isRegLoc regDst then
        let (scratch, used') := borrowScratch used
        used := used'
        regDst := AbsLoc.preg scratch
        insts := insts.push (.mov tag regDst dst)
        needsStore := true
      match regDst with
      | .preg GPR32.ecx =>
          match amount with
          | .imm _ => ()
          | _ =>
              let (scratch, used') := borrowScratch used
              used := used'
              let newReg := AbsLoc.preg scratch
              insts := insts.push (.mov tag newReg regDst)
              regDst := newReg
              needsStore := true
      | _ => ()
      let amt' ←
        match amount with
        | .imm _ => pure amount
        | .preg GPR32.ecx => pure amount
        | _ => do
            insts := insts.push (.mov tag (AbsLoc.preg GPR32.ecx) amount)
            pure (AbsLoc.preg GPR32.ecx)
      insts := insts.push (ctor tag regDst regDst amt')
      if needsStore then
        insts := insts.push (.mov tag dst regDst)
      return insts

private def rewriteInst
    (inst : Inst InstMData String AbsLoc) :
    RewriteM (Array (Inst InstMData String AbsLoc)) := do
  match inst with
  | .mov tag dst src =>
      let dst ← resolveLoc dst
      let src ← resolveLoc src
      pure (lowerMov tag dst src)
  | .add tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerTwoAddr Inst.add tag dst x y)
  | .sub tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerTwoAddr Inst.sub tag dst x y)
  | .band tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerTwoAddr Inst.band tag dst x y)
  | .bor tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerTwoAddr Inst.bor tag dst x y)
  | .xor tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerTwoAddr Inst.xor tag dst x y)
  | .mul tag dst x y =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerMul tag dst x y)
  | .push tag src =>
      let src ← resolveLoc src
      pure #[.push tag src]
  | .pop tag dst =>
      let dst ← resolveLoc dst
      if isImmLoc dst then
        panic! "register allocation: pop destination cannot be immediate"
      else
        pure #[.pop tag dst]
  | .pop' tag =>
      pure #[.pop' tag]
  | .cmp tag x y =>
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerCmpLike Inst.cmp tag x y)
  | .test tag x y =>
      let x ← resolveLoc x
      let y ← resolveLoc y
      pure (lowerCmpLike Inst.test tag x y)
  | .shl tag dst x amt =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let amt ← resolveLoc amt
      pure (lowerShift Inst.shl tag dst x amt)
  | .shr tag dst x amt =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let amt ← resolveLoc amt
      pure (lowerShift Inst.shr tag dst x amt)
  | .sar tag dst x amt =>
      let dst ← resolveLoc dst
      let x ← resolveLoc x
      let amt ← resolveLoc amt
      pure (lowerShift Inst.sar tag dst x amt)
  | .call' tag target =>
      pure #[.call' tag target]
  | inst =>
      panic! s!"register allocation: unexpected instruction {inst}"

private def rewriteTerminal
    (term : Terminal InstMData String AbsLoc) :
    RewriteM (Array (Inst InstMData String AbsLoc) × Terminal InstMData String AbsLoc) := do
  match term with
  | .ret tag v =>
      let v ← resolveLoc v
      if v == AbsLoc.preg GPR32.eax then
        pure (#[], .ret tag v)
      else
        pure (#[(Inst.mov tag (AbsLoc.preg GPR32.eax) v)], .ret tag (AbsLoc.preg GPR32.eax))
  | .br tag cond lt lf =>
      let cond ← resolveLoc cond
      pure (#[], .br tag cond lt lf)
  | .jmp tag lbl => pure (#[], .jmp tag lbl)
  | .jl tag lbl => pure (#[], .jl tag lbl)
  | .jle tag lbl => pure (#[], .jle tag lbl)
  | .jg tag lbl => pure (#[], .jg tag lbl)
  | .jge tag lbl => pure (#[], .jge tag lbl)
  | .jz tag lbl => pure (#[], .jz tag lbl)
  | .jnz tag lbl => pure (#[], .jnz tag lbl)

private def rewriteCFG (cfg : CFG' InstMData String AbsLoc)
    (homes : Std.HashMap DefUse AbsLoc) (nextSlot : Nat) :
    CFG' InstMData String AbsLoc := Id.run do
  let initial : RewriteState := { homes, nextSlot }
  let work : RewriteM (Array (BasicBlock InstMData String AbsLoc)) := do
    let mut blocks : Array (BasicBlock InstMData String AbsLoc) := #[]
    for block in cfg.blocks do
      let mut insts : Array (Inst InstMData String AbsLoc) := #[]
      for inst in block.insts do
        let lowered ← rewriteInst inst
        insts := insts.append lowered
      let (extra, term') ← rewriteTerminal block.terminal
      insts := insts.append extra
      blocks := blocks.push { block with insts := insts, terminal := term' }
    pure blocks
  let (blocks, _) := work.run initial
  { name := cfg.name, blocks := blocks }

def linear_scan_register_allocation (cfg : CFG' InstMData String AbsLoc)
    (intervals : Std.HashMap ValDef Interval) : CFG' InstMData String AbsLoc := Id.run do
  let (homes, nextSlot) := assignStackHomes intervals
  rewriteCFG cfg homes nextSlot
