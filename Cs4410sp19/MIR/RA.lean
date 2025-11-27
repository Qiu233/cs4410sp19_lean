import Cs4410sp19.MIR.Basic
import Cs4410sp19.MIR.Construct
import Cs4410sp19.MIR.MData

namespace Cs4410sp19
namespace MIR

/-!
Compute liveness (live-in and live-out sets) for a CFG'.
The input must be annotated with `InstMData` (so immediates and flags
are represented at the DefUse level). We build per-block use/def sets
from `InstMData.used` / `InstMData.defs` (mapping `DefUse` -> `AbsLoc`) and
run a standard backwards dataflow fixed-point. `DefUse.flags` is ignored
because flags are not represented as `AbsLoc`.
Returns a pair (livein_map, liveout_map) mapping block id to a HashSet of AbsLoc.
-/
def liveness (cfg : CFG' InstMData String AbsLoc) :
    Std.HashMap String (Std.HashSet AbsLoc) × Std.HashMap String (Std.HashSet AbsLoc) := Id.run do

  -- compute use/def for each block from InstMData (ignore immediates)
  let mut use_map : Std.HashMap String (Std.HashSet AbsLoc) := {}
  let mut def_map : Std.HashMap String (Std.HashSet AbsLoc) := {}
  for b in cfg.blocks do
    let mut defs : Std.HashSet AbsLoc := {}
    let mut uses : Std.HashSet AbsLoc := {}

    -- helper to map DefUse -> Option AbsLoc (flags -> none)
    let defuse_to_loc := fun (d : DefUse) => match d with
      | DefUse.vreg v => some (AbsLoc.vreg v)
      | DefUse.greg r => some (AbsLoc.preg r)
      | DefUse.flags   => none

    for inst in b.insts do
      let md := inst.tag
      -- defs first: collect defs into defs set
      for d in md.defs do
        match defuse_to_loc d with
        | some loc => defs := defs.insert loc
        | none => ()
      -- then uses: only add uses not already defined in this block
      for u in md.used do
        match defuse_to_loc u with
        | some loc => if !defs.contains loc then uses := uses.insert loc else ()
        | none => ()

    -- terminal tag may contain uses/defs (e.g. ret uses)
    match b.terminal.tag with
    | md =>
      for d in md.defs do
        match defuse_to_loc d with
        | some loc => defs := defs.insert loc
        | none => ()
      for u in md.used do
        match defuse_to_loc u with
        | some loc => if !defs.contains loc then uses := uses.insert loc else ()
        | none => ()

    use_map := use_map.insert b.id uses
    def_map := def_map.insert b.id defs

  -- initialize live maps
  let mut livein : Std.HashMap String (Std.HashSet AbsLoc) := {}
  let mut liveout : Std.HashMap String (Std.HashSet AbsLoc) := {}
  for b in cfg.blocks do
    livein := livein.insert b.id {}
    liveout := liveout.insert b.id {}

  -- helpers
  let union_sets := fun (s1 s2 : Std.HashSet AbsLoc) => s2.fold (init := s1) fun acc x => acc.insert x
  let sets_equal := fun (s1 s2 : Std.HashSet AbsLoc) =>
    if s1.size != s2.size then false else s1.fold (init := true) fun acc v => acc && s2.contains v

  -- fixed-point iteration (backwards dataflow)
  let mut changed := true
  while changed do
    changed := false
    for b in cfg.blocks do
      let succs := (cfg.config.successors[b.id]?).getD []
      let succ_ids := succs.map fun e => e.B

      -- new_out = union of livein of successors
      let mut new_out : Std.HashSet AbsLoc := {}
      for sid in succ_ids do
        new_out := union_sets new_out ((livein[sid]?).getD {})

      -- new_in = use[b] ∪ (new_out \ def[b])
      let defs := (def_map[b.id]?).getD {}
      let uses := (use_map[b.id]?).getD {}
      let out_minus_defs := new_out.fold (init := {}) fun acc v => if defs.contains v then acc else acc.insert v
      let new_in := union_sets uses out_minus_defs

      let old_out := (liveout[b.id]?).getD {}
      let old_in := (livein[b.id]?).getD {}

      if !(sets_equal old_out new_out && sets_equal old_in new_in) then
        liveout := liveout.insert b.id new_out
        livein := livein.insert b.id new_in
        changed := true

  (livein, liveout)

-- #exit

/-- [start_inc, end_exc) -/
structure Segment where
  start_inc : Nat
  end_exc : Nat
  used_pos : List Nat
deriving Inhabited, Repr

/-- non-overlapping sorted segments -/
structure Interval where
  segs : Array Segment
deriving Inhabited, Repr

instance : ToString Interval where
  toString x := s!"[{String.intercalate ", " (x.segs.toList.map fun x => s!"[{x.start_inc}-{x.end_exc})!{x.used_pos}")}]"

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
      if last.end_exc >= next.start_inc then
        let used := last.used_pos ++ next.used_pos
        let used := used.mergeSort
        let used := used.eraseDups
        res := res.pop.push ⟨last.start_inc, Nat.max last.end_exc next.end_exc, used⟩
      else
        res := res.push next
  return ⟨res⟩

def Interval.addRange : Interval → Nat → Nat → List Nat → Interval := fun l x y used => Interval.merge l ⟨#[⟨x, y, used⟩]⟩

def Interval.setFrom : Interval → Nat → Interval := fun l f => Id.run do
  let mut is := l.segs.toList
  while is.length != 0 do
    let i :: is' := is | unreachable!
    if i.end_exc > f then
      break
    is := is'
  if is.isEmpty then
    return ⟨#[⟨f, f + 1, []⟩]⟩ -- at least live for one instruction
  let i :: is' := is | unreachable!
  return ⟨({i with start_inc := f} :: is').toArray⟩

def build_live_intervals (cfg : CFG' InstMData String AbsLoc) : Std.HashMap AbsLoc Interval := Id.run do
  let (liveIn, _) := liveness cfg
  let blocks := cfg.blocks
  let mut intervals : Std.HashMap AbsLoc Interval := {}

  let basic_from := fun (b : BasicBlock InstMData String AbsLoc) => b.insts[0]?.map (fun x => x.tag.lineno) |>.getD b.terminal.tag.lineno
  let basic_to := fun (b : BasicBlock InstMData String AbsLoc) => (b.insts.back?.map (fun x => x.tag.lineno) |>.getD b.terminal.tag.lineno) + 1

  let defuse_to_loc := fun (d : DefUse) => match d with
    | DefUse.vreg v => some (AbsLoc.vreg v)
    | DefUse.greg r => some (AbsLoc.preg r)
    | DefUse.flags => none

  for b in blocks.reverse do
    let ss := cfg.config.successors[b.id]?.getD []
    let mut live : Std.HashSet AbsLoc := ({} : Std.HashSet AbsLoc)
    for e in ss do
      live := live.insertMany ((liveIn[e.B]?).getD {})

    let term_md := b.terminal.tag
    for u in term_md.used do
      match defuse_to_loc u with
      | some l => live := live.insert l
      | none => ()

    let b_from := 2 * (basic_from b)
    let b_to := 2 * (basic_to b)
    for opd in live.toList do
      intervals := intervals.alter opd fun
        | none => some Interval.empty
        | some x => some x
      let used := b.insts.filterMap fun x =>
        let md := x.tag
        if md.used.foldl (init := false) (fun acc d => acc || (defuse_to_loc d == some opd)) then
          some (2 * md.lineno)
        else
          none
      intervals := intervals.modify opd fun itv => itv.addRange b_from b_to used.toList

    for op in b.insts.reverse do
      let md := op.tag
      for d in md.defs do
        match defuse_to_loc d with
        | some opd =>
          intervals := intervals.alter opd fun
            | none => some Interval.empty
            | some x => some x
          intervals := intervals.modify opd fun itv => itv.setFrom (2 * md.lineno + 1)
          live := live.erase opd
        | none => ()

      for u in md.used do
        match defuse_to_loc u with
        | some opd =>
          intervals := intervals.alter opd fun
            | none => some Interval.empty
            | some x => some x
          let used := b.insts.filterMap fun x =>
            let mdx := x.tag
            if mdx.used.foldl (init := false) (fun acc d => acc || (defuse_to_loc d == some opd)) then
              some (2 * mdx.lineno)
            else
              none
          intervals := intervals.modify opd fun itv => itv.addRange b_from (2 * md.lineno) used.toList
          live := live.insert opd
        | none => ()

    -- no block params in MIR.Basic.BasicBlock

  intervals
