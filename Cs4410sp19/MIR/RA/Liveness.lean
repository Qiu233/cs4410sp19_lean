import Cs4410sp19.MIR.MData

namespace Cs4410sp19.MIR.RegAlloc

abbrev LiveSet := List DefUse

private def union (xs ys : LiveSet) : LiveSet :=
  ys.foldl (fun acc x => if acc.contains x then acc else x :: acc) xs

private def sameSet (xs ys : LiveSet) : Bool :=
  xs.length == ys.length && xs.all ys.contains

private def transfer (tag : InstMData) (live : LiveSet) : LiveSet :=
  union (live.filter fun x => !tag.defs.contains x) tag.used.toList

structure Liveness where
  liveIn : Std.HashMap String LiveSet := {}
  liveOut : Std.HashMap String LiveSet := {}
  before : Std.HashMap Nat LiveSet := {}
  after : Std.HashMap Nat LiveSet := {}
deriving Inhabited

/-- Backward fixed-point analysis. No recursive walks through CFG cycles, and no
    SSA assumption: all definitions of a virtual register share one live set. -/
def computeLiveness (cfg : CFG' InstMData String AbsLoc) : Liveness := Id.run do
  let mut result : Liveness := {}
  let mut changed := true
  while changed do
    changed := false
    for b in cfg.blocks.reverse do
      let out := (cfg.succ b.id).foldl (fun acc s => union acc (result.liveIn[s]?.getD [])) []
      let tags := b.insts.map Inst.tag |>.push b.terminal.tag
      let input := tags.reverse.foldl (fun live tag => transfer tag live) out
      if !sameSet input (result.liveIn[b.id]?.getD []) ||
          !sameSet out (result.liveOut[b.id]?.getD []) then
        changed := true
      result := { result with
        liveIn := result.liveIn.insert b.id input
        liveOut := result.liveOut.insert b.id out }
  for b in cfg.blocks do
    let mut live := result.liveOut[b.id]?.getD []
    for tag in (b.insts.map Inst.tag |>.push b.terminal.tag).reverse do
      result := { result with after := result.after.insert tag.lineno live }
      live := transfer tag live
      result := { result with before := result.before.insert tag.lineno live }
  return result

abbrev Graph := Std.HashMap DefUse LiveSet
abbrev Homes := Std.HashMap VReg AbsLoc

private def allocatable : DefUse → Bool
  | .flags => false
  | _ => true

private def connect (g : Graph) (x y : DefUse) : Graph :=
  if x == y || !allocatable x || !allocatable y then g
  else
    let add := fun (xs : LiveSet) => if xs.contains y then xs else y :: xs
    let g := g.insert x (add (g[x]?.getD []))
    let xs := g[y]?.getD []
    g.insert y (if xs.contains x then xs else x :: xs)

private def clique (g : Graph) (xs : LiveSet) : Graph :=
  xs.foldl (fun g x => xs.foldl (fun g y => connect g x y) g) g

/-- Include simultaneous inputs, simultaneous outputs, and dead writes which
    would otherwise overwrite a live value. Physical registers are precolored. -/
def buildGraph (cfg : CFG' InstMData String AbsLoc) (live : Liveness) : Graph := Id.run do
  let mut g : Graph := {}
  for b in cfg.blocks do
    for tag in b.insts.map Inst.tag |>.push b.terminal.tag do
      for x in tag.used ++ tag.defs do
        if allocatable x && !g.contains x then g := g.insert x []
      g := clique g (live.before[tag.lineno]?.getD [])
      g := clique g (live.after[tag.lineno]?.getD [])
      for d in tag.defs do
        for v in live.after[tag.lineno]?.getD [] do
          g := connect g d v
  return g

private def registers : List GPR32 := [.eax, .ecx, .edx, .ebx]

/-- Simplify/select coloring with optimistic spill candidates. Each select step
    either picks a physical register or a fresh stack slot, so allocation always
    terminates, independently of register pressure. Stack homes are deliberately
    unique; slot reuse needs a separate interference analysis. -/
def colorGraph (g : Graph) (firstSlot : Nat) : Homes := Id.run do
  let vars := g.keys.filterMap fun
    | .vreg v => some v
    | _ => none
  let mut remaining := vars.mergeSort (fun x y => x.name < y.name)
  let mut stack : List VReg := []
  while !remaining.isEmpty do
    let degree := fun (v : VReg) => (g[DefUse.vreg v]?.getD []).countP fun
      | .greg _ => true
      | .vreg n => remaining.contains n
      | .flags => false
    let chosen := (remaining.find? fun v => degree v < registers.length).getD remaining.head!
    stack := chosen :: stack
    remaining := remaining.erase chosen
  let mut homes : Homes := {}
  let mut slot := firstSlot
  for v in stack do
    let forbidden := (g[DefUse.vreg v]?.getD []).filterMap fun
      | .greg r => some r
      | .vreg n => match homes[n]? with
        | some (.preg r) => some r
        | _ => none
      | .flags => none
    match registers.find? (fun r => !forbidden.contains r) with
    | some r => homes := homes.insert v (.preg r)
    | none =>
      homes := homes.insert v (.frame slot)
      slot := slot + 1
  return homes

end Cs4410sp19.MIR.RegAlloc
