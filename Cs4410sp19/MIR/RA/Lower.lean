import Cs4410sp19.MIR.RA.Liveness
import Cs4410sp19.MIR.Assemble

namespace Cs4410sp19.MIR.RegAlloc

abbrev Code := CFG Unit String AbsLoc
/-- `some n` identifies the one semantic operation corresponding to input line n.
    `none` is an inserted copy/save/reload/store, checked independently. -/
abbrev AllocatedCode := CFG (Option Nat) String AbsLoc

private def mem : AbsLoc → Bool
  | .frame _ | .arg _ => true
  | _ => false

/-- Make fixed-register constraints visible before building interference. Saving
    an explicitly live ECX handles machine IR too, not just compiler-generated
    virtual operands. All added memory slots are above the input's frame slots. -/
def prepare (cfg : Code) : Code := Id.run do
  let tagged := compute_mdata cfg
  let live := computeLiveness { tagged with }
  let mut slot := Assemble.requiredFrameSlots cfg
  let mut blocks := #[]
  for b in tagged.blocks do
    let mut insts : Array (Inst Unit String AbsLoc) := #[]
    for i in b.insts do
      let lowerShift := fun (ctor : Unit → AbsLoc → AbsLoc → AbsLoc → Inst Unit String AbsLoc)
          (dst x amount : AbsLoc) => Id.run do
        let base := ctor () dst x amount
        match amount with
        | .imm n => return (#[ctor () dst x (.imm (n &&& 31))], slot)
        | .preg .ecx => return (#[base], slot)
        | _ =>
          if dst == .preg .ecx then
            let tmp := AbsLoc.frame slot
            return (#[.mov () tmp x, .mov () (.preg .ecx) amount,
              ctor () tmp tmp (.preg .ecx), .mov () dst tmp], slot + 1)
          else
            let save := (live.after[i.tag.lineno]?.getD []).contains (.greg .ecx)
            let copies := #[.mov () (.preg .ecx) amount, ctor () dst x (.preg .ecx)]
            if save then
              let tmp := AbsLoc.frame slot
              return (#[.mov () tmp (.preg .ecx)] ++ copies ++ #[.mov () (.preg .ecx) tmp], slot + 1)
            else return (copies, slot)
      let (code, nextSlot) := match i with
        | .shl _ d x n => lowerShift Inst.shl d x n
        | .shr _ d x n => lowerShift Inst.shr d x n
        | .sar _ d x n => lowerShift Inst.sar d x n
        | _ => (#[i.setTag ()], slot)
      insts := insts ++ code
      slot := nextSlot
    let terminal := match b.terminal with
      | .ret _ _ => Terminal.ret () (.preg .eax)
      | t => t.setTag ()
    if let .ret _ value := b.terminal then
      insts := insts.push (.mov () (.preg .eax) value)
    blocks := blocks.push { id := b.id, insts, terminal }
  return { cfg with blocks }

def home (homes : Homes) (loc : AbsLoc) : Except String AbsLoc :=
  match loc with
  | .vreg v => match homes[v]? with
    | some loc => pure loc
    | none => throw s!"register allocation: missing home for {v}"
  | _ => pure loc

private def scratchRegisters : List GPR32 := [.edx, .eax, .ecx, .ebx]

/-- Register scavenging with a dedicated frame slot. Even if every register is
    live, one can be borrowed: save/restore with MOV preserves both its value and
    EFLAGS. Never use PUSH/POP, which would disturb outgoing arguments. Each
    supported x86 shape needs at most one scratch and mentions at most one other
    physical register when it needs that scratch. No recursive spill rewriting. -/
private def withScratch (slot : Nat) (operands : List AbsLoc)
    (body : AbsLoc → Array (Inst (Option Nat) String AbsLoc)) :
    Except String (Array (Inst (Option Nat) String AbsLoc)) := do
  let used := operands.filterMap fun
    | .preg r => some r
    | _ => none
  let some r := scratchRegisters.find? (fun r => !used.contains r)
    | throw "register allocation: invalid instruction needs too many scratch registers"
  let tmp := AbsLoc.preg r
  return #[.mov none (.frame slot) tmp] ++ body tmp ++ #[.mov none tmp (.frame slot)]

private def validDst (dst : AbsLoc) : Except String Unit :=
  match dst with
  | .imm _ | .vreg _ => throw s!"register allocation: invalid destination {dst}"
  | _ => pure ()

private def twoAddr (dst x : AbsLoc) : Except String Unit := do
  validDst dst
  unless dst == x do
    throw s!"register allocation: instruction must be in two-address form ({dst}, {x})"

def lowerInst (scratchSlot : Nat) (inst : Inst Nat String AbsLoc) :
    Except String (Array (Inst (Option Nat) String AbsLoc)) := do
  let tag := some inst.tag
  let binary := fun ctor dst x y => do
    twoAddr dst x
    if mem dst && mem y then
      withScratch scratchSlot [dst, y] fun r => #[.mov none r y, ctor tag dst dst r]
    else pure #[ctor tag dst dst y]
  let compare := fun ctor x y => do
    match x with
    | .imm _ => withScratch scratchSlot [y] fun r => #[.mov none r x, ctor tag r y]
    | _ =>
      if mem x && mem y then
        withScratch scratchSlot [x, y] fun r => #[.mov none r y, ctor tag x r]
      else pure #[ctor tag x y]
  let shift := fun ctor dst x n => do
    twoAddr dst x
    match n with
    | .imm _ | .preg .ecx => pure #[ctor tag dst dst n]
    | _ => throw "register allocation: shift count must be immediate or ECX"
  match inst with
  | .mov _ dst src =>
    validDst dst
    if mem dst && mem src then
      withScratch scratchSlot [dst, src] fun r => #[.mov none r src, .mov tag dst r]
    else pure #[.mov tag dst src]
  | .add _ d x y => binary Inst.add d x y
  | .sub _ d x y => binary Inst.sub d x y
  | .band _ d x y => binary Inst.band d x y
  | .bor _ d x y => binary Inst.bor d x y
  | .xor _ d x y => binary Inst.xor d x y
  | .mul _ d x y =>
    twoAddr d x
    if mem d then
      withScratch scratchSlot [d, y] fun r =>
        #[.mov none r d, .mul tag r r y, .mov none d r]
    else pure #[.mul tag d d y]
  | .cmp _ x y => compare Inst.cmp x y
  | .test _ x y => compare Inst.test x y
  | .shl _ d x n => shift Inst.shl d x n
  | .shr _ d x n => shift Inst.shr d x n
  | .sar _ d x n => shift Inst.sar d x n
  | .push _ x => pure #[.push tag x]
  | .pop _ dst => validDst dst; pure #[.pop tag dst]
  | .pop' _ => pure #[.pop' tag]
  | .call' _ target => pure #[.call' tag target]
  | _ => throw "register allocation: high-level instructions must be lowered first"

def lower (cfg : CFG InstMData String AbsLoc) (homes : Homes) : Except String AllocatedCode := do
  let resolvedBlocks : Array (BasicBlock Nat String AbsLoc) ← cfg.blocks.mapM fun b => do
    let insts ← b.insts.mapM fun i => do
      (← i.mapM_loc (home homes)).setTag i.tag.lineno |> pure
    let terminal ← b.terminal.mapM_loc (home homes)
    pure { id := b.id, insts, terminal := terminal.setTag b.terminal.tag.lineno }
  let resolved : CFG Nat String AbsLoc := { name := cfg.name, blocks := resolvedBlocks }
  let scratchSlot := Assemble.requiredFrameSlots resolved.unsetTag
  let blocks ← resolved.blocks.mapM fun b => do
    let insts ← b.insts.flatMapM (lowerInst scratchSlot)
    pure { id := b.id, insts, terminal := b.terminal.setTag (some b.terminal.tag) }
  return { name := cfg.name, blocks }

end Cs4410sp19.MIR.RegAlloc
