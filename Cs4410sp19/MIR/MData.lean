import Cs4410sp19.MIR.Basic

namespace Cs4410sp19
namespace MIR

def annotate_lineno [Hashable γ] [BEq γ] : CFG Unit γ α → CFG Nat γ α := fun cfg => Id.run do
  let mut bs : Array (BasicBlock Nat γ α) := #[]
  let mut i : Nat := 0
  for b in cfg.blocks do
    let mut xs : Array (Inst Nat γ α) := #[]
    for inst in b.insts do
      xs := xs.push (inst.setTag i)
      i := i + 1
    bs := bs.push (BasicBlock.mk b.id xs (b.terminal.setTag i))
    i := i + 1
  return { name := cfg.name, blocks := bs }

instance : Hashable GPR32 where
  hash
    | .eax => 1
    | .ebx => 2
    | .ecx => 3
    | .edx => 4

instance : Hashable AbsLoc where
  hash
    | .imm n => (n.toUInt64 <<< 3) + 1
    | .preg r => (Hashable.hash r <<< 3) + 2
    | .vreg v => (Hashable.hash v.name <<< 3) + 3
    | .frame n => (n.toUInt64 <<< 3) + 4
    | .arg n => (n.toUInt64 <<< 3) + 5

def Inst.uses : Inst σ γ α → List α
  | .mov _ _ src => [src]
  | .add _ _ x y => [x, y]
  | .sub _ _ x y => [x, y]
  | .mul _ _ x y => [x, y]
  | .band _ _ x y => [x, y]
  | .bor  _ _ x y => [x, y]
  | .xor  _ _ x y => [x, y]
  | .lt _ _ x y => [x, y]
  | .le _ _ x y => [x, y]
  | .gt _ _ x y => [x, y]
  | .ge _ _ x y => [x, y]
  | .eq _ _ x y => [x, y]
  | .ne _ _ x y => [x, y]
  | .push _ x => [x]
  | .pop _ _ => []
  | .pop' _ => []
  | .cmp _ x y => [x, y]
  | .test _ x y => [x, y]
  | .shl _ _ x y => [x, y]
  | .shr _ _ x y => [x, y]
  | .sar _ _ x y => [x, y]
  | .call _ _ _ args => args
  | .call' _ _ => []

def Inst.defs : Inst σ γ α → List α
  | .mov _ dst _ => [dst]
  | .add _ dst _ _ => [dst]
  | .sub _ dst _ _ => [dst]
  | .mul _ dst _ _ => [dst]
  | .band _ dst _ _ => [dst]
  | .bor  _ dst _ _ => [dst]
  | .xor  _ dst _ _ => [dst]
  | .lt _ dst _ _ => [dst]
  | .le _ dst _ _ => [dst]
  | .gt _ dst _ _ => [dst]
  | .ge _ dst _ _ => [dst]
  | .eq _ dst _ _ => [dst]
  | .ne _ dst _ _ => [dst]
  | .push _ _ => []
  | .pop _ dst => [dst]
  | .pop' _ => []
  | .cmp _ _ _ => []
  | .test _ _ _ => []
  | .shl _ dst _ _ => [dst]
  | .shr _ dst _ _ => [dst]
  | .sar _ dst _ _ => [dst]
  | .call _ dst _ _ => [dst]
  | .call' _ _ => []

def Terminal.uses : Terminal σ γ α → List α
  | .jmp _ _ => []
  | .br _ cond _ _ => [cond]
  | .jl _ _ => []
  | .jle _ _ => []
  | .jg _ _ => []
  | .jge _ _ => []
  | .jz _ _ => []
  | .jnz _ _ => []
  | .ret _ v => [v]

inductive DefUse where
  | vreg : VReg → DefUse
  | greg : GPR32 → DefUse
  | flags
deriving Inhabited, Repr, Hashable, BEq

structure InstMData where
  lineno : Nat
  used   : Array DefUse
  defs   : Array DefUse
deriving Inhabited, Repr

-- def InstMData.is_vreg_def : InstMData → VReg → Bool :=
--   fun mdata vreg => mdata.defs.any fun x => x == .vreg vreg

-- def InstMData.is_vreg_use : InstMData → VReg → Bool :=
--   fun mdata vreg => mdata.used.any fun x => x == .vreg vreg

def InstMData.is_def : InstMData → DefUse → Bool :=
  fun mdata d => mdata.defs.any fun x => x == d

def InstMData.is_used : InstMData → DefUse → Bool :=
  fun mdata d => mdata.used.any fun x => x == d

instance : ToString DefUse where
  toString
    | .vreg v => v.name
    | .greg r => toString r
    | .flags => "EFLAGS"

instance : ToString InstMData where
  toString x :=
    s!"line {x.lineno}, used: [{String.intercalate ", " (x.used.toList.map toString)}], defs: [{String.intercalate ", " (x.defs.toList.map toString)}]"

def AbsLoc.toDefUse? : AbsLoc → Option DefUse
  | .vreg v => some (DefUse.vreg v)
  | .preg r => some (DefUse.greg r)
  | _ => none

def compute_mdata (cfg : CFG Unit String AbsLoc) : CFG InstMData String AbsLoc := Id.run do
  let cfg := annotate_lineno cfg
  let blocks := cfg.blocks.map fun b =>
    let insts : Array (Inst InstMData String MIR.AbsLoc) := b.insts.map fun inst => Id.run do
      match inst with
      | .call .. => panic! "compute_mdata: unexpected `call` instruction"
      | .lt .. | .le .. | .gt .. | .ge .. | .eq .. | .ne .. =>
        panic! "compute_mdata: unexpected logical instruction"
      | _ =>
        let lineno := inst.tag
        -- helpers to collect DefUse from AbsLoc
        let add_from_abs := fun (acc : Array DefUse) (a : AbsLoc) =>
          match a with
          | .vreg v => acc.push (DefUse.vreg v)
          | .preg r => acc.push (DefUse.greg r)
          | _ => acc

        -- collect used from Inst.uses
        let mut used := #[]
        for u in inst.uses do
          used := add_from_abs used u

        -- collect defs from Inst.defs
        let mut defs := #[]
        for d in inst.defs do
          defs := add_from_abs defs d

        -- arithmetic-like instructions and cmp/test/set flags
        let mut add_flags := false
        match inst with
        | .add .. | .sub .. | .mul .. | .band .. | .bor .. | .xor .. | .shl .. | .shr .. | .sar .. =>
          add_flags := true
        | .cmp .. | .test .. =>
          add_flags := true
        | _ => ()
        if add_flags then
          defs := defs.push DefUse.flags

        -- handle call' (cdecl clobbers caller-saved registers)
        match inst with
        | .call' .. =>
          defs := defs.push (DefUse.greg GPR32.eax)
          defs := defs.push (DefUse.greg GPR32.ecx)
          defs := defs.push (DefUse.greg GPR32.edx)
        | _ => ()

        inst.setTag { lineno := lineno, used := used, defs := defs }
    let terminal : Terminal InstMData String MIR.AbsLoc := Id.run do
      match b.terminal with
      | .jmp n lbl => Terminal.jmp { lineno := n, used := #[], defs := #[] } lbl
      | .br .. => panic! "compute_mdata: unexpected `br` terminal"
      | .jl n lbl => Terminal.jl { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .jle n lbl => Terminal.jle { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .jg n lbl => Terminal.jg { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .jge n lbl => Terminal.jge { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .jz n lbl => Terminal.jz { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .jnz n lbl => Terminal.jnz { lineno := n, used := #[DefUse.flags], defs := #[] } lbl
      | .ret n v =>
      let mut used_t := #[]
        match v with
        | .vreg vr => used_t := used_t.push (DefUse.vreg vr)
        | .preg r => used_t := used_t.push (DefUse.greg r)
        | _ => ()
        Terminal.ret { lineno := n, used := used_t, defs := #[] } v
    { id := b.id, insts, terminal := terminal : BasicBlock InstMData String MIR.AbsLoc }
  { name := cfg.name, blocks := blocks }
