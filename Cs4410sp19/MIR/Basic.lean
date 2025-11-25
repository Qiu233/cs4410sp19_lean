import Cs4410sp19.Basic
import Cs4410sp19.SSA.Basic
import Cs4410sp19.SSA.Construct
import Cs4410sp19.SSA.DeadBlock
import Cs4410sp19.SSA.TrivialBlock
import Cs4410sp19.SSA.BlockArgs
import Cs4410sp19.SSA.CopyPropagation
-- import Lean

-- run_meta do
--   let s ← `(do a; b;)
--   println! "{s}"

namespace Cs4410sp19
namespace MIR

inductive Inst (σ : Type) (γ : Type) (α : Type) where
  | mov : σ → α → α → Inst σ γ α

  | add : σ → α → α → α → Inst σ γ α
  | sub : σ → α → α → α → Inst σ γ α
  | mul : σ → α → α → α → Inst σ γ α

  | band : σ → α → α → α → Inst σ γ α
  | bor  : σ → α → α → α → Inst σ γ α
  -- | neg  : σ → α → α → Inst σ γ α

  -- | land : σ → α → α → α → Inst σ γ α
  -- | lor  : σ → α → α → α → Inst σ γ α
  | xor  : σ → α → α → α → Inst σ γ α

  | lt : σ → α → α → α → Inst σ γ α
  | le : σ → α → α → α → Inst σ γ α
  | gt : σ → α → α → α → Inst σ γ α
  | ge : σ → α → α → α → Inst σ γ α
  | eq : σ → α → α → α → Inst σ γ α
  | ne : σ → α → α → α → Inst σ γ α

  -- | push : σ → α → Inst σ γ α
  -- | pop  : σ → α → Inst σ γ α

  | cmp  : σ → α → α → α → Inst σ γ α
  | test : σ → α → α → α → Inst σ γ α

  | shl : σ → α → α → α → Inst σ γ α
  | shr : σ → α → α → α → Inst σ γ α
  | sar : σ → α → α → α → Inst σ γ α

  | jmp : σ → γ → Inst σ γ α
  | br  : σ → α → γ → γ → Inst σ γ α
  | jl  : σ → γ → Inst σ γ α
  | jle : σ → γ → Inst σ γ α
  | jg  : σ → γ → Inst σ γ α
  | jge : σ → γ → Inst σ γ α
  | jz  : σ → γ → Inst σ γ α
  | jnz : σ → γ → Inst σ γ α

  | call : σ → α → String → List α → Inst σ γ α
  | ret  : σ → α → Inst σ γ α
deriving Inhabited, Repr, BEq

def Inst.toString [ToString σ] [ToString γ] [ToString α] : Inst σ γ α → String
  |  .mov tag x y             => s!"{tag}\tmov {x}, {y}"
  |  .add tag x y z           => s!"{tag}\tadd {x}, {y}, {z}"
  |  .sub tag x y z           => s!"{tag}\tsub {x}, {y}, {z}"
  |  .mul tag x y z           => s!"{tag}\tmul {x}, {y}, {z}"
  |  .band tag x y z          => s!"{tag}\tand {x}, {y}, {z}"
  |  .bor  tag x y z          => s!"{tag}\tor {x}, {y}, {z}"
  -- |  .neg  tag x y            => s!"{tag}\tneg {x}, {y}"
  -- |  .land tag x y z          => s!"{tag}\tland {x}, {y}, {z}"
  -- |  .lor  tag x y z          => s!"{tag}\tlor {x}, {y}, {z}"
  |  .xor  tag x y z            => s!"{tag}\txor {x}, {y}, {z}"
  |  .lt tag x y z            => s!"{tag}\tlt {x}, {y}, {z}"
  |  .le tag x y z            => s!"{tag}\tle {x}, {y}, {z}"
  |  .gt tag x y z            => s!"{tag}\tgt {x}, {y}, {z}"
  |  .ge tag x y z            => s!"{tag}\tge {x}, {y}, {z}"
  |  .eq tag x y z            => s!"{tag}\teq {x}, {y}, {z}"
  |  .ne tag x y z            => s!"{tag}\tne {x}, {y}, {z}"
  -- | .push tag x            => s!"{tag}\tpush {x}"
  -- | .pop tag x             => s!"{tag}\tpop {x}"
  | .cmp tag x y z           => s!"{tag}\tcmp {x}, {y}, {z}"
  | .test tag x y z          => s!"{tag}\ttest {x}, {y}, {z}"
  |  .shl tag x y z           => s!"{tag}\tshl {x}, {y}, {z}"
  |  .shr tag x y z           => s!"{tag}\tshr {x}, {y}, {z}"
  |  .sar tag x y z           => s!"{tag}\tsar {x}, {y}, {z}"
  |  .jmp tag lbl             => s!"{tag}\tjmp {lbl}"
  |  .br tag cond lt' lf'     => s!"{tag}\tbr {cond}, {lt'}, {lf'}"
  |  .jl tag lbl              => s!"{tag}\tjl {lbl}"
  |  .jle tag lbl             => s!"{tag}\tjle {lbl}"
  |  .jg tag lbl              => s!"{tag}\tjg {lbl}"
  |  .jge tag lbl             => s!"{tag}\tjge {lbl}"
  |  .jz tag lbl              => s!"{tag}\tjz {lbl}"
  |  .jnz tag lbl             => s!"{tag}\tjnz {lbl}"
  |  .call tag dst fname args => s!"{tag}\tcall {dst}, {fname}, [{String.intercalate ", " (args.map ToString.toString)}]"
  |  .ret tag v               => s!"{tag}\tret {v}"

def Inst.toString' [ToString γ] [ToString α] : Inst Unit γ α → String
  |  .mov _ x y             => s!"    mov {x}, {y}"
  |  .add _ x y z           => s!"    add {x}, {y}, {z}"
  |  .sub _ x y z           => s!"    sub {x}, {y}, {z}"
  |  .mul _ x y z           => s!"    mul {x}, {y}, {z}"
  |  .band _ x y z          => s!"    and {x}, {y}, {z}"
  |  .bor  _ x y z          => s!"    or {x}, {y}, {z}"
  -- |  .neg  _ x y            => s!"    neg {x}, {y}"
  -- |  .land _ x y z          => s!"    land {x}, {y}, {z}"
  -- |  .lor  _ x y z          => s!"    lor {x}, {y}, {z}"
  |  .xor  _ x y z            => s!"    xor {x}, {y} {z}"
  |  .lt _ x y z            => s!"    lt {x}, {y}, {z}"
  |  .le _ x y z            => s!"    le {x}, {y}, {z}"
  |  .gt _ x y z            => s!"    gt {x}, {y}, {z}"
  |  .ge _ x y z            => s!"    ge {x}, {y}, {z}"
  |  .eq _ x y z            => s!"    eq {x}, {y}, {z}"
  |  .ne _ x y z            => s!"    ne {x}, {y}, {z}"
  -- | .push _ x            => s!"    push {x}"
  -- | .pop _ x             => s!"    pop {x}"
  | .cmp _ x y z           => s!"    cmp {x}, {y}, {z}"
  | .test _ x y z          => s!"    test {x}, {y}, {z}"
  |  .shl _ x y z           => s!"    shl {x}, {y}, {z}"
  |  .shr _ x y z           => s!"    shr {x}, {y}, {z}"
  |  .sar _ x y z           => s!"    sar {x}, {y}, {z}"
  |  .jmp _ lbl             => s!"    jmp {lbl}"
  |  .br _ cond lt' lf'     => s!"    br {cond}, {lt'}, {lf'}"
  |  .jl _ lbl              => s!"    jl {lbl}"
  |  .jle _ lbl             => s!"    jle {lbl}"
  |  .jg _ lbl              => s!"    jg {lbl}"
  |  .jge _ lbl             => s!"    jge {lbl}"
  |  .jz _ lbl              => s!"    jz {lbl}"
  |  .jnz _ lbl             => s!"    jnz {lbl}"
  |  .call _ dst fname args => s!"    call {dst}, {fname}, [{String.intercalate ", " (args.map ToString.toString)}]"
  |  .ret _ v               => s!"    ret {v}"

instance [ToString σ] [ToString γ] [ToString α] : ToString (Inst σ γ α) where
  toString := Inst.toString

instance (priority := high) [ToString γ] [ToString α] : ToString (Inst Unit γ α) where
  toString := Inst.toString'

structure VReg where
  name : String
deriving Inhabited, Repr, Hashable, BEq

instance : ToString VReg := ⟨fun x => x.name⟩

inductive AbsLoc where
  /-- 32 bit immediate value -/
  | imm : UInt32 → AbsLoc
  /-- virtual register -/
  | vreg : VReg → AbsLoc
  /-- frame slot (of variables) -/
  | frame : Nat → AbsLoc
  /-- arguments -/
  | arg : Nat → AbsLoc
deriving Inhabited, Repr, BEq

instance : ToString AbsLoc where
  toString
    | .imm x => s!"imm({x})"
    | .vreg x => s!"{x}"
    | .frame x => s!"frame[{x}]"
    | .arg x => s!"arg[{x}]"

-- inductive Reg where
--   | eax | ebx | ecx | edx
--   | esp | ebp
--   | edi | esi
-- deriving Inhabited, Repr, BEq

-- inductive Loc where
--   /-- 32 bit immediate value -/
--   | imm : UInt32 → Loc
--   -- /-- virtual register -/
--   -- | vreg : String → Loc
--   /-- physical x86 register -/
--   | reg : Reg → Loc
--   /-- [reg + offset] -/
--   | ref_offset : Reg → UInt32 → Loc
--   /-- hardcoded [address] -/
--   | address : UInt32 → Loc
-- deriving Inhabited, Repr, BEq

structure BasicBlock σ γ α where
  id : γ
  insts : Array (Inst σ γ α)
deriving Inhabited, Repr

inductive Edge (γ : Type) where
  | fall_through (P B : γ)
  | teleport (P B : γ)
deriving Inhabited, Repr

def Edge.P : Edge γ → γ
  | .fall_through P _ => P
  | .teleport P _ => P

def Edge.setP : Edge γ → γ → Edge γ
  | .fall_through _ B, P => .fall_through P B
  | .teleport _ B, P => .teleport P B

def Edge.B : Edge γ → γ
  | .fall_through _ B => B
  | .teleport _ B => B

def Edge.setB : Edge γ → γ → Edge γ
  | .fall_through P _, B => .fall_through P B
  | .teleport P _, B => .teleport P B

structure Edges (γ : Type) [Hashable γ] [BEq γ] where
  edges : Array (Option (Edge γ)) := {}
  table : Std.HashMap (γ × γ) Nat := {}
deriving Inhabited, Repr

structure CFG σ γ [Hashable γ] [BEq γ] α where
  name : String
  blocks : Array (BasicBlock σ γ α)
  edges : Edges γ
deriving Inhabited, Repr

protected def pp_insts [ToString σ] [ToString γ] [ToString α] (insts : List (Inst σ γ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"
protected def pp_insts' [ToString γ] [ToString α] (insts : List (Inst Unit γ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"

protected def pp_cfg [ToString σ] [ToString γ] [ToString α] [Hashable γ] [BEq γ] (cfg : CFG σ γ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    store := store.push s!"{i.id}:"
    store := store.push s!"{MIR.pp_insts i.insts.toList}"
  return String.intercalate "\n" store.toList

protected def pp_cfg' [ToString γ] [ToString α] [Hashable γ] [BEq γ]  (cfg : CFG Unit γ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    store := store.push s!"{i.id}:"
    store := store.push s!"{MIR.pp_insts' i.insts.toList}"
  return String.intercalate "\n" store.toList

def Inst.mapM_loc [Monad m] (f : α → m β) (inst : Inst σ γ α) : m (Inst σ γ β) := do
  match inst with
  | .mov tag x y => return .mov tag (← f x) (← f y)
  | .add tag x y z => return .add tag (← f x) (← f y) (← f z)
  | .sub tag x y z => return .sub tag (← f x) (← f y) (← f z)
  | .mul tag x y z => return .mul tag (← f x) (← f y) (← f z)

  | .band tag x y z => return .band tag (← f x) (← f y) (← f z)
  | .bor  tag x y z => return .bor  tag (← f x) (← f y) (← f z)
  -- | .neg  tag x y => return .neg  tag (← f x) (← f y)

  -- | .land tag x y z => return .land tag (← f x) (← f y) (← f z)
  -- | .lor  tag x y z => return .lor  tag (← f x) (← f y) (← f z)
  | .xor  tag x y z => return .xor  tag (← f x) (← f y) (← f z)

  | .lt tag x y z => return lt tag (← f x) (← f y) (← f z)
  | .le tag x y z => return le tag (← f x) (← f y) (← f z)
  | .gt tag x y z => return gt tag (← f x) (← f y) (← f z)
  | .ge tag x y z => return ge tag (← f x) (← f y) (← f z)
  | .eq tag x y z => return eq tag (← f x) (← f y) (← f z)
  | .ne tag x y z => return ne tag (← f x) (← f y) (← f z)

  -- | .push tag x => return .push tag (← f x)
  -- | .pop tag x => return .pop tag (← f x)
  | .cmp tag x y z => return .cmp tag (← f x) (← f y) (← f z)
  | .test tag x y z => return .test tag (← f x) (← f y) (← f z)

  | .shl tag x y z => return .shl tag (← f x) (← f y) (← f z)
  | .shr tag x y z => return .shr tag (← f x) (← f y) (← f z)
  | .sar tag x y z => return .sar tag (← f x) (← f y) (← f z)
  | .jmp tag lbl => return .jmp tag lbl
  | .br tag cond lt' lf' => return .br tag (← f cond) lt' lf'
  | .jl tag lbl  => return .jl tag lbl
  | .jle tag lbl => return .jle tag lbl
  | .jg tag lbl  => return .jg tag lbl
  | .jge tag lbl => return .jge tag lbl
  | .jz tag lbl  => return .jz tag lbl
  | .jnz tag lbl => return .jnz tag lbl
  | .call tag dst fname args => return .call tag (← f dst) fname (← args.mapM f)
  | .ret tag v => return .ret tag (← f v)

structure State where
  pref : String := "x"
  renaming' : Std.HashMap String String := {}

abbrev M := StateT State FreshM

def get_or_new_renaming (n : String) : M String := do
  let s ← getThe State
  if let some r := s.renaming'[n]? then
    return r
  else
    let new ← gensym s.pref
    modifyThe State fun s => {s with renaming' := s.renaming'.insert n new }
    return new

def get_or_new_renaming' (n : String) : M AbsLoc := do
  let s ← getThe State
  if let some r := s.renaming'[n]? then
    return .vreg ⟨r⟩
  else
    let new ← gensym s.pref
    modifyThe State fun s => {s with renaming' := s.renaming'.insert n new }
    return .vreg ⟨new⟩

def const_false : UInt32 := 0x00000001
def const_true : UInt32 := 0x80000001

def const_int_to_imm : Int → UInt32 := fun x => x.toInt32.toUInt32 <<< 1

def operand_to_loc (op : SSA.Operand) : M AbsLoc := do
  match op with
  | SSA.Operand.param .. => panic! ""
  | .var x => get_or_new_renaming' x.name
  | .const (SSA.ConstVal.bool false) => return AbsLoc.imm const_false
  | .const (SSA.ConstVal.bool true) => return AbsLoc.imm const_true
  | .const (SSA.ConstVal.int v) =>
    if v.toInt32.toBitVec[31] then
      panic! "integer overflow"
    return AbsLoc.imm (const_int_to_imm v)

def resolve_pc_simple (xs : List (SSA.VarName × SSA.Operand)) : M (List (Inst Unit String MIR.AbsLoc)) := do
  let mut g : Std.HashMap String String := {}
  for (v, o) in xs do
    match o with
    | .param .. => unreachable!
    | .var b => g := g.insert v.name b.name
    | .const c => pure ()
  let mut visited : Array String := #[]
  while !g.isEmpty do
    let t := g.filter fun v o => !g.contains o
    if t.isEmpty then
      break
    for (v, o) in t do
      visited := visited.push v
      g := g.erase v
      break
  if !g.isEmpty then
    panic! s!"{decl_name%}: pc contains rings" -- TODO: resolve rings instead of throw error
  -- let r := xs.mergeSort fun (a, o) (b, o') =>
  let xs' := xs.map fun x => ((visited.idxOf? x.fst.name).getD 0, x)
  let xs' := xs'.mergeSort fun (i1, _) (i2, _) => i1 < i2
  xs'.mapM fun (_, dst, x) => do
    let dst' ← get_or_new_renaming' dst.name
    let x' ← operand_to_loc x
    return Inst.mov () dst' x'

local macro "bin_op%" op:ident m:ident dst:term:arg x:term:arg y:term:arg : doElem => do
  let s ← `(doElem| do
      let dst' ← get_or_new_renaming' $(dst).name
      let x' ← operand_to_loc $x
      let y' ← operand_to_loc $y
      $m:ident := $(m).push <| $(op) () dst' x' y')
  return s

def construct_block (block : SSA.BasicBlock Unit String SSA.VarName SSA.Operand) : M (MIR.BasicBlock Unit String MIR.AbsLoc × Array (Edge String)) := do
  assert! block.params.isEmpty
  let mut insts : Array (MIR.Inst Unit String MIR.AbsLoc) := #[]
  let mut edges : Array (Edge String) := #[]
  for i in block.insts do
    match i with
    | SSA.Inst.prim2 _ dst .plus x y =>
      bin_op% Inst.add insts dst x y
    | SSA.Inst.prim2 _ dst .minus x y =>
      bin_op% Inst.sub insts dst x y
    | SSA.Inst.prim2 _ dst .times x y =>
      let dst' ← get_or_new_renaming' dst.name
      let x' ← operand_to_loc x
      let y' ← operand_to_loc y
      insts := insts.push <| .mul () dst' x' y'
      insts := insts.push <| .sar () dst' dst' (.imm 1)
    | SSA.Inst.prim2 _ dst .land x y =>
      bin_op% Inst.band insts dst x y
    | SSA.Inst.prim2 _ dst .lor x y =>
      bin_op% Inst.bor insts dst x y
    | SSA.Inst.prim2 _ dst .lt x y => bin_op% Inst.lt insts dst x y
    | SSA.Inst.prim2 _ dst .le x y => bin_op% Inst.le insts dst x y
    | SSA.Inst.prim2 _ dst .gt x y => bin_op% Inst.gt insts dst x y
    | SSA.Inst.prim2 _ dst .ge x y => bin_op% Inst.ge insts dst x y
    | SSA.Inst.prim2 _ dst .eq x y => bin_op% Inst.eq insts dst x y
    | SSA.Inst.prim2 _ dst .ne x y => bin_op% Inst.ne insts dst x y
    | SSA.Inst.prim1 _ dst .neg x =>
      let dst' ← get_or_new_renaming' dst.name
      let x' ← operand_to_loc x
      insts := insts.push <| Inst.sub () dst' (.imm 0) x'
    | SSA.Inst.prim1 _ dst .not x =>
      let dst' ← get_or_new_renaming' dst.name
      let x' ← operand_to_loc x
      insts := insts.push <| Inst.xor () dst' x' (.imm 0x8000_0000)
    | SSA.Inst.call _ dst name args =>
      let dst' ← get_or_new_renaming' dst.name
      let args' ← args.mapM operand_to_loc
      insts := insts.push <| Inst.call () dst' name args'
    | SSA.Inst.ret _ v =>
      let v' ← operand_to_loc v
      insts := insts.push <| Inst.ret () v'
    | SSA.Inst.get_arg _ dst i =>
      let dst' ← get_or_new_renaming' dst.name
      insts := insts.push <| Inst.mov () dst' (AbsLoc.arg i)
    | SSA.Inst.br _ cond lt' [] lf' [] =>
      let cond' ← operand_to_loc cond
      insts := insts.push <| Inst.br () cond' lt' lf'
      edges := edges.push (.teleport block.id lt')
      edges := edges.push (.teleport block.id lf')
    | SSA.Inst.br .. =>
      panic! s!"{decl_name%}: block args are not expected here"
    | .assign _ dst x =>
      let dst' ← get_or_new_renaming' dst.name
      let x' ← operand_to_loc x
      insts := insts.push <| Inst.mov () dst' x'
    | SSA.Inst.jmp _ target [] =>
      insts := insts.push <| Inst.jmp () target
      edges := edges.push (.teleport block.id target)
    | SSA.Inst.jmp .. =>
      panic! s!"{decl_name%}: block args are not expected here"
    | .pc _ xs =>
      let is ← resolve_pc_simple xs
      insts := insts.append is.toArray
    | .mk_tuple .. | .get_item .. | .prim1 ..
      => panic! s!"{decl_name%}: translation from SSA instruction not implemented: {i.toString}"
  return ({ id := block.id, insts }, edges)

-- #exit

def construct (cfg : SSA.CFG Unit String SSA.VarName SSA.Operand) : M (MIR.CFG Unit String MIR.AbsLoc) := do
  let mut blocks := #[]
  let mut edges : Edges String := {}
  for b in cfg.blocks do
    let (b', es) ← construct_block b
    blocks := blocks.push b'
    let start := edges.edges.size
    let ss := es.mapIdx fun i e => ((e.P, e.B), start + i) -- compute from start
    edges := { edges with edges := edges.edges.append (es.map Option.some), table := edges.table.insertMany ss }
  let mut adjacent : Std.HashSet (String × String) := {}
  for i in [0:blocks.size-1] do
    adjacent := adjacent.insert (blocks[i]!.id, blocks[i+1]!.id)
  for e in [0:edges.edges.size] do
    let some e' := edges.edges[e]! | continue
    if adjacent.contains (e'.P, e'.B) then
      edges := {edges with edges := edges.edges.set! e (some (.fall_through e'.P e'.B))}
  return { name := cfg.name, blocks, edges }

def split_by_logical_op? (block : BasicBlock Unit String MIR.AbsLoc) :
    Option (Array (Inst Unit String MIR.AbsLoc) × Inst Unit String MIR.AbsLoc × Array (Inst Unit String MIR.AbsLoc)) := do
  let (_, i) ← block.insts.zipIdx.find? fun (x, _) => x matches Inst.lt .. | Inst.le .. | Inst.gt .. | Inst.ge .. | Inst.eq .. | Inst.ne ..
  let inst := block.insts[i]!
  let firstHalf := block.insts.take i
  let secondHalf := block.insts.extract (i + 1)
  return (firstHalf, inst, secondHalf)

def reduce_lop (cfg : MIR.CFG Unit String MIR.AbsLoc) : M (MIR.CFG Unit String MIR.AbsLoc) := do
  let mut blocks : Array (BasicBlock Unit String MIR.AbsLoc) := #[]
  let mut edges := cfg.edges
  for block in cfg.blocks do
    assert! !block.insts.isEmpty
    let some (fhalf, inst, shalf) := split_by_logical_op? block
      | blocks := blocks.push block; continue
    match inst with
    | .lt _ c a b =>
      let n ← VReg.mk <$> gensym "n"
      let side ← gensym ".side"
      let shalf_name ← gensym ".label_less"
      let cmp : Inst Unit String MIR.AbsLoc := Inst.cmp () (.vreg n) a b
      let mov_true : Inst Unit String MIR.AbsLoc := Inst.mov () c (.imm const_true)
      let mov_false : Inst Unit String MIR.AbsLoc := Inst.mov () c (.imm const_false)
      let jl : Inst Unit String MIR.AbsLoc := Inst.jl () shalf_name
      let fhalf' := fhalf.append #[cmp, mov_true, jl]
      let block' := { id := block.id, insts := fhalf' : BasicBlock Unit String MIR.AbsLoc }
      let side_block : BasicBlock Unit String MIR.AbsLoc := { id := side, insts := #[ mov_false, Inst.jmp () shalf_name ] }
      let next := { id := shalf_name, insts := shalf : BasicBlock Unit String MIR.AbsLoc }
      blocks := blocks.append #[block', side_block, next]
      let ss := edges.edges.filterMap id |>.filter fun e => e.P == block'.id
      for e in ss do
        let i := edges.table[(e.P, e.B)]!
        let some e' := edges.edges[i]! | unreachable!
        edges := { edges with edges := edges.edges.set! i none }
        edges := { edges with table := edges.table.erase (e.P, e.B) }

    | _ => panic! ""
  sorry

end MIR


-- #exit

-- open SSA

def src := "def f(x, y):
  let t = 7 in
  let x = 5 in
  (if x == 0: 0 else: if x == 1: 1 + 4 else: 2) + (if y == 1: 2 else: 3) + x + t
"

-- #eval do
--   let e ← match (parse_function_decl <* Std.Internal.Parsec.String.ws <* Std.Internal.Parsec.eof).run src with
--     | .error e => println! s!"failed to parse expression due to: {e}"; return
--     | .ok r => pure r
--   let s := ContT.run (m := SSA.M) (do
--     let a ← anf_decl e.decls[0]!
--     let t := (match a with | ADecl.function _ f => f)
--     let r ← liftM <| SSA.cfg_of_function_def t
--     let r : SSA.CFG' Unit String SSA.VarName SSA.Operand := { r with }
--     return r
--     ) (fun n => pure n) |>.run {} |>.run' {}
--   let (r, s) := s.run {}
--   println! "converted:"
--   println! "{SSA.pp_cfg' r.toCFG}\n"

--   let r := SSA.reduce_assign r
--   println! "unary assignment reduced:"
--   println! "{SSA.pp_cfg' r.toCFG}\n"

--   let r := SSA.eliminate_trivial_blocks r
--   println! "trivial blocks reduced:"
--   println! "{SSA.pp_cfg' r.toCFG}\n"

--   let (r, s) := FreshM.run (SSA.eliminate_block_args r) s
--   println! "block args eliminated:"
--   println! "{SSA.pp_cfg' r.toCFG}\n"

--   let (r, s) := FreshM.run (MIR.construct r.toCFG |>.run' {}) {}
--   println! "MIR constructed:"
--   println! "{MIR.pp_cfg' r}\n"
