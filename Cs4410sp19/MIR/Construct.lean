import Cs4410sp19.MIR.Basic

namespace Cs4410sp19
namespace MIR

private structure State where
  pref : String := "x"
  renaming' : Std.HashMap String String := {}

private abbrev M := StateT State FreshM

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
  -- Snapshot every RHS before any destination is overwritten. This handles
  -- chains, cycles, constants and self copies uniformly; coloring can eliminate
  -- redundant moves later. In particular a <- b, b <- c must read the old b.
  let snapshots ← xs.mapM fun (dst, src) => do
    let dst ← get_or_new_renaming' dst.name
    let src ← operand_to_loc src
    let tmp := AbsLoc.vreg ⟨← gensym ".pc"⟩
    return (Inst.mov () tmp src, Inst.mov () dst tmp)
  return snapshots.map Prod.fst ++ snapshots.map Prod.snd

local macro "bin_op% " op:ident m:ident dst:term:arg x:term:arg y:term:arg : doElem => do
  let s ← `(doElem| do
      let dst' ← get_or_new_renaming' $(dst).name
      let x' ← operand_to_loc $x
      let y' ← operand_to_loc $y
      $m:ident := $(m).push <| $(op) () dst' x' y')
  return s

def construct_block (block : SSA.BasicBlock Unit String SSA.VarName SSA.Operand) : M (MIR.BasicBlock Unit String MIR.AbsLoc) := do
  assert! block.params.isEmpty
  let mut insts : Array (MIR.Inst Unit String MIR.AbsLoc) := #[]
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
    -- | SSA.Inst.ret _ v =>
      -- let v' ← operand_to_loc v
      -- insts := insts.push <| Inst.ret () v'
    | SSA.Inst.get_arg _ dst i =>
      let dst' ← get_or_new_renaming' dst.name
      insts := insts.push <| Inst.mov () dst' (AbsLoc.arg i)
    -- | SSA.Inst.br _ cond lt' [] lf' [] =>
    --   let cond' ← operand_to_loc cond
    --   insts := insts.push <| Inst.br () cond' lt' lf'
    --   edges := edges.push (.teleport block.id lt')
    --   edges := edges.push (.teleport block.id lf')
    -- | SSA.Inst.br .. =>
    --   panic! s!"{decl_name%}: block args are not expected here"
    | .assign _ dst x =>
      let dst' ← get_or_new_renaming' dst.name
      let x' ← operand_to_loc x
      insts := insts.push <| Inst.mov () dst' x'
    -- | SSA.Inst.jmp _ target [] =>
    --   insts := insts.push <| Inst.jmp () target
    --   edges := edges.push (.teleport block.id target)
    -- | SSA.Inst.jmp .. =>
    --   panic! s!"{decl_name%}: block args are not expected here"
    | .pc _ xs =>
      let is ← resolve_pc_simple xs
      insts := insts.append is.toArray
    | .mk_tuple .. | .get_item .. | .prim1 ..
      => panic! s!"{decl_name%}: translation from SSA instruction not implemented: {i.toString}"
  let terminal : Terminal Unit String MIR.AbsLoc ←
    match block.terminal with
    | .jmp _ target _ => pure <| Terminal.jmp () target
    | .br _ cond btrue targs bfalse fargs =>
      assert! targs.isEmpty
      assert! fargs.isEmpty
      let cond' ← operand_to_loc cond
      pure <| Terminal.br () cond' btrue bfalse
    | .ret _ value =>
      let value' ← operand_to_loc value
      pure <| Terminal.ret () value'
  return { id := block.id, insts, terminal }

private def construct_core (cfg : SSA.CFG Unit String SSA.VarName SSA.Operand) : M (MIR.CFG' Unit String MIR.AbsLoc) := do
  let blocks ← cfg.blocks.mapM construct_block
  return { name := cfg.name, blocks }

def construct (cfg : SSA.CFG Unit String SSA.VarName SSA.Operand) : FreshM (MIR.CFG' Unit String MIR.AbsLoc) := do
  construct_core cfg |>.run' {}

def Inst.is_logical_op : Inst σ γ α → Bool := fun x => x matches Inst.lt .. | Inst.le .. | Inst.gt .. | Inst.ge .. | Inst.eq .. | Inst.ne ..

def split_by_logical_op? (block : BasicBlock Unit String MIR.AbsLoc) :
    Option (Array (Inst Unit String MIR.AbsLoc) × Inst Unit String MIR.AbsLoc × Array (Inst Unit String MIR.AbsLoc)) := do
  let (_, i) ← block.insts.zipIdx.find? fun (x, _) => x.is_logical_op
  let inst := block.insts[i]!
  let firstHalf := block.insts.take i
  let secondHalf := block.insts.extract (i + 1)
  return (firstHalf, inst, secondHalf)

local macro "cmp_op% " op:ident m:ident block:term:arg c:term:arg x:term:arg y:term:arg fhalf:term:arg shalf:term:arg : doElem => do
  let s ← `(doElem| do
      let side ← gensym ".side"
      let shalf_name ← gensym ".skip"
      let cmp : Inst Unit String MIR.AbsLoc := Inst.cmp () $x $y
      let mov_true : Inst Unit String MIR.AbsLoc := Inst.mov () $c (.imm const_true)
      let mov_false : Inst Unit String MIR.AbsLoc := Inst.mov () $c (.imm const_false)
      let j := $op:ident () shalf_name
      let fhalf' := { id := $(block).id, insts := $(fhalf).append #[cmp, mov_true], terminal := j : BasicBlock Unit String MIR.AbsLoc }
      let side_block : BasicBlock Unit String MIR.AbsLoc := { id := side, insts := #[ mov_false ], terminal := Terminal.jmp () shalf_name }
      let next := { id := shalf_name, insts := $(shalf), terminal := $(block).terminal : BasicBlock Unit String MIR.AbsLoc }
      $m:ident := $(m).append #[fhalf', side_block]
      pure next)
  return s

def reduce_lop (cfg : MIR.CFG Unit String MIR.AbsLoc) : FreshM (MIR.CFG Unit String MIR.AbsLoc) := do
  let mut blocks : Array (BasicBlock Unit String MIR.AbsLoc) := #[]
  for block in cfg.blocks do
    let mut block := block
    while true do
      let some (fhalf, inst, shalf) := split_by_logical_op? block
        | blocks := blocks.push block; break
      match inst with
      | .lt _ c a b => block ← cmp_op% Terminal.jl blocks block c a b fhalf shalf
      | .le _ c a b => block ← cmp_op% Terminal.jle blocks block c a b fhalf shalf
      | .gt _ c a b => block ← cmp_op% Terminal.jg blocks block c a b fhalf shalf
      | .ge _ c a b => block ← cmp_op% Terminal.jge blocks block c a b fhalf shalf
      | .eq _ c a b => block ← cmp_op% Terminal.jz blocks block c a b fhalf shalf
      | .ne _ c a b => block ← cmp_op% Terminal.jnz blocks block c a b fhalf shalf
      | _ => panic! ""
  let mut blocks' := #[]
  for b in blocks do
    let Terminal.br _ cond bt bf := b.terminal
      | blocks' := blocks'.push b; continue
    let cmp : Inst Unit String MIR.AbsLoc := Inst.cmp () cond (.imm (const_true))
    let skip ← gensym ".skip"
    let b' := { id := b.id, insts := b.insts.push cmp, terminal := Terminal.jz () bt : BasicBlock Unit String MIR.AbsLoc }
    let f' := { id := skip, insts := #[], terminal := Terminal.jmp () bf : BasicBlock Unit String MIR.AbsLoc }
    blocks' := blocks'.push b'
    blocks' := blocks'.push f'
  return { name := cfg.name, blocks := blocks' }

def to_c_call (cfg : MIR.CFG Unit String MIR.AbsLoc) : MIR.CFG Unit String MIR.AbsLoc := Id.run do
  let blocks := cfg.blocks.map fun b =>
    let insts : Array (Inst Unit String MIR.AbsLoc) := b.insts.flatMap fun inst =>
      match inst with
      | .call _ d fn args =>
        let padding := (4 - args.length % 4) % 4
        let pads := Array.replicate padding (Inst.push () (.imm 0))
        let pushes := args.toArray.reverse.map fun arg => Inst.push () arg
        let pops := Array.replicate (args.length + padding) (Inst.pop' () : Inst Unit String AbsLoc)
        pads ++ pushes ++ #[.call' () fn, .mov () d (.preg .eax)] ++ pops
      | _ => #[inst]
    { id := b.id, insts, terminal := b.terminal : BasicBlock Unit String MIR.AbsLoc }
  return { name := cfg.name, blocks := blocks }

private def genvreg [Monad m] [MonadNameGen m] (name : String) : m MIR.AbsLoc := (MIR.AbsLoc.vreg ∘ VReg.mk) <$> gensym name

def form (cfg : MIR.CFG Unit String MIR.AbsLoc) : FreshM (MIR.CFG Unit String MIR.AbsLoc) := do
  let binary := fun (ctor : Unit → AbsLoc → AbsLoc → AbsLoc → Inst Unit String AbsLoc)
      (d x y : AbsLoc) => do
    if d == x then return #[ctor () d d y]
    -- A destination that aliases the RHS must not destroy it with the first MOV.
    let (save, y) ← if d == y then do
      let tmp ← genvreg ".twoaddr"
      pure (#[Inst.mov () tmp y], tmp)
    else pure (#[], y)
    return save ++ #[Inst.mov () d x, ctor () d d y]
  let blocks ← cfg.blocks.mapM fun b => do
    let insts : Array (Inst Unit String MIR.AbsLoc) ← b.insts.flatMapM fun inst => do
      match inst with
      | .add _ d x y => binary Inst.add d x y
      | .sub _ d x y => binary Inst.sub d x y
      | .band _ d x y => binary Inst.band d x y
      | .bor _ d x y => binary Inst.bor d x y
      | .xor _ d x y => binary Inst.xor d x y
      | .mul _ d x y => binary Inst.mul d x y
      | .shl _ d x y => binary Inst.shl d x y
      | .shr _ d x y => binary Inst.shr d x y
      | .sar _ d x y => binary Inst.sar d x y
      | .cmp _ x y =>
        if (x matches .vreg ..) then return #[inst]
        let c ← genvreg "c"
        return #[Inst.mov () c x, .cmp () c y]
      | .test _ x y =>
        if (x matches .vreg ..) then return #[inst]
        let c ← genvreg "c"
        return #[Inst.mov () c x, .test () c y]
      | _ => return #[inst]
    return { id := b.id, insts, terminal := b.terminal : BasicBlock Unit String MIR.AbsLoc }
  return { name := cfg.name, blocks := blocks }
