import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

private inductive PatchVariant where
  | split (block : String)
  | pc (inst : Inst Unit String VarName Operand)
deriving Inhabited, Repr, BEq

private structure Patch where
  edgeIdx : Nat
  target : String
  variant : PatchVariant
deriving Inhabited, Repr, BEq

private abbrev PatchList := List Patch
private abbrev PatchMap := Std.HashMap String PatchList

private def add_empty_if_missing (pm : PatchMap) (k : String) : PatchMap :=
  pm.alter k fun
    | none => some []
    | some xs => some xs

private def push_patch (pm : PatchMap) (k : String) (p : Patch) : PatchMap :=
  pm.alter k fun
    | none => some [p]
    | some xs => some (p :: xs)

/- Apply pending patches (if any) to a basic block. This is pure and does not modify the
   patch map; it just inspects it and returns the updated block. -/
def apply_patch_to_block (patches : PatchMap) (p : BasicBlock Unit String VarName Operand) : BasicBlock Unit String VarName Operand :=
  match patches[p.id]? with
  | none => p
  | some brs =>
    if brs.isEmpty then p
    else Id.run do
      let mut term := p.terminal
      for ⟨i, o, s⟩ in brs do
        match s with
        | .split s => -- iteratively erase the args (update terminal)
          term := term.set_branching! o s i []
        | .pc i' => -- insert `pc` (append) and erase the args in the terminal
          assert! brs.length == 1
          let insts' := p.insts.push i'
          let term' := term.set_branching! o o i []
          return { id := p.id, params := p.params, insts := insts', terminal := term' }
      return { id := p.id, params := p.params, insts := p.insts, terminal := term }

def eliminate_block_args [Monad m] [MonadNameGen m] (cfg : CFG' Unit String VarName Operand) : m (CFG' Unit String VarName Operand) := do
  assert! !cfg.blocks.isEmpty
  let succ := cfg.config.successors
  let pred := cfg.config.predecessors
  let mut blocks_rev := #[] -- reversed
  -- the future patches to apply for the predecessor blocks
  -- `P → (Original → (Split ⊕ ParallelCopy))`
  let mut patches : PatchMap := {}
  for B in cfg.blocks.reverse do
    let B := apply_patch_to_block patches B
    if B.params.isEmpty then
      blocks_rev := blocks_rev.push B
      continue
    if pred[B.id]?.isNone || pred[B.id]!.length == 0 then
      blocks_rev := blocks_rev.push B
      continue
    let vs ← B.params.mapM fun n => genvar s!"{B.id}.{n.name}"
    assert! B.params.length == vs.length
    let substPairs := (B.params.zipWith (fun p v => (p, .var v)) vs)
    let subst (i : Inst Unit String VarName Operand) := i.instantiate_params substPairs
    let B'_insts := B.insts.map subst
    let B' : BasicBlock Unit String VarName Operand := { id := B.id, params := [], insts := B'_insts, terminal := B.terminal.instantiate_params substPairs }
    blocks_rev := blocks_rev.push B'
    for ⟨i, P_id, _, _⟩ in pred[B.id]!.reverse do
      patches := patches.alter P_id fun
        | none => some {}
        | some x => some x
      if succ[P_id]?.isNone || succ[P_id]!.length == 0 then
        break
      else
        let P := cfg.get! P_id
        let passed := P.terminal.get_branching_args! B.id i
        assert! passed.length == vs.length
        let pc := Inst.pc () (vs.zip passed)
        if succ[P_id]!.length == 1 then
          match P.terminal with
          | .jmp _ _ _ => patches := patches.modify P_id (List.insert ⟨i, B.id, PatchVariant.pc pc⟩)
          | _ => panic! "expected unconditional jump"
        else
          let splitName ← gensym s!".split_{P_id}_{B.id}_{i}"
          let P_B' : BasicBlock Unit String VarName Operand := { id := splitName, params := [], insts := #[ pc ], terminal := .jmp () B.id [] }
          blocks_rev := blocks_rev.push P_B'
          patches := patches.modify P_id (List.insert ⟨i, B.id, PatchVariant.split splitName⟩)
  let entry := blocks_rev.back!
  let einsts := entry.insts.map fun
    | x@(.assign _ n (.param pname)) =>
      let idx? := entry.params.idxOf? pname
      if let some idx := idx? then
        Inst.get_arg () n idx
      else
        x
    | x => x
  let entry' := { entry with params := [], insts := einsts, terminal := entry.terminal }
  blocks_rev := blocks_rev.set! (blocks_rev.size - 1) entry'
  return { name := cfg.name, blocks := blocks_rev.reverse }
