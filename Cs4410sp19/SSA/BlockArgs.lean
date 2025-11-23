import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

-- TODO: reimplement in a monadic context for clarity
def eliminate_block_args [Monad m] [MonadNameGen m] (cfg : CFG' Unit String VarName Operand) : m (CFG' Unit String VarName Operand) := do
  assert! !cfg.blocks.isEmpty
  let succ := cfg.config.successors
  let pred := cfg.config.predecessors
  let mut blocks' := #[] -- reversed
  -- the future patches to apply for the predecessor blocks
  -- `P → (Original → (Split ⊕ ParallelCopy))`
  let mut patches : Std.HashMap String (List (Nat × String × (String ⊕ Inst Unit String VarName Operand))) := {}
  for B in cfg.blocks.reverse do
    let applyPatch (p : BasicBlock Unit String VarName Operand) : BasicBlock Unit String VarName Operand := Id.run do
      assert! !p.insts.isEmpty
      let some brs := patches[p.id]? | return p
      if brs.isEmpty then
        return p
      let mut last := p.back!
      for (i, o, s) in brs do
        match s with
        | .inl s => -- iteratively erase the args
          last := last.set_branching! o s i []
        | .inr i' => -- insert `pc` before the outgoing `jmp`, and erase the args
          assert! brs.length == 1
          assert! last matches .jmp ..
          let insts' := p.insts.insertIdx! (p.insts.size - 1) i'
          let insts' := insts'.modify (insts'.size - 1) fun x => x.set_branching! o o i []
          return { id := p.id, params := p.params, insts := insts' }
      return { id := p.id, params := p.params, insts := p.insts.set! (p.insts.size - 1) last }
    --
    let B := applyPatch B
    if B.params.isEmpty then
      blocks' := blocks'.push B
      continue
    if pred[B.id]?.isNone || pred[B.id]!.size == 0 then
      blocks' := blocks'.push B
      continue
    let vs ← B.params.mapM fun n => genvar s!"{B.id}.{n.name}"
    assert! B.params.length == vs.length
    let subst (i : Inst Unit String VarName Operand) := i.instantiate_params (B.params.zipWith (fun p v => (p, .var v)) vs)
    let B'_insts := B.insts.map subst
    let B' : BasicBlock Unit String VarName Operand := { id := B.id, params := [], insts := B'_insts }
    blocks' := blocks'.push B'
    for (P_id, i) in pred[B.id]!.reverse do
      patches := patches.alter P_id fun
        | none => some {}
        | some x => some x
      if succ[P_id]?.isNone || succ[P_id]!.size == 0 then
        break
      else
        let P := cfg.get! P_id
        assert! !P.insts.isEmpty
        let P_last := P.back!
        let passed := P_last.get_branching_args! B.id i
        assert! passed.length == vs.length
        let pc := Inst.pc () (vs.zip passed)
        if succ[P_id]!.size == 1 then
          assert! P_last matches .jmp ..
          patches := patches.modify P_id (List.insert (i, B.id, .inr pc))
        else
          let splitName ← gensym s!".split_{P_id}_{B.id}_{i}"
          let P_B' : BasicBlock Unit String VarName Operand := { id := splitName, params := [], insts := #[ pc, .jmp () B.id [] ] }
          blocks' := blocks'.push P_B'
          patches := patches.modify P_id (List.insert (i, B.id, .inl splitName))
  let entry := blocks'.back!
  let einsts := entry.insts.map fun
    | x@(.assign _ n (.param pname)) =>
      let idx? := entry.params.idxOf? pname
      if let some idx := idx? then
        Inst.get_arg () n idx
      else
        x
    | x => x
  let entry' := { entry with params := [], insts := einsts }
  blocks' := blocks'.set! (blocks'.size - 1) entry'
  return { name := cfg.name, blocks := blocks'.reverse }
