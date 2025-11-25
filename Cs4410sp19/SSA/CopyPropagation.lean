import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

def reduce_assign [Hashable γ] [BEq γ] : CFG' σ γ VarName Operand → CFG' σ γ VarName Operand := fun cfg => runST fun σ' => do
  let substs ← ST.mkRef (σ := σ') (α := Std.HashMap VarName Operand) {} -- TODO: use functional data structure
  for node in cfg.blocks do
    for i in node.insts do
      match i with
      | .assign _ x y =>
        match y with
        | .param .. => pure ()
        | _ => substs.modify fun s => s.insert x y
      | _ => pure ()
  while true do
    let mut flag := false
    let s ← substs.get
    for (p, q) in s do
      let Operand.var q := q | continue
      let some q' := s[q]? | continue
      substs.modify fun s => s.insert p q'
      flag := true
      break
    if !flag then
      break
  let substs ← substs.get
  let substs' := substs.toArray
  let blocks : Array (BasicBlock σ γ VarName Operand) := cfg.blocks.map fun b => Id.run do
    let is := b.insts.filterMap fun x => Id.run do
      let _ ← match x with
        | .assign _ n _ => if substs.contains n then return none else pure ()
        | _ => pure ()
      let mut x := x
      for (p, q) in substs' do
        x := x.replace_src_by (Operand.var p) q
      return some x
    return { b with insts := is, terminal := b.terminal }
  return { name := cfg.name, blocks }
