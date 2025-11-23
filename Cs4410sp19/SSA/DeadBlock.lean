import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

def eliminate_dead_blocks [Hashable γ] [BEq γ] (cfg : CFG' σ γ δ α) : CFG' σ γ δ α := runST fun σ' => do
  if h : cfg.blocks.size = 0 then
    return cfg
  else
    let ts ← ST.mkRef (σ := σ') (α := Std.HashSet γ) {}
    let visited x := do
      return (← ts.get).contains x
    let xs ← ST.mkRef (σ := σ') (α := Array γ) #[cfg.blocks[0].id]
    let succ := cfg.config.successors
    while True do
      let mut xs' := #[]
      let r ← xs.get
      for x in r do
        ts.modify (Std.HashSet.insert · x)
        for s in succ[x]? do
          for (a, i) in s do
            if !(← visited a) then -- not visited
              xs' := xs'.push a
      if xs'.isEmpty then
        break
      else
        xs.set xs'
    let blocks ← cfg.blocks.filterMapM fun b => do
      if (← visited b.id) then
        return some b
      else return none
    return { name := cfg.name, blocks }
