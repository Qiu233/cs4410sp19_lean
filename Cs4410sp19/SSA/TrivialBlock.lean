import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

/-!
Definition:
  A **trivial basic block** is a basic block where there is only a single unconditional jump instruction.
  A trivial block may have parameters.
-/

/-- A triple of basic blocks `P → T → B` where `T` is trivial. -/
private structure Triple where
  /-- The predecessor block, which can have multiple outgoing edges. -/
  P : String
  /-- The edge index of `P → T`. -/
  edge : Nat
  /-- The trivial block, consisting of a single unconditional jump instruction. -/
  T : String
  /-- The target block. -/
  B : String
  /-- Block parameter names of `T`. -/
  params : List VarName
  /-- The unique instruction of `T`.
  We track this instruction, so we can iteratively reduce triples by existing triples.
  -/
  jmp : Inst Unit String VarName Operand
deriving Inhabited, Repr

private def Triple.composite (c : Triple) (next : Triple) : Triple := Id.run do
  -- Combine the triples when `c.P → c.T → next.T → next.B` where `c.T` and `next.T` are trivial blocks.
  -- By definition, `c.T` and `next.T` both have only one unconditional jump instruction, inducing a compact
  -- triple `c.P → T' → next.B` where `T'` is a **virtual** block with the same name and parameters of `c.T`,
  -- but with the instruction `next.jmp[next.params ← c.jmp.branching_args[0]]`
  assert! c.B == next.T
  assert! c.T == next.P
  let args := c.jmp.get_branching_args! next.T 0 -- `c.jmp.branching_args[0]`
  assert! next.params.length == args.length
  let T'_jmp := next.jmp.instantiate_params (next.params.zip args)
  return { P := c.P, edge := c.edge, T := c.T, B := next.B, params := c.params, jmp := T'_jmp }

private def Triple.apply (p : BasicBlock Unit String VarName Operand) (t : Triple) : BasicBlock Unit String VarName Operand := Id.run do
  assert! p.id == t.P
  assert! !p.insts.isEmpty
  let p_to_t := p.back!
  let args := p_to_t.get_branching_args! t.T t.edge
  assert! args.length == t.params.length
  let jmp := t.jmp.instantiate_params (t.params.zip args)
  let args' := jmp.get_branching_args! t.B 0
  let p_to_b := p_to_t.set_branching! t.T t.B t.edge args'
  let p' := { p with insts := p.insts.set! (p.insts.size - 1) p_to_b }
  return p'

def eliminate_trivial_blocks (cfg : CFG' Unit String VarName Operand) : CFG' Unit String VarName Operand := Id.run do
  let mut triples : Std.HashMap String (Array Triple) := {} -- `P → (P, T, B)`
  let mut trivial : Std.HashSet String := {}
  for t in cfg.blocks.reverse do
    let some (target, inst) := is_trivial? t | continue
    let ps := pred[t.id]?.getD {}
    if ps.isEmpty then continue
    trivial := trivial.insert t.id
    for (p, edge) in ps do
      let mut trip : Triple := { P := p, edge := edge, T := t.id, B := target, params := t.params, jmp := inst }
      let mut id' := trip.T
      while triples.contains id' do -- loop invariant: `trip' : id' → T → _` for some trivial `T`
        let trip' := triples[id']![0]! -- can have only one descendant
        trip := trip.composite trip'
        id' := trip'.T
      triples := triples.alter p fun
        | none => some #[trip]
        | some x => some (x.push trip)
  if trivial.isEmpty then
    return cfg
  let mut blocks : Array (BasicBlock Unit String VarName Operand) := #[]
  for p in cfg.blocks do
    if trivial.contains p.id then
      continue
    let ts := triples[p.id]?.getD {}
    if ts.isEmpty then
      blocks := blocks.push p
      continue
    let p' := ts.foldl (init := p) Triple.apply
    blocks := blocks.push p'
  return { name := cfg.name, blocks := blocks }
  where
    succ := cfg.config.successors
    pred := cfg.config.predecessors
    is_trivial? (t : BasicBlock Unit String VarName Operand) : Option (String × Inst Unit String VarName Operand) := Id.run do
      assert! !t.insts.isEmpty
      if t.insts.size > 1 then return none
      let ss := succ[t.id]?.getD {}
      assert! ss.size == 1 -- the unconditional jump can only have a single target
      let inst := t.head! -- the single instruction
      let (target, _) ← match inst with
        | .jmp _ target args => pure (target, args)
        | _ => return none
      let (b, i) := ss[0]!
      assert! b == target
      assert! i == 0
      return some (target, inst)
