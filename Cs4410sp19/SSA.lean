import Cs4410sp19.SSA.Basic
import Cs4410sp19.SSA.Construct
import Cs4410sp19.SSA.DeadBlock
import Cs4410sp19.SSA.TrivialBlock
import Cs4410sp19.SSA.BlockArgs
-- import Cs4410sp19.SSA.RegAlloc

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
    return { b with insts := is }
  return { name := cfg.name, blocks }


def pp_insts [ToString σ] [ToString γ] [ToString δ] [ToString α] (insts : List (Inst σ γ δ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"
def pp_insts' [ToString γ] [ToString δ] [ToString α] (insts : List (Inst Unit γ δ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"

def pp_cfg [ToString σ] [ToString γ] [ToString δ] [ToString α] (cfg : CFG σ γ δ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    if i.params.isEmpty then
      store := store.push s!"{i.id}:"
    else
      store := store.push s!"{i.id}({String.intercalate ", " (i.params.map toString)}):"
    store := store.push s!"{pp_insts i.insts.toList}"
  return String.intercalate "\n" store.toList

def pp_cfg' [ToString γ] [ToString δ] [ToString α] (cfg : CFG Unit γ δ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    if i.params.isEmpty then
      store := store.push s!"{i.id}:"
    else
      store := store.push s!"{i.id}(${String.intercalate ", " (i.params.map toString)}):"
    store := store.push s!"{pp_insts' i.insts.toList}"
  return String.intercalate "\n" store.toList

-- #exit

-- def src := "f((let x = 2 in if x == 2: x + 5 else: x + 6), 1, 3)"

def src := "def f(x, y):
  let t = 7 in
  let x = 5 in
  (if x == 0: 0 else: if x == 1: 1 + 4 else: 2) + (if y == 1: 2 else: 3) + x + t
"

-- def src := "def f(x, y):
--   (if x == 0: 0 else: if x == 1: 1 + 4 else: 2) + 2 + x + 1
-- "

-- open RegAlloc in

#eval do
  let e ← match (parse_function_decl <* Std.Internal.Parsec.String.ws <* Std.Internal.Parsec.eof).run src with
    | .error e => println! s!"failed to parse expression due to: {e}"; return
    | .ok r => pure r
  let s := ContT.run (m := M) (do
    let a ← anf_decl e.decls[0]!
    let t := (match a with | ADecl.function _ f => f)
    let r ← liftM <| cfg_of_function_def t
    let r : CFG' Unit String VarName Operand := { r with }
    return r
    ) (fun n => pure n) |>.run {} |>.run' {}
  let (r, s) := s.run {}
  println! "converted:"
  println! "{pp_cfg' r.toCFG}\n"

  let r := reduce_assign r
  println! "unary assignment reduced:"
  println! "{pp_cfg' r.toCFG}\n"

  let r := eliminate_trivial_blocks r
  println! "trivial blocks reduced:"
  println! "{pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (eliminate_block_args r) s
  println! "block args eliminated:"
  println! "{pp_cfg' r.toCFG}\n"
  -- let es := edges r
  -- println! "edges = {es}"
  -- let r : CFG' Unit String VarName VarName := { r with }
  -- let r :=
  -- let r := annotate_lineno r
  -- println! "{pp_cfg r.toCFG}\n"
  -- -- println! "{r.config.predecessors.toArray}"

  -- let lifetime := build_intervals r
  -- let assignment := linear_scan lifetime 4
  -- -- println! "{lifetime.toArray}"
  -- -- for (n, l) in lifetime do
  -- --   println! "{n}:\t{l}"
  -- -- println! ""

  -- let r := RegAlloc.allocate_registers r
  -- println! "registers allocated:"
  -- println! "{pp_cfg r.toCFG}\n"
