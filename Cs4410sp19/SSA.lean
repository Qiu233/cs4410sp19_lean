import Cs4410sp19.SSA.Basic
import Cs4410sp19.SSA.Construct
import Cs4410sp19.SSA.DeadBlock
import Cs4410sp19.SSA.TrivialBlock
import Cs4410sp19.SSA.BlockArgs
import Cs4410sp19.SSA.CopyPropagation

namespace Cs4410sp19
namespace SSA

def normalize_vars [Monad m] [MonadNameGen m] (vpref : String) (ppref : String) : CFG' σ String VarName Operand → m (CFG' σ String VarName Operand) :=
  fun cfg => StateT.run' (σ := Std.HashMap String String) (s := {}) do
    let get_or_new (n : String) := do
      let rn ← get
      if let some r := rn[n]? then
        return r
      else
        let new ← gensym vpref
        modify fun rn => rn.insert n new
        return new
    let get_or_new_param (bName : String) (n : String) := do
      let n := s!"{bName}.{n}"
      let rn ← get
      if let some r := rn[n]? then
        return r
      else
        let new ← gensym ppref
        modify fun rn => rn.insert n new
        return new
    let get_param! (bName : String) (n : String) := do
      let n := s!"{bName}.{n}"
      let rn ← get
      if let some r := rn[n]? then
        return r
      else
        unreachable!
    let blocks ← cfg.blocks.mapM fun b => do
      let insts ← b.insts.mapM fun inst =>
        inst.mapM_dst fun v =>
          VarName.mk <$> get_or_new v.name
      return { b with insts }
    let blocks ← blocks.mapM fun b => do
      let insts ← b.insts.mapM fun inst => do
        inst.mapM_src fun
          | Operand.var v => do
            let r ← get_or_new v.name
            return Operand.var ⟨r⟩
          | op => return op
      return { b with insts }
    let blocks ← blocks.mapM fun b => do
      let params ← b.params.mapM fun p => do
        let r ← get_or_new_param b.id p.name
        return VarName.mk r
      let insts ← b.insts.mapM fun inst => do
        inst.mapM_src fun
          | Operand.param v => do
            let r ← get_param! b.id v.name
            return Operand.param ⟨r⟩
          | op => return op
      return { b with params, insts }
    return { name := cfg.name, blocks }

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
  let (r, _) := s.run {}
  println! "converted:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := reduce_assign r
  println! "unary assignment reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := eliminate_trivial_blocks r
  println! "trivial blocks reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (normalize_vars "x" "a" r) {}
  println! "variables normalized:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (eliminate_block_args r) s
  println! "block args eliminated:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

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
