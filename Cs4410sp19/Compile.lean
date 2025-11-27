import Cs4410sp19.Basic
import Cs4410sp19.Parser
import Cs4410sp19.Compile.Basic
import Cs4410sp19.ANF
import Cs4410sp19.Tych
import Cs4410sp19.SSA
import Cs4410sp19.MIR

namespace Cs4410sp19

def error_non_number := "
error_non_number:
  push eax
  push 1
  call error
  add esp, 4 * 2
"

def error_non_bool := "
error_non_bool:
  push eax
  push 2
  call error
  add esp, 4 * 2
"

def error_non_tuple := "
error_non_tuple:
  push eax
  push 3
  call error
  add esp, 4 * 2
"

private def externs : List String := ["error", "error_tuple_size_mismatch", "print",]

private def helpers : List String := [error_non_number, error_non_bool, error_non_tuple]



private def compile_decl (f : Decl (Location × Option (Typ String.Pos))) : Except String String := do
  let s := ContT.run (m := SSA.M) (do
    let a ← anf_decl f
    let t := (match a with | ADecl.function _ f => f)
    let r ← liftM <| SSA.cfg_of_function_def t
    let r : SSA.CFG' Unit String SSA.VarName SSA.Operand := { r with }
    return r
    ) (fun n => pure n) |>.run {} |>.run' {}
  let (r, s) := s.run {}
  -- println! "converted:"
  -- println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.reduce_assign r
  -- println! "unary assignment reduced:"
  -- println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.eliminate_trivial_blocks r
  -- println! "trivial blocks reduced:"
  -- println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, _) := FreshM.run (SSA.eliminate_block_args r) s
  -- println! "block args eliminated:"
  -- println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.construct r.toCFG |>.run' {}) {}
  -- println! "MIR constructed:"
  -- println! "{MIR.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.reduce_lop r.toCFG) s
  -- println! "logical operators reduced:"
  -- println! "{MIR.pp_cfg' r}\n"

  let r := MIR.to_c_call r
  -- println! "call unfolded:"
  -- println! "{MIR.pp_cfg' r}\n"

  let (r, s) := FreshM.run (MIR.form r) s
  -- println! "two address formation:"
  -- println! "{MIR.pp_cfg' r}\n"

  let r := MIR.compute_mdata r
  -- println! "mdata:"
  -- println! "{MIR.pp_cfg r}\n"

  -- let ds := defs_in {r with}
  -- println! "{ds (.vreg ⟨"x.8"⟩) ".join.2"}"

  -- println! "{live_in {r with } (.vreg ⟨"x.8"⟩) ".join.2"}"
  -- println! "{defs_out {r with } (.greg .eax) ".join.2"}"

  -- let t := liveness_of_def {r with} (.greg .eax) 95
  -- println! "{t}"
  let intervals := MIR.build_live_intervals {r with}

  -- let itvs := intervals.toList.mergeSort fun x y => x.fst.def_pos < y.fst.def_pos
  -- println! "intervals (sorted by def_pos):"
  -- for (i, t) in itvs do
  --   println! "{i.d}, {i.def_pos}: {t}"

  let r := MIR.linear_scan_register_allocation {r with} intervals

  -- println! "\nregister allocated:"
  -- println! "{MIR.pp_cfg' r.unsetTag.toCFG}\n"

  let asm := MIR.assemble r.toCFG.unsetTag
  -- println! "{Assembler.asm_to_string asm}"

  return Assembler.asm_to_string asm

private def compile_prog_core (prog : Program (Location × Option (Typ String.Pos))) (builtin : Std.HashMap String TypeScheme) : Except String String := do
  let _prog_type ← Tych.type_check_prog prog builtin
  let mut store := #[]
  for md in prog.decls do
    for d in md.decls do
      let code ← compile_decl d
      store := store.push s!"{d.name}:"
      store := store.push code
  let main : Decl (Location × Option (Typ String.Pos)) := .function (Location.mk 0 0, none) { name := "", params := [], body := prog.exe_code, ret_type? := none }
  let mainCode ← compile_decl main
  return s!"section .text
global our_code_starts_here
\n
{String.intercalate "\n" (externs.map (s!"extern {·}"))}
{String.intercalate "\n" helpers}
\n
{String.intercalate "\n" store.toList}
\n
our_code_starts_here:
  mov esi, dword [esp + 4]
  add ESI, 7
  and ESI, 0xfffffff8\n
{mainCode}
"

def compile_prog (prog : Program (Location × Option (Typ String.Pos))) : Except String String :=
  compile_prog_core prog ({ ("print", TypeScheme.mk ["T"] (Typ.arrow [(Typ.var () "T")] (Typ.var () "T"))) })

-- private def compile_prog_core (prog : Program (Location × Option (Typ String.Pos))) (builtin : Std.HashMap String TypeScheme) : Except String String := do
--   let _prog_type ← Tych.type_check_prog prog builtin
--   let init_env : Env := { functions := Std.HashSet.ofList builtin.keys }
--   let (decls, exe) ← (do
--     let prog' ← anf_prog prog
--     compile_anfed_prog_core prog') |>.run' init_env |>.run' {} -- run in the initial environment
--   let ds := decls.map fun (d, is) =>
--     s!"{d}:\n{asm_to_string is}\n"
--   let ds := String.intercalate "\n" ds.toList
--   let main := asm_to_string exe
--   return s!"section .text
-- {String.intercalate "\n" (externs.map (s!"extern {·}"))}
-- {String.intercalate "\n" helpers}
-- {ds}
-- global our_code_starts_here
-- our_code_starts_here:
--   mov esi, dword [esp + 4]
--   add ESI, 7
--   and ESI, 0xfffffff8
-- {main}"

-- def compile_prog (prog : Program (Location × Option (Typ String.Pos))) : Except String String :=
--   compile_prog_core prog ({ ("print", TypeScheme.mk ["T"] (Typ.arrow [(Typ.var () "T")] (Typ.var () "T"))) })
