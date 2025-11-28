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
  -- dbg_trace "converted:"
  -- dbg_trace "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.reduce_assign r
  -- dbg_trace "unary assignment reduced:"
  -- dbg_trace "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.eliminate_trivial_blocks r
  -- dbg_trace "trivial blocks reduced:"
  -- dbg_trace "{SSA.pp_cfg' r.toCFG}\n"

  let (r, _) := FreshM.run (SSA.eliminate_block_args r) s
  -- dbg_trace "block args eliminated:"
  -- dbg_trace "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.construct r.toCFG |>.run' {}) {}
  -- dbg_trace "MIR constructed:"
  -- dbg_trace "{MIR.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.reduce_lop r.toCFG) s
  -- dbg_trace "logical operators reduced:"
  -- dbg_trace "{MIR.pp_cfg' r}\n"

  let r := MIR.to_c_call r
  -- dbg_trace "call unfolded:"
  -- dbg_trace "{MIR.pp_cfg' r}\n"

  let (r, s) := FreshM.run (MIR.form r) s
  dbg_trace "two address formation:"
  dbg_trace "{MIR.pp_cfg' r}\n"

  let r := MIR.compute_mdata r
  -- dbg_trace "mdata:"
  -- dbg_trace "{MIR.pp_cfg r}\n"

  let intervals := MIR.build_live_intervals {r with}

  let r := MIR.linear_scan_register_allocation {r with} intervals

  dbg_trace "\nregister allocated:"
  dbg_trace "{MIR.pp_cfg' r.unsetTag.toCFG}\n"

  let asm := MIR.assemble r.toCFG.unsetTag
  -- dbg_trace "{Assembler.asm_to_string asm}"

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
