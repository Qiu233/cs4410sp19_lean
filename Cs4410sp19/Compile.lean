import Cs4410sp19.Basic
import Cs4410sp19.Parser
import Cs4410sp19.Compile.Basic
import Cs4410sp19.ANF
import Cs4410sp19.Tych

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

private def compile_prog_core (prog : Program (Location × Option (Typ String.Pos))) (builtin : Std.HashMap String TypeScheme) : Except String String := do
  let _prog_type ← Tych.type_check_prog prog builtin
  let init_env : Env := { functions := Std.HashSet.ofList builtin.keys }
  let (decls, exe) ← (do
    let prog' ← anf_prog prog
    compile_anfed_prog_core prog') |>.run' init_env -- run in the initial environment
  let ds := decls.map fun (d, is) =>
    s!"{d}:\n{asm_to_string is}\n"
  let ds := String.intercalate "\n" ds.toList
  let main := asm_to_string exe
  return s!"section .text
{String.intercalate "\n" (externs.map (s!"extern {·}"))}
{String.intercalate "\n" helpers}
{ds}
global our_code_starts_here
our_code_starts_here:
  mov esi, dword [esp + 4]
  add ESI, 7
  and ESI, 0xfffffff8
{main}"

def compile_prog (prog : Program (Location × Option (Typ String.Pos))) : Except String String :=
  compile_prog_core prog ({ ("print", TypeScheme.mk ["T"] (Typ.arrow [(Typ.var () "T")] (Typ.var () "T"))) })
