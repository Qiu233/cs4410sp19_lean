import Cs4410sp19.Basic
import Cs4410sp19.Parser
import Cs4410sp19.Compile.Basic
import Cs4410sp19.Compile.ANF
import Cs4410sp19.Compile.Tych

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

def externs : List String := ["error", "print"]

def helpers : List String := [error_non_number, error_non_bool]

def compile_prog (prog : Program (Location × Option (Typ String.Pos))) : Except String String := do
  let init_env : Env := { function_names := #["print"] }
  let (decls, exe) ← (do
    Tych.type_check_prog prog
    let prog' ← anf_prog prog
    compile_anfed_prog_core prog') |>.run' init_env
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
{main}"
