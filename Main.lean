import Cs4410sp19

def compile (program : Int) : String :=
s!"section .text
global our_code_starts_here
our_code_starts_here:
  mov eax, {program}
  ret\n"

def main (args : List String) : IO Unit := do
  let some input_file := args[0]? | throw (IO.Error.userError "??")
  let input_program ← String.toInt! <$> IO.FS.readFile ⟨input_file⟩
  let program := compile input_program
  println! "{program}"
