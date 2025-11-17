import Std
import Cs4410sp19

open Cs4410sp19

def _root_.main (args : List String) : IO Unit := do
  let some input_file := args[0]? |
    IO.println "no input file"
    IO.Process.exit 255
  let outIdx? := args.findIdx? (· == "-o")
  let out? := outIdx? >>= fun x => args[x + 1]?
  let input_program ← IO.FS.readFile ⟨input_file⟩
  let prog ← match run_parse_prog input_program with
    | .ok expr => pure expr
    | .error e =>
      IO.println s!"parse failed due to error: {e}"
      IO.Process.exit 255
  let program ← match compile_prog prog with
    | .ok p => pure p
    | .error e =>
      IO.println s!"compilation failed due to error: {e}"
      IO.Process.exit 255
  match out? with
  | .some out => IO.FS.writeFile out program
  | .none => println! "{program}"
