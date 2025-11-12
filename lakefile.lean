import Lake
open Lake DSL

package "cs4410sp19" where
  version := v!"0.1.0"

lean_lib «Cs4410sp19» where
  -- add library configuration options here

@[default_target]
lean_exe "cs4410sp19" where
  root := `Main

@[default_script]
script «.» args do
  let name := args[0]?.getD "main"
  let src_file : System.FilePath := "ws" / s!"{name}.int"
  unless (← src_file.pathExists) && (← not <$> src_file.isDir) do
    throw <| IO.Error.userError s!"file {src_file} does not exist"
    return -1
  let asm_file : System.FilePath := "ws" / s!"{name}.s"
  let obj_file : System.FilePath := "ws" / s!"{name}.o"
  let run_file : System.FilePath := "ws" / s!"{name}.run"
  let a ← exe `cs4410sp19 #[src_file.toString, "-o", asm_file.toString]
  unless a == 0 do
    throw <| IO.Error.userError s!"failed to compile {src_file}"
    return a
  let b ← IO.Process.run { cmd := "nasm", args := #[ "-f", "elf32", "-o", obj_file.toString, asm_file.toString ] }
  IO.print s!"{b}"
  let b ← IO.Process.run { cmd := "clang", args := #[ "-m32", "-o", run_file.toString, "wrapper/main.c", obj_file.toString ] }
  IO.print s!"{b}"
  let b ← IO.Process.run { cmd := run_file.toString }
  IO.print s!"{b}"
  return 0
