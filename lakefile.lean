import Lake
open Lake DSL
open System

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
    throw <| IO.userError s!"file {src_file} does not exist"
    return -1
  let asm_file : System.FilePath := "ws" / s!"{name}.s"
  let obj_file : System.FilePath := "ws" / s!"{name}.o"
  let run_file : System.FilePath := "ws" / s!"{name}.run"
  let a ← exe `cs4410sp19 #[src_file.toString, "-o", asm_file.toString]
  unless a == 0 do
    throw <| IO.userError s!"failed to compile {src_file}"
    return a
  let b ← IO.Process.run { cmd := "nasm", args := #[ "-f", "elf32", "-o", obj_file.toString, asm_file.toString ] }
  IO.print s!"{b}"
  let b ← IO.Process.run { cmd := "clang", args := #[ "-m32", "-o", run_file.toString, "wrapper/main.c", obj_file.toString ] }
  IO.print s!"{b}"
  let b ← IO.Process.run { cmd := run_file.toString }
  IO.println s!"{b}"
  return 0

open Lean in
def test_file (src_file : FilePath) : ScriptM Unit := do
  unless src_file.extension.isEqSome "int" do
    return
  let asm_file := src_file.withExtension "s"
  let obj_file := src_file.withExtension "o"
  let run_file := src_file.withExtension "run"
  let out := src_file.withExtension "out"
  unless (← out.pathExists) do
    throw <| IO.userError s!"file \"{src_file}\" has no corresponding .out file, ignored"
  if (← out.isDir) then
    throw <| IO.userError s!"path \"{out}\" is a directory, ignored"
  let expected ← IO.FS.readFile out
  let a ← exe `cs4410sp19 #[src_file.toString, "-o", asm_file.toString]
  unless a == 0 do
    throw <| IO.userError s!"failed to compile {src_file}"
  let b ← IO.Process.output { cmd := "nasm", args := #[ "-f", "elf32", "-o", obj_file.toString, asm_file.toString ] }
  unless b.exitCode = 0 do
    throw <| IO.userError s!"failed to assemble the assembly source file \"{asm_file}\" due to error: {b.stderr}"
  let b ← IO.Process.output { cmd := "clang", args := #[ "-m32", "-o", run_file.toString, "wrapper/main.c", obj_file.toString ] }
  unless b.exitCode = 0 do
    throw <| IO.userError s!"failed to link the object file \"{obj_file}\" due to error: {b.stderr}"
  let b ← IO.Process.run { cmd := run_file.toString }
  if b ≠ expected then
    throw <| IO.userError s!"[{src_file}] failed: expected {expected}, but got {b}"
  else
    println! s!"[{src_file}] succeeded: {b}"

partial def traverse [Monad m] [MonadLiftT IO m] (dir : FilePath) (x : FilePath → m Unit) : m Unit := do
  let es ← dir.readDir
  let es := List.mergeSort es.toList (fun x y => x.fileName ≤ y.fileName)
  for e in es do
    let p := e.path
    let isDir ← p.isDir.toIO
    if isDir then
      traverse p x
    else
      x p

@[test_driver]
script test args do
  let root : FilePath := "./tests"
  let path := args.foldl (init := root) (· / ·)
  unless ← path.pathExists do
    throw <| IO.userError s!"path {path} does not exist"
  if ← path.isDir then
    traverse path test_file
  else
    test_file path
  return 0
