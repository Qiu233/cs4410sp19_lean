import Std
import Cs4410sp19
import Cs4410sp19.Cont
import Cs4410sp19.SSA
import Cs4410sp19.MIR

open Cs4410sp19

open MIR

def _root_.main (args : List String) : IO Unit := do
  let input_file ← match args[0]? with
    | some f => pure f
    | _ =>
      IO.println "no input file"
      IO.Process.exit 255
  -- let outIdx? := args.findIdx? (· == "-o")
  -- let out? := outIdx? >>= fun x => args[x + 1]?
  -- let input_program ← IO.FS.readFile ⟨input_file⟩
  -- let prog ← match run_parse_prog input_program with
  --   | .ok expr => pure expr
  --   | .error e =>
  --     IO.println s!"parse failed due to error: {e}"
  --     IO.Process.exit 255
  -- let program ← match compile_prog prog with
  --   | .ok p => pure p
  --   | .error e =>
  --     IO.println s!"compilation failed due to error: {e}"
  --     IO.Process.exit 255
  -- match out? with
  -- | .some out => IO.FS.writeFile out program
  -- | .none => println! "{program}"
  let src ← IO.FS.readFile input_file
  let code ← match run_parse_prog src with
    | .error e => println! s!"failed to parse program due to: {e}"; return
    | .ok r => pure r
  let e := code.decls[0]!
  let s := ContT.run (m := SSA.M) (do
    let a ← anf_decl e.decls[0]!
    let t := (match a with | ADecl.function _ f => f)
    let r ← liftM <| SSA.cfg_of_function_def t
    let r : SSA.CFG' Unit String SSA.VarName SSA.Operand := { r with }
    return r
    ) (fun n => pure n) |>.run {} |>.run' {}
  let (r, s) := s.run {}
  println! "converted:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.reduce_assign r
  println! "unary assignment reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let r := SSA.eliminate_trivial_blocks r
  println! "trivial blocks reduced:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, _) := FreshM.run (SSA.eliminate_block_args r) s
  println! "block args eliminated:"
  println! "{SSA.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.construct r.toCFG |>.run' {}) {}
  println! "MIR constructed:"
  println! "{MIR.pp_cfg' r.toCFG}\n"

  let (r, s) := FreshM.run (MIR.reduce_lop r.toCFG) s
  println! "logical operators reduced:"
  println! "{MIR.pp_cfg' r}\n"

  let r := MIR.to_c_call r
  println! "call unfolded:"
  println! "{MIR.pp_cfg' r}\n"

  let (r, s) := FreshM.run (MIR.form r) s
  println! "two address formation:"
  println! "{MIR.pp_cfg' r}\n"

  let r := MIR.compute_mdata r
  println! "mdata:"
  println! "{MIR.pp_cfg r}\n"

  -- let ds := defs_in {r with}
  -- println! "{ds (.vreg ⟨"x.8"⟩) ".join.2"}"

  -- println! "{live_in {r with } (.vreg ⟨"x.8"⟩) ".join.2"}"
  -- println! "{defs_out {r with } (.greg .eax) ".join.2"}"

  -- let t := liveness_of_def {r with} (.greg .eax) 95
  -- println! "{t}"
  let intervals := build_live_intervals {r with}
  -- let itvs := sorry
  let itvs := intervals.toList.mergeSort fun x y => x.fst.def_pos < y.fst.def_pos
  println! "intervals (sorted by def_pos):"
  for (i, t) in itvs do
    println! "{i.d}, {i.def_pos}: {t}"
  let r := linear_scan_register_allocation {r with} intervals

  println! "\nregister allocated:"
  println! "{MIR.pp_cfg' r.unsetTag.toCFG}\n"
