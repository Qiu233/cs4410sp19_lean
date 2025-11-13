import Cs4410sp19.Basic
import Cs4410sp19.Parser

namespace Cs4410sp19

structure Context where
  slots : List (String × Int) := []

structure Env where
  names : Std.HashMap String Nat := {}

abbrev CompileM := ReaderT Context <| StateM Env

def CompileM.run : CompileM α → α := fun x => (x {} {}).fst

def getEnv : CompileM Env := getThe Env

def gensym (pref : String) : CompileM String := do
  let count ← modifyGet (fun env =>
    let names' := env.names.alter pref (fun | .none => .some 0 | .some x => .some x)
    (names'[pref]!, { env with names := names'.modify pref (· + 1) }))
  let name := s!"{pref}_{count}"
  return name

def gen_label (suggestedName : String) : CompileM String := do
  gensym s!"label_{suggestedName}"

def with_new_var (name : String) (x : Int → CompileM α) : CompileM α := do
  let slots ← Context.slots <$> read
  let slot := slots.length + 1
  withReader (fun ctx => { ctx with slots := (name, slot) :: ctx.slots }) (x slot)

def get_slot! (name : String) : CompileM Int := fun ctx =>
  match ctx.slots.lookup name with
  | none => panic! s!"\"{name}\" is absent"
  | some x => return x

def with_tmp_var (pref : String := "tmp") (x : String → Int → CompileM α) : CompileM α := do
  let tmp ← gensym pref
  with_new_var tmp (x tmp)

def anf : Expr → CompileM Expr
  | e@(.num _) | e@(.id _) => pure e
  | .prim2 op lhs rhs => do
    let name_lhs ← gensym "lhs"
    let name_rhs ← gensym "rhs"
    .let_in name_lhs <$>
      anf lhs <*>
      (.let_in name_rhs <$>
        anf rhs <*>
        pure (.prim2 op (.id name_lhs) (.id name_rhs))
      )
  | .let_in name value kont =>
    .let_in name <$> (anf value) <*> (anf kont)
  | .ite cond bp bn => do
    let name ← gensym "tmp"
    .let_in name <$> (anf cond) <*> (Expr.ite (.id name) <$> anf bp <*> anf bn)

open Expr in
@[simp]
theorem anf_is_anf {ctx env} (e : Expr) : Expr.IsANF (anf e ctx env).fst := by
  induction e generalizing env with
  | num x =>
    simp [anf]
    apply IsANF.of_imm
    apply IsImm.num
  | id name =>
    simp [anf]
    apply IsANF.of_imm
    apply IsImm.id
  | let_in name value kont ihv ihk =>
    exact IsANF.let_in ihv ihk
  | ite cond bp bn ihc ihp ihn =>
    apply IsANF.let_in
    . apply ihc
    . apply IsANF.ite
      . apply IsImm.id
      . apply ihp
      . apply ihn
  | prim2 op lhs rhs ihl ihr =>
    apply IsANF.let_in
    . apply ihl
    . apply IsANF.let_in
      . apply ihr
      . apply IsANF.prim2
        . apply IsImm.id
        . apply IsImm.id

open Expr in
@[simp]
theorem anf_is_anf' (e : Expr) : Expr.IsANF (anf e).run := anf_is_anf e

def Arg.of_slot : Int → Arg := fun slot => .reg_offset .esp (-slot)

private def combine_insts [Monad m] : m (Array Instruction) → m (Array Instruction) → m (Array Instruction) :=
  fun x y => (· ++ ·) <$> x <*> y

local infixl:65 " <++> " => combine_insts

def Expr.arg_of_IsImm (e : Expr) : e.IsImm → CompileM Arg := fun _ => do
  match e with
  | .num x => return .const x
  | .id x =>
    let slot ← get_slot! x
    return Arg.of_slot slot

def compile_anf (e : Expr) (h : e.IsANF) : CompileM (Array Instruction) := do
  match e with
  | .num n => return #[.mov (.reg .eax) (.const n)]
  | .id name =>
    let slot ← get_slot! name
    return #[.mov (.reg .eax) (Arg.of_slot slot)]
  | .let_in name value cont =>
    compile_anf value (by cases h; contradiction; assumption) <++> with_new_var name fun slot =>
      pure #[ .mov (Arg.of_slot slot) (.reg .eax) ] <++> compile_anf cont (by cases h; contradiction; assumption)
  | .prim2 .plus x y =>
    let lhs ← x.arg_of_IsImm (by cases h; contradiction; assumption)
    let rhs ← y.arg_of_IsImm (by cases h; contradiction; assumption)
    return #[ .mov (.reg .eax) lhs, .add (.reg .eax) rhs ]
  | .prim2 .minus x y =>
    let lhs ← x.arg_of_IsImm (by cases h; contradiction; assumption)
    let rhs ← y.arg_of_IsImm (by cases h; contradiction; assumption)
    return #[ .mov (.reg .eax) lhs, .sub (.reg .eax) rhs ]
  | .prim2 .times x y =>
    let lhs ← x.arg_of_IsImm (by cases h; contradiction; assumption)
    let rhs ← y.arg_of_IsImm (by cases h; contradiction; assumption)
    return #[ .mov (.reg .eax) lhs, .mul rhs ]
  | .ite cond bp bn =>
    let label_else ← gen_label "if_false"
    let label_done ← gen_label "done"
    let c ← cond.arg_of_IsImm (by cases h; contradiction; assumption)
    pure #[ .mov (.reg .eax) c, .cmp (.reg .eax) (.const 0), .je label_else ]
      <++> compile_anf bp (by cases h; contradiction; assumption)
      <++> pure #[ .jmp label_done, .label label_else ]
      <++> compile_anf bn (by cases h; contradiction; assumption)
      <++> pure #[ .label label_done ]

def compile_expr (e : Expr) : CompileM (Array Instruction) := fun ctx env => do
  let r := anf e ctx env
  compile_anf r.fst (by simp [r]) ctx r.snd

def compile_prog (e : Expr) : String :=
  let instrs := compile_expr e |>.run
  let asm_string := asm_to_string instrs
  let prelude := "
section .text
global our_code_starts_here
our_code_starts_here:"
  let suffix := "ret"
  s!"{prelude}\n{asm_string}\n{suffix}"
