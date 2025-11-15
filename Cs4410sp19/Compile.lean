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

def get_slot! (name : String) : ExceptT String CompileM Int := do
  let ctx ← read
  match ctx.slots.lookup name with
  | none => throw s!"\"{name}\" is absent"
  | some x => return x

def with_tmp_var (pref : String := "tmp") (x : String → Int → CompileM α) : CompileM α := do
  let tmp ← gensym pref
  with_new_var tmp (x tmp)

def anf : Expr → CompileM Expr
  | e@(.num _) | e@(.id _)
  | e@(.bool _) => pure e
  | .prim1 op operand => do
    let name ← gensym "oprnd"
    .let_in name <$>
      anf operand <*>
      (pure (.prim1 op (.id name))
      )
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
  | prim1 op x ih =>
    apply IsANF.let_in
    . apply ih
    . apply IsANF.prim1
      apply IsImm.id
  | prim2 op lhs rhs ihl ihr =>
    apply IsANF.let_in
    . apply ihl
    . apply IsANF.let_in
      . apply ihr
      . apply IsANF.prim2
        . apply IsImm.id
        . apply IsImm.id
  | bool x =>
    apply IsANF.of_imm
    apply IsImm.bool

open Expr in
@[simp]
theorem anf_is_anf' (e : Expr) : Expr.IsANF (anf e).run := anf_is_anf e

def Arg.of_slot : Int → Arg := fun slot => .reg_offset .esp (-slot)

private def combine_insts [Monad m] : m (Array Instruction) → m (Array Instruction) → m (Array Instruction) :=
  fun x y => (· ++ ·) <$> x <*> y

local infixl:65 " <++> " => combine_insts

def const_false : Arg := .const 0x00000001
def const_true : Arg := .const 0x80000001

def compile_imm (e : Expr) (h : e.IsImm) : ExceptT String CompileM Arg := do
  match e with
  | .num n =>
    if n > 1073741823 || n < -1073741824 then
      throw s!"Integer overflow: {n}"
    return .const (n <<< 1)
  | .bool .false => return const_false
  | .bool .true => return const_true
  | .id name =>
    let slot ← get_slot! name
    return Arg.of_slot slot

local macro "is_anf! " h:term : tactic => `(tactic| focus cases $h:term; contradiction; assumption)

private def eax := Arg.reg (.eax)

private def load_number_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jnz "error_non_number" ]

private def load_bool_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jz "error_non_number" ]

def compile_anf (e : Expr) (h : e.IsANF) : ExceptT String CompileM (Array Instruction) := do
  match e with
  | .num n =>
    let arg ← compile_imm (.num n) (by simp)
    return load_number_checked arg
  | .bool x =>
    let arg ← compile_imm (.bool x) (by simp)
    return #[.mov eax arg]
  | .id name =>
    let arg ← compile_imm (.id name) (by simp)
    return #[.mov eax arg]
  | .let_in name value cont =>
    compile_anf value (by is_anf! h) <++> with_new_var name fun slot =>
      pure #[ .mov (Arg.of_slot slot) eax ] <++> compile_anf cont (by is_anf! h)
  | .ite cond bp bn =>
    let label_else ← gen_label "if_false"
    let label_done ← gen_label "done"
    let c ← compile_imm cond (by is_anf! h)
    pure #[ .mov eax c, .cmp eax const_false, .je label_else ]
      <++> compile_anf bp (by is_anf! h)
      <++> pure #[ .jmp label_done, .label label_else ]
      <++> compile_anf bn (by is_anf! h)
      <++> pure #[ .label label_done ]
  | .prim1 .neg x =>
    let x ← compile_imm x (by is_anf! h)
    return load_number_checked x ++ #[ .mov eax (.const 0), .sub eax x ]
  | .prim1 .not x =>
    let x ← compile_imm x (by is_anf! h)
    return load_bool_checked x ++ #[ .xor eax (.const 0x8000_0000) ]
  | .prim2 .plus x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .add eax rhs ]
  | .prim2 .minus x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .sub eax rhs ]
  | .prim2 .times x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .mul rhs, .sar eax (.const 1) ]
  | .prim2 .land x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    return load_bool_checked rhs ++ load_bool_checked lhs ++ #[ .and eax rhs ]
  | .prim2 .lor x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    return load_bool_checked rhs ++ load_bool_checked lhs ++ #[ .or eax rhs ]
  | .prim2 .lt x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_less ← gen_label "less"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jl label_less,
      .mov eax const_false,
      .label label_less ]
  | .prim2 .le x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_le ← gen_label "less_eq"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jle label_le,
      .mov eax const_false,
      .label label_le ]
  | .prim2 .gt x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_greater ← gen_label "greater"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jg label_greater,
      .mov eax const_false,
      .label label_greater ]
  | .prim2 .ge x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_ge ← gen_label "greater_eq"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jge label_ge,
      .mov eax const_false,
      .label label_ge ]
  | .prim2 .eq x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_eq ← gen_label "equal"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .je label_eq,
      .mov eax const_false,
      .label label_eq ]
  | .prim2 .ne x y =>
    let lhs ← compile_imm x (by is_anf! h)
    let rhs ← compile_imm y (by is_anf! h)
    let label_ne ← gen_label "not_equal"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_false,
      .je label_ne,
      .mov eax const_true,
      .label label_ne ]

def compile_expr (e : Expr) : ExceptT String CompileM (Array Instruction) := fun ctx env => do
  let r := anf e ctx env
  compile_anf r.fst (by simp [r]) ctx r.snd

def error_non_number := "
error_non_number:
  push eax
  push 1
  call error
  add esp, 4 * 2
"

def helpers : List String := [error_non_number]

def prelude : String := s!"
section .text
extern error
global our_code_starts_here
{String.intercalate "\n" helpers}
our_code_starts_here:"

def compile_prog (e : Expr) : Except String String := do
  let instrs ← compile_expr e |>.run.run
  let asm_string := asm_to_string instrs
  let prelude := «prelude»
  let suffix := "ret"
  return s!"{prelude}\n{asm_string}\n{suffix}"
