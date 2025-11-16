import Cs4410sp19.Basic
import Cs4410sp19.Parser

namespace Cs4410sp19

inductive StackSlot where
  /-- `ebp i` is `[ebp + i * 4]` -/
  | ebp : Int → StackSlot
  /-- `esp i` is `[esp + i * 4]` -/
  | esp : Int → StackSlot
deriving BEq, Inhabited, Repr

structure Env where
  names : Std.HashMap String Nat := {}
  function_names : Array String := #[]

/-- context for sub-function compilation -/
structure Context where
  available_functions : Array String := #[]
  arg_slots : List (String × StackSlot) := []
  var_slots : List (String × StackSlot) := []

/-- volatile state for sub-function compilation -/
structure State where
  names : Std.HashMap String Nat := {}
  max_stack_slots : Nat := 0
  used_constants : Array String := #[]

abbrev CompileFuncM := ReaderT Context <| StateM State

def CompileFuncM.run : CompileFuncM α → α := fun x => (x {} {}).fst
def CompileFuncM.run' : CompileFuncM α → Context → State → (α × State) := fun x c s => (x c s)

def gensym (pref : String) : CompileFuncM String := do
  let count ← modifyGet (fun s =>
    let names' := s.names.alter pref (fun | .none => .some 0 | .some x => .some x)
    (names'[pref]!, { s with names := names'.modify pref (· + 1) }))
  let name := s!"{pref}_{count}"
  return name

def gen_label (suggestedName : String) : CompileFuncM String := do
  gensym s!"label_{suggestedName}"

def with_args (ids : Array String) (x : Array (String × StackSlot) → CompileFuncM α) : CompileFuncM α := do
  let new := ids.foldl (init := []) fun acc x => (x, StackSlot.ebp (acc.length + 2)) :: acc
  withReader (fun ctx => { ctx with arg_slots := new }) (x new.toArray)

def with_new_var (name : String) (x : StackSlot → CompileFuncM α) : CompileFuncM α := do
  let slots ← Context.var_slots <$> read
  let slot := .ebp (-(slots.length + 1))
  modify (fun s => {s with max_stack_slots := s.max_stack_slots.max (slots.length + 1)})
  withReader (fun ctx => { ctx with var_slots := (name, slot) :: ctx.var_slots }) (x slot)

def get_slot! (name : String) : ExceptT String CompileFuncM StackSlot := do
  let ctx ← read
  match ctx.var_slots.lookup name with -- search for variables first
  | none =>
    match ctx.arg_slots.lookup name with
    | none => throw s!"\"{name}\" is undefined"
    | some x => return x
  | some x => return x

def with_tmp_var (pref : String := "tmp") (x : String → StackSlot → CompileFuncM α) : CompileFuncM α := do
  let tmp ← gensym pref
  with_new_var tmp (x tmp)

def add_used_constants (name : String) : CompileFuncM Unit := do
  modify fun s => {s with used_constants := s.used_constants.push name}

def anf : Expr → CompileFuncM Expr
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
  | .call name args => do
    let names ← args.mapM fun x => do
      let n ← gensym "tmp"
      let y ← anf x
      pure (n, y)
    let i := Expr.call name (names.map (.id ∘ Prod.fst))
    return names.foldr (init := i) (fun t acc => Expr.let_in t.fst t.snd acc)

set_option warn.sorry false

open Expr in
@[simp]
theorem anf_is_anf {ctx s} (e : Expr) : Expr.IsANF (anf e ctx s).fst := by
  cases e with
  | num x =>
    simp [anf]
    apply IsANF.of_imm
    apply IsImm.num
  | id name =>
    simp [anf]
    apply IsANF.of_imm
    apply IsImm.id
  | let_in name value kont =>
    simp [anf]
    apply IsANF.let_in (anf_is_anf _) (anf_is_anf _)
  | ite cond bp bn =>
    simp [anf]
    apply IsANF.let_in
    . apply anf_is_anf
    . apply IsANF.ite
      . apply IsImm.id
      . apply anf_is_anf
      . apply anf_is_anf
  | prim1 op x =>
    simp [anf]
    apply IsANF.let_in
    . apply anf_is_anf
    . apply IsANF.prim1
      apply IsImm.id
  | prim2 op lhs rhs =>
    simp [anf]
    apply IsANF.let_in
    . apply anf_is_anf
    . apply IsANF.let_in
      . apply anf_is_anf
      . apply IsANF.prim2
        . apply IsImm.id
        . apply IsImm.id
  | bool x =>
    simp [anf]
    apply IsANF.of_imm
    apply IsImm.bool
  | call name args =>
    simp [anf]
    induction args generalizing s with
    | nil =>
      apply IsANF.call
      intro _ h'
      simp at h'
    | cons arg args ih => sorry -- TODO: prove this. It is really hard.

open Expr in
@[simp]
theorem anf_is_anf' (e : Expr) : Expr.IsANF (anf e).run := anf_is_anf e

def StackSlot.to_arg : StackSlot → Arg
  | .esp i => .reg_offset .esp i
  | .ebp i => .reg_offset .ebp i

private def combine_insts [Monad m] : m (Array Instruction) → m (Array Instruction) → m (Array Instruction) :=
  fun x y => (· ++ ·) <$> x <*> y

local infixl:65 " <++> " => combine_insts

def const_false : Arg := .const 0x00000001
def const_true : Arg := .const 0x80000001

def compile_imm (e : Expr) (h : e.IsImm) : ExceptT String CompileFuncM Arg := do
  match e with
  | .num n =>
    if n > 1073741823 || n < -1073741824 then
      throw s!"Integer overflow: {n}"
    return .const (n <<< 1)
  | .bool .false => return const_false
  | .bool .true => return const_true
  | .id name =>
    let slot ← get_slot! name
    return slot.to_arg

local macro "is_anf! " h:term : tactic => `(tactic| focus cases $h:term; contradiction; assumption)

private def eax := Arg.reg (.eax)

private def load_number_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jnz "error_non_number" ]

private def load_bool_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jz "error_non_bool" ]

def compile_anf (e : Expr) (h : e.IsANF) : ExceptT String CompileFuncM (Array Instruction) := do
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
      pure #[ .mov (slot.to_arg) eax ] <++> compile_anf cont (by is_anf! h)
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
  | .call name args =>
    let avai ← Context.available_functions <$> read
    unless avai.contains name do
      throw s!"function \"{name}\" is undefined"
    add_used_constants name
    let n := args.length
    have : ∀ x ∈ args, x.IsImm := by cases h; contradiction; assumption
    let mut ts := #[]
    for h : arg in args do
      ts := ts.push (← compile_imm arg (by apply this; apply h))
    let rs := ts.reverse.flatMap (fun t => #[ .mov eax t, .push eax ])
    return rs ++ #[ .call name, .add (.reg .esp) (.const (4 * n)) ]

def compile_expr (e : Expr) : ExceptT String CompileFuncM (Array Instruction) := fun ctx s => do
  let r := anf e ctx s
  compile_anf r.fst (by simp [r]) ctx r.snd

abbrev CompileDeclM := ExceptT String (StateM Env)

def func_prolog (n : Nat) : Array Instruction :=
  #[ .push (.reg .ebp), .mov (.reg .ebp) (.reg .esp), .sub (.reg .esp) (.const (4 * n)) ]

def func_epilog : Array Instruction :=
  #[ .mov (.reg .esp) (.reg .ebp), .pop (.reg .ebp), .ret ]

def compile_decl (e : Decl) : CompileDeclM (Array Instruction) := do
  match e with
  | .mk name ids body =>
    let env ← get
    if env.function_names.contains name then
      throw s!"function \"{name}\" already exists"
    if ids.eraseDups.length != ids.length then
      throw s!"arguments {ids} contain duplicates"
    let ns ← modifyGet fun env => (let function_names := env.function_names.push name; (function_names, {env with function_names}))
    let do_compile := with_args ids.toArray fun _ => compile_expr body
    let (result, s) := do_compile.run' { available_functions := ns } { names := ← Env.names <$> get }
    modify fun env => { env with names := s.names }
    let result ← result
    let a : Array Instruction :=
      func_prolog s.max_stack_slots
      ++ result ++
      func_epilog
    return a

def compile_prog_core (e : Program) : CompileDeclM (Array (String × (Array Instruction)) × (Array Instruction)) := do
  let mut store := #[]
  for d in e.decls do
    store := store.push <| (d.name, ← compile_decl d)
  let functions ← Env.function_names <$> get
  let (result, s) := compile_expr e.exe_code |>.run' { available_functions := functions } { names := ← Env.names <$> get }
  modify fun env => { env with names := s.names }
  let result ← result
  let result := func_prolog s.max_stack_slots ++ result ++ func_epilog
  return (store, result)

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

def prelude : String := s!"
section .text
{String.intercalate "\n" (externs.map (s!"extern {·}"))}
global our_code_starts_here
{String.intercalate "\n" helpers}
our_code_starts_here:"

def compile_prog (e : Program) : Except String String := do
  -- let instrs ← compile_expr e |>.run.run
  let (decls, exe) ← compile_prog_core e |>.run' { function_names := #["print"] }
  let ds := decls.map fun (d, is) =>
    s!"{d}:\n{asm_to_string is}\n"
  let ds := String.intercalate "\n" ds.toList
  -- let asm_string := asm_to_string instrs
  let main := asm_to_string exe
  -- let prelude := «prelude»
  -- let suffix := "ret"
  -- return s!"{prelude}\n{asm_string}\n{suffix}"
  return s!"section .text
{String.intercalate "\n" (externs.map (s!"extern {·}"))}
{String.intercalate "\n" helpers}
{ds}
global our_code_starts_here
our_code_starts_here:
{main}"
