import Cs4410sp19.Basic
import Cs4410sp19.Parser

namespace Cs4410sp19

inductive StackSlot where
  /-- `ebp i` is `[ebp + i * 4]` -/
  | ebp : Int → StackSlot
  /-- `esp i` is `[esp + i * 4]` -/
  | esp : Int → StackSlot
deriving BEq, Inhabited, Repr

class MonadNameGen (m : Type → Type) where
  gensym : String → m String

instance {m n} [MonadLift m n] [inst : MonadNameGen m] : MonadNameGen n where
  gensym x := MonadLift.monadLift (inst.gensym x)

export MonadNameGen (gensym)

section

structure Env where
  names : Std.HashMap String Nat := {}
  function_names : Array String := #[]

abbrev CompileM := ExceptT String (StateM Env)

def CompileM.run : CompileM α → Env → (Except String α × Env) := fun x env => x env

def CompileM.gensym (pref : String) : CompileM String := do
  let count ← modifyGet (fun s =>
    let names' := s.names.alter pref (fun | .none => .some 0 | .some x => .some x)
    (names'[pref]!, { s with names := names'.modify pref (· + 1) }))
  let name := s!"{pref}_{count}"
  return name

instance : MonadNameGen CompileM := ⟨CompileM.gensym⟩

def gen_label [MonadNameGen m] (suggestedName : String) : m String :=
  gensym s!"label_{suggestedName}"

end

section

/-- context for sub-function compilation -/
structure Context where
  available_functions : Array String := #[]
  arg_slots : List (String × StackSlot) := []
  var_slots : List (String × StackSlot) := []

/-- volatile state for sub-function compilation -/
structure State where
  max_stack_slots : Nat := 0
  used_constants : Array String := #[]

abbrev CompileFuncM := ReaderT Context <| StateT State CompileM

def CompileFuncM.run : CompileFuncM α → CompileM α := fun x => Prod.fst <$> (x {} {})

def CompileFuncM.run' : CompileFuncM α → Context → State → CompileM (α × State) := fun x c s => (x c s)

end

def with_args (ids : Array String) (x : Array (String × StackSlot) → CompileFuncM α) : CompileFuncM α := do
  let new := ids.foldl (init := []) fun acc x => (x, StackSlot.ebp (acc.length + 2)) :: acc
  withReader (fun ctx => { ctx with arg_slots := new }) (x new.toArray)

def with_new_var (name : String) (x : StackSlot → CompileFuncM α) : CompileFuncM α := do
  let slots ← Context.var_slots <$> read
  let slot := .ebp (-(slots.length + 1))
  modify (fun s => {s with max_stack_slots := s.max_stack_slots.max (slots.length + 1)})
  withReader (fun ctx => { ctx with var_slots := (name, slot) :: ctx.var_slots }) (x slot)

def get_slot! (name : String) : CompileFuncM StackSlot := do
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

partial def anf : Expr α → CompileFuncM (AExpr Unit) := helpA
where
  helpA (e : Expr α) : CompileFuncM (AExpr Unit) := do
    let (ans, setup) ← helpC e
    return setup.foldr (init := AExpr.cexpr ans) (fun (name, val) acc => AExpr.let_in () name val acc)
  helpI (e : Expr α) : CompileFuncM ((ImmExpr Unit) × Array (String × (CExpr Unit))) := do
    match e with
    | .num _ x => return (.num () x, #[])
    | .id _ x => return (.id () x, #[])
    | .bool _ x => return (.bool () x, #[])
    | .prim1 _ op operand =>
      let (operand', is) ← helpI operand
      let name_res ← gensym "result"
      return (ImmExpr.id () name_res, is ++ #[(name_res, CExpr.prim1 () op operand')])
    | .prim2 _ .times lhs rhs =>
      let (lhs', ls) ← helpI lhs
      let (rhs', rs) ← helpI rhs
      let name_res ← gensym "result"
      if rhs' matches .num .. then
        -- trick: when rhs is an immediate number, say `6`, the instruction `mul 6` is invalid, so we must lift the immediate to a stack slot here
        let name_tmp ← gensym "tmp"
        return (ImmExpr.id () name_res, ls ++ rs ++ #[(name_tmp, CExpr.imm rhs'), (name_res, CExpr.prim2 () .times lhs' (ImmExpr.id () name_tmp))])
      else
        return (ImmExpr.id () name_res, ls ++ rs ++ #[(name_res, CExpr.prim2 () .times lhs' rhs')])
    | .prim2 _ op lhs rhs => do
      let (lhs', ls) ← helpI lhs
      let (rhs', rs) ← helpI rhs
      let name_res ← gensym "result"
      return (ImmExpr.id () name_res, ls ++ rs ++ #[(name_res, CExpr.prim2 () op lhs' rhs')])
    | .let_in _ name value kont =>
      let (value', cs) ← helpC value
      let (kont', ks) ← helpC kont
      let name_res ← gensym "result"
      return (ImmExpr.id () name_res, cs ++ #[(name, value')] ++ ks ++ #[(name_res, kont')])
    | .ite _ cond bp bn =>
      let (cond', setup) ← helpI cond
      let bp' ← helpA bp
      let bn' ← helpA bn
      let name_res ← gensym "result"
      return (ImmExpr.id () name_res, setup ++ #[(name_res, CExpr.ite () cond' bp' bn')])
    | .call _ name args =>
      let ts ← args.mapM helpI
      let setups := ts.toArray.unzip.snd.flatMap id
      let args' := ts.unzip.fst
      let name_res ← gensym "result"
      return (ImmExpr.id () name_res, setups ++ #[(name_res, CExpr.call () name args')])
  helpC (e : Expr α) : CompileFuncM ((CExpr Unit) × Array (String × (CExpr Unit))) := do
    match e with
    | .prim1 _ op operand =>
      let (operand', setup) ← helpI operand
      return (CExpr.prim1 () op operand', setup)
    | .prim2 _ .times lhs rhs =>
      let (lhs', ls) ← helpI lhs
      let (rhs', rs) ← helpI rhs
      if rhs' matches .num .. then
        -- trick: when rhs is an immediate number, say `6`, the instruction `mul 6` is invalid, so we must lift the immediate to a stack slot here
        let name_tmp ← gensym "tmp"
        return (CExpr.prim2 () .times lhs' (ImmExpr.id () name_tmp), ls ++ rs ++ #[(name_tmp, CExpr.imm rhs')])
      else
        return (CExpr.prim2 () .times lhs' rhs', ls ++ rs)
    | .prim2 _ op lhs rhs =>
      let (lhs', ls) ← helpI lhs
      let (rhs', rs) ← helpI rhs
      return (CExpr.prim2 () op lhs' rhs', ls ++ rs)
    | .let_in _ name value kont =>
      let (value', cs) ← helpC value
      let (kont', ks) ← helpC kont
      return (kont', cs ++ #[(name, value')] ++ ks)
    | .ite _ cond bp bn =>
      let (cond', setup) ← helpI cond
      let bp' ← helpA bp
      let bn' ← helpA bn
      return (CExpr.ite () cond' bp' bn', setup)
    | .call _ name args =>
      let ts ← args.mapM helpI
      let setups := ts.toArray.unzip.snd.flatMap id
      let args' := ts.unzip.fst
      return (CExpr.call () name args', setups)
    | _ =>
      let (imm, setup) ← helpI e
      return (CExpr.imm imm, setup)

def StackSlot.to_arg : StackSlot → Arg
  | .esp i => .reg_offset .esp i
  | .ebp i => .reg_offset .ebp i

private def combine_insts [Monad m] : m (Array Instruction) → m (Array Instruction) → m (Array Instruction) :=
  fun x y => (· ++ ·) <$> x <*> y

local infixl:65 " <++> " => combine_insts

def const_false : Arg := .const 0x00000001
def const_true : Arg := .const 0x80000001

def ImmExpr.arg (e : ImmExpr α) : CompileFuncM Arg := do
  match e with
  | .num _ n =>
    if n > 1073741823 || n < -1073741824 then
      throw s!"Integer overflow: {n}"
    return .const (n <<< 1)
  | .bool _ .false => return const_false
  | .bool _ .true => return const_true
  | .id _ name =>
    let slot ← get_slot! name
    return slot.to_arg

private def eax := Arg.reg (.eax)

private def load_number_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jnz "error_non_number" ]

private def load_bool_checked (src : Arg) : Array Instruction :=
  #[ .mov eax src, .test eax (.const 0x00000001), .jz "error_non_bool" ]

mutual

partial def compile_cexpr (e : CExpr α) : CompileFuncM (Array Instruction) := do
  match e with
  | .imm x =>
    match x with
    | .num _ n =>
      let arg ← ImmExpr.arg (.num () n)
      return load_number_checked arg
    | .bool _ x =>
      let arg ← ImmExpr.arg (.bool () x)
      return #[.mov eax arg]
    | .id _ name =>
      let arg ← ImmExpr.arg (.id () name)
      return #[.mov eax arg]
  | .prim1 _ .neg x =>
    let x ← x.arg
    return load_number_checked x ++ #[ .mov eax (.const 0), .sub eax x ]
  | .prim1 _ .not x =>
    let x ← x.arg
    return load_bool_checked x ++ #[ .xor eax (.const 0x8000_0000) ]
  | .prim2 _ .plus x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .add eax rhs ]
  | .prim2 _ .minus x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .sub eax rhs ]
  | .prim2 _ .times x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    return load_number_checked rhs ++ load_number_checked lhs ++ #[ .mul rhs, .sar eax (.const 1) ]
  | .prim2 _ .land x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    return load_bool_checked rhs ++ load_bool_checked lhs ++ #[ .and eax rhs ]
  | .prim2 _ .lor x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    return load_bool_checked rhs ++ load_bool_checked lhs ++ #[ .or eax rhs ]
  | .prim2 _ .lt x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_less ← gen_label "less"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jl label_less,
      .mov eax const_false,
      .label label_less ]
  | .prim2 _ .le x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_le ← gen_label "less_eq"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jle label_le,
      .mov eax const_false,
      .label label_le ]
  | .prim2 _ .gt x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_greater ← gen_label "greater"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jg label_greater,
      .mov eax const_false,
      .label label_greater ]
  | .prim2 _ .ge x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_ge ← gen_label "greater_eq"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .jge label_ge,
      .mov eax const_false,
      .label label_ge ]
  | .prim2 _ .eq x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_eq ← gen_label "equal"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_true,
      .je label_eq,
      .mov eax const_false,
      .label label_eq ]
  | .prim2 _ .ne x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_ne ← gen_label "not_equal"
    return load_number_checked rhs ++ load_number_checked lhs ++ #[
      .cmp eax rhs,
      .mov eax const_false,
      .je label_ne,
      .mov eax const_true,
      .label label_ne ]
  | .ite _ cond bp bn =>
    let label_else ← gen_label "if_false"
    let label_done ← gen_label "done"
    let c ← cond.arg
    pure #[ .mov eax c, .cmp eax const_false, .je label_else ]
      <++> compile_anf bp
      <++> pure #[ .jmp label_done, .label label_else ]
      <++> compile_anf bn
      <++> pure #[ .label label_done ]
  | .call _ name args =>
    let avai ← Context.available_functions <$> read
    unless avai.contains name do
      throw s!"function \"{name}\" is undefined"
    add_used_constants name
    let n := args.length
    let mut ts := #[]
    for imm in args do
      ts := ts.push (← imm.arg)
    let rs := ts.reverse.flatMap (fun t => #[ .mov eax t, .push eax ])
    return rs ++ #[ .call (name.replace "-" "_"), .add (.reg .esp) (.const (4 * n)) ]

partial def compile_anf (e : AExpr α) : CompileFuncM (Array Instruction) := do
  match e with
  | .cexpr c => compile_cexpr c
  | .let_in _ name value cont =>
    compile_cexpr value <++> with_new_var name fun slot =>
      pure #[ .mov (slot.to_arg) eax ] <++> compile_anf cont

end

def compile_expr (e : Expr α) : CompileFuncM (Array Instruction) := do
  let r ← anf e
  compile_anf r

def func_prolog (n : Nat) : Array Instruction :=
  #[ .push (.reg .ebp), .mov (.reg .ebp) (.reg .esp), .sub (.reg .esp) (.const (4 * n)) ]

def func_epilog : Array Instruction :=
  #[ .mov (.reg .esp) (.reg .ebp), .pop (.reg .ebp), .ret ]

def compile_function_def (e : FuncDef) : CompileM (Array Instruction) := do
  let ⟨name, ids, body⟩ := e
  let env ← get
  if env.function_names.contains name then
    throw s!"function \"{name}\" already exists"
  if ids.eraseDups.length != ids.length then
    throw s!"arguments {ids} contain duplicates"
  let ns ← modifyGet fun env => (let function_names := env.function_names.push name; (function_names, {env with function_names}))
  let do_compile := with_args ids.toArray fun _ => compile_expr body
  let (result, s) ← do_compile.run' { available_functions := ns } {}
  let a : Array Instruction :=
    func_prolog s.max_stack_slots
    ++ result ++
    func_epilog
  return a

def compile_decl (e : Decl) : CompileM (Array Instruction) := do
  match e with
  | .function f => compile_function_def f

def compile_prog_core (e : Program α) : CompileM (Array (String × (Array Instruction)) × (Array Instruction)) := do
  let mut store := #[]
  for d in e.decls do
    store := store.push <| (d.name.replace "-" "_", ← compile_decl d)
  let functions ← Env.function_names <$> get
  let (result, s) ← compile_expr e.exe_code |>.run' { available_functions := functions } {}
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

def compile_prog (e : Program α) : Except String String := do
  let (decls, exe) ← compile_prog_core e |>.run' { function_names := #["print"] }
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
