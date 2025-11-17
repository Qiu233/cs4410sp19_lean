import Cs4410sp19.Basic
import Cs4410sp19.Compile.Basic
import Cs4410sp19.Compile.ANF.Basic

namespace Cs4410sp19

partial def anf [Monad m] [MonadNameGen m] : Expr α → m (AExpr Unit) := helpA
where
  helpA (e : Expr α) : m (AExpr Unit) := do
    let (ans, setup) ← helpC e
    return setup.foldr (init := AExpr.cexpr ans) (fun (name, val) acc => AExpr.let_in () name val acc)
  helpI (e : Expr α) : m ((ImmExpr Unit) × Array (String × (CExpr Unit))) := do
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
    | .let_in _ name _ value kont =>
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
  helpC (e : Expr α) : m ((CExpr Unit) × Array (String × (CExpr Unit))) := do
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
    | .let_in _ name  _ value kont =>
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

partial def compile_imm (e : ImmExpr α) : CompileFuncM (Array Instruction) := do
  match e with
  | .num _ n =>
    let arg ← ImmExpr.arg (.num () n)
    return load_number_checked arg
  | .bool _ x =>
    let arg ← ImmExpr.arg (.bool () x)
    return #[.mov eax arg]
  | .id _ name =>
    let arg ← ImmExpr.arg (.id () name)
    return #[.mov eax arg]

mutual

partial def compile_cexpr (e : CExpr α) (tail_pos : Bool) : CompileFuncM (Array Instruction) := do
  match e with
  | .imm x => compile_imm x
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
    return #[
      .mov eax lhs,
      .cmp eax rhs,
      .mov eax const_true,
      .je label_eq,
      .mov eax const_false,
      .label label_eq ]
  | .prim2 _ .ne x y =>
    let lhs ← x.arg
    let rhs ← y.arg
    let label_ne ← gen_label "not_equal"
    return #[
      .mov eax lhs,
      .cmp eax rhs,
      .mov eax const_false,
      .je label_ne,
      .mov eax const_true,
      .label label_ne ]
  | .ite _ cond bp bn =>
    let label_else ← gen_label "if_false"
    let label_done ← gen_label "done"
    let c ← cond.arg
    let ps ← compile_aexpr bp tail_pos
    let ns ← compile_aexpr bn tail_pos
    return #[ .mov eax c, .cmp eax const_false, .je label_else ] ++ ps ++ #[ .jmp label_done, .label label_else ] ++ ns ++ #[ .label label_done ]
  | .call _ name args =>
    let avai ← Env.functions <$> getThe Env
    unless avai.contains name do
      throw s!"function \"{name}\" is undefined"
    add_used_constants name
    let asm_name := name.replace "-" "_"
    let n := args.length
    let mut ts := #[]
    for imm in args do
      ts := ts.push (← imm.arg)
    let current_decl? ← Context.current_decl? <$> read
    if tail_pos && (Prod.fst <$> current_decl?).isEqSome name then -- calling self
      let rs := ts.zipIdx |>.flatMap (fun (t, i) => #[ .mov eax t, .mov (.reg_offset .ebp (i + 2)) (.reg .eax) ])
      return rs ++ #[ .jmp (current_decl?.get!.snd) ]
    else
      let rs := ts.reverse.flatMap (fun t => #[ .mov eax t, .push eax ])
      return rs ++ #[ .call asm_name, .add (.reg .esp) (.const (4 * n)) ]

partial def compile_aexpr (e : AExpr α) (tail_pos : Bool) : CompileFuncM (Array Instruction) := do
  match e with
  | .cexpr c => compile_cexpr c tail_pos
  | .let_in _ name value cont =>
    (· ++ ·) <$> compile_cexpr value false <*> with_new_var name fun slot =>
      (#[ .mov (slot.to_arg) eax ] ++ ·) <$> compile_aexpr cont tail_pos

end

variable [Monad m] [MonadNameGen m]
in section

def anf_function_def : FuncDef α → m (AFuncDef Unit) := fun ⟨name, body, params, _⟩ => do
  let params' := params.map Prod.fst
  return ⟨name, params', ← anf body⟩

def anf_decl : Decl α → m (ADecl Unit)
  | .function _ d => do
    .function () <$> anf_function_def d

def anf_mutual_decl : MutualDecl α → m (AMutualDecl Unit) := fun x => do
  AMutualDecl.mk () <$> (x.decls.mapM anf_decl)

def anf_prog : Program α → m (AProgram Unit) := fun ⟨_, decls, e⟩ => do
  let decls' ← decls.mapM anf_mutual_decl
  let e' ← anf e
  return ⟨(), decls', e'⟩

end

def func_prolog (n : Nat) : Array Instruction :=
  #[ .push (.reg .ebp), .mov (.reg .ebp) (.reg .esp), .sub (.reg .esp) (.const (4 * n)) ]

def func_epilog : Array Instruction :=
  #[ .mov (.reg .esp) (.reg .ebp), .pop (.reg .ebp), .ret ]

def compile_anfed_function_def (e : AFuncDef α) : CompileM (Array Instruction) := do
  let ⟨name, ids, body⟩ := e
  -- let env ← get
  -- if env.functions.contains name then
  --   throw s!"function \"{name}\" already exists"
  if ids.eraseDups.length != ids.length then
    throw s!"arguments {ids} contain duplicates"
  -- modify fun env => (let functions := env.functions.insert name; {env with functions})
  let do_compile := with_args ids.toArray fun _ => compile_aexpr body true
  let label_body ← gen_label s!"{name.replace "-" "_"}_body"
  let (result, s) ← do_compile.run { current_decl? := (name, label_body) } {}
  let a : Array Instruction :=
    func_prolog s.max_stack_slots
    ++ #[ .label label_body ]
    ++ result ++
    func_epilog
  return a

def compile_anfed_decl (e : ADecl α) : CompileM (Array Instruction) := do
  match e with
  | .function _ f => compile_anfed_function_def f

def compile_anfed_mutual_decl (e : AMutualDecl α) : CompileM (Array (String × (Array Instruction))) := do
  let mut data := #[]
  for d in e.decls do
    modify fun env => {env with functions := env.functions.insert d.name}
  for d in e.decls do
    let code ← compile_anfed_decl d
    data := data.push (d.name.replace "-" "_", code)
  return data

def compile_anfed_prog_core (e : AProgram α) : CompileM (Array (String × (Array Instruction)) × (Array Instruction)) := do
  let mut store := #[]
  for d in e.decls do
    let code ← compile_anfed_mutual_decl d
    store := store.append code
  let (result, s) ← compile_aexpr e.exe_code true |>.run { current_decl? := none } {}
  let result := func_prolog s.max_stack_slots ++ result ++ func_epilog
  return (store, result)
