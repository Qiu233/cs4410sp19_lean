import Cs4410sp19.Basic
import Cs4410sp19.Compile.Basic
import Cs4410sp19.Parser

namespace Cs4410sp19.Tych

partial local instance : ToString (Typ α) where
  toString x :=
    let rec go
    | .var _ x => s!"'{x}"
    | .const _ x => x
    | .arrow [arg] ret => s!"{go arg} -> {go ret}"
    | .arrow args ret => s!"({String.intercalate ", " (List.map go args)}) -> {go ret}"
    | .app ctor args => s!"{go ctor}<{String.intercalate ", " (List.map go args)}>"
    go x

local instance : ToString TypeScheme where
  toString := fun ⟨params, body⟩ =>
    s!"∀ [{String.intercalate ", " (List.map (s!"'{·}") params)}] . {body}"

def subst_type (in_type : Typ Unit) (name : String) (type : Typ Unit) : Typ Unit := go in_type
  where go t :=
    match t with
    | Typ.var _ v => if v == name then type else t
    | Typ.const .. => t
    | Typ.arrow argTypes retType =>
      Typ.arrow (argTypes.map go) (go retType)
    | Typ.app ctor argTypes =>
      Typ.app (go ctor) (argTypes.map go)

def subst_type_scheme (in_type : TypeScheme) (name : String) (type : Typ Unit) : TypeScheme :=
  if in_type.params.contains name then
    in_type
  else
    {in_type with body := subst_type in_type.body name type}

structure LocalContext where
  current_decls : List (String × Typ Unit) := {}
  localDecls : List (String × Typ Unit) := {}
  type_params : Std.HashMap String String := {}

structure TypeVarContext where
  assignment : List (String × Typ Unit) := {}

structure State where
  names : Std.HashMap String Nat := {}
  functions : Std.HashMap String TypeScheme

abbrev TypeM := StateT TypeVarContext <| ReaderT LocalContext <| StateT State (Except String)

def TypeM.gensym (pref : String) : TypeM String := do
  let count ← modifyGetThe State (fun s =>
    let names' := s.names.alter pref (fun | .none => .some 0 | .some x => .some x)
    (names'[pref]!, { s with names := names'.modify pref (· + 1) }))
  let name := s!"{pref}.{count}"
  return name

instance : MonadNameGen TypeM := ⟨TypeM.gensym⟩

private def _root_.Cs4410sp19.TypeScheme.instantiate1 : TypeScheme → Typ Unit → TypeM TypeScheme := fun scheme type => do
  let x :: xs := scheme.params | throw "impossible"
  let body' := subst_type scheme.body x type
  return TypeScheme.mk xs body'

private def _root_.Cs4410sp19.TypeScheme.instantiate : TypeScheme → List (Typ Unit) → TypeM TypeScheme := fun scheme types => do
  unless types.length ≤ scheme.arity do throw "impossible"
  types.foldlM (init := scheme) TypeScheme.instantiate1

def new_type_var : String → TypeM (Typ Unit) := fun name => do
  let name' ← gensym name
  return Typ.var () name'

local notation "Expr'" => Expr (Location × (Option (Typ String.Pos)))
local notation "Typ'" => Typ Unit

private partial def type_eqv : Typ α → Typ β → Bool
  | Typ.var _ x, Typ.var _ y => x == y
  | Typ.const _ x, Typ.const _ y => x == y
  | Typ.arrow args_x ret_x, Typ.arrow args_y ret_y => args_x.length == args_y.length && type_eqv ret_x ret_y && List.all (args_x.zipWith (ys := args_y) type_eqv) id
  | Typ.app ctor_x args_x, Typ.app ctor_y args_y => args_x.length == args_y.length && type_eqv ctor_x ctor_y && List.all (args_x.zipWith (ys := args_y) type_eqv) id
  | _, _ => false

local instance : BEq (Typ α) := ⟨type_eqv⟩

partial def collect_vars : Typ α → List String := fun t => go {} t |>.run' {} |>.reverse
  where go (ns : List String) (type : Typ α) : StateM (Std.HashSet String) (List String) := do
    match type with
    | Typ.var _ x =>
      if (← get).contains x then
        return ns
      modify fun s => s.insert x
      return x :: ns
    | Typ.const .. => return ns
    | Typ.arrow args ret => do
      let mut ns := ns
      for arg in args do
        ns ← go ns arg
      ns ← go ns ret
      return ns
    | Typ.app ctor args => do
      let mut ns := ns
      ns ← go ns ctor
      for arg in args do
        ns ← go ns arg
      return ns

def instantiate_vars : Typ Unit → TypeM (Typ Unit) := fun type => do
  let s ← getThe TypeVarContext
  let vars := collect_vars type
  let mut t := type
  -- single pass
  -- we don't need to calculate the iterated fixpoint
  for name in vars do
    match s.assignment.lookup name with
    | some type' =>
      t := subst_type t name type'
    | none => pure ()
  return t

def _root_.Cs4410sp19.TypeScheme.instantiate_with_fresh_vars : TypeScheme → TypeM Typ' := fun scheme => do
  let ns ← List.range scheme.arity |>.mapM fun _ => new_type_var "T"
  TypeScheme.body <$> scheme.instantiate ns

def is_type_param? : Typ' → TypeM (Option Typ') := fun t => do
  match t with
  | Typ.var _ name =>
    let c ← read
    c.type_params.get? name |>.mapM fun x => return Typ.var () x
  | _ => return none

def assign! : String → Typ' → TypeM Unit := fun name type => do
  let s ← getThe TypeVarContext
  if s.assignment.lookup name |>.isSome then
    throw s!"type variable '{name} is already assigned"
  let subst := s.assignment.map fun (n, x) => (n, subst_type x name type)
  modifyThe TypeVarContext fun st => {st with assignment := (name, type) :: subst}

partial def unify : Typ' → Typ' → TypeM Unit := fun x y => do
  if x == y then
    return
  match x, y with
  | .var _ x, e => do
    let s ← getThe TypeVarContext
    match s.assignment.lookup x with
    | none =>
      assign! x (← instantiate_vars e)
    | some e' =>
      unify e' e
  | e, .var _ x => do
    let s ← getThe TypeVarContext
    match s.assignment.lookup x with
    | none =>
      assign! x (← instantiate_vars e)
    | some e' =>
      unify e e'
  | .const _ x, .const _ y =>
    unless x == y do
      throw s!"cannot unify type {x} with {y}"
  | .arrow args_x ret_x, .arrow args_y ret_y => do
    assert! args_x.length == args_y.length
    unify ret_x ret_y
    _ ← args_x.zipWithM (bs := args_y) unify
  | .app ctor_x args_x, .app ctor_y args_y => do
    assert! args_x.length == args_y.length
    unify ctor_x ctor_y
    _ ← args_x.zipWithM (bs := args_y) unify
  | x, y => throw s!"cannot unify type {x} with {y}"

private def get_decl! (name : String) : TypeM Typ' := do
  let c ← read
  c.localDecls.lookup name |>.getDM (throw s!"identifier {name} does not exist")

private def with_decl (name : String) (type : Typ') (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with localDecls := (name, type) :: ctx.localDecls }) x

private def with_decls (decls : List (String × Typ')) (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with localDecls := decls.reverse ++ ctx.localDecls }) x

private def with_type_params (decls : Std.HashMap String String) (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with type_params := decls }) x

private def with_current_decls (decls : List (String × Typ Unit)) (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with current_decls := decls }) x

private def get_const! (name : String) : TypeM TypeScheme := do
  let s ← getThe State
  s.functions.get? name |>.getDM (throw s!"constant {name} is undefined")

private partial def type_is_const : Typ α → String → Bool
  | Typ.const _ x, s => x == s
  | _, _ => false

private def type_int : Typ Unit := Typ.const () "Int"
private def type_bool : Typ Unit := Typ.const () "Bool"

def throw_type_is_not (loc : Location) (s : Typ') : TypeM Unit := throw s!"{loc}: expression is expected to have type {s}"

def binary_ops : Prim2 → TypeScheme
  | .eq | .ne =>
    TypeScheme.mk ["T"] (Typ.arrow [(Typ.var () "T"), (Typ.var () "T")] type_bool)
  | .lor | .land =>
    TypeScheme.mk [] (Typ.arrow [type_bool, type_bool] type_bool)
  | .lt | .gt | .le | .ge =>
    TypeScheme.mk [] (Typ.arrow [type_int, type_int] type_bool)
  | .plus | .minus | .times =>
    TypeScheme.mk [] (Typ.arrow [type_int, type_int] type_int)

def unary_ops : Prim1 → TypeScheme
  | .not =>
    TypeScheme.mk [] (Typ.arrow [type_bool] type_bool)
  | .neg =>
    TypeScheme.mk [] (Typ.arrow [type_int] type_int)

mutual

partial def infer_type (e : Expr') : TypeM Typ' := do
  let hint? := e.tag.snd
  let type ← match e with
    | .num .. => return type_int
    | .bool .. => return type_bool
    | .id _ name => get_decl! name
    | .let_in _ name varType? value kont =>
      let varType ← match varType? with
        | some varType =>
          type_check_expr value varType.unsetTag
          pure varType.unsetTag
        | none => infer_type value
      with_decl name varType do
        infer_type kont
    | .prim1 _ op x =>
      let scheme := unary_ops op
      let Typ.arrow [type_operand'] retType ← scheme.instantiate_with_fresh_vars | unreachable!
      unify type_operand' (← infer_type x)
      instantiate_vars retType
    | .prim2 _ op lhs rhs =>
      let scheme := binary_ops op
      let Typ.arrow [type_lhs', type_rhs'] retType ← scheme.instantiate_with_fresh_vars | unreachable!
      unify type_lhs' (← infer_type lhs)
      unify type_rhs' (← infer_type rhs)
      instantiate_vars retType
    | .ite _ cond bp bn =>
      type_check_expr cond type_bool
      let scheme := TypeScheme.mk ["T"] (Typ.arrow [type_bool, (Typ.var () "T"), (Typ.var () "T")] (Typ.var () "T"))
      let Typ.arrow [_, ptype', ntype'] retType ← scheme.instantiate_with_fresh_vars | unreachable!
      unify ptype' (← infer_type bp)
      unify ntype' (← infer_type bn)
      instantiate_vars retType
    | .call loc name args =>
      let current_decls ← LocalContext.current_decls <$> read
      match current_decls.lookup name with
      | some declType =>
        let argTypes ← args.mapM infer_type
        let retType ← new_type_var "R"
        unify (Typ.arrow argTypes retType) declType
        instantiate_vars retType
      | none =>
        let scheme ← get_const! name
        let Typ.arrow argTypes retType ← scheme.instantiate_with_fresh_vars | unreachable!
        unless argTypes.length == args.length do
          throw s!"{loc}: function {name} expected {argTypes.length} arguments, but {args.length} are given"
        let _ ← argTypes.zipWithM (bs := args) (fun t e => do unify t (← infer_type e))
        instantiate_vars retType
  hint?.forM fun hint => do
    let hint := hint.unsetTag
    let p? ← is_type_param? hint
    match p? with
    | none =>
      match hint with
      | .var _ name =>
        throw s!"invalid type parameter '{name}"
      | _ => pure ()
      unify type hint
    | some p => unify type p
  instantiate_vars type

private partial def type_check_expr (e : Expr') (type : Typ') : TypeM Unit := do
  let actual ← infer_type e
  unify type actual

end

private def generalize (type : Typ') : TypeM TypeScheme := do
  let type ← instantiate_vars type
  let unbound := collect_vars type
  return TypeScheme.mk unbound type

private def type_check_mutual_decl (decl : MutualDecl (Location × Option (Typ String.Pos))) : TypeM (List (String × TypeScheme)) := do
  let decls := decl.decls
  let generate_types (e : Decl (Location × Option (Typ String.Pos))) : TypeM _ := do
    match e with
    | .function _ fundef' =>
      let fundef := fundef'.unsetTag
      -- We need to replace textual explicit type variables (like 'a, 'b) with fresh
      -- internal type variables so that different functions' explicit type
      -- variable names do not alias each other. Also preserve sharing when the
      -- same textual name appears multiple times in the same signature.
      -- let mapping := (Std.HashMap.emptyWithCapacity 8 : Std.HashMap String String)

      let mut mapping : Std.HashMap String String := {}
      let mut freshNames : List String := {}
      let mut acc : List (String × Typ' × Option String) := {}
      for (x, t) in fundef.params do
        match t with
        | none => do
          let tv ← new_type_var "A"
          acc := (x, tv, none) :: acc
        | some (Typ.var _ name) =>
          match mapping.get? name with
          | some nm =>
            acc := ((x, Typ.var () nm, some nm) :: acc)
          | none => do
            let tv ← new_type_var name
            match tv with
            | Typ.var _ nm =>
              mapping := mapping.insert name nm
              freshNames := freshNames ++ [nm]
              acc := ((x, tv, some nm) :: acc)
            | _ =>
              acc := ((x, tv, none) :: acc)
        | some t =>
          acc := ((x, t, none) :: acc)
      let params' := acc.reverse
      let mapping' := mapping
      let freshNames' := freshNames

      let paramTypes := params'.map fun (_, x, _) => x
      let params := params'.map fun (x, y, _) => (x, y)

      let (retType, mapping', freshNames'') ←
        match fundef.ret_type? with
        | some (Typ.var _ name) =>
          match mapping'.get? name with
          | some nm => pure (Typ.var () nm, mapping', freshNames')
          | none => do
            let tv ← new_type_var name
            match tv with
            | Typ.var _ nm => pure (tv, mapping'.insert name nm, freshNames' ++ [nm])
            | _ => pure (tv, mapping', freshNames')
        | some t => pure (t, mapping', freshNames')
        | none => do
          let tv ← new_type_var "R"
          pure (tv, mapping', freshNames')

      -- typeParams should be the fresh names created for explicit variables
      let typeParams := freshNames''

      let selfType ← new_type_var "F"
      unify selfType (Typ.arrow paramTypes retType)
      return ((fundef.name, selfType), typeParams, params, retType, fundef'.body, mapping')
  let decls' ← decls.mapM generate_types
  let current_decls := decls'.unzip.fst
  with_current_decls current_decls do
    for ((_, _), _, params, retType, body, mapping') in decls' do
      with_type_params mapping' <|
        with_decls params <|
          type_check_expr body retType
  let result ← decls'.mapM fun ((name, selfType), _, _, _, _) => do
    let r ← generalize selfType
    -- dbg_trace s!"generalized: {name} : {r}"
    return (name, r)
  return result

private def type_check_main (e : Expr (Location × Option (Typ String.Pos))) : TypeM Typ' := do
  let selfType ← new_type_var "M"
  let type ← infer_type e
  unify selfType type
  let type' ← instantiate_vars type
  let unbound := collect_vars type
  if unbound.length > 0 then
    throw "type of the main expression cannot contain free variable(s)"
  return type'

private def type_check_prog_core (prog : Program (Location × Option (Typ String.Pos))) : ReaderT LocalContext (StateT State (Except String)) Typ' := do
  let decls := prog.decls
  for mdecl in decls do
    let mutuals ← type_check_mutual_decl mdecl |>.run' {}
    let existing ← State.functions <$> getThe State
    let dup? := mdecl.decls.find? fun d => existing.contains d.name
    dup?.forM fun dup =>
      throw s!"declaration of {dup.name} already exists"
    for (name, ts) in mutuals do
      modifyThe State fun s => {s with functions := s.functions.insert name ts}
  let mainType ← type_check_main prog.exe_code |>.run' {}
  return mainType

def type_check_prog (prog : Program (Location × Option (Typ String.Pos))) (builtin : Std.HashMap String TypeScheme) : Except String Typ' := do
  type_check_prog_core prog {} |>.run' { functions := builtin }
