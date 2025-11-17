import Cs4410sp19.Basic
import Cs4410sp19.Compile.Basic
import Cs4410sp19.Parser

namespace Cs4410sp19.Tych

partial local instance : ToString (Typ α) where
  toString x :=
    let rec go
    | .var _ x => s!"'{x}"
    | .const _ x => x
    | .arrow args ret => s!"({String.intercalate ", " (List.map go args.toList)}) -> {go ret}"
    | .app ctor args => s!"{go ctor}<{String.intercalate ", " (List.map go args.toList)}>"
    go x

structure LocalContext where
  localDecls : List (String × Typ Unit) := {}

structure State where
  global_consts : Std.HashMap String (Typ Unit) := {}

abbrev TypeM := ReaderT LocalContext <| StateT State CompileM

local notation "Expr'" => Expr (Location × Option (Typ String.Pos))
local notation "Typ'" => Typ Unit

private def get_decl! (name : String) : TypeM Typ' := fun c => c.localDecls.lookup name |>.getDM (throw s!"identifier {name} does not exist")

private def with_decl (name : String) (type : Typ') (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with localDecls := (name, type) :: ctx.localDecls }) x

private def with_decls (decls : List (String × Typ')) (x : TypeM α) : TypeM α :=
  withReader (fun ctx => { ctx with localDecls := decls.reverse ++ ctx.localDecls }) x

private def get_const! (name : String) : TypeM Typ' := do
  let s ← get
  s.global_consts.get? name |>.getDM (throw s!"constant {name} is undefined")


private def insert_const (name : String) (type : Typ Unit) : TypeM Unit := do
  modify fun s => {s with global_consts := s.global_consts.insert name type}

-- private def with_decls_rev (decls : List (String × Typ')) (x : TypeM α) : TypeM α :=
--   withReader (fun ctx => { ctx with localDecls := decls ++ ctx.localDecls }) x

private partial def type_eqv : Typ α → Typ β → Bool
  | Typ.var _ x, Typ.var _ y => x == y
  | Typ.const _ x, Typ.const _ y => x == y
  | Typ.arrow args_x ret_x, Typ.arrow args_y ret_y => args_x.size == args_y.size && type_eqv ret_x ret_y && Array.all (args_x.zipWith (bs := args_y) type_eqv) id
  | Typ.app ctor_x args_x, Typ.app ctor_y args_y => args_x.size == args_y.size && type_eqv ctor_x ctor_y && Array.all (args_x.zipWith (bs := args_y) type_eqv) id
  | _, _ => false

private partial def type_is_const : Typ α → String → Bool
  | Typ.const _ x, s => x == s
  | _, _ => false

local instance : BEq (Typ α) := ⟨type_eqv⟩

private def type_int : Typ Unit := Typ.const () "Int"
private def type_bool : Typ Unit := Typ.const () "Bool"

private partial def type_check_expr (e : Expr') (type : Typ') : TypeM Unit := do
  match e with
  | .num loc _ =>
    unless type_is_const type "Int" do
      throw s!"{loc}: expression is expected to have type Int"
  | .id loc name =>
    let actual ← get_decl! name
    unless actual == type do
      throw s!"{loc}: expression is expected to have type {type}, but got {actual}"
  | .bool loc _ =>
    unless type_is_const type "Bool" do
      throw s!"{loc}: expression is expected to have type Bool"
  | .let_in _ name varType value kont =>
    type_check_expr value varType.unsetTag
    with_decl name varType.unsetTag do
      type_check_expr kont type
  | .prim1 _ .neg x => type_check_expr x type_int
  | .prim1 _ .not x => type_check_expr x type_bool
  | .prim2 loc .lor lhs rhs
  | .prim2 loc .land lhs rhs =>
    type_check_expr lhs type_bool
    type_check_expr rhs type_bool
    unless type_is_const type "Bool" do
      throw s!"{loc}: expression is expected to have type Bool"
  | .prim2 loc .eq lhs rhs
  | .prim2 loc .ne lhs rhs =>
    let (_, some type_lhs) := lhs.tag |
      throw s!"{lhs.tag.fst}: type of lhs must be given beforehand"
    let (_, some type_rhs) := rhs.tag |
      throw s!"{lhs.tag.fst}: type of rhs must be given beforehand"
    type_check_expr lhs type_lhs.unsetTag
    type_check_expr rhs type_rhs.unsetTag
    unless type_is_const type "Bool" do
      throw s!"{loc}: expression is expected to have type Bool"
  | .prim2 loc .lt lhs rhs
  | .prim2 loc .gt lhs rhs
  | .prim2 loc .le lhs rhs
  | .prim2 loc .ge lhs rhs =>
    type_check_expr lhs type_int
    type_check_expr rhs type_int
    unless type_is_const type "Bool" do
      throw s!"{loc}: expression is expected to have type Bool"
  | .prim2 loc .plus lhs rhs
  | .prim2 loc .minus lhs rhs
  | .prim2 loc .times lhs rhs =>
    type_check_expr lhs type_int
    type_check_expr rhs type_int
    unless type_is_const type "Int" do
      throw s!"{loc}: expression is expected to have type Int"
  | .ite _ cond bp bn =>
    type_check_expr cond type_bool
    type_check_expr bp type
    type_check_expr bn type
  | .call loc name args =>
    let Typ.arrow argTypes retType ← get_const! name | unreachable!
    unless retType == type do
      throw s!"{loc}: function {name} returns {retType}, but {type} is expected here"
    unless argTypes.size == args.length do
      throw s!"{loc}: function {name} expected {argTypes.size} arguments, but {args.length} are given"
    let _ ← argTypes.zipWithM (bs := args.toArray) (fun t e => type_check_expr e t)

private def type_check_decl (e : Decl (Location × Option (Typ String.Pos))) : TypeM Unit := do
  match e with
  | .function _ fundef =>
    let params := fundef.params.map fun (x, t) => (x, t.unsetTag)
    let paramTypes := params.toArray.unzip.snd.map Typ.unsetTag
    insert_const fundef.name (Typ.arrow paramTypes fundef.ret_type.unsetTag)
    let _ ← with_decls params <| type_check_expr fundef.body fundef.ret_type.unsetTag

private def type_check_prog_core (prog : Program (Location × Option (Typ String.Pos))) : TypeM Unit := do
  let decls := prog.decls
  let _ ← decls.mapM type_check_decl
  let (_, some main_type) := prog.exe_code.tag
    | throw "type of the main expression must be given beforehand"
  type_check_expr prog.exe_code main_type.unsetTag

def type_check_prog (prog : Program (Location × Option (Typ String.Pos))) : CompileM Unit := Prod.fst <$> type_check_prog_core prog {} {}
