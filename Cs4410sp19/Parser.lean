import Std
import Cs4410sp19.Basic

namespace Cs4410sp19

structure FileMap where
  private mk' ::
  private src : String
  /-- [0, ..., eoi+1] -/
  private indexes : Array (String.Pos)
deriving Inhabited, Repr

structure Location where
  row : Nat
  column : Nat
deriving Inhabited, Repr

instance : ToString Location where
  toString x := s!"{x.row}:{x.column}"

/-- returns `none` if out of range -/
def FileMap.lookup : FileMap → String.Pos → Option Location
  | ⟨src, xs⟩, pos => do
    assert! !xs.isEmpty
    let lineStartIdx ← List.range (xs.size - 1) |>.find? fun i => pos < xs[i + 1]!
    let mut lineStart := xs[lineStartIdx]!
    let mut count := 0
    while lineStart < pos do
      lineStart := src.next lineStart
      count := count + 1
    return ⟨lineStartIdx + 1, count⟩

def FileMap.mk : String → FileMap := fun s => Id.run do
  let mut pos : String.Pos := ⟨0⟩
  let mut indexes := #[pos]
  let endPos := s.endPos
  while pos < endPos do
    pos := s.next pos
    let c := s.get pos
    if c == '\n' then
      indexes := indexes.push pos
  indexes := indexes.push endPos
  return ⟨s, indexes⟩

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

def pos : Parser String.Pos := fun it => ParseResult.success it it.i

local notation "Expr" => Expr (String.Pos × Option (Typ String.Pos))

private def atom : String → Parser Unit := fun x => pstring x *> ws

/-- useful for trailing parsers (e.g. binary operators) -/
private partial def fix (cont : α → Parser α) : α → Parser α := fun c => (cont c >>= fix cont) <|> pure c

def parse_infixl (ops : List (String × Prim2)) (next : Parser Expr) : Parser Expr := do
  let head ← next
  ws
  assert! ops.length != 0
  let op :: ops := ops | unreachable!
  let gen := fun (op, op') => fun c => pstring op *> ws *> (Expr.prim2 head.tag op' c <$> next) <* ws
  let ts := ops.foldl (α := Expr → Parser Expr) (β := String × Prim2) (init := gen op) fun acc x => (fun t => acc t <|> (gen x) t)
  fix ts head

def parse_num_val : Parser Int := do
  let neg ← optional (pchar '-')
  let body ← digits
  ws
  if neg.isSome then
    return -body
  else
    return body

def parse_ident_no_ws : Parser String := do
  let leading ← asciiLetter <|> pchar '_'
  let following ← many (asciiLetter <|> pchar '_' <|> pchar '-' <|> digit)
  return String.mk (leading :: following.toList)

private def sepBy (sep : Parser Unit) (x : Parser α) (allow_ws : Bool := true) : Parser (Array α) := (do
  let head ← x
  if allow_ws then ws
  let trailing ← many (sep *> x)
  return #[head] ++ trailing) <|> pure #[]

private def sepBy1 (sep : Parser Unit) (x : Parser α) (allow_ws : Bool := true) : Parser (Array α) := do
  let head ← x
  if allow_ws then ws
  let trailing ← many (sep *> x)
  return #[head] ++ trailing

def parse_ident : Parser String := parse_ident_no_ws <* ws

mutual

partial def parse_type_var : Parser (Typ String.Pos) := do
  let pos ← pos
  _ ← pchar '\''
  let name ← parse_ident
  ws
  return Typ.var pos name

partial def parse_type_const : Parser (Typ String.Pos) := do
  let pos ← pos
  let x ← pstring "Int" <|> pstring "Bool"
  ws
  return Typ.const pos x

partial def parse_type_atomic : Parser (Typ String.Pos) :=
  attempt parse_type_var
    <|> attempt (do
      let pos ← pos
      atom "("
      let head ← parse_type
      let trailing ← many1 do
        atom "*"
        parse_type
      atom ")"
      return Typ.tuple pos (head :: trailing.toList)
      )
    <|> attempt (do
      let pos ← pos
      atom "("
      atom ")"
      return Typ.tuple pos []
      )
    <|> attempt (do
      atom "("
      let type ← parse_type
      atom ")"
      pure type
      )
    <|> parse_type_const

partial def parse_type : Parser (Typ String.Pos) := do
  parse_type_atomic

end

variable (pe : Parser Expr) in
mutual

partial def parse_let_in : Parser Expr := do
  let pos ← pos
  atom "let"
  let name ← parse_ident
  ws
  let type? ← optional <| attempt do
    atom ":"
    parse_type
  atom "="
  let value ← pe
  ws
  atom "in"
  let body ← pe
  ws
  return .let_in (pos, none) name (type?.mapM fun t => t.mapM (m := Id) fun x => (x, none)) value body

partial def parse_ite : Parser Expr := do
  let pos ← pos
  atom "if"
  let cond ← pe
  atom ":"
  let bp ← pe
  atom "else"
  atom ":"
  let bn ← pe
  return .ite (pos, none) cond bp bn

partial def parse_exprs : Parser (Array Expr) := (do
  let head ← pe
  ws
  let trailing ← many (atom "," *> pe)
  return #[head] ++ trailing) <|> pure #[]

partial def parse_function_call : Parser Expr := do
  let pos ← pos
  let name ← parse_ident_no_ws
  atom "("
  let args ← sepBy (atom ",") pe true
  atom ")"
  return .call (pos, none) name args.toList

partial def parse_true : Parser Expr := do
  let pos ← pos
  atom "true"
  return (.bool (pos, none) .true)

partial def parse_false : Parser Expr := do
  let pos ← pos
  atom "false"
  return (.bool (pos, none) .false)

partial def parse_tuple : Parser Expr :=
  attempt (do
    let pos ← pos
    atom "("
    atom ")"
    return (.tuple (pos, none) [])
    )
  <|> (do
    let pos ← pos
    atom "("
    let head ← pe
    let trailing ← many1 do
      atom ","
      pe
    atom ")"
    return (.tuple (pos, none) (head :: trailing.toList)))

partial def parse_expr_atomic : Parser Expr := do
  attempt (pos >>= fun pos => Expr.num (pos, none) <$> parse_num_val)
  <|> attempt parse_tuple
  <|> attempt (pchar '(' *> ws *> pe <* ws <* pchar ')' <* ws)
  <|> attempt parse_true
  <|> attempt parse_false
  <|> attempt parse_function_call
  <|> attempt (pos >>= fun pos => Expr.id (pos, none) <$> parse_ident)

partial def parse_tuple_access : Parser Expr := do
  let expr ← parse_expr_atomic
  (fix trail expr)
  <|> return expr
  where trail expr : Parser Expr := do
    let pos ← pos
    atom "["
    let idx ← parse_num_val
    if idx < 0 then
      fail "indexing of tuple access must be non-negative"
    atom "of"
    let n ← parse_num_val
    if n ≤ 0 then
      fail "size of tuple access must be positive"
    unless idx < n do
      fail "indexing of tuple access must be strictly smaller than the size"
    atom "]"
    return .get_item (pos, none) expr idx.natAbs n.natAbs

partial def parse_expr_inner : Parser Expr := attempt parse_let_in <|> attempt parse_ite <|> parse_tuple_access

partial def parse_pair_access : Parser Expr := do
  (do
    let pos ← pos
    atom "fst"
    Expr.prim1 (pos, none) .fst <$> parse_expr_inner
    ) <|>
  (do
    let pos ← pos
    atom "snd"
    Expr.prim1 (pos, none) .snd <$> parse_expr_inner
    ) <|> parse_expr_inner

partial def parse_neg : Parser Expr := do
  attempt (do
    let pos ← pos
    atom "-"
    Expr.prim1 (pos, none) .neg <$> parse_pair_access
    ) <|> parse_pair_access

partial def parse_not : Parser Expr := do
  attempt (do
    let pos ← pos
    atom "!"
    Expr.prim1 (pos, none) .not <$> parse_not
    ) <|> parse_neg

partial def parse_mul : Parser Expr := parse_infixl [("*", .times)] parse_not

partial def parse_add_sub : Parser Expr := parse_infixl [("+", .plus), ("-", .minus)] parse_mul

partial def parse_hcmp : Parser Expr := parse_infixl (next := parse_add_sub)
  [("<=", .le), (">=", .ge), ("<", .lt), (">", .gt)]

partial def parse_mcmp : Parser Expr := parse_infixl (next := parse_hcmp)
  [("==", .eq), ("!=", .ne)]

partial def parse_land : Parser Expr := parse_infixl (next := parse_mcmp) [("&&", .land)]

partial def parse_lor : Parser Expr := parse_infixl (next := parse_land) [("||", .lor)]

partial def parse_expr_annotated : Parser Expr := do
  let e ← parse_lor
  let type? ← optional <| attempt do
    atom ":"
    parse_type
  return e.setTag (e.tag.fst, e.tag.snd.getDM type?)

partial def parse_expr_outer : Parser Expr := parse_expr_annotated

end

partial def parse_expr : Parser Expr := do
  ws
  parse_expr_outer parse_expr

def parse_param : Parser (String × Option (Typ String.Pos)) := do
  let name ← parse_ident
  let type? ← optional <| attempt do
    atom ":"
    parse_type
  return (name, type?)

def parse_function_params : Parser (Array (String × Option (Typ String.Pos))) := sepBy (atom ",") parse_param true

def parse_function_decl_sig : Parser (Decl (String.Pos × Option (Typ String.Pos))) := do
  let pos ← pos
  let name ← parse_ident
  atom "("
  let args ← parse_function_params
  atom ")"
  let ret_type? ← optional <| attempt do
    atom "->"
    parse_type
  atom ":"
  let body ← parse_expr
  let args := args.map fun (x, y) => (x, y.mapM (m := Id) fun p => p.mapM fun q => (q, none))
  let ret_type := ret_type?.mapM fun r => r.mapM (m := Id) fun p => (p, none)
  return Decl.function (pos, none) <| FuncDef.mk name body args.toList ret_type

def parse_function_decl : Parser (MutualDecl (String.Pos × Option (Typ String.Pos))) := do
  let pos ← pos
  atom "def"
  let head ← parse_function_decl_sig
  let trailing ← many (atom "and" *> parse_function_decl_sig)
  return MutualDecl.mk (pos, none) (head :: trailing.toList)

def parse_prog : Parser (Program (String.Pos × Option (Typ String.Pos))) := do
  let pos ← pos
  let decls ← many parse_function_decl
  let body ← parse_expr
  ws
  eof
  return .mk (pos, none) decls body

end

def run_parse_prog (input : String) : Except String (Program (Location × Option (Typ String.Pos))) := do
  let map := FileMap.mk input
  let expr ← match parse_prog input.mkIterator with
    | Std.Internal.Parsec.ParseResult.success _ r => pure r
    | Std.Internal.Parsec.ParseResult.error pos err => throw s!"{(map.lookup pos.i).get!}:{err}"
  let result ← expr.mapM fun (x, t) => do
    let y ← map.lookup x |>.getDM (throw s!"impossible")
    pure (y, t)
  return result
