import Std
import Cs4410sp19.Basic

namespace Cs4410sp19

structure FileMap where
  private mk' ::
  private src : String
  /-- [0, ..., eoi+1] -/
  private indexes : Array (String.Pos)

structure Location where
  row : Nat
  column : Nat
deriving Inhabited, Repr

/-- returns `none` if out of range -/
def FileMap.lookup : FileMap → String.Pos → Option Location
  | ⟨src, xs⟩, pos => do
    assert! xs.isEmpty
    let lineStartIdx ← List.range (xs.size - 1) |>.find? fun i => pos < xs[i + 1]!
    let mut lineStart := xs[lineStartIdx]!
    let mut count := 0
    while lineStart < pos do
      lineStart := src.next lineStart
      count := count + 1
    return ⟨lineStartIdx, count⟩

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

local notation "Expr" => Expr String.Pos

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

private def sepBy1 (sep : Parser α) (x : Parser α) (allow_ws : Bool := true) : Parser (Array α) := do
  let head ← x
  if allow_ws then ws
  let trailing ← many (sep *> x)
  return #[head] ++ trailing

def parse_ident : Parser String := parse_ident_no_ws <* ws

variable (pe : Parser Expr) in
mutual

partial def parse_let_in : Parser Expr := do
  let pos ← pos
  atom "let"
  let name ← parse_ident
  ws
  atom "="
  let value ← pe
  ws
  atom "in"
  let body ← pe
  ws
  return .let_in pos name value body

partial def parse_ite : Parser Expr := do
  let pos ← pos
  atom "if"
  let cond ← pe
  atom ":"
  let bp ← pe
  atom "else"
  atom ":"
  let bn ← pe
  return .ite pos cond bp bn

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
  return .call pos name args.toList

partial def parse_true : Parser Expr := do
  let pos ← pos
  atom "true"
  return (.bool pos .true)

partial def parse_false : Parser Expr := do
  let pos ← pos
  atom "false"
  return (.bool pos .false)

partial def parse_expr_inner : Parser Expr := do
  attempt (pos >>= fun pos => Expr.num pos <$> parse_num_val)
  <|> attempt parse_let_in <|> attempt parse_ite
  <|> attempt (pchar '(' *> ws *> pe <* ws <* pchar ')' <* ws)
  <|> attempt parse_true
  <|> attempt parse_false
  <|> attempt parse_function_call
  <|> attempt (pos >>= fun pos => Expr.id pos <$> parse_ident)

partial def parse_neg : Parser Expr := do
  attempt (do
    let pos ← pos
    atom "-"
    Expr.prim1 pos .neg <$> parse_neg
    ) <|> parse_expr_inner

partial def parse_not : Parser Expr := do
  attempt (do
    let pos ← pos
    atom "!"
    Expr.prim1 pos .not <$> parse_not
    ) <|> parse_neg

partial def parse_mul : Parser Expr := parse_infixl [("*", .times)] parse_not

partial def parse_add_sub : Parser Expr := parse_infixl [("+", .plus), ("-", .minus)] parse_mul

partial def parse_hcmp : Parser Expr := parse_infixl (next := parse_add_sub)
  [("<=", .le), (">=", .ge), ("<", .lt), (">", .gt)]

partial def parse_mcmp : Parser Expr := parse_infixl (next := parse_hcmp)
  [("==", .eq), ("!=", .ne)]

partial def parse_land : Parser Expr := parse_infixl (next := parse_mcmp) [("&&", .land)]

partial def parse_lor : Parser Expr := parse_infixl (next := parse_land) [("||", .lor)]

partial def parse_expr_outer : Parser Expr := parse_lor

end

partial def parse_expr : Parser Expr := do
  ws
  parse_expr_outer parse_expr

def parse_function_decl : Parser Decl := do
  atom "def"
  let name ← parse_ident
  atom "("
  let ids ← sepBy (atom ",") parse_ident true
  atom ")"
  atom ":"
  let body ← parse_expr
  return Decl.function <| FuncDef.mk name ids.toList body

def parse_prog : Parser (Program String.Pos) := do
  let decls ← many parse_function_decl
  let body ← parse_expr
  return .mk decls body

end

def run_parse_prog (input : String) : Except String (Program Location) := do
  let map := FileMap.mk input
  let expr ← parse_prog.run input
  let some result := expr.mapM (fun x => map.lookup x)
    | throw "impossible: FileMap is not correct"
  return result
