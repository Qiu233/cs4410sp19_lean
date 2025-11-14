import Std
import Cs4410sp19.Basic

namespace Cs4410sp19

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

private def atom : String → Parser Unit := fun x => pstring x *> ws

/-- useful for trailing parsers (e.g. binary operators) -/
private partial def fix (cont : α → Parser α) : α → Parser α := fun c => (cont c >>= fix cont) <|> pure c

def parse_infixl (ops : List (String × Prim2)) (next : Parser Expr) : Parser Expr := do
  let head ← next
  ws
  assert! ops.length != 0
  let op :: ops := ops | unreachable!
  let gen := fun (op, op') => fun c => pstring op *> ws *> (Expr.prim2 op' c <$> next) <* ws
  let ts := ops.foldl (α := Expr → Parser Expr) (β := String × Prim2) (init := gen op) fun acc x => (fun t => acc t <|> (gen x) t)
  fix ts head

variable (pe : Parser Expr)
mutual

partial def parse_num_val : Parser Int := do
  let neg ← optional (pchar '-')
  let body ← digits
  ws
  if neg.isSome then
    return -body
  else
    return body

partial def parse_ident : Parser String := do
  let leading ← asciiLetter <|> pchar '_'
  let following ← many (asciiLetter <|> pchar '_' <|> digit)
  ws
  return String.mk (leading :: following.toList)

partial def parse_let_in : Parser Expr := do
  atom "let"
  let name ← parse_ident
  ws
  atom "="
  let value ← pe
  ws
  atom "in"
  let body ← pe
  ws
  return .let_in name value body

partial def parse_ite : Parser Expr := do
  atom "if"
  let cond ← pe
  atom "then"
  let bp ← pe
  atom "else"
  let bn ← pe
  return .ite cond bp bn

partial def parse_expr_inner : Parser Expr := do
  attempt (Expr.num <$> parse_num_val)
  <|> attempt parse_let_in <|> attempt parse_ite
  <|> attempt (pchar '(' *> ws *> pe <* ws <* pchar ')' <* ws)
  <|> attempt (atom "true" *> pure (.bool .true))
  <|> attempt (atom "false" *> pure (.bool .false))
  <|> attempt (Expr.id <$> parse_ident)

partial def parse_neg : Parser Expr := do
  attempt (atom "-" *> Expr.prim1 .neg <$> parse_expr_inner) <|> parse_expr_inner

partial def parse_not : Parser Expr := do
  attempt (atom "!" *> Expr.prim1 .not <$> parse_neg) <|> parse_neg

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

end
