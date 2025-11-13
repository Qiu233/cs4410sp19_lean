import Std
import Cs4410sp19.Basic

namespace Cs4410sp19

open Std.Internal.Parsec Std.Internal.Parsec.String in

section

private def atom : String → Parser Unit := fun x => pstring x *> ws

/-- useful for trailing parsers (e.g. binary operators) -/
private partial def fix (cont : α → Parser α) : α → Parser α := fun c => (cont c >>= fix cont) <|> pure c

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
  <|> attempt (Expr.id <$> parse_ident)

partial def parse_mul : Parser Expr := do
  let head ← parse_expr_inner
  ws
  fix (fun c => pchar '*' *> ws *> (.prim2 .times c <$> parse_expr_inner) <* ws) head

partial def parse_add_sub : Parser Expr := do
  let head ← parse_mul
  ws
  fix (fun c =>
    (pchar '+' *> ws *> (.prim2 .plus c <$> parse_mul) <* ws)
    <|> (pchar '-' *> ws *> (.prim2 .minus c <$> parse_mul) <* ws)) head

partial def parse_expr_outer : Parser Expr := parse_add_sub

end

partial def parse_expr : Parser Expr := do
  ws
  parse_expr_outer parse_expr

end
