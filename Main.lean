import Std
import Cs4410sp19

namespace Cs4410sp19

inductive Reg where
  | eax
  | esp
deriving Inhabited

inductive Arg where
  | const : Int → Arg
  | reg : Reg → Arg
  | reg_offset : Reg → Int → Arg
deriving Inhabited

inductive Instruction where
  | mov : Arg → Arg → Instruction
  | add : Arg → Arg → Instruction
  | sub : Arg → Arg → Instruction
deriving Inhabited

instance : ToString Reg where
  toString
  | .eax => "eax"
  | .esp => "esp"

instance : ToString Arg where
  toString
  | .const v => s!"{v}"
  | .reg r => s!"{r}"
  | .reg_offset r i => s!"[{r} + 4 * {i}]"

instance : ToString Instruction where
  toString
  | .mov dst src => s!"mov {dst}, {src}"
  | .add dst src => s!"add {dst}, {src}"
  | .sub dst src => s!"sub {dst}, {src}"

def asm_to_string : List Instruction → String := fun xs =>
  String.intercalate "\n" (xs.map toString)

inductive Expr where
  | num : Int → Expr
  | add1 : Expr → Expr
  | sub1 : Expr → Expr
  | id : String → Expr
  | let_in : String → Expr → Expr → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
deriving Inhabited

open Std.Internal.Parsec Std.Internal.Parsec.String in
mutual

partial def parse_num_val : Parser Int := do
  let neg ← optional (pchar '-')
  let body ← digits
  ws
  if neg.isSome then
    return -body
  else
    return body

partial def parse_add1 : Parser Expr := do
  _ ← pstring "add1("
  ws
  let val ← parse_expr
  ws
  _ ← pchar ')'
  ws
  return .add1 val

partial def parse_sub1 : Parser Expr := do
  _ ← pstring "sub1("
  ws
  let val ← parse_expr
  ws
  _ ← pchar ')'
  ws
  return .sub1 val

partial def parse_ident : Parser String := do
  let leading ← asciiLetter <|> pchar '_'
  let following ← many (asciiLetter <|> pchar '_' <|> digit)
  ws
  return String.mk (leading :: following.toList)

partial def parse_let_in : Parser Expr := do
  _ ← pstring "let"
  ws
  let name ← parse_ident
  ws
  _ ← pstring "="
  ws
  let value ← parse_expr
  ws
  _ ← pstring "in"
  ws
  let body ← parse_expr
  ws
  return .let_in name value body

partial def parse_expr' : Parser Expr := do
  attempt (Expr.num <$> parse_num_val)
  <|> attempt parse_add1 <|> attempt parse_sub1
  <|> attempt parse_let_in
  <|> attempt (Expr.id <$> parse_ident)
  <|> attempt (pchar '(' *> ws *> parse_expr <* ws <* pchar ')' <* ws)

partial def parse_add_sub : Parser Expr := do
  let head ← parse_expr'
  ws
  let rec fn (c : Expr) := show Parser Expr from do
    ((pchar '+' *> ws *> (.add c <$> parse_expr') <* ws) >>= fn)
    <|> ((pchar '-' *> ws *> (.sub c <$> parse_expr') <* ws) >>= fn)
    <|> pure c
  fn head

partial def parse_expr : Parser Expr := do
  ws
  parse_add_sub

end

structure Env where
  slots : List (String × Int) := []
  names : Std.HashMap String Nat := {}

def Env.gensym (pref : String) : Env → (String × Env) := fun env =>
  let names' := env.names.alter pref (fun | .none => .some 0 | .some x => .some x)
  let v := names'[pref]!
  let name := s!"{pref}_{v}"
  (name, { env with names := names'.modify pref (· + 1) })

def Env.push_var (name : String) : Env → (Int × Env) := fun env =>
  let slot := env.slots.length + 1
  let env' := { env with slots := (name, slot) :: env.slots }
  (slot, env')

def Env.get_slot! (name : String) : Env → Int := fun env => env.slots.lookup name |>.get!

def Env.gen_tmp (pref : String := "tmp") : Env → (Int × Env) := fun env =>
  let (tmp, env) := env.gensym pref
  env.push_var tmp

def Arg.of_slot : Int → Arg := fun slot => .reg_offset .esp (-slot)

def compile_expr (env : Env) (e : Expr) : List Instruction :=
  match e with
  | .num n => [.mov (.reg .eax) (.const n)]
  | .add1 e => compile_expr env e ++ [.add (.reg .eax) (.const 1)]
  | .sub1 e => compile_expr env e ++ [.add (.reg .eax) (.const (-1))]
  | .id name =>
    let slot := env.get_slot! name
    [.mov (.reg .eax) (Arg.of_slot slot)]
  | .let_in name value cont =>
    let (slot, env') := env.push_var name
    compile_expr env value
      ++ [ .mov (Arg.of_slot slot) (.reg .eax) ]
      ++ compile_expr env' cont
  | .add x y =>
    let (slot_l, env_l) := env.gen_tmp "tmp_l"
    let a := compile_expr env_l x ++ [.mov (Arg.of_slot slot_l) (.reg .eax)]
    let (slot_r, env_r) := env_l.gen_tmp "tmp_r"
    let b := compile_expr env_r y ++ [.mov (Arg.of_slot slot_r) (.reg .eax)]
    let c : List Instruction := [ .mov (.reg .eax) (Arg.of_slot slot_l), .add (.reg .eax) (Arg.of_slot slot_r) ]
    a ++ b ++ c
  | .sub x y =>
    let (slot_l, env_l) := env.gen_tmp "tmp_l"
    let a := compile_expr env_l x ++ [.mov (Arg.of_slot slot_l) (.reg .eax)]
    let (slot_r, env_r) := env_l.gen_tmp "tmp_r"
    let b := compile_expr env_r y ++ [.mov (Arg.of_slot slot_r) (.reg .eax)]
    let c : List Instruction := [ .mov (.reg .eax) (Arg.of_slot slot_l), .sub (.reg .eax) (Arg.of_slot slot_r) ]
    a ++ b ++ c


def compile_prog (e : Expr) : String :=
  let instrs := compile_expr {} e
  let asm_string := asm_to_string instrs
  let prelude := "
section .text
global our_code_starts_here
our_code_starts_here:"
  let suffix := "ret"
  s!"{prelude}\n{asm_string}\n{suffix}"

def _root_.main (args : List String) : IO Unit := do
  let some input_file := args[0]? | panic! "input file does not exist"
  let input_program ← IO.FS.readFile ⟨input_file⟩
  let expr := match parse_expr.run input_program with | .ok expr => expr | .error e => panic! s!"parse failed due to error: {e}"
  let program := compile_prog expr
  println! "{program}"
