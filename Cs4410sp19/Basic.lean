
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
  | mul : Arg → Instruction
  | label : String → Instruction
  | cmp : Arg → Arg → Instruction
  | jmp : String → Instruction
  | je : String → Instruction
deriving Inhabited

instance : ToString Reg where
  toString
  | .eax => "eax"
  | .esp => "esp"

instance : ToString Arg where
  toString
  | .const v => s!"{v}"
  | .reg r => s!"{r}"
  | .reg_offset r i => s!"dword [{r} + 4 * {i}]"

instance : ToString Instruction where
  toString
  | .mov dst src => s!"mov {dst}, {src}"
  | .add dst src => s!"add {dst}, {src}"
  | .sub dst src => s!"sub {dst}, {src}"
  | .mul src => s!"mul {src}"
  | .label name => s!"{name}:"
  | .cmp x y => s!"cmp {x}, {y}"
  | .jmp name => s!"jmp {name}"
  | .je name => s!"je {name}"

def asm_to_string : Array Instruction → String := fun xs =>
  String.intercalate "\n" (xs.map toString).toList

inductive Prim2 where
  | plus | minus | times
deriving Inhabited, Repr

inductive Expr where
  | num : Int → Expr
  | id : String → Expr
  | let_in : String → Expr → Expr → Expr
  | prim2 : Prim2 → Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr
deriving Inhabited, Repr

def Expr.is_imm (e : Expr) : Bool :=
  match e with
  | .num _ | .id _ => true
  | _ => false

def Expr.is_anf (e : Expr) : Bool :=
  match e with
  | .prim2 _ x y => x.is_anf && y.is_anf
  | .let_in _ v k => v.is_anf && k.is_anf
  | .ite cond bp bn => cond.is_imm && bp.is_anf && bn.is_anf
  | _ => e.is_imm

inductive Expr.IsImm : Expr → Prop where
  | num x : IsImm (.num x)
  | id name : IsImm (.id name)

inductive Expr.IsANF : Expr → Prop where
  | of_imm {e} : Expr.IsImm e → e.IsANF
  | prim2 {op : Prim2} {x y : Expr} : x.IsImm → y.IsImm → (Expr.prim2 op x y).IsANF
  | let_in {name} {v k : Expr} : v.IsANF → k.IsANF → (Expr.let_in name v k).IsANF
  | ite {cond bp bn : Expr} : cond.IsImm → bp.IsANF → bn.IsANF → (Expr.ite cond bp bn).IsANF
