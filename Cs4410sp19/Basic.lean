
namespace Cs4410sp19

inductive Reg where
  | eax
  | esp
  | ebp
deriving Inhabited

inductive Arg where
  | const : Int → Arg
  | reg : Reg → Arg
  | reg_offset : Reg → Int → Arg
deriving Inhabited

inductive Instruction where
  | mov : Arg → Arg → Instruction
  | push : Arg → Instruction
  | pop : Arg → Instruction
  | call : String → Instruction
  | ret : Instruction
  | add : Arg → Arg → Instruction
  | sub : Arg → Arg → Instruction
  | mul : Arg → Instruction
  | shl : Arg → Arg → Instruction
  | shr : Arg → Arg → Instruction
  | sar : Arg → Arg → Instruction
  | and : Arg → Arg → Instruction
  | or : Arg → Arg → Instruction
  | xor : Arg → Arg → Instruction
  | label : String → Instruction
  | cmp : Arg → Arg → Instruction
  | test : Arg → Arg → Instruction
  | jmp : String → Instruction
  | je : String → Instruction
  | jl : String → Instruction
  | jle : String → Instruction
  | jg : String → Instruction
  | jge : String → Instruction
  | jz : String → Instruction
  | jnz : String → Instruction
deriving Inhabited

instance : ToString Reg where
  toString
  | .eax => "eax"
  | .esp => "esp"
  | .ebp => "ebp"

instance : ToString Arg where
  toString
  | .const v => s!"{v}"
  | .reg r => s!"{r}"
  | .reg_offset r i => s!"dword [{r} + 4 * {i}]"

instance : ToString Instruction where
  toString
  | .mov dst src => s!"mov {dst}, {src}"
  | .push src => s!"push {src}"
  | .pop src => s!"pop {src}"
  | .call dst => s!"call {dst}"
  | .ret => s!"ret"
  | .add dst src => s!"add {dst}, {src}"
  | .sub dst src => s!"sub {dst}, {src}"
  | .mul src => s!"mul {src}"
  | .shl dst bits => s!"shl {dst}, {bits}"
  | .shr dst bits => s!"shr {dst}, {bits}"
  | .sar dst bits => s!"sar {dst}, {bits}"
  | .and dst src => s!"and {dst}, {src}"
  | .or dst src => s!"or {dst}, {src}"
  | .xor dst src => s!"xor {dst}, {src}"
  | .label name => s!"{name}:"
  | .cmp x y => s!"cmp {x}, {y}"
  | .test x y => s!"test {x}, {y}"
  | .jmp name => s!"jmp {name}"
  | .je name => s!"je {name}"
  | .jl name => s!"jl {name}"
  | .jle name => s!"jle {name}"
  | .jg name => s!"jg {name}"
  | .jge name => s!"jge {name}"
  | .jz name => s!"jz {name}"
  | .jnz name => s!"jnz {name}"

def asm_to_string : Array Instruction → String := fun xs =>
  String.intercalate "\n" (xs.map toString).toList

inductive Prim1 where
  | neg | not
deriving Inhabited, Repr

inductive Prim2 where
  | plus | minus | times
  | land | lor | lt | le | gt | ge | eq | ne
deriving Inhabited, Repr

inductive Expr where
  | num : Int → Expr
  | id : String → Expr
  | let_in : String → Expr → Expr → Expr
  | prim1 : Prim1 → Expr → Expr
  | prim2 : Prim2 → Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | bool : Bool → Expr
  | call : String → List Expr → Expr
deriving Inhabited, Repr

structure Decl where
  name : String
  params : List String
  body : Expr

structure Program where
  decls : Array Decl
  exe_code : Expr

inductive Expr.IsImm : Expr → Prop where
  | num x : IsImm (.num x)
  | id name : IsImm (.id name)
  | bool x : IsImm (.bool x)

attribute [simp] Expr.IsImm.num Expr.IsImm.id Expr.IsImm.bool

inductive Expr.IsANF : Expr → Prop where
  | of_imm {e} : Expr.IsImm e → e.IsANF
  | prim1 {op : Prim1} {x : Expr} : x.IsImm → (Expr.prim1 op x).IsANF
  | prim2 {op : Prim2} {x y : Expr} : x.IsImm → y.IsImm → (Expr.prim2 op x y).IsANF
  | let_in {name} {v k : Expr} : v.IsANF → k.IsANF → (Expr.let_in name v k).IsANF
  | ite {cond bp bn : Expr} : cond.IsImm → bp.IsANF → bn.IsANF → (Expr.ite cond bp bn).IsANF
  | call {name args} : (∀ arg ∈ args, arg.IsImm) → (Expr.call name args).IsANF

instance Expr.IsImm.dec : DecidablePred Expr.IsImm := fun x => by
  cases x with
  | num _
  | id _
  | bool _ =>
    apply Decidable.isTrue; simp
  | _ =>
    apply Decidable.isFalse
    intro hn
    cases hn

local macro "neg!" : tactic => `(tactic| focus
  apply Decidable.isFalse
  intro hn
  cases hn
  contradiction
  contradiction)

instance Expr.IsANF.dec : DecidablePred Expr.IsANF := fun x => by
  if h : x.IsImm then
    apply Decidable.isTrue
    apply Expr.IsANF.of_imm h
  else
    cases x with
    | prim1 op x =>
      if h' : x.IsImm then
        apply Decidable.isTrue
        apply Expr.IsANF.prim1 h'
      else neg!
    | prim2 op x y =>
      if h1 : x.IsImm then
        if h2 : y.IsImm then
          apply Decidable.isTrue
          apply Expr.IsANF.prim2 h1 h2
        else neg!
      else neg!
    | let_in var value kont =>
      match Expr.IsANF.dec value, Expr.IsANF.dec kont with
      | .isFalse h1, _ => neg!
      | .isTrue h1, .isFalse _ => neg!
      | .isTrue h1, .isTrue h2 =>
        apply Decidable.isTrue
        apply Expr.IsANF.let_in h1 h2
    | ite cond bp bn =>
      match Expr.IsImm.dec cond, Expr.IsANF.dec bp, Expr.IsANF.dec bn with
      | .isFalse h1, _, _ => neg!
      | .isTrue h1, .isFalse h2, _ => neg!
      | .isTrue h1, .isTrue h2, .isFalse _ => neg!
      | .isTrue h1, .isTrue h2, .isTrue h3 =>
        apply Decidable.isTrue
        apply Expr.IsANF.ite h1 h2 h3
    | call name args =>
      have : Decidable (∀ x ∈ args, x.IsImm) := inferInstance
      cases this with
      | isFalse h' => neg!
      | isTrue h' =>
        apply Decidable.isTrue
        apply Expr.IsANF.call h'
    | _ =>
      apply Decidable.isFalse
      intro hn
      cases hn <;> contradiction
