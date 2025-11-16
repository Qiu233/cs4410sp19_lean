
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

inductive Expr (α : Type) where
  | num : α → Int → Expr α
  | id : α → String → Expr α
  | let_in : α → String → Expr α → Expr α → Expr α
  | prim1 : α → Prim1 → Expr α → Expr α
  | prim2 : α → Prim2 → Expr α → Expr α → Expr α
  | ite : α → Expr α → Expr α → Expr α → Expr α
  | bool : α → Bool → Expr α
  | call : α → String → List (Expr α) → Expr α
deriving Inhabited, Repr

def Expr.tag : Expr α → α
  | num x ..
  | id x ..
  | let_in x ..
  | prim1 x ..
  | prim2 x ..
  | ite x ..
  | bool x ..
  | call x .. => x

partial def Expr.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Expr α → m (Expr β) := fun e =>
  match e with
  | num tag x => return num (← f tag) x
  | bool tag x => return bool (← f tag) x
  | id tag name => return id (← f tag) name
  | let_in tag name value kont =>
    return let_in (← f tag) name (← Expr.mapM f value) (← Expr.mapM f kont)
  | prim1 tag op x =>
    return prim1 (← f tag) op (← Expr.mapM f x)
  | prim2 tag op x y =>
    return prim2 (← f tag) op (← Expr.mapM f x) (← Expr.mapM f y)
  | ite tag cond bp bn =>
    return ite (← f tag) (← Expr.mapM f cond) (← Expr.mapM f bp) (← Expr.mapM f bn)
  | call tag name xs =>
    return call (← f tag) name (← xs.mapM (fun x => Expr.mapM f x))

def Expr.unsetTag : Expr α → Expr Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

structure FuncDef where
  name : String
  params : List String
  body : Expr String.Pos

inductive Decl where
  | function : FuncDef → Decl

def Decl.name : Decl → String
  | .function f => f.name

structure Program (α : Type) where
  decls : Array Decl
  exe_code : Expr α

def Program.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Program α → m (Program β) := fun p => do
  let r ← p.exe_code.mapM f
  return Program.mk p.decls r

def Program.unsetTag : Program α → Program Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

inductive ImmExpr (α : Type) where
  | num   : α → Int → ImmExpr α
  | bool  : α → Bool → ImmExpr α
  | id    : α → String → ImmExpr α
deriving Inhabited, Repr

def ImmExpr.tag : ImmExpr α → α
  | .num x ..
  | .bool x ..
  | .id x .. => x

partial def ImmExpr.mapM {α β} {m : Type → Type} [Monad m] (f : α → m β) : ImmExpr α → m (ImmExpr β)
  | num tag x => return num (← f tag) x
  | bool tag x => return bool (← f tag) x
  | id tag name => return id (← f tag) name

def ImmExpr.unsetTag : ImmExpr α → ImmExpr Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

mutual

inductive CExpr (α : Type) where
  | prim1 : α → Prim1 → ImmExpr α → CExpr α
  | prim2 : α → Prim2 → ImmExpr α → ImmExpr α → CExpr α
  | ite   : α → ImmExpr α → AExpr α → AExpr α → CExpr α
  | call  : α → String → List (ImmExpr α) → CExpr α
  | imm   : ImmExpr α → CExpr α
deriving Inhabited, Repr

inductive AExpr (α : Type) where
  | let_in : α → String → CExpr α → AExpr α → AExpr α
  | cexpr : CExpr α → AExpr α
deriving Inhabited, Repr

end

def CExpr.tag : CExpr α → α
  | .prim1 x ..
  | .prim2 x ..
  | .ite x ..
  | .call x .. => x
  | .imm x => x.tag

def AExpr.tag : AExpr α → α
  | .let_in x .. => x
  | .cexpr x => x.tag

mutual

partial def CExpr.mapM {α β} [Inhabited β] {m : Type → Type} [Monad m] (f : α → m β) : CExpr α → m (CExpr β) := fun e => do
  match e with
  | .imm x => return .imm (← x.mapM f)
  | .prim1 tag op x =>
    return .prim1 (← f tag) op (← x.mapM f)
  | .prim2 tag op x y =>
    return .prim2 (← f tag) op (← x.mapM f) (← y.mapM f)
  | .ite tag cond bp bn =>
    return .ite (← f tag) (← cond.mapM f) (← bp.mapM f) (← bn.mapM f)
  | .call tag name xs =>
    return .call (← f tag) name (← xs.mapM (fun x => x.mapM f))

partial def AExpr.mapM {α β} [Inhabited β] {m : Type → Type} [Monad m] (f : α → m β) : AExpr α → m (AExpr β) := go
where
  go e := do
    match e with
    | .let_in tag name value kont =>
      return .let_in (← f tag) name (← value.mapM f) (← go kont)
    | .cexpr c => return .cexpr <| ← c.mapM f

end

def CExpr.unsetTag : CExpr α → CExpr Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

def AExpr.unsetTag : AExpr α → AExpr Unit := fun e => Id.run <| e.mapM (fun _ => pure ())
