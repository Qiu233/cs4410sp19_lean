import Cs4410sp19.Basic
import Cs4410sp19.Compile.Basic

namespace Cs4410sp19

inductive ImmExpr (α : Type) where
  | num   : α → Int → ImmExpr α
  | bool  : α → Bool → ImmExpr α
  | id    : α → String → ImmExpr α
deriving Inhabited, Repr

def ImmExpr.tag : ImmExpr α → α
  | .num x ..
  | .bool x ..
  | .id x .. => x

def ImmExpr.setTag : ImmExpr α → α → ImmExpr α
  | num _ x, tag => .num tag x
  | bool _ x, tag => .bool tag x
  | id _ name, tag => .id tag name

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

def CExpr.setTag : CExpr α → α → CExpr α
  | prim1 _ op x, tag => .prim1 tag op x
  | prim2 _ op x y, tag => .prim2 tag op x y
  | ite _ cond bp bn, tag => .ite tag cond bp bn
  | call _ name xs, tag => .call tag name xs
  | imm x, tag => .imm (x.setTag tag)

def AExpr.tag : AExpr α → α
  | .let_in x .. => x
  | .cexpr x => x.tag

def AExpr.setTag : AExpr α → α → AExpr α
  | .let_in _ name value kont, tag => .let_in tag name value kont
  | .cexpr x, tag => .cexpr (x.setTag tag)

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

structure AFuncDef α where
  name : String
  params : List String
  body : AExpr α

def AFuncDef.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : AFuncDef α → m (AFuncDef β) :=
  fun ⟨name, params, body⟩ => do return ⟨name, params, ← body.mapM f⟩

def AFuncDef.unsetTag : AFuncDef α → AFuncDef Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

inductive ADecl α where
  | function : α → AFuncDef α → ADecl α

def ADecl.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : ADecl α → m (ADecl β)
  | .function tag d => .function <$> f tag <*> d.mapM f

def ADecl.unsetTag : ADecl α → ADecl Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

def ADecl.setTag : ADecl α → α → ADecl α
  | .function _ f, tag => .function tag f

def ADecl.name : ADecl α → String
  | .function _ f => f.name

structure AMutualDecl α where
  tag : α
  decls : List (ADecl α)

def AMutualDecl.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : AMutualDecl α → m (AMutualDecl β) := fun p => do
  let tag' ← f p.tag
  let decls' ← (p.decls.mapM fun x => x.mapM f)
  return AMutualDecl.mk tag' decls'

def AMutualDecl.unsetTag : AMutualDecl α → AMutualDecl Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

structure AProgram (α : Type) where
  tag : α
  decls : Array (AMutualDecl α)
  exe_code : AExpr α

def AProgram.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : AProgram α → m (AProgram β) := fun p => do
  let tag' ← f p.tag
  let decls' ← (p.decls.mapM fun x => x.mapM f)
  let r ← p.exe_code.mapM f
  return AProgram.mk tag' decls' r

def AProgram.unsetTag : AProgram α → AProgram Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

def AProgram.setTag : AProgram α → α → AProgram α := fun p tag => { p with tag := tag }
