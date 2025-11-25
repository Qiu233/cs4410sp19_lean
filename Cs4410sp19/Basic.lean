import Std
namespace Cs4410sp19

inductive Reg where
  | eax
  | esp
  | ebp
  | esi
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
  | .esi => "esi"

instance : ToString Arg where
  toString
  | .const v => s!"{v}"
  | .reg r => s!"{r}"
  | .reg_offset r i => s!"dword [{r} + 4 * {i}]"

instance : ToString Instruction where
  toString
  | .mov dst src    => s!"\tmov {dst}, {src}"
  | .push src       => s!"\tpush {src}"
  | .pop src        => s!"\tpop {src}"
  | .call dst       => s!"\tcall {dst}"
  | .ret            => s!"\tret"
  | .add dst src    => s!"\tadd {dst}, {src}"
  | .sub dst src    => s!"\tsub {dst}, {src}"
  | .mul src        => s!"\tmul {src}"
  | .shl dst bits   => s!"\tshl {dst}, {bits}"
  | .shr dst bits   => s!"\tshr {dst}, {bits}"
  | .sar dst bits   => s!"\tsar {dst}, {bits}"
  | .and dst src    => s!"\tand {dst}, {src}"
  | .or dst src     => s!"\tor {dst}, {src}"
  | .xor dst src    => s!"\txor {dst}, {src}"
  | .label name     => s!"{name}:"
  | .cmp x y        => s!"\tcmp {x}, {y}"
  | .test x y       => s!"\ttest {x}, {y}"
  | .jmp name       => s!"\tjmp {name}"
  | .je name        => s!"\tje {name}"
  | .jl name        => s!"\tjl {name}"
  | .jle name       => s!"\tjle {name}"
  | .jg name        => s!"\tjg {name}"
  | .jge name       => s!"\tjge {name}"
  | .jz name        => s!"\tjz {name}"
  | .jnz name       => s!"\tjnz {name}"

def asm_to_string : Array Instruction → String := fun xs =>
  String.intercalate "\n" (xs.map toString).toList

inductive Prim1 where
  | neg | not
  | fst | snd
deriving Inhabited, Repr, BEq

inductive Prim2 where
  | plus | minus | times
  | land | lor | lt | le | gt | ge | eq | ne
deriving Inhabited, Repr, BEq

inductive Typ (α : Type) where
  | var : α → String → Typ α
  | const : α → String → Typ α
  | arrow : List (Typ α) → Typ α → Typ α
  | app : Typ α → List (Typ α) → Typ α
  | tuple : α → List (Typ α) → Typ α
deriving Inhabited, Repr

partial def Typ.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Typ α → m (Typ β)
  | var tag x => return var (← f tag) x
  | const tag x => return const (← f tag) x
  | arrow args result => return arrow (← args.mapM (Typ.mapM f)) (← Typ.mapM f result)
  | app ctor args => return app (← Typ.mapM f ctor) (← args.mapM (Typ.mapM f))
  | tuple tag xs => return tuple (← f tag) (← xs.mapM (Typ.mapM f))
def Typ.unsetTag : Typ α → Typ Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

structure TypeScheme where
  params : List String
  body : Typ Unit
deriving Inhabited, Repr

def TypeScheme.arity : TypeScheme → Nat := fun s => s.params.length

inductive Expr (α : Type) where
  | num : α → Int → Expr α
  | id : α → String → Expr α
  | let_in : α → String → Option (Typ α) → Expr α → Expr α → Expr α
  | prim1 : α → Prim1 → Expr α → Expr α
  | prim2 : α → Prim2 → Expr α → Expr α → Expr α
  | ite : α → Expr α → Expr α → Expr α → Expr α
  | bool : α → Bool → Expr α
  | call : α → String → List (Expr α) → Expr α
  | tuple : α → List (Expr α) → Expr α
  | get_item : α → Expr α → Nat → Nat → Expr α
deriving Inhabited, Repr

def Expr.tag : Expr α → α
  | num x ..
  | id x ..
  | let_in x ..
  | prim1 x ..
  | prim2 x ..
  | ite x ..
  | bool x ..
  | tuple x ..
  | get_item x ..
  | call x .. => x

partial def Expr.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Expr α → m (Expr β) := fun e =>
  match e with
  | num tag x => return num (← f tag) x
  | bool tag x => return bool (← f tag) x
  | id tag name => return id (← f tag) name
  | let_in tag name type value kont =>
    return let_in (← f tag) name (← type.mapM fun x => x.mapM f) (← Expr.mapM f value) (← Expr.mapM f kont)
  | prim1 tag op x =>
    return prim1 (← f tag) op (← Expr.mapM f x)
  | prim2 tag op x y =>
    return prim2 (← f tag) op (← Expr.mapM f x) (← Expr.mapM f y)
  | ite tag cond bp bn =>
    return ite (← f tag) (← Expr.mapM f cond) (← Expr.mapM f bp) (← Expr.mapM f bn)
  | call tag name xs =>
    return call (← f tag) name (← xs.mapM (fun x => Expr.mapM f x))
  | tuple tag xs =>
    return tuple (← f tag) (← xs.mapM (Expr.mapM f))
  | get_item tag x i n =>
    return get_item (← f tag) (← Expr.mapM f x) i n

def Expr.unsetTag : Expr α → Expr Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

def Expr.setTag : Expr α → α → Expr α
  | .num _ x, tag => .num tag x
  | .bool _ x, tag => .bool tag x
  | .id _ name, tag => .id tag name
  | .let_in _ name type value kont, tag => .let_in tag name type value kont
  | .prim1 _ op x, tag => .prim1 tag op x
  | .prim2 _ op x y, tag => .prim2 tag op x y
  | .ite _ cond bp bn, tag => .ite tag cond bp bn
  | .call _ name xs, tag => .call tag name xs
  | .tuple _ xs, tag => .tuple tag xs
  | .get_item _ x i n, tag => .get_item tag x i n

structure FuncDef α where
  name : String
  body : Expr α
  params : List (String × Option (Typ α))
  ret_type? : Option (Typ α)
deriving Inhabited, Repr

def FuncDef.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : FuncDef α → m (FuncDef β) := fun ⟨name, body, params, ret_type?⟩ => do
  let body' ← body.mapM f
  let params' ← params.mapM fun (x, y) => (x, ·) <$> y.mapM fun t => t.mapM f
  let ret_type?' ← ret_type?.mapM fun x => x.mapM f
  return ⟨name, body', params', ret_type?'⟩

def FuncDef.unsetTag : FuncDef α → FuncDef Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

inductive Decl α where
  | function : α → FuncDef α → Decl α
deriving Inhabited, Repr

def Decl.name : Decl α → String
  | .function _ f => f.name

def Decl.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Decl α → m (Decl β)
  | .function tag d => .function <$> f tag <*> d.mapM f

def Decl.unsetTag : Decl α → Decl Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

structure MutualDecl α where
  tag : α
  decls : List (Decl α)
deriving Inhabited, Repr

def MutualDecl.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : MutualDecl α → m (MutualDecl β) := fun p => do
  let tag' ← f p.tag
  let decls' ← (p.decls.mapM fun x => x.mapM f)
  return MutualDecl.mk tag' decls'

def MutualDecl.unsetTag : MutualDecl α → MutualDecl Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

structure Program (α : Type) where
  tag : α
  decls : Array (MutualDecl α)
  exe_code : Expr α
deriving Inhabited, Repr

def Program.mapM {α β} {m : Type → Type} [Inhabited β] [Monad m] (f : α → m β) : Program α → m (Program β) := fun p => do
  let tag' ← f p.tag
  let decls' ← (p.decls.mapM fun x => x.mapM f)
  let r ← p.exe_code.mapM f
  return Program.mk tag' decls' r

def Program.unsetTag : Program α → Program Unit := fun e => Id.run <| e.mapM (fun _ => pure ())

class MonadNameGen (m : Type → Type) where
  gensym : String → m String

export MonadNameGen (gensym)

instance {m n} [MonadLift m n] [inst : MonadNameGen m] : MonadNameGen n where
  gensym x := MonadLift.monadLift (inst.gensym x)

structure NameGen where
  names : Std.HashMap String Nat := {}

abbrev FreshM := StateM NameGen

def FreshM.run (x : FreshM α) (ng : NameGen) : (α × NameGen) := StateT.run x ng

def FreshM.gensym (pref : String) : FreshM String := do
  let count ← modifyGet (fun s =>
    let names' := s.names.alter pref (fun | .none => .some 0 | .some x => .some x)
    (names'[pref]!, { s with names := names'.modify pref (· + 1) }))
  let name := s!"{pref}.{count}"
  return name

instance : MonadNameGen FreshM where
  gensym := FreshM.gensym

-- structure Lens (m : Type → Type) (σ : Type) (α : Type) where
--   get : σ → m α
--   set : σ → α → m σ

-- class NameLens (m : Type → Type) (σ : Type) extends ForIn m σ (Lens m σ String) where

-- def NameLens.normalize [Monad m] [MonadNameGen m] (lens : NameLens m σ) (pref : String) : σ → m σ := fun input => do
--   let lenses ← lens.toForIn.forIn (β := Array (Lens m σ String)) input {} (fun n b => pure (.yield <| b.push n))
--   let mut rn : Std.HashMap String String := {}
--   let mut t := input
--   for lens in lenses do
--     let v ← lens.get t
--     if let some r := rn[v]? then
--       t ← lens.set t r
--     else
--       let new ← gensym pref
--       rn := rn.insert v new
--       t ← lens.set t new
--   return t
