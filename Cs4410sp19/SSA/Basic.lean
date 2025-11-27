import Cs4410sp19.Basic
import Cs4410sp19.ANF.Basic
import Cs4410sp19.Cont
import Cs4410sp19.Parser
import Cs4410sp19.ANF

namespace Cs4410sp19
namespace SSA

inductive ConstVal where
  | int : Int → ConstVal
  | bool : Bool → ConstVal
deriving Inhabited, Repr, BEq

structure VarName where
  name : String
deriving Inhabited, Repr, BEq, Hashable

instance : ToString ConstVal where
  toString
    | .int x => s!"{x}"
    | .bool x => s!"{x}"

instance : ToString VarName where
  toString x := s!"{x.name}"

local instance : ToString Prim2 where
  toString
    | Prim2.eq      => "=="
    | Prim2.ne      => "!="
    | Prim2.ge      => ">="
    | Prim2.gt      => ">"
    | Prim2.le      => "<="
    | Prim2.lt      => "<"
    | Prim2.lor     => "||"
    | Prim2.land    => "&&"
    | Prim2.times   => "*"
    | Prim2.minus   => "-"
    | Prim2.plus    => "+"

local instance : ToString Prim1 where
  toString
    | Prim1.neg => "-"
    | Prim1.snd => "snd"
    | Prim1.fst => "fst"
    | Prim1.not => "!"

inductive Inst (σ : Type) (γ : Type) (δ : Type) (α : Type) where
  | assign : σ → δ → α → Inst σ γ δ α
  | prim2 : σ → δ → Prim2 → α → α → Inst σ γ δ α
  | prim1 : σ → δ → Prim1 → α → Inst σ γ δ α
  | call : σ → δ → String → List α → Inst σ γ δ α
  | mk_tuple : σ → δ → List α → Inst σ γ δ α
  | get_item : σ → δ → α → Nat → Nat → Inst σ γ δ α
  | pc : σ → List (δ × α) → Inst σ γ δ α
  | get_arg : σ → δ → Nat → Inst σ γ δ α
deriving Inhabited, Repr, BEq

/- Terminal: extracted branching/jump/return instructions -/
inductive Terminal (σ : Type) (γ : Type) (α : Type) where
  | jmp  : σ → γ → List α → Terminal σ γ α
  | br   : σ → α → γ → List α → γ → List α → Terminal σ γ α
  | ret  : σ → α → Terminal σ γ α
deriving Inhabited, Repr, BEq

instance [ToString σ] [ToString γ] [ToString α] : ToString (Terminal σ γ α) where
  toString
    | .jmp tag target args => s!"{tag}:\tjmp {target}({String.intercalate ", " (args.map ToString.toString)})"
    | .br tag cond btrue targs bfalse fargs => s!"{tag}:\tbr {cond} {btrue}({String.intercalate ", " (targs.map ToString.toString)}) {bfalse}({String.intercalate ", " (fargs.map ToString.toString)})"
    | .ret tag value => s!"{tag}:\tret {value}"

instance (priority := high) [ToString γ] [ToString α] : ToString (Terminal Unit γ α) where
  toString
    | .jmp _ target args => s!"    jmp {target}({String.intercalate ", " (args.map ToString.toString)})"
    | .br _ cond btrue targs bfalse fargs => s!"    br {cond} {btrue}({String.intercalate ", " (targs.map ToString.toString)}) {bfalse}({String.intercalate ", " (fargs.map ToString.toString)})"
    | .ret _ value => s!"    ret {value}"


def Terminal.get_branching_args! [BEq γ] : Terminal σ γ α → γ → Nat → List α := fun t b i =>
  let error_no_block (_ : Unit) := panic! s!"{decl_name%}: no such block"
  match t with
  | .jmp _ target args =>
    assert! i == 0
    if target == b then args else error_no_block ()
  | .br _ _ btrue targs bfalse fargs =>
    if i == 0 then
      assert! btrue == b
      targs
    else if i == 1 then
      assert! bfalse == b
      fargs
    else error_no_block ()
  | .ret _ _ => panic! s!"{decl_name%}: instruction is not supported"

def Terminal.set_branching! [BEq γ] [Inhabited σ] [Inhabited γ] [Inhabited α] : Terminal σ γ α → γ → γ → Nat → List α → Terminal σ γ α := fun t b b' i args' =>
  let error_no_block (_ : Unit) := panic! s!"{decl_name%}: no such block"
  match t with
  | .jmp tag target _ =>
    assert! i == 0
    if target == b then .jmp tag b' args' else error_no_block ()
  | .br tag cond btrue targs bfalse fargs =>
    if i == 0 then
      assert! btrue == b
      .br tag cond b' args' bfalse fargs
    else if i == 1 then
      assert! bfalse == b
      .br tag cond btrue targs b' args'
    else error_no_block ()
  | .ret _ _ => panic! s!"{decl_name%}: instruction is not supported"

@[always_inline, specialize]
def Terminal.mapM_src [Monad m] (f : α → m β) : Terminal σ γ α → m (Terminal σ γ β) := fun t => do
  match t with
  | .jmp tag tgt xs => return .jmp tag tgt (← xs.mapM f)
  | .br tag cond bt targs bf fargs => return .br tag (← f cond) bt (← targs.mapM f) bf (← fargs.mapM f)
  | .ret tag v => return .ret tag (← f v)

@[always_inline, specialize]
def Terminal.map_src (f : α → β) : Terminal σ γ α → Terminal σ γ β := fun t => t.mapM_src (m := Id) f

@[always_inline, specialize]
def Terminal.replace_src (f : α → Option α) : Terminal σ γ α → Terminal σ γ α
  | .jmp tag tgt xs => .jmp tag tgt (xs.map fun x => (f x).getD x)
  | .br tag cond bt targs bf fargs => .br tag ((f cond).getD cond) bt (targs.map fun x => (f x).getD x) bf (fargs.map fun x => (f x).getD x)
  | .ret tag v => .ret tag ((f v).getD v)

@[always_inline, specialize]
def Terminal.replace_src_by [BEq α] (a b : α) : Terminal σ γ α → Terminal σ γ α := fun t =>
  t.replace_src (fun x => if x == a then some b else Option.none)

def Inst.output_operands : Inst σ γ δ α → List δ
  | .assign _ n _       => [n]
  | .prim2 _ n _ _ _    => [n]
  | .prim1 _ n _ _      => [n]
  | .call _ n _ _       => [n]
  | .mk_tuple _ n _     => [n]
  | .get_item _ n _ _ _ => [n]
  | .pc _ xs            => xs.unzip.fst
  | .get_arg _ n _      => [n]

def Inst.input_operands : Inst σ γ δ α → List α
  | .assign _ _ v       => [v]
  | .prim2 _ _ _ x y    => [x, y]
  | .prim1 _ _ _ x      => [x]
  | .call _ _ _ xs      => xs
  | .mk_tuple _ _ xs    => xs
  | .get_item _ _ v _ _ => [v]
  | .pc _ xs            => xs.unzip.snd
  | .get_arg _ _ _      => []

def Inst.tag : Inst σ γ δ α → σ
  | .assign tag _ _       => tag
  | .prim2 tag _ _ _ _    => tag
  | .prim1 tag _ _ _      => tag
  | .call tag _ _ _       => tag
  | .mk_tuple tag _ _     => tag
  | .get_item tag _ _ _ _ => tag
  | .pc tag _             => tag
  | .get_arg tag _ _      => tag

def Inst.setTag : Inst σ γ δ α → σ' → Inst σ' γ δ α
  | .assign _ n v,                tag => .assign tag n v
  | .prim2 _ n op x y,            tag => .prim2 tag n op x y
  | .prim1 _ n op x,              tag => .prim1 tag n op x
  | .call _ n fn xs,              tag => .call tag n fn xs
  | .mk_tuple _ n xs,             tag => .mk_tuple tag n xs
  | .get_item _ n v i size,       tag => .get_item tag n v i size
  | .pc _ xs,                     tag => .pc tag xs
  | .get_arg _ n i,               tag => .get_arg tag n i

-- branching is represented in `BasicBlock.terminal` now

private def pp_block_args [ToString α] : List α → String
  | [] => ""
  | args => s!"({String.intercalate ", " (args.map ToString.toString)})"

private def is_infix : Prim2 → Bool := fun _ => true -- true for all now

def Inst.toString [ToString σ] [ToString γ] [ToString δ] [ToString α] : Inst σ γ δ α → String
  | .assign tag n v                 => s!"{tag}:\t{n} ← {v}"
  | .prim2 tag n op x y             =>
    if is_infix op then
      s!"{tag}:\t{n} ← {x} {op} {y}"
    else
      s!"{tag}:\t{n} ← op({op})({x}, {y})"
  | .prim1 tag n op x               => s!"{tag}:\t{n} ← op({op}) {x}"
  | .call tag n fn xs               => s!"{tag}:\t{n} ← call {fn}({String.intercalate ", " (xs.map ToString.toString)})"
  | .mk_tuple tag n xs              => s!"{tag}:\t{n} ← tuple ({String.intercalate ",    " (xs.map ToString.toString)})"
  | .get_item tag n v i size        => s!"{tag}:\t{n} ← tuple_get ({i} of {size}) {v}"
  | .pc tag xs                      => s!"{tag}:\tpc \{ {String.intercalate ",           " (xs.map fun (d, a) => s!"{d} ← {a}")} }"
  | .get_arg tag n i                => s!"{tag}:\t{n} ← get_arg {i}"

def Inst.toString' [ToString γ] [ToString δ] [ToString α] : Inst σ γ δ α → String
  | .assign _ n v                   => s!"    {n} ← {v}"

  | .prim2 _ n op x y               =>
    if is_infix op then
      s!"    {n} ← {x} {op} {y}"
    else
      s!"    {n} ← op({op})({x}, {y})"
  | .prim1 _ n op x                 => s!"    {n} ← op({op}) {x}"
  | .call _ n fn xs                 => s!"    {n} ← call {fn}({String.intercalate ", " (xs.map ToString.toString)})"
  | .mk_tuple _ n xs                => s!"    {n} ← tuple ({String.intercalate ", " (xs.map ToString.toString)})"
  | .get_item _ n v i size          => s!"    {n} ← tuple_get ({i} of {size}) {v}"
  | .pc _ xs                        => s!"    pc \{ {String.intercalate "," (xs.map fun (d, a) => s!"{d} ← {a}")} }"
  | .get_arg _ n i                  => s!"    {n} ← get_arg {i}"

scoped instance (priority := low) [ToString σ] [ToString γ] [ToString δ] [ToString α] : ToString (Inst σ γ δ α) := ⟨Inst.toString⟩

scoped instance (priority := high) [ToString γ] [ToString δ] [ToString α] : ToString (Inst Unit γ δ α) := ⟨Inst.toString'⟩

structure BasicBlock σ γ δ α where
  id : γ
  params : List VarName
  insts : Array (Inst σ γ δ α)
  terminal : Terminal σ γ α
deriving Inhabited, Repr

-- def BasicBlock.head! [Inhabited σ] [Inhabited γ] [Inhabited δ] [Inhabited α] : BasicBlock σ γ δ α → Inst σ γ δ α := fun b =>
--   assert! !b.insts.isEmpty
--   b.insts[0]!

-- def BasicBlock.back! [Inhabited σ] [Inhabited γ] [Inhabited δ] [Inhabited α] : BasicBlock σ γ δ α → Inst σ γ δ α := fun b =>
--   assert! !b.insts.isEmpty
--   b.insts.back!

structure Edge (γ α : Type) where
  idx : Nat
  start : γ
  target : γ
  args : List α
deriving Inhabited, Repr

def BasicBlock.succ : BasicBlock σ γ δ α → List (Edge γ α) := fun b =>
  match b.terminal with
  | .jmp _ target args => [⟨0, b.id, target, args⟩]
  | .br _ _ btrue targs bfalse fargs => [⟨0, b.id, btrue, targs⟩, ⟨1, b.id, bfalse, fargs⟩]
  | .ret .. => []

structure CFG σ γ δ α where
  name : String
  blocks : Array (BasicBlock σ γ δ α)
deriving Inhabited, Repr

inductive Operand where
  | var : VarName → Operand
  | param : VarName → Operand
  | const : ConstVal → Operand
deriving Inhabited, Repr, BEq

instance : ToString Operand where
  toString
    | .var name => s!"{name}"
    | .param name => s!"${name}"
    | .const x => s!"{x}"

-- private def CFG.edges [Hashable γ] [BEq γ] : CFG σ γ δ α → Array (γ × γ × Nat) := fun cfg => Id.run do
--   let mut es : Array (γ × γ × Nat) := {}
--   for node in cfg.blocks do
--     match node.terminal with
--     | .jmp _ target _ =>
--       es := es.push (node.id, target, 0)
--     | .br _ _ btrue _ bfalse _ =>
--       es := es.push (node.id, btrue, 0)
--       es := es.push (node.id, bfalse, 1)
--     | .ret _ _ => pure ()
--   return es

-- private def CFG.successors [Hashable γ] [BEq γ] : CFG σ γ δ α → Std.HashMap γ (Array (γ × Nat)) := fun cfg =>
--   let es := CFG.edges cfg
--   let t := es.groupByKey (fun (k, _) => k)
--   t.map fun _ v => v.unzip.snd.toList.mergeSort (fun (_, k1) (_, k2) => k1 ≤ k2) |>.toArray

-- private def CFG.predecessors [Hashable γ] [BEq γ] : CFG σ γ δ α → Std.HashMap γ (Array (γ × Nat)) := fun cfg =>
--   let es := CFG.edges cfg
--   let t := es.groupByKey (fun (_, k, _) => k)
--   t.map fun _ v => v.map (fun (x, _, i) => (x, i)) |>.toList.mergeSort (fun (_, k1) (_, k2) => k1 ≤ k2) |>.toArray

structure CFG.Config (σ γ δ α : Type) [Hashable γ] [BEq γ] where
  /-- sorted -/
  protected successors : Std.HashMap γ (List (Edge γ α))
  /-- sorted -/
  protected predecessors : Std.HashMap γ (List (Edge γ α))
  protected quick_table : Std.HashMap γ (BasicBlock σ γ δ α)
deriving Inhabited, Repr

private def CFG.config [Hashable γ] [BEq γ] : CFG σ γ δ α → CFG.Config σ γ δ α := fun cfg =>
  let quick_table := Std.HashMap.ofList <| Array.toList <| cfg.blocks.map fun x => (x.id, x)
  let ss := Std.HashMap.ofList <| cfg.blocks.toList.map fun b => (b.id, b.succ)
  let ps := cfg.blocks.toList.flatMap (fun b => b.succ) |>.groupByKey fun x => x.target
  ⟨ss, ps, quick_table⟩

/-- Bundled version of `CFG` so we won't recompute the edges again and again.
The default value of `config` allows *implicitly* rebuilding when reconstructing the struct.
-/
structure CFG' σ γ δ α [Hashable γ] [BEq γ] extends CFG σ γ δ α where
  config : CFG.Config σ γ δ α := toCFG.config
deriving Inhabited, Repr

def CFG'.get? [Hashable γ] [BEq γ] : CFG' σ γ δ α → γ → Option (BasicBlock σ γ δ α) := fun cfg id => cfg.config.quick_table[id]?

def CFG'.get! [Hashable γ] [BEq γ] [Inhabited σ] [Inhabited γ] [Inhabited δ] [Inhabited α] : CFG' σ γ δ α → γ → BasicBlock σ γ δ α := fun cfg id =>
  match cfg.get? id with
  | none => panic! "CFG'.get!: quick lookup failed"
  | some x => x

-- instance [Monad m] : ForIn m (BasicBlock σ γ α) (Inst σ γ δ α) where
--   forIn block b f := ForIn.forIn (m := m) (ρ := Array (Inst σ γ δ α)) block.insts b f

-- instance {m σ γ α} [Monad m] : ForIn m (CFG σ γ α) (Inst σ γ δ α) where
  -- forIn cfg b f := do
  --   let mut b := b
  --   for b' in cfg.blocks do
  --     b ← ForIn.forIn (m := m) (ρ := BasicBlock σ γ α) b' b f
  --   return b

@[always_inline, specialize]
def Inst.mapM_src [Monad m] (f : α → m β) : Inst σ γ δ α → m (Inst σ γ δ β) := fun e => do
  match e with
  | .assign tag n v                => return .assign tag n (← f v)
  | .prim2 tag n op x y            => return .prim2 tag n op (← f x) (← f y)
  | .prim1 tag n op x              => return .prim1 tag n op (← f x)
  | .call tag n fn xs              => return .call tag n fn (← xs.mapM f)
  | .mk_tuple tag n xs             => return .mk_tuple tag n (← xs.mapM f)
  | .get_item tag n v i size       => return .get_item tag n (← f v) i size
  | .pc tag xs                     => return .pc tag (← xs.mapM fun (d, x) => (d, ·) <$> f x)
  | .get_arg tag n i               => return .get_arg tag n i

@[always_inline, specialize]
def Inst.mapM_dst [Monad m] (f : δ → m δ') : Inst σ γ δ α → m (Inst σ γ δ' α) := fun e => do
  match e with
  | .assign tag n v                => return .assign tag (← f n) v
  | .prim2 tag n op x y            => return .prim2 tag (← f n) op x y
  | .prim1 tag n op x              => return .prim1 tag (← f n) op x
  | .call tag n fn xs              => return .call tag (← f n) fn xs
  | .mk_tuple tag n xs             => return .mk_tuple tag (← f n) xs
  | .get_item tag n v i size       => return .get_item tag (← f n) v i size
  | .pc tag xs                     => return .pc tag (← xs.mapM fun (d, x) => (·, x) <$> f d)
  | .get_arg tag n i               => return .get_arg tag (← f n) i

@[always_inline, specialize]
def Inst.map_src (f : α → β) : Inst σ γ δ α → Inst σ γ δ β := fun e => e.mapM_src (m := Id) f

@[always_inline, specialize]
def Inst.replace_src (f : α → Option α) : Inst σ γ δ α → Inst σ γ δ α := fun e => e.map_src ex
  where ex c := (f c).getD c

@[always_inline, specialize]
def Inst.replace_src_by [BEq α] (a b : α) : Inst σ γ δ α → Inst σ γ δ α := fun e =>
  Inst.replace_src (fun x => if x == a then some b else none) e

@[always_inline, specialize]
def Inst.instantiate_param (paramName : VarName) (value : Operand) : Inst σ γ δ Operand → Inst σ γ δ Operand := fun e =>
  e.replace_src (fun x => if x == .param paramName then some value else none)

@[always_inline, specialize]
def Inst.instantiate_params (xs : List (VarName × Operand)) : Inst σ γ δ Operand → Inst σ γ δ Operand := fun e =>
  e.replace_src fun
    | .param x => xs.lookup x
    | _ => none

@[always_inline, specialize]
def Terminal.instantiate_params (xs : List (VarName × Operand)) : Terminal σ γ Operand → Terminal σ γ Operand := fun t =>
  t.replace_src fun
    | .param x => xs.lookup x
    | _ => Option.none

@[always_inline, specialize]
def BasicBlock.mapM_src [Monad m] (f : α → m β) : BasicBlock σ γ δ α → m (BasicBlock σ γ δ β) := fun b => do
  -- let params' ← b.params.mapM f
  let insts' ← b.insts.mapM fun x => x.mapM_src f
  let terminal' ← b.terminal.mapM_src f
  return { b with params := b.params, insts := insts', terminal := terminal' }

@[always_inline, specialize]
def BasicBlock.map_src (f : α → β) : BasicBlock σ γ δ α → BasicBlock σ γ δ β := fun b => b.mapM_src (m := Id) f

@[always_inline, specialize]
def BasicBlock.replace_src (f : α → Option α) : BasicBlock σ γ δ α → BasicBlock σ γ δ α := fun b =>
  { b with insts := b.insts.map fun x => x.replace_src f, terminal := b.terminal.replace_src f }

def genvar [Monad m] [MonadNameGen m] (s : String) : m VarName := do
  let n ← gensym s
  return ⟨n⟩

protected def pp_insts [ToString σ] [ToString γ] [ToString δ] [ToString α] (insts : List (Inst σ γ δ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"
protected def pp_insts' [ToString γ] [ToString δ] [ToString α] (insts : List (Inst Unit γ δ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"

protected def pp_cfg [ToString σ] [ToString γ] [ToString δ] [ToString α] (cfg : CFG σ γ δ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    if i.params.isEmpty then
      store := store.push s!"{i.id}:"
    else
      store := store.push s!"{i.id}({String.intercalate ", " (i.params.map (s!"${·}"))}):"
    store := store.append (i.insts.map Inst.toString)
    store := store.push s!"{i.terminal}"
  return String.intercalate "\n" store.toList

protected def pp_cfg' [ToString γ] [ToString δ] [ToString α] (cfg : CFG Unit γ δ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    if i.params.isEmpty then
      store := store.push s!"{i.id}:"
    else
      store := store.push s!"{i.id}({String.intercalate ", " (i.params.map (s!"${·}"))}):"
    store := store.append (i.insts.map Inst.toString')
    store := store.push s!"{i.terminal}"
  return String.intercalate "\n" store.toList
