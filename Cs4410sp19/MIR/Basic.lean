import Cs4410sp19.Basic
import Cs4410sp19.SSA.Basic
import Cs4410sp19.SSA.Construct
import Cs4410sp19.SSA.DeadBlock
import Cs4410sp19.SSA.TrivialBlock
import Cs4410sp19.SSA.BlockArgs
import Cs4410sp19.SSA.CopyPropagation

namespace Cs4410sp19
namespace MIR

inductive Inst (σ : Type) (γ : Type) (α : Type) where
  | mov : σ → α → α → Inst σ γ α

  | add : σ → α → α → α → Inst σ γ α
  | sub : σ → α → α → α → Inst σ γ α
  | mul : σ → α → α → α → Inst σ γ α

  | band : σ → α → α → α → Inst σ γ α
  | bor  : σ → α → α → α → Inst σ γ α
  -- | neg  : σ → α → α → Inst σ γ α

  -- | land : σ → α → α → α → Inst σ γ α
  -- | lor  : σ → α → α → α → Inst σ γ α
  | xor  : σ → α → α → α → Inst σ γ α

  | lt : σ → α → α → α → Inst σ γ α
  | le : σ → α → α → α → Inst σ γ α
  | gt : σ → α → α → α → Inst σ γ α
  | ge : σ → α → α → α → Inst σ γ α
  | eq : σ → α → α → α → Inst σ γ α
  | ne : σ → α → α → α → Inst σ γ α

  | push : σ → α → Inst σ γ α
  | pop  : σ → α → Inst σ γ α
  | pop'  : σ → Inst σ γ α

  | cmp  : σ → α → α → Inst σ γ α
  | test : σ → α → α → Inst σ γ α

  | shl : σ → α → α → α → Inst σ γ α
  | shr : σ → α → α → α → Inst σ γ α
  | sar : σ → α → α → α → Inst σ γ α

  | call : σ → α → String → List α → Inst σ γ α
  | call' : σ → String → Inst σ γ α
deriving Inhabited, Repr, BEq

def Inst.tag : Inst σ γ α → σ
  | .mov tag _ _             => tag
  | .add tag _ _ _           => tag
  | .sub tag _ _ _           => tag
  | .mul tag _ _ _           => tag
  | .band tag _ _ _          => tag
  | .bor  tag _ _ _          => tag
  -- | .neg  tag _ _            => tag
  -- | .land tag _ _ _          => tag
  -- | .lor  tag _ _ _          => tag
  | .xor  tag _ _ _            => tag
  | .lt tag _ _ _            => tag
  | .le tag _ _ _            => tag
  | .gt tag _ _ _            => tag
  | .ge tag _ _ _            => tag
  | .eq tag _ _ _            => tag
  | .ne tag _ _ _            => tag
  | .push tag _            => tag
  | .pop tag _             => tag
  | .pop' tag              => tag
  | .cmp tag _ _           => tag
  | .test tag _ _          => tag
  | .shl tag _ _ _           => tag
  | .shr tag _ _ _           => tag
  | .sar tag _ _ _           => tag
  | .call tag _ _ _         => tag
  | .call' tag _            => tag

def Inst.setTag : Inst σ γ α → σ' → Inst σ' γ α
  | .mov _ x y, tag => .mov tag x y
  | .add _ x y z, tag => .add tag x y z
  | .sub _ x y z, tag => .sub tag x y z
  | .mul _ x y z, tag => .mul tag x y z
  | .band _ x y z, tag => .band tag x y z
  | .bor  _ x y z, tag => .bor  tag x y z
  -- | .neg  _ x y, tag => .neg  tag x y
  -- | .land _ x y z, tag => .land tag x y z
  -- | .lor  _ x y z, tag => .lor  tag x y z
  | .xor  _ x y z, tag => .xor  tag x y z
  | .lt _ x y z, tag => .lt tag x y z
  | .le _ x y z, tag => .le tag x y z
  | .gt _ x y z, tag => .gt tag x y z
  | .ge _ x y z, tag => .ge tag x y z
  | .eq _ x y z, tag => .eq tag x y z
  | .ne _ x y z, tag => .ne tag x y z
  | .push _ x, tag => .push tag x
  | .pop  _ x, tag => .pop  tag x
  | .pop' _, tag => .pop'  tag
  | .cmp _ x y, tag => .cmp tag x y
  | .test _ x y, tag => .test tag x y
  | .shl _ x y z, tag => .shl tag x y z
  | .shr _ x y z, tag => .shr tag x y z
  | .sar _ x y z, tag => .sar tag x y z
  | .call _ dst fname args, tag => .call tag dst fname args
  | .call' _ target, tag => .call' tag target

def Inst.toString [ToString σ] [ToString γ] [ToString α] : Inst σ γ α → String
  |  .mov tag x y             => s!"{tag}:\tmov {x}, {y}"
  |  .add tag x y z           => s!"{tag}:\tadd {x}, {y}, {z}"
  |  .sub tag x y z           => s!"{tag}:\tsub {x}, {y}, {z}"
  |  .mul tag x y z           => s!"{tag}:\tmul {x}, {y}, {z}"
  |  .band tag x y z          => s!"{tag}:\tand {x}, {y}, {z}"
  |  .bor  tag x y z          => s!"{tag}:\tor {x}, {y}, {z}"
  -- |  .neg  tag x y            => s!"{tag}\tneg {x}, {y}"
  -- |  .land tag x y z          => s!"{tag}\tland {x}, {y}, {z}"
  -- |  .lor  tag x y z          => s!"{tag}\tlor {x}, {y}, {z}"
  |  .xor  tag x y z            => s!"{tag}\txor {x}, {y}, {z}"
  |  .lt tag x y z            => s!"{tag}:\tlt {x}, {y}, {z}"
  |  .le tag x y z            => s!"{tag}:\tle {x}, {y}, {z}"
  |  .gt tag x y z            => s!"{tag}:\tgt {x}, {y}, {z}"
  |  .ge tag x y z            => s!"{tag}:\tge {x}, {y}, {z}"
  |  .eq tag x y z            => s!"{tag}:\teq {x}, {y}, {z}"
  |  .ne tag x y z            => s!"{tag}:\tne {x}, {y}, {z}"
  | .push tag x            => s!"{tag}:\tpush {x}"
  | .pop tag x             => s!"{tag}:\tpop {x}"
  | .pop' tag             => s!"{tag}:\tpop"
  | .cmp tag x y           => s!"{tag}:\tcmp {x}, {y}"
  | .test tag x y          => s!"{tag}:\ttest {x}, {y}"
  |  .shl tag x y z           => s!"{tag}:\tshl {x}, {y}, {z}"
  |  .shr tag x y z           => s!"{tag}:\tshr {x}, {y}, {z}"
  |  .sar tag x y z           => s!"{tag}:\tsar {x}, {y}, {z}"
  |  .call tag dst fname args => s!"{tag}:\tcall {dst}, {fname}, [{String.intercalate ", " (args.map ToString.toString)}]"
  |  .call' tag target => s!"{tag}:\tcall {target}"

def Inst.toString' [ToString γ] [ToString α] : Inst Unit γ α → String
  |  .mov _ x y             => s!"    mov {x}, {y}"
  |  .add _ x y z           => s!"    add {x}, {y}, {z}"
  |  .sub _ x y z           => s!"    sub {x}, {y}, {z}"
  |  .mul _ x y z           => s!"    mul {x}, {y}, {z}"
  |  .band _ x y z          => s!"    and {x}, {y}, {z}"
  |  .bor  _ x y z          => s!"    or {x}, {y}, {z}"
  -- |  .neg  _ x y            => s!"    neg {x}, {y}"
  -- |  .land _ x y z          => s!"    land {x}, {y}, {z}"
  -- |  .lor  _ x y z          => s!"    lor {x}, {y}, {z}"
  |  .xor  _ x y z            => s!"    xor {x}, {y} {z}"
  |  .lt _ x y z            => s!"    lt {x}, {y}, {z}"
  |  .le _ x y z            => s!"    le {x}, {y}, {z}"
  |  .gt _ x y z            => s!"    gt {x}, {y}, {z}"
  |  .ge _ x y z            => s!"    ge {x}, {y}, {z}"
  |  .eq _ x y z            => s!"    eq {x}, {y}, {z}"
  |  .ne _ x y z            => s!"    ne {x}, {y}, {z}"
  | .push _ x            => s!"    push {x}"
  | .pop _ x             => s!"    pop {x}"
  | .pop' _             => s!"    pop"
  | .cmp _ x y           => s!"    cmp {x}, {y}"
  | .test _ x y          => s!"    test {x}, {y}"
  |  .shl _ x y z           => s!"    shl {x}, {y}, {z}"
  |  .shr _ x y z           => s!"    shr {x}, {y}, {z}"
  |  .sar _ x y z           => s!"    sar {x}, {y}, {z}"
  |  .call _ dst fname args => s!"    call {dst}, {fname}, [{String.intercalate ", " (args.map ToString.toString)}]"
  |  .call' _ target => s!"    call {target}"

instance [ToString σ] [ToString γ] [ToString α] : ToString (Inst σ γ α) where
  toString := Inst.toString

instance (priority := high) [ToString γ] [ToString α] : ToString (Inst Unit γ α) where
  toString := Inst.toString'

inductive Terminal (σ : Type) (γ : Type) (α : Type) where
  | ret : σ → α → Terminal σ γ α
  | jmp : σ → γ → Terminal σ γ α
  | br  : σ → α → γ → γ → Terminal σ γ α
  | jl  : σ → γ → Terminal σ γ α
  | jle : σ → γ → Terminal σ γ α
  | jg  : σ → γ → Terminal σ γ α
  | jge : σ → γ → Terminal σ γ α
  | jz  : σ → γ → Terminal σ γ α
  | jnz : σ → γ → Terminal σ γ α
deriving Inhabited, Repr, BEq

def Terminal.tag : Terminal σ γ α → σ
  | .ret tag _           => tag
  | .jmp tag _          => tag
  | .br tag _ _ _       => tag
  | .jl tag _           => tag
  | .jle tag _          => tag
  | .jg tag _           => tag
  | .jge tag _          => tag
  | .jz tag _           => tag
  | .jnz tag _          => tag

def Terminal.setTag : Terminal σ γ α → σ' → Terminal σ' γ α
  | .ret _ v,           tag => .ret tag v
  | .jmp _ lbl,         tag => .jmp tag lbl
  | .br _ cond lt' lf', tag => .br tag cond lt' lf'
  | .jl _ lbl,          tag => .jl tag lbl
  | .jle _ lbl,         tag => .jle tag lbl
  | .jg _ lbl,          tag => .jg tag lbl
  | .jge _ lbl,         tag => .jge tag lbl
  | .jz _ lbl,          tag => .jz tag lbl
  | .jnz _ lbl,         tag => .jnz tag lbl

def Terminal.toString [ToString σ] [ToString γ] [ToString α] : Terminal σ γ α → String
  |  .jmp tag lbl             => s!"{tag}:\tjmp {lbl}"
  |  .br tag cond lt' lf'     => s!"{tag}:\tbr {cond}, {lt'}, {lf'}"
  |  .jl tag lbl              => s!"{tag}:\tjl {lbl}"
  |  .jle tag lbl             => s!"{tag}:\tjle {lbl}"
  |  .jg tag lbl              => s!"{tag}:\tjg {lbl}"
  |  .jge tag lbl             => s!"{tag}:\tjge {lbl}"
  |  .jz tag lbl              => s!"{tag}:\tjz {lbl}"
  |  .jnz tag lbl             => s!"{tag}:\tjnz {lbl}"
  |  .ret tag v               => s!"{tag}:\tret {v}"

def Terminal.toString' [ToString γ] [ToString α] : Terminal Unit γ α → String
  |  .jmp _ lbl             => s!"    jmp {lbl}"
  |  .br _ cond lt' lf'     => s!"    br {cond}, {lt'}, {lf'}"
  |  .jl _ lbl              => s!"    jl {lbl}"
  |  .jle _ lbl             => s!"    jle {lbl}"
  |  .jg _ lbl              => s!"    jg {lbl}"
  |  .jge _ lbl             => s!"    jge {lbl}"
  |  .jz _ lbl              => s!"    jz {lbl}"
  |  .jnz _ lbl             => s!"    jnz {lbl}"
  |  .ret _ v               => s!"    ret {v}"

instance [ToString σ] [ToString γ] [ToString α] : ToString (Terminal σ γ α) where
  toString := Terminal.toString

instance (priority := high) [ToString γ] [ToString α] : ToString (Terminal Unit γ α) where
  toString := Terminal.toString'

structure VReg where
  name : String
deriving Inhabited, Repr, Hashable, BEq

instance : ToString VReg := ⟨fun x => x.name⟩

inductive GPR32 where
  | eax | ebx | ecx | edx
deriving Inhabited, Repr, BEq

instance : ToString GPR32 where
  toString
    | .eax => "eax"
    | .ebx => "ebx"
    | .ecx => "ecx"
    | .edx => "edx"

inductive AbsLoc where
  /-- 32 bit immediate value -/
  | imm : UInt32 → AbsLoc
  | preg : GPR32 → AbsLoc
  /-- virtual register -/
  | vreg : VReg → AbsLoc
  /-- frame slot (of variables) -/
  | frame : Nat → AbsLoc
  /-- arguments -/
  | arg : Nat → AbsLoc
deriving Inhabited, Repr, BEq

instance : ToString AbsLoc where
  toString
    | .imm x => s!"{x}"
    | .vreg x => s!"{x}"
    | .frame x => s!"frame[{x}]"
    | .arg x => s!"arg[{x}]"
    | .preg x => s!"{x}"

-- inductive Loc where
--   /-- 32 bit immediate value -/
--   | imm : UInt32 → Loc
--   -- /-- virtual register -/
--   -- | vreg : String → Loc
--   /-- physical x86 register -/
--   | reg : Reg → Loc
--   /-- [reg + offset] -/
--   | ref_offset : Reg → UInt32 → Loc
--   /-- hardcoded [address] -/
--   | address : UInt32 → Loc
-- deriving Inhabited, Repr, BEq

structure BasicBlock σ γ α where
  id : γ
  insts : Array (Inst σ γ α)
  terminal : Terminal σ γ α
deriving Inhabited, Repr

structure Edge (γ : Type) where
  P : γ
  B : γ
deriving Inhabited, Repr

@[always_inline]
def Edge.setB : Edge γ → γ → Edge γ := fun e b => {e with B := b}

structure CFG σ γ α where
  name : String
  blocks : Array (BasicBlock σ γ α)
deriving Inhabited, Repr

structure CFG.Config (σ γ α : Type) [Hashable γ] [BEq γ] where
  /-- sorted -/
  protected successors : Std.HashMap γ (List (Edge γ))
  /-- sorted -/
  protected predecessors : Std.HashMap γ (List (Edge γ))
  protected quick_table : Std.HashMap γ (BasicBlock σ γ α)
deriving Inhabited, Repr

private def CFG.config [Hashable γ] [BEq γ] : CFG σ γ α → CFG.Config σ γ α := fun cfg =>
  assert! !cfg.blocks.isEmpty
  let quick_table := Std.HashMap.ofList <| Array.toList <| cfg.blocks.map fun x => (x.id, x)
  let l := cfg.blocks.toList
  let pairs := l.zipWith (ys := l.tail) fun x y => (x, y)
  let edges : List (Edge γ) := pairs.flatMap fun (p, b) =>
    match p.terminal with
    | .jmp _ target   => [⟨p.id, target⟩]
    | .br _ _ lt' lf' => [⟨p.id, lt'⟩, ⟨p.id, lf'⟩]
    | .jl _ target    => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .jle _ target   => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .jg _ target    => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .jge _ target   => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .jz _ target    => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .jnz _ target   => [⟨p.id, b.id⟩, ⟨p.id, target⟩]
    | .ret _ _        => unreachable! -- impossible, because the returning block can only be the last block
  let ss := edges.groupByKey fun x => x.P
  let ps := edges.groupByKey fun x => x.B
  ⟨ss, ps, quick_table⟩

/-- Bundled version of `CFG` so we won't recompute the edges again and again.
The default value of `config` allows *implicitly* rebuilding when reconstructing the struct.
-/
structure CFG' σ γ α [Hashable γ] [BEq γ] extends CFG σ γ α where
  config : CFG.Config σ γ α := toCFG.config
deriving Inhabited, Repr

def CFG'.unsetTag [Hashable γ] [BEq γ] : CFG' σ γ α → CFG' Unit γ α := fun cfg =>
  let blocks := cfg.blocks.map fun b => { id := b.id, insts := b.insts.map fun x => x.setTag (), terminal := b.terminal.setTag () }
  { name := cfg.name, blocks }

def CFG'.get? [Hashable γ] [BEq γ] : CFG' σ γ α → γ → Option (BasicBlock σ γ α) := fun cfg id => cfg.config.quick_table[id]?

def CFG'.get! [Hashable γ] [BEq γ] [Inhabited σ] [Inhabited γ] [Inhabited δ] [Inhabited α] : CFG' σ γ α → γ → BasicBlock σ γ α := fun cfg id =>
  match cfg.get? id with
  | none => panic! "CFG'.get!: quick lookup failed"
  | some x => x

def CFG'.pred [Hashable γ] [BEq γ] : CFG' σ γ α → γ → Array γ := fun cfg id => cfg.config.predecessors[id]?.getD {} |>.toArray |>.map Edge.P

def CFG'.succ [Hashable γ] [BEq γ] : CFG' σ γ α → γ → Array γ := fun cfg id => cfg.config.successors[id]?.getD {} |>.toArray |>.map Edge.B

def CFG.isEntryBlock [BEq γ] : CFG σ γ α → γ → Bool := fun cfg id =>
  cfg.blocks[0]?.map (fun x => x.id == id) |>.getD false

def CFG.isExitBlock [BEq γ] : CFG σ γ α → γ → Bool := fun cfg id =>
  cfg.blocks.back?.map (fun x => x.id == id) |>.getD false

protected def pp_insts [ToString σ] [ToString γ] [ToString α] (insts : List (Inst σ γ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"
protected def pp_insts' [ToString γ] [ToString α] (insts : List (Inst Unit γ α)) := insts.map (fun x => s!"{x}") |> String.intercalate "\n"

protected def pp_cfg [ToString σ] [ToString γ] [ToString α] [Hashable γ] [BEq γ] (cfg : CFG σ γ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    store := store.push s!"{i.id}:"
    store := store.append (i.insts.map Inst.toString)
    store := store.push s!"{i.terminal}"
  return String.intercalate "\n" store.toList

protected def pp_cfg' [ToString γ] [ToString α] [Hashable γ] [BEq γ]  (cfg : CFG Unit γ α) : String := Id.run do
  let mut store := #[]
  for i in cfg.blocks do
    store := store.push s!"{i.id}:"
    store := store.append (i.insts.map Inst.toString')
    store := store.push s!"{i.terminal}"
  return String.intercalate "\n" store.toList

def Terminal.mapM_loc [Monad m] (f : α → m β) (inst : Terminal σ γ α) : m (Terminal σ γ β) := do
  match inst with
  | .jmp tag lbl => return .jmp tag lbl
  | .br tag cond lt' lf' => return .br tag (← f cond) lt' lf'
  | .jl tag lbl  => return .jl tag lbl
  | .jle tag lbl => return .jle tag lbl
  | .jg tag lbl  => return .jg tag lbl
  | .jge tag lbl => return .jge tag lbl
  | .jz tag lbl  => return .jz tag lbl
  | .jnz tag lbl => return .jnz tag lbl
  | .ret tag v => return .ret tag (← f v)

def Inst.mapM_loc [Monad m] (f : α → m β) (inst : Inst σ γ α) : m (Inst σ γ β) := do
  match inst with
  | .mov tag x y => return .mov tag (← f x) (← f y)
  | .add tag x y z => return .add tag (← f x) (← f y) (← f z)
  | .sub tag x y z => return .sub tag (← f x) (← f y) (← f z)
  | .mul tag x y z => return .mul tag (← f x) (← f y) (← f z)

  | .band tag x y z => return .band tag (← f x) (← f y) (← f z)
  | .bor  tag x y z => return .bor  tag (← f x) (← f y) (← f z)
  -- | .neg  tag x y => return .neg  tag (← f x) (← f y)

  -- | .land tag x y z => return .land tag (← f x) (← f y) (← f z)
  -- | .lor  tag x y z => return .lor  tag (← f x) (← f y) (← f z)
  | .xor  tag x y z => return .xor  tag (← f x) (← f y) (← f z)

  | .lt tag x y z => return lt tag (← f x) (← f y) (← f z)
  | .le tag x y z => return le tag (← f x) (← f y) (← f z)
  | .gt tag x y z => return gt tag (← f x) (← f y) (← f z)
  | .ge tag x y z => return ge tag (← f x) (← f y) (← f z)
  | .eq tag x y z => return eq tag (← f x) (← f y) (← f z)
  | .ne tag x y z => return ne tag (← f x) (← f y) (← f z)

  | .push tag x => return .push tag (← f x)
  | .pop tag x => return .pop tag (← f x)
  | .pop' tag => return .pop' tag
  | .cmp tag x y => return .cmp tag (← f x) (← f y)
  | .test tag x y => return .test tag (← f x) (← f y)

  | .shl tag x y z => return .shl tag (← f x) (← f y) (← f z)
  | .shr tag x y z => return .shr tag (← f x) (← f y) (← f z)
  | .sar tag x y z => return .sar tag (← f x) (← f y) (← f z)
  | .call tag dst fname args => return .call tag (← f dst) fname (← args.mapM f)
  | .call' tag target => return .call' tag target
