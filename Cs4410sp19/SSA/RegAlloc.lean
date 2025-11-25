-- import Cs4410sp19.SSA.Basic

-- namespace Cs4410sp19
-- namespace SSA
-- namespace RegAlloc

-- def annotate_lineno [Hashable γ] [BEq γ] : CFG' Unit γ δ α → CFG' Nat γ δ α := fun cfg => Id.run do
--   let mut bs : Array (BasicBlock Nat γ δ α) := #[]
--   let mut i : Nat := 0
--   for b in cfg.blocks do
--     let mut xs : Array (Inst Nat γ δ α) := #[]
--     for inst in b.insts do
--       xs := xs.push (inst.setTag i)
--       i := i + 1
--     bs := bs.push (BasicBlock.mk b.id b.params xs b.terminal)
--   return { name := cfg.name, blocks := bs }

-- /-- [start_inc, end_exc) -/
-- structure Interval where
--   start_inc : Nat
--   end_exc : Nat
--   used_pos : List Nat
-- deriving Inhabited, Repr

-- /-- non-overlapping sorted intervals -/
-- structure Lifetime where
--   intervals : Array Interval
-- deriving Inhabited, Repr

-- scoped instance : ToString Lifetime where
--   toString x := s!"[{String.intercalate ", " (x.intervals.toList.map fun x => s!"[{x.start_inc}-{x.end_exc})!{x.used_pos}")}]"

-- def Lifetime.empty : Lifetime := ⟨#[]⟩

-- def Lifetime.merge : Lifetime → Lifetime → Lifetime := fun x y => Id.run do
--   -- merge the overlapping intervals
--   let mut res : Array Interval := #[]
--   let mut i := 0
--   let mut j := 0
--   while i < x.intervals.size || j < y.intervals.size do
--     let next ←
--       if i < x.intervals.size && (j >= y.intervals.size || x.intervals[i]!.start_inc <= y.intervals[j]!.start_inc) then
--         let curr := x.intervals[i]!
--         i := i + 1
--         pure curr
--       else
--         let curr := y.intervals[j]!
--         j := j + 1
--         pure curr
--     if res.isEmpty then
--       res := res.push next
--     else
--       let last := res.back!
--       if last.end_exc >= next.start_inc then
--         let used := last.used_pos ++ next.used_pos
--         let used := used.mergeSort
--         let used := used.eraseDups
--         res := res.pop.push ⟨last.start_inc, Nat.max last.end_exc next.end_exc, used⟩
--       else
--         res := res.push next
--   return ⟨res⟩

-- def Lifetime.addRange : Lifetime → Nat → Nat → List Nat → Lifetime := fun l x y used => Lifetime.merge l ⟨#[⟨x, y, used⟩]⟩

-- def Lifetime.setFrom : Lifetime → Nat → Lifetime := fun l f => Id.run do
--   let mut is := l.intervals.toList
--   while is.length != 0 do
--     let i :: is' := is | unreachable!
--     if i.end_exc > f then
--       break
--     is := is'
--   if is.isEmpty then
--     return ⟨#[⟨f, f + 1, []⟩]⟩ -- at least live for one instruction
--   let i :: is' := is | unreachable!
--   return ⟨({i with start_inc := f} :: is').toArray⟩

-- end RegAlloc

-- -- #eval Lifetime.merge ⟨#[⟨1, 3, []⟩, ⟨7, 10, []⟩]⟩ ⟨#[⟨0, 2, []⟩, ⟨9, 12, []⟩]⟩

-- private def BasicBlock.from : BasicBlock Nat String VarName Operand → Nat := fun b => b.head!.tag

-- private def BasicBlock.to : BasicBlock Nat String VarName Operand → Nat := fun b => b.back!.tag + 1

-- private def BasicBlock.from_to : BasicBlock Nat String VarName Operand → (Nat × Nat) := fun b => (b.head!.tag, b.back!.tag + 1)

-- def RegAlloc.build_intervals (cfg : CFG' Nat String VarName Operand) : Std.HashMap VarName Lifetime := Id.run do
--   assert! cfg.blocks.all (fun x => x.params.isEmpty) -- TODO: error handling
--   let blocks := cfg.blocks
--   let mut liveIn : Std.HashMap String (Std.HashSet VarName) := {}
--   let mut intervals : Std.HashMap VarName Lifetime := {}
--   for b in blocks.reverse do
--     let ss := cfg.config.successors[b.id]?.getD #[]
--     let mut live := ss.foldl (init := ({} : Std.HashSet VarName)) (fun acc (s, _) => acc.insertMany (liveIn[s]?.getD {}))
--     match b.terminal with
--     | .jmp _ _ args =>
--       live := live.insertMany (args.filterMap fun
--         | .var v => some v
--         | _ => none)
--     | .br _ cond _ pargs _ nargs =>
--       live := live.insertMany (pargs.filterMap fun
--         | .var v => some v
--         | _ => none)
--       live := live.insertMany (nargs.filterMap fun
--         | .var v => some v
--         | _ => none)
--       -- condition operand should also be considered live
--       match cond with
--       | .var v => live := live.insert v
--       | _ => pure ()
--     | .ret _ v =>
--       match v with
--       | .var v => live := live.insert v
--       | _ => pure ()
--     for opd in live do
--       intervals := intervals.alter opd fun
--         | none => some Lifetime.empty
--         | some x => some x
--       let used := b.insts.filterMap fun x => if x.input_operands.contains (.var opd) then some x.tag else none
--       intervals := intervals.modify opd fun itv => itv.addRange b.from b.to used.toList
--     for op in b.insts.reverse do
--       for opd in op.output_operands do
--         intervals := intervals.alter opd fun
--           | none => some Lifetime.empty
--           | some x => some x
--         intervals := intervals.modify opd fun itv => itv.setFrom op.tag
--         live := live.erase opd
--       for opd in op.input_operands.filterMap fun
--         | .var v => some v
--         | _ => none do
--         intervals := intervals.alter opd fun
--           | none => some Lifetime.empty
--           | some x => some x
--         let used := b.insts.filterMap fun x => if x.input_operands.contains (.var opd) then some x.tag else none
--         intervals := intervals.modify opd fun itv => itv.addRange b.from op.tag used.toList
--         live := live.insert opd
--     for x in b.params do
--       live := live.erase x
--     -- TODO: handle loop header; we still don't have loops
--     liveIn := liveIn.insert b.id live
--   return intervals

-- namespace RegAlloc

-- private def lifetime_start (it : Lifetime) : Nat :=
--   it.intervals[0]!.start_inc

-- private def lifetime_end (it : Lifetime) : Nat :=
--   it.intervals.back!.end_exc

-- /- linear_scan:
--    - input: map from variable -> Lifetime and number of registers
--    - output: map from variable -> Option register number (none => spilled)
--   This implements the classic linear-scan algorithm: sort intervals by start,
--   maintain an active set sorted by end, reuse freed registers, and spill the
--   interval with the latest end when no registers are free.
-- -/

-- /- small helper structs for the linear-scan allocator -/
-- private structure LSItem where
--   var : VarName
--   life : Lifetime
--   start : Nat
--   endPos : Nat
-- deriving Inhabited

-- private structure ActiveEntry where
--   var : VarName
--   reg : Nat
--   endPos : Nat
-- deriving Inhabited

-- private inductive RAResult where
--   | reg (id : Nat)
--   | spill (slot : Nat)
-- deriving Inhabited, Repr

-- /-- TODO: reuse frame slots when possible -/
-- def linear_scan (intervals : Std.HashMap VarName Lifetime) (num_regs : Nat) : Std.HashMap VarName RAResult := Id.run do
--   -- collect items and sort by start
--   let items := intervals.toList.map fun (v, it) =>
--     if it.intervals.isEmpty then
--       { var := v, life := it, start := 0, endPos := 0 : LSItem }
--     else
--       { var := v, life := it, start := lifetime_start it, endPos := lifetime_end it }
--   let items := items.mergeSort fun a b => a.start < b.start

--   let mut mapping : Std.HashMap VarName RAResult := {}
--   let mut active : List ActiveEntry := []
--   let mut free_regs : List Nat := (List.range num_regs).reverse
--   let mut frameSlotIdx := 0
--   for it in items do
--     let v := it.var
--     let start := it.start
--     let endPos := it.endPos

--     -- expire old intervals whose end <= start
--     let mut new_active : List ActiveEntry := []
--     let mut fr := free_regs
--     for a in active do
--       match a with
--       | ⟨_, areg, aend⟩ =>
--         if aend <= start then
--           fr := areg :: fr
--         else
--           new_active := a :: new_active
--     active := new_active.reverse
--     free_regs := fr

--     match free_regs with
--     | [] =>
--       -- no free registers, pick the active interval with largest end to consider spilling
--       let active_rev := active.reverse
--       match active_rev with
--       | [] =>
--         -- no active items (shouldn't happen if no free regs), spill current
--         mapping := mapping.insert v (RAResult.spill frameSlotIdx)
--         frameSlotIdx := frameSlotIdx + 1
--       | (spill :: rest) =>
--         match spill with
--         | ⟨spillVar, spillReg, spillEnd⟩ =>
--           if spillEnd > endPos then
--             -- spill the active interval with the furthest end, give its register to current
--             mapping := mapping.insert spillVar (RAResult.spill frameSlotIdx)
--             frameSlotIdx := frameSlotIdx + 1
--             -- remove the spilled from active and add current
--             active := rest.reverse
--             mapping := mapping.insert v (RAResult.reg spillReg)
--             active := { var := v, reg := spillReg, endPos := endPos } :: active
--             active := active.mergeSort fun a b => a.endPos < b.endPos
--           else
--             -- current interval ends earlier or equal, so spill current
--             mapping := mapping.insert v (RAResult.spill frameSlotIdx)
--             frameSlotIdx := frameSlotIdx + 1
--     | (r :: rs) =>
--       -- assign a free register r to v
--       free_regs := rs
--       mapping := mapping.insert v (RAResult.reg r)
--       active := { var := v, reg := r, endPos := endPos } :: active
--       active := active.mergeSort fun a b => a.endPos < b.endPos

--   return mapping

-- inductive GReg where
--   | eax | ebx | ecx | edx
-- deriving Inhabited, Repr

-- inductive Src where
--   | const : ConstVal → Src
--   | physReg : GReg → Src
--   | frameIdx : Nat → Src
-- deriving Inhabited, Repr

-- inductive Dst where
--   | physReg : GReg → Dst
--   | frameIdx : Nat → Dst
-- deriving Inhabited, Repr

-- instance : ToString GReg where
--   toString
--     | .eax => "eax"
--     | .ebx => "ebx"
--     | .ecx => "ecx"
--     | .edx => "edx"

-- instance : ToString Src where
--   toString
--     | .const x => s!"{x}"
--     | .physReg x => s!"{x}"
--     | .frameIdx x => s!"frame({x})"

-- instance : ToString Dst where
--   toString
--     | .physReg x => s!"{x}"
--     | .frameIdx x => s!"frame({x})"

-- def allocate_registers (cfg : CFG' Nat String VarName Operand) : CFG' Nat String Dst Src := Id.run do
--   -- the block args must have been eliminated
--   assert! cfg.blocks.all (fun x => x.params.isEmpty) -- TODO: error handling
--   let regs := #[GReg.eax, .ebx, .ecx, .edx]
--   let lifetime := build_intervals cfg
--   let assignment := linear_scan lifetime regs.size
--   let get_dst : VarName → Dst := fun name =>
--     match assignment[name]! with
--     | .spill slot => Dst.frameIdx slot
--     | .reg i => Dst.physReg regs[i]!
--   let get_src : Operand → Src := fun op =>
--     match op with
--     | .var name =>
--       match assignment[name]! with
--       | .spill slot => Src.frameIdx slot
--       | .reg i => Src.physReg regs[i]!
--     | .const x => Src.const x
--     | .param .. => unreachable! -- upon register allocation, the block args must have been reduced
--   let mut blocks' : Array (BasicBlock Nat String Dst Src) := #[]
--   for b in cfg.blocks do
--     let mut insts' := #[]
--     for inst in b.insts do
--       let r : Inst Nat String Dst Src :=
--         match inst with
--         | .assign   tag n v                       => .assign tag (get_dst n) (get_src v)
--         | .prim2    tag n op x y                  => .prim2 tag (get_dst n) op (get_src x) (get_src y)
--         | .prim1    tag n op x                    => .prim1 tag (get_dst n) op (get_src x)
--         | .call     tag n fn xs                   => .call tag (get_dst n) fn (xs.map get_src)
--         | .mk_tuple tag n xs                      => .mk_tuple tag (get_dst n) (xs.map get_src)
--         | .get_item tag n v i size                => .get_item tag (get_dst n) (get_src v) i size
--         | .pc       tag xs                        => .pc tag (xs.map fun (d, x) => (get_dst d, get_src x))
--         | .get_arg  tag n i                       => .get_arg tag (get_dst n) i
--       insts' := insts'.push r
--     let term' := match b.terminal with
--       | .jmp tag tgt args => .jmp tag tgt (args.map get_src)
--       | .br tag cond bt targs bf fargs => .br tag (get_src cond) bt (targs.map get_src) bf (fargs.map get_src)
--       | .ret tag v => .ret tag (get_src v)
--     blocks' := blocks'.push { id := b.id, params := [], insts := insts', terminal := term' : BasicBlock Nat String Dst Src }
--   return { name := cfg.name, blocks := blocks' }

-- end RegAlloc
