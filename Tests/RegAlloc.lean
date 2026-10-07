import Cs4410sp19.MIR

open Cs4410sp19 Cs4410sp19.MIR Cs4410sp19.MIR.RegAlloc

private def v (n : Nat) : AbsLoc := .vreg ⟨s!"v.{n}"⟩
private abbrev I := Inst Unit String AbsLoc
private abbrev B := BasicBlock Unit String AbsLoc

private structure Flags where
  zero : Bool := false
  less : Bool := false
  deriving Inhabited

private def arithmeticFlags (a b r : UInt32) (subtract : Bool) : Flags :=
  let sa := a >>> 31 != 0
  let sb := b >>> 31 != 0
  let sr := r >>> 31 != 0
  let overflow := (if subtract then sa != sb else sa == sb) && sr != sa
  { zero := r == 0, less := sr != overflow }

private structure Machine where
  values : Std.HashMap AbsLoc UInt32 := {}
  flags : Flags := {}
  stack : List UInt32 := []
  deriving Inhabited

private def read (s : Machine) : AbsLoc → UInt32
  | .imm n => n
  | loc => s.values[loc]?.getD 0

private def put (s : Machine) (loc : AbsLoc) (n : UInt32) : Machine :=
  { s with values := s.values.insert loc n }

private def evalInst (s : Machine) (i : I) : Machine := Id.run do
  let binary := fun d x y op flags =>
    let a := read s x
    let b := read s y
    let r := op a b
    { put s d r with flags := flags a b r }
  let bitFlags := fun (_ _ r : UInt32) => Flags.mk (r == 0) (r >>> 31 != 0)
  match i with
  | .mov _ d x => return put s d (read s x)
  | .add _ d x y => return binary d x y (· + ·) (fun a b r => arithmeticFlags a b r false)
  | .sub _ d x y => return binary d x y (· - ·) (fun a b r => arithmeticFlags a b r true)
  | .mul _ d x y => return put s d (read s x * read s y)
  | .band _ d x y => return binary d x y (· &&& ·) bitFlags
  | .bor _ d x y => return binary d x y (· ||| ·) bitFlags
  | .xor _ d x y => return binary d x y (· ^^^ ·) bitFlags
  | .cmp _ x y => return { s with flags := arithmeticFlags (read s x) (read s y) (read s x - read s y) true }
  | .test _ x y => return { s with flags := bitFlags 0 0 (read s x &&& read s y) }
  | .shl _ d x n => return put s d (read s x <<< (read s n &&& 31))
  | .shr _ d x n => return put s d (read s x >>> (read s n &&& 31))
  | .sar _ d x n =>
    return put s d ((read s x).toInt32 >>> (read s n &&& 31).toInt32).toUInt32
  | .push _ x => return { s with stack := read s x :: s.stack }
  | .pop _ d => return put { s with stack := s.stack.tail } d (s.stack.headD 0)
  | .pop' _ => return { s with stack := s.stack.tail }
  | .call' _ "ra_clobber" =>
    let s := put s (.preg .eax) (s.stack.headD 0 + 6)
    let s := put s (.preg .ecx) 0x55aa55aa
    return put s (.preg .edx) 0xaa55aa55
  | _ => unreachable!

/-- Small independent interpreter used only on defined, bounded MIR fixtures.
    Native execution also checks x86 encodings, flags, stack alignment and ABI. -/
private def interpret (cfg : Code) : Except String UInt32 := do
  let mut s : Machine := { values := { (.arg 0, 123), (.arg 1, 456) } }
  let mut block := 0
  for _ in [:10000] do
    let some b := cfg.blocks[block]? | throw "test interpreter: fell off CFG"
    for i in b.insts do s := evalInst s i
    if let .ret _ x := b.terminal then return read s x
    let target := match b.terminal with
      | .ret _ _ => none
      | .jmp _ label => some label
      | .jz _ label => if s.flags.zero then some label else none
      | .jnz _ label => if !s.flags.zero then some label else none
      | .jl _ label => if s.flags.less then some label else none
      | .jle _ label => if s.flags.less || s.flags.zero then some label else none
      | .jg _ label => if !s.flags.less && !s.flags.zero then some label else none
      | .jge _ label => if !s.flags.less then some label else none
      | .br _ cond t f => some (if read s cond == 0x80000001 then t else f)
    match target with
    | none => block := block + 1
    | some target =>
      let some idx := cfg.blocks.findIdx? (·.id == target) | throw "test interpreter: missing target"
      block := idx
  throw "test interpreter: fuel exhausted"

private def single (insts : Array I) (result : AbsLoc) (name := "fixture") : Code :=
  { name, blocks := #[{ id := ".entry", insts, terminal := .ret () result }] }

private def pressure (seed : Nat) (calls := false) : Code := Id.run do
  let mut insts : Array I := #[]
  let mut random := seed + 1
  let next := fun (n : Nat) => (n * 1664525 + 1013904223) % 4294967296
  for n in [:18] do
    random := next random
    insts := insts.push (.mov () (v n) (.imm random.toUInt32))
  if calls then insts := insts.push (.call () (v 18) "ra_clobber" [v 0])
  for k in [:50] do
    random := next random
    let d := v (random % 18)
    random := next random
    let src := v (random % 18)
    let i : I := match k % 6 with
      | 0 => .add () d d src
      | 1 => .sub () d d src
      | 2 => .mul () d d src
      | 3 => .xor () d d src
      | 4 => .mov () d src
      | _ => .bor () d d src
    insts := insts.push i
  insts := insts.push (.mov () (v 19) (v 0))
  for n in [1:18] do insts := insts.push (.add () (v 19) (v 19) (v n))
  if calls then insts := insts.push (.add () (v 19) (v 19) (v 18))
  return to_c_call (single insts (v 19))

private def fixtures : List (String × Code) :=
  [("registers", single #[.mov () (v 0) (.imm 17), .add () (v 0) (v 0) (.imm 4)] (v 0)),
   ("arguments", single #[.mov () (v 0) (.arg 0), .add () (v 0) (v 0) (.arg 1)] (v 0)),
   ("entry-abi", single #[.mov () (v 0) (.imm 21)] (v 0) ""),
   ("fixed-shift", single #[.mov () (v 0) (.imm 3), .mov () (v 1) (.imm 4),
     .shl () (v 0) (v 0) (v 1), .add () (v 0) (v 0) (v 1)] (v 0)),
   ("preserve-ecx", single #[.mov () (.preg .ecx) (.imm 7),
     .mov () (v 0) (.imm 3), .mov () (v 1) (.imm 2),
     .shl () (v 0) (v 0) (v 1), .add () (v 0) (v 0) (.preg .ecx)] (v 0)),
   ("shift-ecx-destination", single #[.mov () (.preg .ecx) (.imm 3),
     .mov () (v 0) (.imm 2), .shl () (.preg .ecx) (.preg .ecx) (v 0)] (.preg .ecx)),
   ("shift-mask", single #[.mov () (v 0) (.imm 7), .shl () (v 0) (v 0) (.imm 33)] (v 0)),
   ("arithmetic-shift", single #[.mov () (v 0) (.imm 0xfffffff8),
     .mov () (v 1) (.imm 2), .sar () (v 0) (v 0) (v 1)] (v 0)),
   ("logical-shift", single #[.mov () (v 0) (.imm 0xfffffff8),
     .mov () (v 1) (.imm 2), .shr () (v 0) (v 0) (v 1)] (v 0)),
   ("scavenge-live-registers", single #[.mov () (.preg .eax) (.imm 10),
     .mov () (.preg .ebx) (.imm 20), .mov () (.preg .ecx) (.imm 30), .mov () (.preg .edx) (.imm 40),
     .mov () (.frame 0) (.imm 3), .mov () (.frame 1) (.imm 2),
     .mul () (.frame 0) (.frame 0) (.preg .edx), .add () (.frame 0) (.frame 0) (.frame 1),
     .add () (.frame 0) (.frame 0) (.preg .eax), .add () (.frame 0) (.frame 0) (.preg .ebx),
     .add () (.frame 0) (.frame 0) (.preg .ecx), .add () (.frame 0) (.frame 0) (.preg .edx)] (.frame 0)),
   ("multiple-definitions", { name := "fixture", blocks := #[
     { id := ".entry", insts := #[.mov () (v 0) (.imm 9), .cmp () (v 0) (.imm 10)], terminal := .jl () ".left" },
     { id := ".right", insts := #[.mov () (v 1) (.imm 3)], terminal := .jmp () ".join" },
     { id := ".left", insts := #[.mov () (v 1) (.imm 5)], terminal := .jmp () ".join" },
     { id := ".join", insts := #[.add () (v 1) (v 1) (v 0)], terminal := .ret () (v 1) }] }),
   ("loop-and-early-return", { name := "fixture", blocks := #[
     { id := ".entry", insts := #[.mov () (v 0) (.imm 10), .mov () (v 1) (.imm 0)], terminal := .jmp () ".loop" },
     { id := ".exit", insts := #[], terminal := .ret () (v 1) },
     { id := ".loop", insts := #[.add () (v 1) (v 1) (v 0), .sub () (v 0) (v 0) (.imm 1),
       .cmp () (v 0) (.imm 0)], terminal := .jle () ".exit" },
     { id := ".back", insts := #[], terminal := .jmp () ".loop" }] }),
   ("spill-preserves-flags", { name := "fixture", blocks := #[
     { id := ".entry", insts := #[.mov () (.frame 0) (.imm 9), .mov () (.frame 1) (.imm 7),
       .cmp () (.frame 0) (.frame 1), .mov () (.frame 2) (.frame 0)], terminal := .jg () ".yes" },
     { id := ".no", insts := #[], terminal := .ret () (.imm 0) },
     { id := ".yes", insts := #[], terminal := .ret () (.frame 2) }] })]

private def spillLoop : Code := Id.run do
  let mut entry : Array I := #[]
  for n in [:16] do entry := entry.push (.mov () (v n) (.imm (n + 1).toUInt32))
  entry := entry.push (.mov () (v 16) (.imm 5))
  let mut loop : Array I := #[]
  for n in [:16] do loop := loop.push (.add () (v n) (v n) (v ((n + 1) % 16)))
  loop := loop ++ #[.call () (v 18) "ra_clobber" [v 0], .add () (v 1) (v 1) (v 18),
    .sub () (v 16) (v 16) (.imm 1), .cmp () (v 16) (.imm 0)]
  let mut exit : Array I := #[.mov () (v 17) (v 0)]
  for n in [1:16] do exit := exit.push (.add () (v 17) (v 17) (v n))
  return to_c_call { name := "fixture", blocks := #[
    { id := ".entry", insts := entry, terminal := .jmp () ".loop" },
    { id := ".loop", insts := loop, terminal := .jnz () ".loop" },
    { id := ".exit", insts := exit, terminal := .ret () (v 17) }] }

private def branchFixture (insts : Array I) (term : Terminal Unit String AbsLoc) : Code :=
  { name := "fixture", blocks := #[
    { id := ".entry", insts, terminal := term },
    { id := ".no", insts := #[], terminal := .ret () (.imm 0) },
    { id := ".yes", insts := #[], terminal := .ret () (.imm 1) }] }

private def extraFixtures : List (String × Code) :=
  [("spill-loop-with-call", spillLoop),
   ("unreachable-block", { name := "fixture", blocks := #[
     { id := ".entry", insts := #[], terminal := .ret () (.imm 7) },
     { id := ".dead", insts := #[], terminal := .ret () (v 0) }] }),
   ("signed-compare-overflow", branchFixture #[.mov () (.frame 0) (.imm 1),
     .cmp () (.imm 0x80000000) (.frame 0)] (.jl () ".yes")),
   ("add-overflow-flags", branchFixture #[.mov () (.frame 0) (.imm 0x7fffffff),
     .mov () (.frame 1) (.imm 1), .add () (.frame 0) (.frame 0) (.frame 1)] (.jge () ".yes")),
   ("memory-test-flags", branchFixture #[.mov () (.frame 0) (.imm 9),
     .mov () (.frame 1) (.imm 7), .test () (.frame 0) (.frame 1)] (.jnz () ".yes")),
   ("push-pop", single #[.mov () (v 0) (.imm 17), .push () (v 0),
     .mov () (v 0) (.imm 2), .pop () (v 1)] (v 1)),
   ("memory-argument-copy", single #[.mov () (.arg 0) (.arg 1)] (.arg 0)),
   ("zero-shift-preserves-flags", branchFixture #[.mov () (.frame 0) (.imm 7),
     .mov () (v 0) (.imm 32), .cmp () (.frame 0) (.imm 7),
     .shl () (.frame 0) (.frame 0) (v 0)] (.jz () ".yes"))]

private def parallelFixture (pairs : List (SSA.VarName × SSA.Operand)) (subtract := false) : Code :=
  let cfg : SSA.CFG Unit String SSA.VarName SSA.Operand := { name := "fixture", blocks := #[
    { id := ".entry", params := [], insts := #[
      .assign () ⟨"a"⟩ (.const (.int 1)), .assign () ⟨"b"⟩ (.const (.int 2)),
      .assign () ⟨"c"⟩ (.const (.int 3)), .pc () pairs,
      .prim2 () ⟨"result"⟩ (if subtract then .minus else .plus) (.var ⟨"a"⟩) (.var ⟨"b"⟩)],
      terminal := .ret () (.var ⟨"result"⟩) }] }
  let (r, names) := FreshM.run (construct cfg) {}
  (FreshM.run (form r.toCFG) names).1

private def command (cmd : String) (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd, args }
  unless result.exitCode == 0 do
    throw (IO.userError s!"{cmd} failed ({result.exitCode}): {result.stderr}\n{result.stdout}")

private def native (code : Code) (expected : UInt32) : IO Unit := do
  let dir : System.FilePath := ".lake/build/ra-tests"
  IO.FS.createDirAll dir
  let asm := dir / "case.s"
  let obj := dir / "case.o"
  let c := dir / "probe.c"
  let exe := dir / "case.run"
  let body := Assembler.asm_to_string (assemble code)
  IO.FS.writeFile asm s!"section .text
global allocated_case, ra_probe
allocated_case:
{body}
ra_clobber:
  mov eax, esp
  and eax, 15
  cmp eax, 12
  jne .alignment_error
  mov eax, dword [esp + 4]
  add eax, 6
  mov ecx, 0x55aa55aa
  mov edx, 0xaa55aa55
  ret
.alignment_error:
  mov eax, 0xbadbad
  ret
ra_probe:
  push ebp
  mov ebp, esp
  push ebx
  push esi
  push edi
  sub esp, 4
  and esp, 0xfffffff0
  mov dword [ebp - 16], esp
  mov ebx, 0x12345678
  mov esi, 0x23456789
  mov edi, 0x3456789a
  push 0
  push 0
  push 456
  push 123
  call allocated_case
  add esp, 16
  cmp esp, dword [ebp - 16]
  jne .abi_error
  cmp eax, {expected}
  jne .value_error
  cmp ebx, 0x12345678
  jne .abi_error
  cmp esi, 0x23456789
  jne .abi_error
  cmp edi, 0x3456789a
  jne .abi_error
  mov eax, 0
  jmp .done
.value_error:
  mov eax, 1
  jmp .done
.abi_error:
  mov eax, 2
.done:
  lea esp, [ebp - 12]
  pop edi
  pop esi
  pop ebx
  pop ebp
  ret
section .note.GNU-stack noalloc noexec nowrite progbits
"
  IO.FS.writeFile c "extern int ra_probe(void); int main(void) { return ra_probe(); }\n"
  command "nasm" #["-f", "elf32", "-o", obj.toString, asm.toString]
  command "cc" #["-m32", "-no-pie", "-o", exe.toString, c.toString, obj.toString]
  command exe.toString #[]

private def require {α} (r : Except String α) : IO α :=
  match r with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def test (name : String) (cfg : Code) : IO Allocation := do
  let expected ← require (interpret cfg)
  let allocation ← require (allocate cfg)
  let actual ← require (interpret allocation.code)
  unless expected == actual do
    throw (IO.userError s!"{name}: expected {expected}, got {actual}")
  try native allocation.code expected
  catch error => throw (IO.userError s!"{name}: {error}")
  return allocation

private def checkerTests (a : Allocation) : IO Unit := do
  let removed := { a.allocated with blocks := a.allocated.blocks.map fun b =>
    { b with insts := b.insts.filter fun i => i.tag.isNone } }
  unless (checkAllocation a.original removed) matches .error _ do
    throw (IO.userError "checker accepted removed semantic operations")
  let mut changed := false
  let mut blocks := #[]
  for b in a.allocated.blocks do
    let mut insts := #[]
    for i in b.insts do
      if !changed then
        if let .mov none d (.frame _) := i then
          changed := true
          insts := insts.push (.mov none d (.imm 0))
          continue
      insts := insts.push i
    blocks := blocks.push { b with insts }
  unless changed do throw (IO.userError "fixture did not exercise a spill reload")
  unless (checkAllocation a.original { a.allocated with blocks }) matches .error _ do
    throw (IO.userError "checker accepted a corrupted spill reload")
  let badHomes := a.homes.map fun _ _ => AbsLoc.preg .eax
  let corrupted ← require (lower a.original badHomes)
  unless (checkAllocation a.original corrupted) matches .error _ do
    throw (IO.userError "checker accepted colliding live values")
  let called ← require (allocate (to_c_call (single #[.mov () (v 0) (.imm 17),
    .call () (v 1) "ra_clobber" [.imm 123], .add () (v 0) (v 0) (.imm 1)] (v 0))))
  let missingClobbers := { called.original with blocks := called.original.blocks.map fun b =>
    { b with insts := b.insts.map fun i => match i with
      | .call' tag name => .call' { tag with defs := #[] } name
      | _ => i } }
  let bad ← require (lower missingClobbers (called.homes.insert ⟨"v.0"⟩ (.preg .ecx)))
  unless (checkAllocation missingClobbers bad) matches .error _ do
    throw (IO.userError "checker trusted missing call-clobber metadata")

public def main : IO Unit := do
  for (name, cfg) in fixtures do
    let _ ← test name cfg
  for (name, cfg) in extraFixtures do
    let _ ← test name cfg
  for (name, pairs, subtract, expected) in [
      ("parallel-chain", [(SSA.VarName.mk "a", SSA.Operand.var ⟨"b"⟩), (⟨"b"⟩, .var ⟨"c"⟩)], false, 10),
      ("parallel-cycle", [(SSA.VarName.mk "a", SSA.Operand.var ⟨"b"⟩), (⟨"b"⟩, .var ⟨"a"⟩)], true, 2),
      ("parallel-constant", [(SSA.VarName.mk "a", SSA.Operand.var ⟨"b"⟩), (⟨"b"⟩, .const (.int 9))], false, 22),
      ("parallel-self", [(SSA.VarName.mk "a", SSA.Operand.var ⟨"a"⟩), (⟨"b"⟩, .var ⟨"b"⟩)], false, 6)] do
    let cfg := parallelFixture pairs subtract
    unless (← require (interpret cfg)) == expected do
      throw (IO.userError s!"{name}: parallel-copy lowering changed the result")
    let _ ← test name cfg
  let operators : List (Unit → AbsLoc → AbsLoc → AbsLoc → I) :=
    [Inst.add, Inst.sub, Inst.mul, Inst.band, Inst.bor, Inst.xor, Inst.shl, Inst.shr, Inst.sar]
  for (op, idx) in operators.zipIdx do
    let cfg := single #[.mov () (v 0) (.imm 0xffffffe0), .mov () (v 1) (.imm 2),
      op () (v 1) (v 0) (v 1)] (v 1)
    let formed := (FreshM.run (form cfg) {}).1
    unless (← require (interpret cfg)) == (← require (interpret formed)) do
      throw (IO.userError s!"two-address conversion destroyed RHS for operator {idx}")
    let _ ← test s!"two-address-rhs-{idx}" formed
  let trivial ← require (allocate fixtures.head!.2)
  unless trivial.homes.toList.all (fun (_, loc) => loc matches .preg _) do
    throw (IO.userError "low-pressure fixture failed to allocate registers")
  let pressured ← test "pressure" (pressure 0)
  unless pressured.homes.toList.any (fun (_, loc) => loc matches .frame _) do
    throw (IO.userError "pressure fixture did not spill")
  checkerTests pressured
  let mut slots : Homes := {}
  let mut slot := Assemble.requiredFrameSlots pressured.original.unsetTag
  for v in pressured.homes.keys do
    slots := slots.insert v (.frame slot)
    slot := slot + 1
  let allStack ← require (lower pressured.original slots)
  require (checkAllocation pressured.original allStack)
  native allStack.unsetTag (← require (interpret pressured.original.unsetTag))
  for seed in [:64] do
    let _ ← test s!"generated-{seed}" (pressure seed (seed % 2 == 0))
  IO.println "Register allocation: 100 interpreted/native fixtures and checker corruption tests passed."
