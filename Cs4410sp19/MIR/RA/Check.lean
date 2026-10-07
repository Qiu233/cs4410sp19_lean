import Cs4410sp19.MIR.RA.Lower

namespace Cs4410sp19.MIR.RegAlloc

private inductive Symbol where
  | value : AbsLoc → Symbol
  | flags
  deriving Inhabited, BEq, Hashable

private abbrev Symbols := List Symbol
private abbrev CheckState := Std.HashMap Symbol Symbols

private def readLoc (s : CheckState) (x : AbsLoc) : Symbols :=
  match x with
  | .imm _ => [.value x]
  | _ => s[Symbol.value x]?.getD []

private def write (s : CheckState) (key : Symbol) (values : Symbols) : CheckState :=
  if values.isEmpty then s.erase key else s.insert key values.eraseDups

private def sameSymbols (x y : Symbols) : Bool :=
  x.length == y.length && x.all y.contains

private def sameState (a b : CheckState) : Bool :=
  a.toList.all (fun (k, v) => sameSymbols v (b[k]?.getD [])) &&
  b.toList.all (fun (k, v) => sameSymbols v (a[k]?.getD []))

private def meet (a b : CheckState) : CheckState :=
  a.fold (fun s k vs => write s k (vs.filter ((b[k]?.getD []).contains))) {}

private def initialState (original : CFG InstMData String AbsLoc) : CheckState := Id.run do
  let mut s : CheckState := {}
  for r in [GPR32.eax, .ebx, .ecx, .edx] do
    s := s.insert (.value (.preg r)) [.value (.preg r)]
  s := s.insert .flags [.flags]
  for b in original.blocks do
    let operands := b.insts.toList.flatMap (fun i => i.uses ++ i.defs) ++ b.terminal.uses
    for loc in operands do
      match loc with
      | .arg _ | .frame _ => s := s.insert (.value loc) [.value loc]
      | _ => pure ()
  return s

-- Model implicit effects independently of InstMData: a metadata bug must not
-- make both the allocator and its checker forget the same call clobber.
private def implicitDefs (i : Inst σ String AbsLoc) : Symbols :=
  match i with
  | .call' .. => [.value (.preg .eax), .value (.preg .ecx), .value (.preg .edx), .flags]
  | .add .. | .sub .. | .mul .. | .band .. | .bor .. | .xor ..
  | .shl .. | .shr .. | .sar .. | .cmp .. | .test .. | .pop' .. => [.flags]
  | _ => []

private def checkInputs (s : CheckState) (expected actual : List AbsLoc) (line : Nat) :
    Except String Unit := do
  unless expected.length == actual.length do
    throw s!"allocation checker: operand count changed at line {line}"
  for (e, a) in expected.zip actual do
    unless (readLoc s a).contains (.value e) do
      throw s!"allocation checker: line {line} reads {a}, which no longer contains {e}"

private def checkFlags (s : CheckState) (term : Terminal InstMData String AbsLoc) : Except String Unit := do
  let needsFlags := match term with
    | .jl .. | .jle .. | .jg .. | .jge .. | .jz .. | .jnz .. => true
    | _ => false
  if needsFlags && !(s[Symbol.flags]?.getD []).contains .flags then
    throw s!"allocation checker: flags lost before line {term.tag.lineno}"

/-- Symbolic execution tracks the *current* value of each original virtual or
    physical register. Redefinitions invalidate old aliases everywhere. Inserted
    MOVs only transport symbols; they may not create a missing source value. -/
private def execute (s : CheckState) (original : Inst InstMData String AbsLoc)
    (actual : Inst (Option Nat) String AbsLoc) (checking : Bool) : Except String CheckState := do
  if checking then
    checkInputs s original.uses actual.uses original.tag.lineno
  let copied := match actual with
    | .mov _ _ src => readLoc s src
    | _ => []
  let killed := (original.defs.map Symbol.value ++ implicitDefs original).eraseDups
  let mut result := s.fold (fun acc k values => write acc k (values.filter fun v => !killed.contains v)) {}
  for (expected, actualDst) in original.defs.zip actual.defs do
    let aliases := copied.filter fun v => !killed.contains v
    result := write result (.value actualDst) (.value expected :: aliases)
  for d in implicitDefs actual do
    match d with
    | .flags => result := write result .flags [.flags]
    | .value (.preg r) =>
      if !original.defs.contains (.preg r) then
        result := write result (.value (.preg r)) [.value (.preg r)]
    | _ => pure ()
  return result

private def runBlock (refs : Std.HashMap Nat (Inst InstMData String AbsLoc))
    (block : BasicBlock (Option Nat) String AbsLoc) (input : CheckState) (checking : Bool) :
    Except String CheckState := do
  let mut s := input
  for i in block.insts do
    match i.tag with
    | some n =>
      let some original := refs[n]? | throw s!"allocation checker: unknown origin {n}"
      s ← execute s original i checking
    | none =>
      let .mov _ dst src := i | throw "allocation checker: inserted instruction must be MOV"
      s := write s (.value dst) (readLoc s src)
  return s

private def mem : AbsLoc → Bool
  | .frame _ | .arg _ => true
  | _ => false

private def validDst : AbsLoc → Bool
  | .preg _ | .frame _ | .arg _ => true
  | _ => false

/-- Check actual x86 operand shapes without relying on assembly-time assertions
    (which may be erased by the compiler if their results are unused). -/
def checkInstruction (i : Inst σ String AbsLoc) : Except String Unit := do
  for loc in i.uses ++ i.defs do
    if loc matches .vreg _ then throw "allocation checker: unresolved virtual register"
  let binary := fun d x y => validDst d && d == x && !(mem d && mem y)
  let shift := fun d x n => validDst d && d == x && match n with
    | .imm n => n.toNat < 256
    | .preg .ecx => true
    | _ => false
  let valid := match i with
    | .mov _ d x => validDst d && !(mem d && mem x)
    | .add _ d x y | .sub _ d x y | .band _ d x y | .bor _ d x y | .xor _ d x y => binary d x y
    | .mul _ d x _ => d == x && (d matches .preg _)
    | .cmp _ x y | .test _ x y => validDst x && !(mem x && mem y)
    | .shl _ d x n | .shr _ d x n | .sar _ d x n => shift d x n
    | .pop _ d => validDst d
    | .push _ _ | .pop' _ | .call' _ _ => true
    | _ => false
  unless valid do throw "allocation checker: illegal x86 instruction shape"

private def sameInstShape (a : Inst σ String AbsLoc) (b : Inst τ String AbsLoc) : Bool :=
  (a.mapM_loc (m := Id) fun _ => pure ()).setTag () ==
    (b.mapM_loc (m := Id) fun _ => pure ()).setTag ()

private def sameTerminalShape (a : Terminal σ String AbsLoc) (b : Terminal τ String AbsLoc) : Bool :=
  (a.mapM_loc (m := Id) fun _ => pure ()).setTag () ==
    (b.mapM_loc (m := Id) fun _ => pure ()).setTag ()

/-- Independently verify semantic-operation order, legal instructions, and
    symbolic dataflow at every reachable use. Joins intersect known aliases;
    loops are solved to a fixed point before checking. Unvisited predecessors
    are initially top, not an empty state that could falsely reject a loop. -/
def checkAllocation (original : CFG InstMData String AbsLoc) (actual : AllocatedCode) :
    Except String Unit := do
  unless original.blocks.map (·.id) == actual.blocks.map (·.id) do
    throw "allocation checker: block order or labels changed"
  let mut refs : Std.HashMap Nat (Inst InstMData String AbsLoc) := {}
  for (before, after) in original.blocks.zip actual.blocks do
    unless after.insts.filterMap (·.tag) == before.insts.map (·.tag.lineno) do
      throw s!"allocation checker: operations lost or reordered in {before.id}"
    for i in before.insts do refs := refs.insert i.tag.lineno i
    for i in after.insts do
      checkInstruction i
      if let some n := i.tag then
        let some old := refs[n]? | throw "allocation checker: unknown operation"
        unless sameInstShape old i do throw "allocation checker: operation changed"
      else
        unless i matches .mov .. do throw "allocation checker: inserted operation changes semantics"
    unless after.terminal.tag == some before.terminal.tag.lineno &&
        sameTerminalShape before.terminal after.terminal do
      throw "allocation checker: terminal changed"
    match after.terminal with
    | .br .. => throw "allocation checker: high-level branch remains"
    | .ret _ (.preg .eax) => pure ()
    | .ret .. => throw "allocation checker: return must use EAX"
    | _ => pure ()
  let cfg : CFG' (Option Nat) String AbsLoc := { actual with }
  let entry := initialState original
  let incoming := fun (out : Std.HashMap String CheckState) (idx : Nat) (id : String) => Id.run do
    let mut s := if idx == 0 then some entry else none
    for p in cfg.pred id do
      if let some prev := out[p]? then
        s := some (match s with | none => prev | some old => meet old prev)
    return s
  let mut outputs : Std.HashMap String CheckState := {}
  let mut changed := true
  while changed do
    changed := false
    for (b, idx) in actual.blocks.zipIdx do
      if let some input := incoming outputs idx b.id then
        let output ← runBlock refs b input false
        if !(outputs[b.id]?.isSome) || !sameState (outputs[b.id]?.getD {}) output then
          outputs := outputs.insert b.id output
          changed := true
  for ((old, b), idx) in (original.blocks.zip actual.blocks).zipIdx do
    if let some input := incoming outputs idx b.id then
      let output ← runBlock refs b input true
      checkInputs output old.terminal.uses b.terminal.uses old.terminal.tag.lineno
      checkFlags output old.terminal

end Cs4410sp19.MIR.RegAlloc
