import Cs4410sp19.Assembler
import Cs4410sp19.MIR.Basic
import Cs4410sp19.MIR.MData

namespace Cs4410sp19
namespace MIR

namespace Assemble

structure Context where
  frameSlots : Nat

@[inline] private def Context.frameBytes (ctx : Context) : Nat :=
  ctx.frameSlots * 4

@[inline] private def Context.requireSlot (ctx : Context) (slot : Nat) : Unit :=
  if slot < ctx.frameSlots then
    ()
  else
    panic! s!"assemble: frame slot {slot} exceeds allocated stack slots ({ctx.frameSlots})"

private def gprToReg : GPR32 → Assembler.Reg
  | .eax => Assembler.Reg.eax
  | .ebx => Assembler.Reg.ebx
  | .ecx => Assembler.Reg.ecx
  | .edx => Assembler.Reg.edx

private def frameOffset (slot : Nat) : Int :=
  let bytes := (slot + 1) * 4
  Int.negOfNat bytes

private def argOffset (idx : Nat) : Int :=
  let bytes := 8 + idx * 4
  Int.ofNat bytes

private def isMemLoc : AbsLoc → Bool
  | .frame _ | .arg _ => true
  | _ => false

private def isImmLoc : AbsLoc → Bool
  | .imm _ => true
  | _ => false

private def isRegLoc : AbsLoc → Bool
  | .preg _ => true
  | _ => false

private def ensureDestNotImm (op : String) (dst : AbsLoc) : Unit :=
  if isImmLoc dst then
    panic! s!"assemble: {op} destination cannot be an immediate ({dst})"
  else
    ()

private def ensureNotBothMem (op : String) (lhs rhs : AbsLoc) : Unit :=
  if isMemLoc lhs && isMemLoc rhs then
    panic! s!"assemble: {op} does not allow two memory operands ({lhs}, {rhs})"
  else
    ()

private def ensureTwoAddr (op : String) (dst first : AbsLoc) : Unit :=
  if dst == first then
    ()
  else
    panic! s!"assemble: {op} requires destination and first operand to be identical (dst={dst}, first={first})"

private def ensureShiftAmount (op : String) (amount : AbsLoc) : Unit :=
  match amount with
  | .imm _ => ()
  | .preg .ecx => ()
  | .preg r => panic! s!"assemble: {op} shift count register must be ecx/CL, got {r}"
  | _ => panic! s!"assemble: {op} shift count must be immediate or ecx, got {amount}"

private def ensureCmpLhs (op : String) (lhs : AbsLoc) : Unit :=
  if isImmLoc lhs then
    panic! s!"assemble: {op} cannot use an immediate as the first operand ({lhs})"
  else
    ()

private def ensureMulDestReg (dst : AbsLoc) : Unit :=
  if isRegLoc dst then
    ()
  else
    panic! s!"assemble: imul destination must be a register, got {dst}"

private def toArg (ctx : Context) : AbsLoc → Assembler.Arg
  | .imm v => Assembler.Arg.imm v
  | .preg r => Assembler.Arg.reg (gprToReg r)
  | .frame slot =>
      let _ := ctx.requireSlot slot
      Assembler.Arg.reg_offset Assembler.Reg.ebp (frameOffset slot)
  | .arg idx => Assembler.Arg.reg_offset Assembler.Reg.ebp (argOffset idx)
  | .vreg v => panic! s!"assemble: unresolved virtual register {v}"

private def instOperands : Inst σ γ AbsLoc → Array AbsLoc
  | .mov _ dst src => #[dst, src]
  | .add _ dst x y => #[dst, x, y]
  | .sub _ dst x y => #[dst, x, y]
  | .mul _ dst x y => #[dst, x, y]
  | .band _ dst x y => #[dst, x, y]
  | .bor _ dst x y => #[dst, x, y]
  | .xor _ dst x y => #[dst, x, y]
  | .push _ x => #[x]
  | .pop _ dst => #[dst]
  | .pop' _ => #[]
  | .cmp _ x y => #[x, y]
  | .test _ x y => #[x, y]
  | .shl _ dst x y => #[dst, x, y]
  | .shr _ dst x y => #[dst, x, y]
  | .sar _ dst x y => #[dst, x, y]
  | .call' _ _ => #[]
  | .call .. => panic! "assemble: unexpected high-level call instruction"
  | .lt .. | .le .. | .gt .. | .ge .. | .eq .. | .ne .. => panic! "assemble: logical instructions must be lowered before assembly"

private def termOperands : Terminal σ γ AbsLoc → Array AbsLoc
  | .ret _ v => #[v]
  | .br .. => panic! "assemble: branch terminals must be lowered before assembly"
  | _ => #[]

def requiredFrameSlots (cfg : CFG Unit String AbsLoc) : Nat := Id.run do
  let mut needed := 0
  for block in cfg.blocks do
    for inst in block.insts do
      for loc in instOperands inst do
        match loc with
        | .frame slot =>
            let slotsNeeded := slot + 1
            needed := Nat.max needed slotsNeeded
        | _ => ()
    for loc in termOperands block.terminal do
      match loc with
      | .frame slot =>
          let slotsNeeded := slot + 1
          needed := Nat.max needed slotsNeeded
      | _ => ()
  return needed

def prologue (ctx : Context) : Array Assembler.Instruction :=
  Id.run do
    let mut insts : Array Assembler.Instruction :=
      #[Assembler.Instruction.push (Assembler.Arg.reg Assembler.Reg.ebp),
        Assembler.Instruction.mov (Assembler.Arg.reg Assembler.Reg.ebp)
          (Assembler.Arg.reg Assembler.Reg.esp)]
    let frameBytes := ctx.frameBytes
    if frameBytes == 0 then
      insts
    else
      insts.push (Assembler.Instruction.sub (Assembler.Arg.reg Assembler.Reg.esp)
        (Assembler.Arg.imm (UInt32.ofNat frameBytes)))

private def epilog : Array Assembler.Instruction :=
  #[Assembler.Instruction.mov (Assembler.Arg.reg Assembler.Reg.esp)
      (Assembler.Arg.reg Assembler.Reg.ebp),
    Assembler.Instruction.pop (Assembler.Arg.reg Assembler.Reg.ebp),
    Assembler.Instruction.ret]

private def assembleInst (ctx : Context) :
    Inst Unit String AbsLoc → Array Assembler.Instruction
  | .mov _ dst src =>
      let _ := ensureDestNotImm "mov" dst
      let _ := ensureNotBothMem "mov" dst src
      #[Assembler.Instruction.mov (toArg ctx dst) (toArg ctx src)]
  | .add _ dst x y =>
      let _ := ensureTwoAddr "add" dst x
      let _ := ensureDestNotImm "add" dst
      let _ := ensureNotBothMem "add" dst y
      #[Assembler.Instruction.add (toArg ctx dst) (toArg ctx y)]
  | .sub _ dst x y =>
      let _ := ensureTwoAddr "sub" dst x
      let _ := ensureDestNotImm "sub" dst
      let _ := ensureNotBothMem "sub" dst y
      #[Assembler.Instruction.sub (toArg ctx dst) (toArg ctx y)]
  | .band _ dst x y =>
      let _ := ensureTwoAddr "and" dst x
      let _ := ensureDestNotImm "and" dst
      let _ := ensureNotBothMem "and" dst y
      #[Assembler.Instruction.and (toArg ctx dst) (toArg ctx y)]
  | .bor _ dst x y =>
      let _ := ensureTwoAddr "or" dst x
      let _ := ensureDestNotImm "or" dst
      let _ := ensureNotBothMem "or" dst y
      #[Assembler.Instruction.or (toArg ctx dst) (toArg ctx y)]
  | .xor _ dst x y =>
      let _ := ensureTwoAddr "xor" dst x
      let _ := ensureDestNotImm "xor" dst
      let _ := ensureNotBothMem "xor" dst y
      #[Assembler.Instruction.xor (toArg ctx dst) (toArg ctx y)]
  | .mul _ dst x y =>
      let _ := ensureDestNotImm "imul" dst
      let _ := ensureMulDestReg dst
      #[Assembler.Instruction.imul (toArg ctx dst) (toArg ctx x) (toArg ctx y)]
  | .push _ src =>
      #[Assembler.Instruction.push (toArg ctx src)]
  | .pop _ dst =>
      let _ := ensureDestNotImm "pop" dst
      #[Assembler.Instruction.pop (toArg ctx dst)]
  | .pop' _ =>
      #[Assembler.Instruction.add (Assembler.Arg.reg Assembler.Reg.esp)
        (Assembler.Arg.imm (UInt32.ofNat 4))]
  | .cmp _ x y =>
      let _ := ensureCmpLhs "cmp" x
      let _ := ensureNotBothMem "cmp" x y
      #[Assembler.Instruction.cmp (toArg ctx x) (toArg ctx y)]
  | .test _ x y =>
      let _ := ensureCmpLhs "test" x
      let _ := ensureNotBothMem "test" x y
      #[Assembler.Instruction.test (toArg ctx x) (toArg ctx y)]
  | .shl _ dst x amount =>
      let _ := ensureTwoAddr "shl" dst x
      let _ := ensureDestNotImm "shl" dst
      let _ := ensureShiftAmount "shl" amount
      #[Assembler.Instruction.shl (toArg ctx dst) (toArg ctx amount)]
  | .shr _ dst x amount =>
      let _ := ensureTwoAddr "shr" dst x
      let _ := ensureDestNotImm "shr" dst
      let _ := ensureShiftAmount "shr" amount
      #[Assembler.Instruction.shr (toArg ctx dst) (toArg ctx amount)]
  | .sar _ dst x amount =>
      let _ := ensureTwoAddr "sar" dst x
      let _ := ensureDestNotImm "sar" dst
      let _ := ensureShiftAmount "sar" amount
      #[Assembler.Instruction.sar (toArg ctx dst) (toArg ctx amount)]
  | .call' _ target =>
      #[Assembler.Instruction.call target]
  | inst =>
      panic! s!"assemble: unsupported instruction after lowering: {inst}"

private def assembleTerminal (ctx : Context) :
    Terminal Unit String AbsLoc → Array Assembler.Instruction
  | .jmp _ target => #[Assembler.Instruction.jmp target]
  | .jl _ target => #[Assembler.Instruction.jl target]
  | .jle _ target => #[Assembler.Instruction.jle target]
  | .jg _ target => #[Assembler.Instruction.jg target]
  | .jge _ target => #[Assembler.Instruction.jge target]
  | .jz _ target => #[Assembler.Instruction.jz target]
  | .jnz _ target => #[Assembler.Instruction.jnz target]
  | .ret _ value =>
      let insts := #[Assembler.Instruction.mov (Assembler.Arg.reg Assembler.Reg.eax) (toArg ctx value)]
      insts ++ epilog
  | term =>
      panic! s!"assemble: unsupported terminal after lowering: {term}"

def assembleBlock (ctx : Context) (block : BasicBlock Unit String AbsLoc) :
    Array Assembler.Instruction :=
  Id.run do
    let mut insts : Array Assembler.Instruction := #[]
    for inst in block.insts do
      insts := insts.append (assembleInst ctx inst)
    insts := insts.append (assembleTerminal ctx block.terminal)
    insts

end Assemble

open Assemble

def assemble (cfg : CFG Unit String AbsLoc) : Array Assembler.Instruction := Id.run do
  let frameSlots := Assemble.requiredFrameSlots cfg
  let ctx : Assemble.Context := { frameSlots := frameSlots }
  let mut insts : Array Assembler.Instruction := #[]
  let mut first := true
  for block in cfg.blocks do
    insts := insts.push (Assembler.Instruction.label block.id)
    if first then
      insts := insts.append (Assemble.prologue ctx)
      first := false
    insts := insts.append (Assemble.assembleBlock ctx block)
  insts

end MIR
end Cs4410sp19
