
namespace Cs4410sp19.Assembler

inductive Reg where
  | eax | ebx | edx | ecx
  | esp | ebp
  | esi | edi
deriving Inhabited

inductive Arg where
  | imm : UInt32 → Arg
  | reg : Reg → Arg
  | reg_offset : Reg → Int → Arg
  | mem : UInt32 → Arg
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
  | .ebx => "ebx"
  | .ecx => "ecx"
  | .edx => "edx"
  | .esp => "esp"
  | .ebp => "ebp"
  | .esi => "esi"
  | .edi => "edi"

instance : ToString Arg where
  toString
  | .imm v => s!"{v}"
  | .reg r => s!"{r}"
  | .reg_offset r i => s!"dword [{r} + {i}]"
  | .mem x => s!"[{x}]"

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
