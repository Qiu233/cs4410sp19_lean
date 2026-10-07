
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
  -- | mul : Arg → Instruction
  | imul : Arg → Arg → Instruction
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
  | .mov dst src    => s!"  mov {dst}, {src}"
  | .push src       => s!"  push {src}"
  | .pop src        => s!"  pop {src}"
  | .call dst       => s!"  call {dst}"
  | .ret            => s!"  ret"
  | .add dst src    => s!"  add {dst}, {src}"
  | .sub dst src    => s!"  sub {dst}, {src}"
  -- | .mul src        => s!"  mul {src}"
  | .imul dst src => s!"  imul {dst}, {src}"
  | .shl dst bits   => s!"  shl {dst}, {bits}"
  | .shr dst bits   => s!"  shr {dst}, {bits}"
  | .sar dst bits   => s!"  sar {dst}, {bits}"
  | .and dst src    => s!"  and {dst}, {src}"
  | .or dst src     => s!"  or {dst}, {src}"
  | .xor dst src    => s!"  xor {dst}, {src}"
  | .label name     => s!"{name}:"
  | .cmp x y        => s!"  cmp {x}, {y}"
  | .test x y       => s!"  test {x}, {y}"
  | .jmp name       => s!"  jmp {name}"
  | .je name        => s!"  je {name}"
  | .jl name        => s!"  jl {name}"
  | .jle name       => s!"  jle {name}"
  | .jg name        => s!"  jg {name}"
  | .jge name       => s!"  jge {name}"
  | .jz name        => s!"  jz {name}"
  | .jnz name       => s!"  jnz {name}"

def asm_to_string : Array Instruction → String := fun xs =>
  String.intercalate "\n" (xs.map toString).toList
