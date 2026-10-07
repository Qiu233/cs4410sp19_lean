import Cs4410sp19.MIR.RA.Check

namespace Cs4410sp19.MIR

namespace RegAlloc

structure Allocation where
  original : CFG InstMData String AbsLoc
  homes : Homes
  allocated : AllocatedCode
  code : Code

/-- Native global graph coloring with total spill lowering. The checker runs on
    every function, before tags are erased and before assembly is emitted. -/
def allocate (cfg : Code) : Except String Allocation := do
  let original := compute_mdata (prepare cfg)
  let bundled : CFG' InstMData String AbsLoc := { original with }
  let live := computeLiveness bundled
  let graph := buildGraph bundled live
  let homes := colorGraph graph (Assemble.requiredFrameSlots original.unsetTag)
  let allocated ← lower original homes
  checkAllocation original allocated
  return { original, homes, allocated, code := allocated.unsetTag }

end RegAlloc

def allocate_registers (cfg : CFG Unit String AbsLoc) : Except String (CFG Unit String AbsLoc) := do
  return (← RegAlloc.allocate cfg).code

end Cs4410sp19.MIR
