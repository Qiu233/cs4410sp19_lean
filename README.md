# cs4410sp19

## preparation

```bash
$ sudo apt install build-essential gcc-multilib nasm
```

## run

To compile and run the fle `ws/main.int`:
```bash
$ lake run
```

To run the tests:
```bash
$ lake test
```

To run some specific tests (e.g. type checking):
```bash
$ lake test -- tych
```

The register-allocation source and machine-IR tests can be run separately:
```bash
$ lake test -- regalloc
```

## register allocation

The native Lean allocator uses backward CFG liveness and global interference
graph coloring over `eax`, `ebx`, `ecx`, and `edx`. It supports multiple
definitions, loops, and multiple return blocks. Fixed-register shift/return
constraints are made explicit before coloring; calls clobber the caller-saved
registers. The assembly pass preserves callee-saved registers and aligns calls.

An uncolorable virtual register receives its own frame slot. Spill lowering uses
legal x86 memory operands and, when necessary, borrows a physical register with
an explicit frame-slot save and restore. These copies preserve EFLAGS and do
not change the parameter stack. Allocation removes one graph node per step and
spill lowering expands each instruction once: register pressure cannot cause
an allocation failure or an endless spill/reallocation loop. Stack-slot reuse
and live-range splitting are future optimizations.

Every allocation is checked before assembly. The checker verifies operation
order, instruction shapes, and symbolic value flow through inserted copies,
spills, reloads, CFG joins, and loops. It models call clobbers independently of
the allocator's metadata. Its input is lowered, two-address MIR; type checking
and other language-feature lowering remain separate compiler stages.

`lake exe ra-tests` compares 100 MIR fixtures using an independent interpreter
and actual 32-bit x86 execution, including ABI and call-alignment probes. It
also verifies that the checker rejects deliberately corrupted allocations.
