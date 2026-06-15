import JoltBytecode.InstructionEquivalence.LoadReservedFamily.Common

/-!
# LR.D proof boundary

There is intentionally no `lrdProgram_eq_sail` theorem in this file.

The Rust-faithful Jolt expansion for `LR.D` is concrete:

1. write `rs1` into `reservation_d`;
2. write `rs1` into `reservation_w`;
3. run an ordinary `LD` into `rd`.

The generated Lean Sail semantics is not just an ordinary load. `LR.D` runs
`execute_LOADRES`, which performs the memory read and then calls
`load_reservation (bits_of_physaddr paddr) 8`.

That hook is an opaque axiom:

```
axiom load_reservation : Arch.pa -> Nat -> SailM Unit
```

The Sail state has no visible reservation field in `SequentialState`, and the
`regs` map is keyed only by the generated architectural `Register` enum. There
is no `Register` key for LR/SC reservation state. The related query hooks
`match_reservation` and `valid_reservation` are pure `Bool` functions, so they
cannot inspect the Sail state either.

As a result, this equivalence is not currently provable as a closed theorem.
Assuming `load_reservation p 8 s = .ok () s` would collapse Sail `LR.D` to an
ordinary `LD`, but that would be an external trust assumption and would not prove
the reservation behavior that Jolt models with virtual registers.

The intended theorem shape is left here, commented out, so the API target is
visible without introducing a `sorry` warning in `lake build`.

```
theorem lrdProgram_eq_sail
    (rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (h_mem : LoadReservedMemoryContext 8 addr addr js.sail) :
    projectResult ((JoltISA.execProgram
      (JoltISA.lrdProgram rs1 rd)).run js) =
      (execute_LOADRES false false rs1 8 rd).run js.sail := by
  -- Not provable without a trusted reservation-state contract for Sail.
```
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr

set_option autoImplicit true

noncomputable section

namespace LoadReservedFamily

end LoadReservedFamily

end
