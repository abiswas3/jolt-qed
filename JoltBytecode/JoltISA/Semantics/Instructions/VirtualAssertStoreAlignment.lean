import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualAssertStoreAlignment instruction semantics

Run lemmas for the store-alignment assertion instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful store-alignment assertion: when the effective address masked by
the instruction's alignment mask is zero, the assertion retires without
changing the combined Sail/Jolt state. -/
theorem execInstr_VirtualAssertStoreAlignment_run_aligned (base : regidx) (imm : BitVec 12)
    (mask : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits base js.sail = .ok x js.sail)
    (halign : (x + sign_extend (m := 64) imm) &&& mask = 0) :
    (execInstr (.VirtualAssertStoreAlignment base imm mask)).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.run]
  rw [if_neg (by intro h; exact h halign)]
  rfl

/-- Failed store-alignment assertion: the virtual assertion returns exactly
the Sail store/AMO address-alignment exception and prevents the tail of the
program from running. -/
theorem execInstr_VirtualAssertStoreAlignment_run_misaligned (base : regidx) (imm : BitVec 12)
    (mask : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits base js.sail = .ok x js.sail)
    (hmis : (x + sign_extend (m := 64) imm) &&& mask ≠ 0) :
    (execInstr (.VirtualAssertStoreAlignment base imm mask)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (x + sign_extend (m := 64) imm), ExceptionType.E_SAMO_Addr_Align ())) js := by
  unfold execInstr liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.run]
  rw [if_pos hmis]
  rfl

end JoltISA

end
