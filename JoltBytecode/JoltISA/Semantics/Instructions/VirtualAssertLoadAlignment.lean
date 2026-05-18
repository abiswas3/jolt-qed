import JoltBytecode.JoltISA.Semantics.Lemmas

/-!
# VirtualAssertLoadAlignment instruction semantics

Run lemmas for the load-alignment assertion instruction.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- Successful load-alignment assertion: when the effective address masked by
the instruction's alignment mask is zero, the assertion retires and does not
change either Sail state or virtual registers. -/
theorem execInstr_VirtualAssertLoadAlignment_run_aligned (base : regidx) (imm : BitVec 12)
    (mask : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits base js.sail = .ok x js.sail)
    (halign : (x + sign_extend (m := 64) imm) &&& mask = 0) :
    (execInstr (.VirtualAssertLoadAlignment base imm mask)).run js =
      .ok RETIRE_SUCCESS js := by
  unfold execInstr liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.run]
  rw [if_neg (by intro h; exact h halign)]
  rfl

/-- Failed load-alignment assertion: when the effective address has a masked
low bit set, the assertion returns Sail's load-address-alignment exception. -/
theorem execInstr_VirtualAssertLoadAlignment_run_misaligned (base : regidx) (imm : BitVec 12)
    (mask : BitVec 64) (js : SailJoltState) (x : BitVec 64)
    (hread : rX_bits base js.sail = .ok x js.sail)
    (hmis : (x + sign_extend (m := 64) imm) &&& mask ≠ 0) :
    (execInstr (.VirtualAssertLoadAlignment base imm mask)).run js =
      .ok (ExecutionResult.Memory_Exception
        (Virtaddr (x + sign_extend (m := 64) imm), ExceptionType.E_Load_Addr_Align ())) js := by
  unfold execInstr liftSail
  simp only [hread, bind, EStateM.bind, pure, EStateM.run]
  rw [if_pos hmis]
  rfl

end JoltISA

end
