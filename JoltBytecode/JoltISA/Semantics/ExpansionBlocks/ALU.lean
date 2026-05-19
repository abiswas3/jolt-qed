import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.RegisterOps

/-!
# ALU expansion block semantics

These lemmas describe source-instruction inline blocks after they have been
lowered to real Jolt ISA rows.  They keep instruction-equivalence proofs from
depending on source-level pseudo-instructions that are not part of `JoltISA.Instr`.
-/

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- The Rust `SLLI` block's `VirtualMULI` value is the same left shift that
Sail uses for `SLLI`. -/
theorem slli_block_value_eq (x : BitVec 64) (shamt : BitVec 6) :
    jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt := by
  unfold jolt_virtual_muli_value slliMultiplier shift_bits_left
  exact (shiftLeft_eq_mul_pow2 x shamt.toNat).symm

/-- The encoded `SRAI` bitmask has trailing-zero count equal to the immediate
shift amount. -/
theorem ctz_sraiBitmask (shamt : BitVec 6) :
    ctz (sraiBitmask shamt) = shamt.toNat := by
  unfold sraiBitmask srliBitmask
  simp only [Nat.shiftLeft_eq, one_mul]
  set shift := shamt.toNat
  have h_lt : shift < 64 := by
    have := shamt.isLt
    norm_num at this
    exact this
  have h_diff_pos : 0 < 64 - shift := by omega
  have h_m_pos : 0 < 2 ^ (64 - shift) - 1 := by
    have : 2 ≤ 2 ^ (64 - shift) :=
      le_trans (show (2 : Nat) ≤ 2 ^ 1 from by norm_num)
        (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  rw [mul_comm, ctz_mul_pow2 shift h_m_pos, ctz_of_odd (pow2_sub_one_odd h_diff_pos)]
  omega

/-- The Rust `SRAI` block's `VirtualSRAI` value is the same arithmetic right
shift that Sail uses for `SRAI`. -/
theorem srai_block_value_eq (x : BitVec 64) (shamt : BitVec 6) :
    jolt_virtual_srai_value x (sraiBitmask shamt) = shift_bits_right_arith x shamt := by
  unfold jolt_virtual_srai_value shift_bits_right_arith
  simp [Sail.BitVec.toNatInt, ctz_sraiBitmask]

/-- The lowered `SLLI` block from a real source to a virtual destination reads
the architectural source and writes the shifted value to the virtual register. -/
private theorem slli_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualMULI (.vreg vd) (.xreg rs) (slliMultiplier shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt :=
    slli_block_value_eq x shamt
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The lowered `SLLI` block from a real source to a real destination reads the
architectural source and writes the shifted value through Sail. -/
private theorem slli_block_run_xreg_xreg
    (rd rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (shift_bits_left x shamt) js.sail = .ok () s') :
    (execInstr (.VirtualMULI (.xreg rd) (.xreg rs) (slliMultiplier shamt))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  have h_value :
      jolt_virtual_muli_value x (slliMultiplier shamt) = shift_bits_left x shamt :=
    slli_block_value_eq x shamt
  unfold execInstr readSrc writeDst liftSail
  simp only [h, h_value, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- Existential package for the lowered `SLLI` block from a real source to a
virtual destination.  It exposes the source read, the virtual-register write,
preservation of other virtual registers, and the block's effect on every
continuation program. -/
theorem exists_state_after_slli_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_left x shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (slliBlock (.vreg vd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold slliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using slli_block_run_vreg_xreg vd rs shamt js x h)]

/-- Existential package for the lowered `SLLI` block from a real source to a
real destination.  It exposes the source read, the architectural write,
preservation of virtual registers, and the block's effect on every continuation
program. -/
theorem exists_state_after_slli_block_run_xreg_xreg
    (rd rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = stateAfterWrite js.sail rd (shift_bits_left x shamt) ∧
      js'.vregs = js.vregs ∧
      ∀ tail,
        (execProgram (slliBlock (.xreg rd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  obtain ⟨s', h_write⟩ := wX_shape rd (shift_bits_left x shamt) js.sail
  let js' : SailJoltState := { sail := s', vregs := js.vregs }
  have h_sail_after_slli :
      s' = stateAfterWrite js.sail rd (shift_bits_left x shamt) :=
    wX_bits_eq_stateAfterWrite rd (shift_bits_left x shamt) js.sail s' h_write
  refine ⟨js', h, ?_, rfl, ?_⟩
  · exact h_sail_after_slli
  · intro tail
    unfold slliBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using slli_block_run_xreg_xreg rd rs shamt js x s' h h_write)]

/-- The lowered `SRAI` block from a virtual source to a virtual destination
writes the arithmetic right shift selected by the immediate. -/
private theorem srai_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    (execInstr (.VirtualSRAI (.vreg vd) (.vreg vs) (sraiBitmask shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith (js.vregs vs) shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_srai_value (js.vregs vs) (sraiBitmask shamt) =
        shift_bits_right_arith (js.vregs vs) shamt :=
    srai_block_value_eq (js.vregs vs) shamt
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- The lowered `SRAI` block from a real source to a virtual destination reads
the architectural source and writes the arithmetic right shift. -/
private theorem srai_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualSRAI (.vreg vd) (.xreg rs) (sraiBitmask shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then shift_bits_right_arith x shamt else js.vregs r } := by
  have h_value :
      jolt_virtual_srai_value x (sraiBitmask shamt) = shift_bits_right_arith x shamt :=
    srai_block_value_eq x shamt
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, h_value, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Existential package for the lowered `SRAI` block from a virtual source to
a virtual destination.  It exposes the virtual-register write, preservation of
other virtual registers, and the block's effect on every continuation program. -/
theorem exists_state_after_srai_block_run_vreg_vreg
    (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_right_arith (js.vregs vs) shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.vreg vs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right_arith (js.vregs vs) shamt else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold sraiBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using srai_block_run_vreg_vreg vd vs shamt js)]

/-- Existential package for the lowered `SRAI` block from a real source to a
virtual destination.  It exposes the source read, virtual-register write,
preservation of other virtual registers, and the block's effect on every
continuation program. -/
theorem exists_state_after_srai_block_run_vreg_xreg
    (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = js.sail ∧
      js'.vregs vd = shift_bits_right_arith x shamt ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      ∀ tail,
        (execProgram (sraiBlock (.vreg vd) (.xreg rs) shamt tail)).run js =
          (execProgram tail).run js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then shift_bits_right_arith x shamt else js.vregs r }
  refine ⟨js', h, rfl, ?_, ?_, ?_⟩
  · simp [js']
  · intro r hne
    simp [js', hne]
  · intro tail
    unfold sraiBlock
    rw [execProgram_instr_run_retire _ _ js js'
      (by simpa only [js'] using srai_block_run_vreg_xreg vd rs shamt js x h)]

end JoltISA

end
