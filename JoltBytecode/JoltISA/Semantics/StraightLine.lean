import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.Instructions.ADDI
import JoltBytecode.JoltISA.Semantics.Instructions.ANDI
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.ORI
import JoltBytecode.JoltISA.Semantics.Instructions.SLLI
import JoltBytecode.JoltISA.Semantics.Instructions.Sub
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualMULI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualPow2
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualPow2W
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRA
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRAI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRL
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSRLI
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualShiftRightBitmask
import JoltBytecode.JoltISA.Semantics.Instructions.VirtualSignExtendWord

/-!
# Straight-line Jolt ISA execution

These lemmas describe how `execProgram` steps through structured instruction
programs.  They are meant for bytecode expansions whose instructions usually
retire normally one after another, while still preserving the non-retire
short-circuiting behavior needed by loads.
-/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualMovsign` from a real register to a virtual register reads the real source,
writes the sign mask to the virtual destination, and leaves the Sail state
unchanged. -/
theorem movsign_run_vreg_xreg (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualMovsign (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualMovsign` from a real source to a virtual destination, packaged as
an instruction step from a known base Sail state. -/
theorem exists_state_after_movsign_run_vreg_xreg
    (vd : VReg) (rs : regidx) (js : SailJoltState)
    (s : SailState) (x : BitVec 64)
    (h_sail : js.sail = s)
    (h_read : rX_bits rs s = .ok x s) :
    ∃ js',
      rX_bits rs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_movsign_value x ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.VirtualMovsign (.vreg vd) (.xreg rs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_read_current : rX_bits rs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_read
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r }
  refine ⟨js', h_read_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using movsign_run_vreg_xreg vd rs js x h_read_current

/-- `XORI` on virtual registers is a pure virtual-register update.  It is one
of the extraction steps in the byte, halfword, and unsigned-word load
expansions. -/
theorem execInstr_xori_vreg_vreg_run (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) :
    (execInstr (.XORI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs vs ^^^ sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Jolt RV64 `LUI` writes the normalized immediate directly.  This is the
store-family mask materialization step used by `SB` and `SH`. -/
theorem execInstr_lui_vreg_run (vd : VReg) (imm : BitVec 64)
    (js : SailJoltState) :
    (execInstr (.LUI (.vreg vd) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then imm else js.vregs r } := by
  unfold execInstr writeDst writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLL` on virtual registers shifts one virtual value by the low six bits of
another virtual value.  This is the common "move the requested lane to the top
of the dword" step for byte, halfword, and unsigned-word loads. -/
theorem execInstr_sll_vreg_vreg_vreg_run (vd value shamt : VReg)
    (js : SailJoltState) :
    (execInstr (.SLL (.vreg vd) (.vreg value) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              shift_bits_left (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shamt) 5 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLL` can also read the value from a real register and the shift amount
from a virtual register before writing a virtual scratch register.  Store
expansions use this to move the low byte/halfword/word of `rs2` into the target
lane of the loaded dword. -/
theorem execInstr_sll_xreg_vreg_vreg_run (vd : VReg) (rs : regidx) (shamt : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.SLL (.vreg vd) (.xreg rs) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then
              shift_bits_left x (Sail.BitVec.extractLsb (js.vregs shamt) 5 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SRLI` on virtual registers is a pure virtual-register update.  `SW` uses
it to turn all-ones into the 32-bit store mask before shifting that mask into
the target word lane. -/
theorem execInstr_srli_vreg_vreg_run (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    (execInstr (.SRLI (.vreg vd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_right (js.vregs vs) shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `AND` on virtual registers is a pure virtual-register update.  Store
expansions use it to keep only the changed bytes under the shifted mask. -/
theorem execInstr_and_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.AND (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs &&& js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SRL` from virtual registers to a real register performs the final logical
right shift for `LW`, writing the shifted value through Sail's architectural
register write. -/
theorem execInstr_srl_vreg_vreg_xreg_run (rd : regidx) (value shamt : VReg)
    (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd
        (shift_bits_right (js.vregs value) (Sail.BitVec.extractLsb (js.vregs shamt) 5 0))
        js.sail = .ok () s') :
    (execInstr (.SRL (.xreg rd) (.vreg value) (.vreg shamt))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- `SRLI` from a virtual register to a real register performs the final
zero-extending extraction step for unsigned byte, halfword, and word loads. -/
theorem execInstr_srli_vreg_xreg_run (rd : regidx) (vs : VReg)
    (shamt : BitVec 6) (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (shift_bits_right (js.vregs vs) shamt) js.sail = .ok () s') :
    (execInstr (.SRLI (.xreg rd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- `SRAI` from a virtual register to a real register performs the final
sign-extending extraction step for signed byte and halfword loads. -/
theorem execInstr_srai_vreg_xreg_run (rd : regidx) (vs : VReg)
    (shamt : BitVec 6) (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (shift_bits_right_arith (js.vregs vs) shamt) js.sail = .ok () s') :
    (execInstr (.SRAI (.xreg rd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- Successful `LD`: if Sail's dword read pipeline returns `value`, then the
Jolt-ISA `LD` writes that dword to the destination virtual register and
continues with `RETIRE_SUCCESS`. -/
theorem ld_run_vreg_vreg_from_memory_read (vd base : VReg) (imm : BitVec 12)
    (js : SailJoltState) (value : BitVec 64)
    (h :
      vmem_read_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 0 8
        (Load Data) false false false js.sail =
        .ok (Ok value) js.sail) :
    (execInstr (.LD vd base imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold execInstr readVReg liftSail writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [h]
  simp only [EStateM.bind, EStateM.pure, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet]

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
low bit set, the assertion returns the same load-address-alignment exception
that Sail will later produce for the corresponding `execute_LOAD`. -/
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

/-- Successful `SD`: if Sail's dword write pipeline returns success, then the
Jolt-ISA `SD` retires with the produced Sail state and preserves virtual
registers. -/
theorem execInstr_sd_vreg_run_of_write (base value : VReg) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (h :
      vmem_write_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 8
        (js.vregs value) (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    (execInstr (.SD base value imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [h]
  rfl

/-- `MULHU` from two real sources to a virtual destination reads both real
sources, writes the unsigned high product, and leaves the Sail state unchanged
when both reads are state-preserving. -/
theorem mulhu_run_vreg_xreg_xreg (vd : VReg) (lhs rhs : regidx)
    (js : SailJoltState) (x y : BitVec 64)
    (h₁ : rX_bits lhs js.sail = .ok x js.sail)
    (h₂ : rX_bits rhs js.sail = .ok y js.sail) :
    (execInstr (.MULHU (.vreg vd) (.xreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_mulhu_value x y else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h₁, h₂, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `MULHU` from two real sources to a virtual destination, packaged from a
known base Sail state. -/
theorem exists_state_after_mulhu_run_vreg_xreg_xreg
    (vd : VReg) (lhs rhs : regidx) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : rX_bits lhs s = .ok x s)
    (h_rhs : rX_bits rhs s = .ok y s) :
    ∃ js',
      rX_bits lhs js.sail = .ok x js.sail ∧
      rX_bits rhs js.sail = .ok y js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_mulhu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.MULHU (.vreg vd) (.xreg lhs) (.xreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_lhs_current : rX_bits lhs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_lhs
  have h_rhs_current : rX_bits rhs js.sail = .ok y js.sail := by
    simpa only [h_sail] using h_rhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_mulhu_value x y else js.vregs r }
  refine ⟨js', h_lhs_current, h_rhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js']
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using
      mulhu_run_vreg_xreg_xreg vd lhs rhs js x y h_lhs_current h_rhs_current

/-- `MULHU` from a virtual source and a real source to a virtual destination
reads the real source through Sail and writes the unsigned high product. -/
theorem mulhu_run_vreg_vreg_xreg (vd lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail) :
    (execInstr (.MULHU (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_mulhu_value (js.vregs lhs) y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `MULHU` from a virtual source and a real source to a virtual destination,
packaged from a known virtual-source value and a known base Sail state. -/
theorem exists_state_after_mulhu_run_vreg_vreg_xreg
    (vd lhs : VReg) (rhs : regidx) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : rX_bits rhs s = .ok y s) :
    ∃ js',
      rX_bits rhs js.sail = .ok y js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = jolt_mulhu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.MULHU (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_rhs_current : rX_bits rhs js.sail = .ok y js.sail := by
    simpa only [h_sail] using h_rhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_mulhu_value (js.vregs lhs) y else js.vregs r }
  refine ⟨js', h_rhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js', h_lhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using mulhu_run_vreg_vreg_xreg vd lhs rhs js y h_rhs_current

/-- `XOR` from a real source and a virtual source to a virtual destination reads
the real source through Sail and writes the xor result. -/
theorem xor_run_vreg_xreg_vreg (vd : VReg) (lhs : regidx) (rhs : VReg)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits lhs js.sail = .ok x js.sail) :
    (execInstr (.XOR (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x ^^^ js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `XOR` from a real source and a virtual source to a virtual destination,
packaged from a known virtual-source value and a known base Sail state. -/
theorem exists_state_after_xor_run_vreg_xreg_vreg
    (vd : VReg) (lhs : regidx) (rhs : VReg) (js : SailJoltState)
    (s : SailState) (x y : BitVec 64)
    (h_sail : js.sail = s)
    (h_lhs : rX_bits lhs s = .ok x s)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      rX_bits lhs js.sail = .ok x js.sail ∧
      js'.sail = s ∧
      js'.vregs vd = x ^^^ y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.XOR (.vreg vd) (.xreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  have h_lhs_current : rX_bits lhs js.sail = .ok x js.sail := by
    simpa only [h_sail] using h_lhs
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then x ^^^ js.vregs rhs else js.vregs r }
  refine ⟨js', h_lhs_current, ?_, ?_, ?_, ?_⟩
  · exact h_sail
  · simp [js', h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using xor_run_vreg_xreg_vreg vd lhs rhs js x h_lhs_current

/-- `XOR` on virtual sources and a virtual destination reads both virtual
sources, writes their xor, and leaves the Sail state unchanged. -/
theorem xor_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs ^^^ js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `XOR` from two virtual sources to a virtual destination, packaged from
known virtual-source values. -/
theorem exists_state_after_xor_run_vreg_vreg_vreg
    (vd lhs rhs : VReg) (js : SailJoltState) (x y : BitVec 64)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = x ^^^ y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then js.vregs lhs ^^^ js.vregs rhs else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_lhs, h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using xor_run_vreg_vreg_vreg vd lhs rhs js

/-- `SLTU` on virtual sources and a virtual destination reads both virtual
sources and writes the unsigned less-than flag. -/
theorem sltu_run_vreg_vreg_vreg (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLTU` from two virtual sources to a virtual destination, packaged from
known virtual-source values. -/
theorem exists_state_after_sltu_run_vreg_vreg_vreg
    (vd lhs rhs : VReg) (js : SailJoltState) (x y : BitVec 64)
    (h_lhs : js.vregs lhs = x)
    (h_rhs : js.vregs rhs = y) :
    ∃ js',
      js'.sail = js.sail ∧
      js'.vregs vd = jolt_sltu_value x y ∧
      (∀ r, r ≠ vd → js'.vregs r = js.vregs r) ∧
      (execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
        .ok RETIRE_SUCCESS js' := by
  let js' : SailJoltState :=
    { sail := js.sail
      vregs := fun r => if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs)
        else js.vregs r }
  refine ⟨js', rfl, ?_, ?_, ?_⟩
  · simp [js', h_lhs, h_rhs]
  · intro r hne
    simp [js', hne]
  · simpa only [js'] using sltu_run_vreg_vreg_vreg vd lhs rhs js

/-- If the head instruction retires successfully, running a program continues
from the state produced by that instruction and executes the tail. -/
theorem execProgram_instr_run_retire (instr : Instr) (rest : Program)
    (js js' : SailJoltState)
    (h : (execInstr instr).run js = .ok RETIRE_SUCCESS js') :
    (execProgram (.instr instr rest)).run js = (execProgram rest).run js' := by
  change execInstr instr js = .ok RETIRE_SUCCESS js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]
  rfl

/-- If the head instruction throws an error, running a program throws the same
error and does not execute the tail. -/
theorem execProgram_instr_run_error (instr : Instr) (rest : Program)
    (js js' : SailJoltState) (e : Error exception)
    (h : (execInstr instr).run js = .error e js') :
    (execProgram (.instr instr rest)).run js = .error e js' := by
  change execInstr instr js = .error e js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]

/-- If the head instruction returns a memory exception as an ordinary
`ExecutionResult`, the structured program returns that exception immediately
and does not execute the tail.  This is the program-level early-exit rule used
by alignment assertions and failed memory reads. -/
theorem execProgram_instr_run_memory_exception (instr : Instr) (rest : Program)
    (js js' : SailJoltState) (e : virtaddr × ExceptionType)
    (h : (execInstr instr).run js = .ok (ExecutionResult.Memory_Exception e) js') :
    (execProgram (.instr instr rest)).run js =
      .ok (ExecutionResult.Memory_Exception e) js' := by
  change execInstr instr js = .ok (ExecutionResult.Memory_Exception e) js' at h
  simp only [execProgram_instr, EStateM.run, bind, EStateM.bind]
  rw [h]
  rfl

end JoltISA

end
