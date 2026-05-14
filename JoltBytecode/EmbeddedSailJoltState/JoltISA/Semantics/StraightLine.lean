import JoltBytecode.EmbeddedSailJoltState.JoltISA.Semantics.Lemmas

/-!
# Straight-line Jolt ISA execution

These lemmas describe how `execProgram` steps through structured instruction
programs.  They are meant for bytecode expansions whose instructions usually
retire normally one after another, while still preserving the non-retire
short-circuiting behavior needed by loads.

This seems to be my step one instruction, state looks like this lemmas. 
TODO: Not sure this is the right place for these.
-/

/- set_option maxHeartbeats 1_000_000_000 -/

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace JoltISA

/-- `VirtualMovsign` from a real register to a virtual register reads the real source,
writes the sign mask to the virtual destination, and leaves the Sail state
unchanged. -/
theorem execInstr_movsign_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualMovsign (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_movsign_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ANDI` on virtual registers reads the virtual source, writes the masked
value to the virtual destination, and leaves the Sail state unchanged. -/
theorem execInstr_andi_vreg_vreg_run (vd vs : VReg) (imm : BitVec 12)
    (js : SailJoltState) :
    (execInstr (.ANDI (.vreg vd) (.vreg vs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs vs &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ADDI` from a real register to a virtual register is the load/store setup
step used by the Rust expansions.  It reads the architectural base register
through Sail, writes the effective address to a virtual register, and leaves
the Sail state unchanged when the read is state-preserving. -/
theorem execInstr_addi_xreg_vreg_run (vd : VReg) (rs : regidx)
    (imm : BitVec 12) (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ADDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then x + sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

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

/-- `SLLI` on virtual registers is a pure virtual-register update.  Load
expansions use it to multiply a byte offset by eight before shifting the
loaded dword. -/
theorem execInstr_slli_vreg_vreg_run (vd vs : VReg) (shamt : BitVec 6)
    (js : SailJoltState) :
    (execInstr (.SLLI (.vreg vd) (.vreg vs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left (js.vregs vs) shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
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

/-- `VirtualSignExtendWord` from a real register to the same real register models Jolt's
virtual sign-extension instruction after an `LW` shift.  The theorem is stated
for any real source and destination because the semantics supports that
generality. -/
theorem execInstr_sextw_xreg_xreg_run (rd rs : regidx)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (hr : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)) js.sail =
      .ok () s') :
    (execInstr (.VirtualSignExtendWord (.xreg rd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [hr, bind, EStateM.bind, pure, EStateM.pure, EStateM.run, hw]

/-- Successful `LD`: if Sail's dword read pipeline returns `value`, then the
Jolt-ISA `LD` writes that dword to the destination virtual register and
continues with `RETIRE_SUCCESS`. -/
theorem execInstr_ld_vreg_run_of_read (vd base : VReg) (imm : BitVec 12)
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

/-- `ADD` on virtual sources and a virtual destination reads both virtual
sources, writes their sum, and leaves the Sail state unchanged. -/
theorem execInstr_add_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.ADD (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs + js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ADD` from two virtual sources to a real destination reads both virtual
sources, writes their sum through `wX_bits`, and preserves virtual registers. -/
theorem execInstr_add_vreg_vreg_xreg_run (rd : regidx) (lhs rhs : VReg)
    (js : SailJoltState) (s' : SailState)
    (h : wX_bits rd (js.vregs lhs + js.vregs rhs) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, h]

/-- `ADD` from two real sources to a real destination reads both architectural
sources and writes their sum through Sail.  This is the instruction effect used
by the program-level `ADDW` expansion before the final sign-extension step. -/
theorem execInstr_add_xreg_xreg_xreg_run (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x + y) js.sail = .ok () s') :
    (execInstr (.ADD (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `SUB` from two real sources to a real destination reads both architectural
sources and writes their difference through Sail. -/
theorem execInstr_sub_xreg_xreg_xreg_run (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x - y) js.sail = .ok () s') :
    (execInstr (.SUB (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `ADDI` from a real source to a real destination reads the source through
Sail and writes the immediate sum through Sail. -/
theorem execInstr_addi_xreg_xreg_run (rd rs1 : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x + sign_extend (m := 64) imm) js.sail = .ok () s') :
    (execInstr (.ADDI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `MUL` from a virtual source and a real source to a virtual destination reads
the real source through Sail, writes the low product to the virtual destination,
and leaves the Sail state unchanged when the real read is state-preserving. -/
theorem execInstr_mul_vreg_xreg_vreg_run (vd lhs : VReg) (rhs : regidx)
    (js : SailJoltState) (y : BitVec 64)
    (h : rX_bits rhs js.sail = .ok y js.sail) :
    (execInstr (.MUL (.vreg vd) (.vreg lhs) (.xreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs * y else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `MUL` from a real source and a virtual source to a real destination is the
second instruction in the `SLL` and `SLLW` program expansions.  It consumes the
scratch virtual register computed by a preceding power-of-two instruction and
writes the product through Sail. -/
theorem execInstr_mul_xreg_xreg_vreg_run (rd rs1 : regidx) (vs2 : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (x * js.vregs vs2) js.sail = .ok () s') :
    (execInstr (.MUL (.xreg rd) (.xreg rs1) (.vreg vs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `MUL` from two real sources to a real destination reads both architectural
sources and writes the low product through Sail. -/
theorem execInstr_mul_xreg_xreg_xreg_run (rd rs1 rs2 : regidx)
    (js : SailJoltState) (x y : BitVec 64) (s' : SailState)
    (h₁ : rX_bits rs1 js.sail = .ok x js.sail)
    (h₂ : rX_bits rs2 js.sail = .ok y js.sail)
    (hw : wX_bits rd (x * y) js.sail = .ok () s') :
    (execInstr (.MUL (.xreg rd) (.xreg rs1) (.xreg rs2))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h₁, h₂, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualMULI` from a real source to a real destination multiplies the
source by the encoded immediate and writes the result through Sail. -/
theorem execInstr_virtualMULI_xreg_xreg_run (rd rs1 : regidx)
    (imm : BitVec 64) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs1 js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_muli_value x imm) js.sail = .ok () s') :
    (execInstr (.VirtualMULI (.xreg rd) (.xreg rs1) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualPow2` from a real source to a virtual destination writes
`2 ^ rs[5:0]` to the scratch virtual register and leaves Sail unchanged. -/
theorem execInstr_virtualPow2_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualPow2 (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_virtual_pow2_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualPow2W` is the word-sized power-of-two helper.  It writes
`2 ^ rs[4:0]` to a virtual destination and leaves Sail unchanged. -/
theorem execInstr_virtualPow2W_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualPow2W (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_virtual_pow2w_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualShiftRightBitmask` from a real source to a virtual destination
materializes the bitmask consumed by `VirtualSRL` and `VirtualSRA`. -/
theorem execInstr_virtualShiftRightBitmask_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value x else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualShiftRightBitmask` can also read the shift amount from a virtual
register, which is how the word-shift expansions feed masked shift amounts
into `VirtualSRL`/`VirtualSRA`. -/
theorem execInstr_virtualShiftRightBitmask_vreg_vreg_run (vd vs : VReg)
    (js : SailJoltState) :
    (execInstr (.VirtualShiftRightBitmask (.vreg vd) (.vreg vs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then jolt_virtual_shift_right_bitmask_value (js.vregs vs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualSRLI` from a real source to a real destination writes the logical
right shift selected by the encoded immediate bitmask. -/
theorem execInstr_virtualSRLI_xreg_xreg_run (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srli_value x bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRLI (.xreg rd) (.xreg rs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualSRLI` can consume a value from a virtual register and write the
logical shift result to a real destination. -/
theorem execInstr_virtualSRLI_vreg_xreg_run (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srli_value (js.vregs vs) bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRLI (.xreg rd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRAI` from a real source to a real destination writes the
arithmetic right shift selected by the encoded immediate bitmask. -/
theorem execInstr_virtualSRAI_xreg_xreg_run (rd rs : regidx)
    (bitmask : Nat) (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srai_value x bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.xreg rs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run]

/-- `VirtualSRAI` can consume a value from a virtual register and write the
arithmetic shift result to a real destination. -/
theorem execInstr_virtualSRAI_vreg_xreg_run (rd : regidx) (vs : VReg)
    (bitmask : Nat) (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srai_value (js.vregs vs) bitmask) js.sail = .ok () s') :
    (execInstr (.VirtualSRAI (.xreg rd) (.vreg vs) bitmask)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRL` from a real value and a virtual bitmask to a real destination
is the two-instruction `SRL` program's final write. -/
theorem execInstr_virtualSRL_xreg_vreg_xreg_run (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_srl_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRL (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRL` can also read both its value and its bitmask from virtual
registers before writing the result to a real destination. -/
theorem execInstr_virtualSRL_vreg_vreg_xreg_run (rd : regidx) (vvalue vbitmask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_srl_value (js.vregs vvalue) (js.vregs vbitmask))
      js.sail = .ok () s') :
    (execInstr (.VirtualSRL (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRA` from a real value and a virtual bitmask to a real destination
is the arithmetic sibling of `execInstr_virtualSRL_xreg_vreg_xreg_run`. -/
theorem execInstr_virtualSRA_xreg_vreg_xreg_run (rd rs : regidx) (vbitmask : VReg)
    (js : SailJoltState) (x : BitVec 64) (s' : SailState)
    (h : rX_bits rs js.sail = .ok x js.sail)
    (hw : wX_bits rd (jolt_virtual_sra_value x (js.vregs vbitmask)) js.sail = .ok () s') :
    (execInstr (.VirtualSRA (.xreg rd) (.xreg rs) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [h, hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `VirtualSRA` can read both its value and its bitmask from virtual registers
before writing the result through Sail. -/
theorem execInstr_virtualSRA_vreg_vreg_xreg_run (rd : regidx) (vvalue vbitmask : VReg)
    (js : SailJoltState) (s' : SailState)
    (hw : wX_bits rd (jolt_virtual_sra_value (js.vregs vvalue) (js.vregs vbitmask))
      js.sail = .ok () s') :
    (execInstr (.VirtualSRA (.xreg rd) (.vreg vvalue) (.vreg vbitmask))).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc writeDst readVReg liftSail
  simp only [hw, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]

/-- `SLLI` from a real source to a virtual destination writes the shifted value
to the scratch register and leaves Sail unchanged. -/
theorem execInstr_slli_xreg_vreg_run (vd : VReg) (rs : regidx) (shamt : BitVec 6)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.SLLI (.vreg vd) (.xreg rs) shamt)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then shift_bits_left x shamt else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ORI` from a real source to a virtual destination is the word-shift helper
that sets bit five of a variable shift amount before bitmask encoding. -/
theorem execInstr_ori_xreg_vreg_run (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ORI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x ||| sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `ANDI` from a real source to a virtual destination is the word arithmetic
right-shift helper that masks the variable shift amount to five bits. -/
theorem execInstr_andi_xreg_vreg_run (vd : VReg) (rs : regidx) (imm : BitVec 12)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.ANDI (.vreg vd) (.xreg rs) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then x &&& sign_extend (m := 64) imm else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `VirtualSignExtendWord` from a real source to a virtual destination computes the
word-sign-extended scratch value used by `SRAW` and `SRAIW`. -/
theorem execInstr_sextw_xreg_vreg_run (vd : VReg) (rs : regidx)
    (js : SailJoltState) (x : BitVec 64)
    (h : rX_bits rs js.sail = .ok x js.sail) :
    (execInstr (.VirtualSignExtendWord (.vreg vd) (.xreg rs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r =>
            if r = vd then sign_extend (m := 64) (Sail.BitVec.extractLsb x 31 0)
            else js.vregs r } := by
  unfold execInstr readSrc writeDst liftSail writeVReg
  simp only [h, bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `MULHU` from two real sources to a virtual destination reads both real
sources, writes the unsigned high product, and leaves the Sail state unchanged
when both reads are state-preserving. -/
theorem execInstr_mulhu_xreg_xreg_vreg_run (vd : VReg) (lhs rhs : regidx)
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

/-- `MULHU` from a virtual source and a real source to a virtual destination
reads the real source through Sail and writes the unsigned high product. -/
theorem execInstr_mulhu_vreg_xreg_vreg_run (vd lhs : VReg) (rhs : regidx)
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

/-- `XOR` from a real source and a virtual source to a virtual destination reads
the real source through Sail and writes the xor result. -/
theorem execInstr_xor_xreg_vreg_vreg_run (vd : VReg) (lhs : regidx) (rhs : VReg)
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

/-- `XOR` on virtual sources and a virtual destination reads both virtual
sources, writes their xor, and leaves the Sail state unchanged. -/
theorem execInstr_xor_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.XOR (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then js.vregs lhs ^^^ js.vregs rhs else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- `SLTU` on virtual sources and a virtual destination reads both virtual
sources and writes the unsigned less-than flag. -/
theorem execInstr_sltu_vreg_vreg_vreg_run (vd lhs rhs : VReg)
    (js : SailJoltState) :
    (execInstr (.SLTU (.vreg vd) (.vreg lhs) (.vreg rhs))).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then jolt_sltu_value (js.vregs lhs) (js.vregs rhs) else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

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
