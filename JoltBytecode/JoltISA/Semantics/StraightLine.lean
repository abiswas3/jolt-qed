import JoltBytecode.JoltISA.Semantics.Lemmas
import JoltBytecode.JoltISA.Semantics.Instructions.ADDI
import JoltBytecode.JoltISA.Semantics.Instructions.ANDI
import JoltBytecode.JoltISA.Semantics.Instructions.Add
import JoltBytecode.JoltISA.Semantics.Instructions.Mul
import JoltBytecode.JoltISA.Semantics.Instructions.ORI
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

/-- Successful `LD`: if Sail's dword read pipeline returns `value`, then the
Jolt-ISA `LD` writes that dword to the destination virtual register and
continues with `RETIRE_SUCCESS`. -/
theorem ld_run_vreg_vreg_from_memory_read (vd base : VReg) (imm : BitVec 12)
    (js : SailJoltState) (value : BitVec 64)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h :
      vmem_read_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 0 8
        (Load Data) false false false js.sail =
        .ok (Ok value) js.sail) :
    (execInstr (.LD (.vreg vd) (.vreg base) imm)).run js =
      .ok RETIRE_SUCCESS
        { sail := js.sail
          vregs := fun r => if r = vd then value else js.vregs r } := by
  unfold execInstr readSrc writeDst readVReg liftSail writeVReg
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  have h' :
      vmem_read_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm))
        (0#64) 8 (Load Data) false false false js.sail =
        .ok (Ok value) js.sail := by
    simpa using h
  simp [EStateM.bind, h', modify, modifyGet, MonadStateOf.modifyGet]
  rfl

/-- Successful `SD`: if Sail's dword write pipeline returns success, then the
Jolt-ISA `SD` retires with the produced Sail state and preserves virtual
registers. -/
theorem execInstr_sd_vreg_run_of_write (base value : VReg) (imm : BitVec 12)
    (js : SailJoltState) (s' : SailState)
    (h_align :
      (js.vregs base + sign_extend (m := 64) imm) &&& (7 : BitVec 64) = 0)
    (h :
      vmem_write_addr (Virtaddr (js.vregs base + sign_extend (m := 64) imm)) 8
        (js.vregs value) (Store Data) false false false js.sail =
        .ok (Ok true) s') :
    (execInstr (.SD (.vreg base) (.vreg value) imm)).run js =
      .ok RETIRE_SUCCESS { sail := s', vregs := js.vregs } := by
  unfold execInstr readSrc readVReg liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get]
  rw [if_pos h_align]
  simp [EStateM.bind, h]
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
