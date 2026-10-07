/-
Facts about Jolt RAM in an honest trace: execution never removes a byte from memory,
the starting memory holds every byte of Rust's RAM, and so the 64 bits an SD
overwrites are present when it runs.
-/
import JoltConstraints.trace_interface

set_option autoImplicit false

open Sail PreSail LeanRV64D.Functions

namespace MemoryKept

-- A Jolt step that, when it succeeds, removes no byte from memory.
def Preserves {Value : Type} (step : JoltMonad Value) : Prop :=
  ∀ (state after : SailJoltState) (value : Value),
    step state = .ok value after → ∀ address ∈ state.sail.mem, address ∈ after.sail.mem

-- A step that leaves memory exactly as it was removes nothing from it.
theorem mem_unchanged_rule {Value : Type} {step : JoltMonad Value}
    (unchanged : ∀ (state after : SailJoltState) (value : Value),
      step state = .ok value after → after.sail.mem = state.sail.mem) :
    Preserves step := by
  intro state after value runs address present
  rw [unchanged state after value runs]
  exact present

theorem pure_rule {Value : Type} (value : Value) : Preserves (pure value) :=
  mem_unchanged_rule (fun state after result runs => by cases runs; rfl)

theorem bind_rule {Value Next : Type} {first : JoltMonad Value} {next : Value → JoltMonad Next}
    (keepsFirst : Preserves first) (keepsNext : ∀ value, Preserves (next value)) :
    Preserves (first >>= next) := by
  intro state after result runs address present
  cases firstRun : first state with
  | error failure middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    cases runs
  | ok value middle =>
    simp only [bind, EStateM.bind, firstRun] at runs
    exact keepsNext value middle after result runs address
      (keepsFirst state middle value firstRun address present)

theorem get_rule : Preserves (get : JoltMonad SailJoltState) :=
  mem_unchanged_rule (fun state after value runs => by cases runs; rfl)

theorem throw_rule {Value : Type} (failure : Error exception) :
    Preserves (throw failure : JoltMonad Value) := by
  intro state after value runs
  cases runs

-- A lifted Sail step that leaves memory as it was.
theorem lift_rule {Value : Type} {step : SailM Value}
    (unchanged : ∀ (sail after : SailState) (value : Value),
      step sail = .ok value after → after.mem = sail.mem) :
    Preserves (liftSail step) := by
  apply mem_unchanged_rule
  intro state after value runs
  unfold liftSail at runs
  cases stepRun : step state.sail with
  | error failure sail =>
    rw [stepRun] at runs
    cases runs
  | ok result sail =>
    rw [stepRun] at runs
    cases runs
    exact unchanged _ _ _ stepRun

theorem readReg_rule (register : Register) : Preserves (liftSail (Sail.readReg register)) :=
  lift_rule (fun sail after value runs => by rw [readReg_pure register sail value after runs])

theorem writeReg_rule (register : Register) (value : RegisterType register) :
    Preserves (liftSail (Sail.writeReg register value)) :=
  lift_rule (fun sail after result runs => by cases runs; rfl)

theorem arch_pc_rule : Preserves (liftSail (get_arch_pc ())) :=
  lift_rule (fun sail after value runs => by
    unfold get_arch_pc at runs
    rw [readReg_pure Register.PC sail value after runs])

theorem jump_rule (target : BitVec 64) : Preserves (liftSail (jump_to target)) :=
  lift_rule (fun sail after result runs => by
    rcases jump_to_shape target sail after result runs with same | written
    · rw [same]
    · rw [written])

theorem read_rule (source : JoltISA.Src) : Preserves (JoltISA.readSrc source) := by
  cases source with
  | vreg register =>
    exact mem_unchanged_rule (fun state after value runs => by
      simp only [JoltISA.readSrc_vreg, readVReg_run] at runs
      cases runs
      rfl)
  | xreg register =>
    exact lift_rule (fun sail after value runs => by
      rw [rX_bits_pure register sail value after runs])

theorem write_rule (destination : JoltISA.Dst) (value : BitVec 64) :
    Preserves (JoltISA.writeDst destination value) := by
  cases destination with
  | vreg register =>
    exact mem_unchanged_rule (fun state after result runs => by
      simp only [JoltISA.writeDst, writeVReg] at runs
      split at runs
      · cases runs
      · cases runs
        rfl)
  | xreg register =>
    exact lift_rule (fun sail after result runs => by
      rw [wX_bits_eq_stateAfterWrite register value sail after runs]
      rfl)

theorem load_doubleword_rule (address : BitVec 64) :
    Preserves (JoltISA.Mmu.load_doubleword address) :=
  mem_unchanged_rule (fun state after value runs => by
    rw [JoltISA.Mmu.load_doubleword_state runs])

-- Writing 64 bits into RAM only adds bytes.
theorem write_ram_doubleword_keeps (mem : Std.ExtHashMap Nat (BitVec 8)) (ea : Nat)
    (value : BitVec 64) (address : Nat) (present : address ∈ mem) :
    address ∈ JoltISA.Mmu.write_ram_doubleword mem ea value := by
  unfold JoltISA.Mmu.write_ram_doubleword
  suffices kept : ∀ (offsets : List Nat) (current : Std.ExtHashMap Nat (BitVec 8)),
      address ∈ current → address ∈ offsets.foldl
        (fun mem k => mem.insert (ea + k) (value.extractLsb' (8 * k) 8)) current from
    kept _ _ present
  intro offsets
  induction offsets with
  | nil => intro current inCurrent; exact inCurrent
  | cons k rest ih =>
    intro current inCurrent
    exact ih _ (Std.ExtHashMap.mem_insert.mpr (Or.inr inCurrent))

-- Storing one byte only adds it to memory, or changes the device.
theorem store_raw_keeps {state after : SailJoltState} {ea : Nat} {value : BitVec 8}
    (stored : JoltISA.Mmu.store_raw? state ea value = some after)
    (address : Nat) (present : address ∈ state.sail.mem) : address ∈ after.sail.mem := by
  simp only [JoltISA.Mmu.store_raw?] at stored
  repeat' split at stored
  all_goals first
    | (cases stored; exact Std.ExtHashMap.mem_insert.mpr (Or.inr present))
    | (cases stored; exact present)
    | cases stored
    | (cases deviceStore : state.jolt_device.store? ea value <;>
        simp [deviceStore] at stored
       cases stored
       exact present)

-- Storing bytes one at a time only adds bytes to memory.
theorem store_bytes_keeps (ea : Nat) (value : BitVec 64) (address : Nat) :
    ∀ (offsets : List Nat) (start : Option SailJoltState) (after : SailJoltState),
      (∀ state, start = some state → address ∈ state.sail.mem) →
      offsets.foldl (fun current k => current.bind fun state =>
        JoltISA.Mmu.store_raw? state (ea + k) (value.extractLsb' (8 * k) 8)) start = some after →
      address ∈ after.sail.mem := by
  intro offsets
  induction offsets with
  | nil => intro start after present stored; exact present after stored
  | cons k rest ih =>
    intro start after present stored
    simp only [List.foldl] at stored
    apply ih _ after _ stored
    intro state stepped
    cases start with
    | none => simp at stepped
    | some before =>
      simp only [Option.bind] at stepped
      exact store_raw_keeps stepped address (present before rfl)

theorem store_doubleword_rule (address value : BitVec 64) :
    Preserves (JoltISA.Mmu.store_doubleword address value) := by
  intro state after result runs kept present
  simp only [JoltISA.Mmu.store_doubleword] at runs
  repeat' split at runs
  all_goals first
    | (cases runs; exact present)
    | (cases runs; exact write_ram_doubleword_keeps _ _ _ _ present)
    | (rename_i stored
       cases runs
       exact store_bytes_keeps _ value kept _ (some state) _
         (fun before same => by cases same; exact present) stored)
    | cases runs

theorem execHostIO_rule : Preserves JoltISA.execHostIO :=
  mem_unchanged_rule (fun state after result runs => by
    rw [execHostIO_keeps_sail state after result runs])

end MemoryKept

macro "memory_kept_auto" : tactic => `(tactic|
  repeat' first
  | with_reducible exact MemoryKept.read_rule _
  | with_reducible exact MemoryKept.write_rule _ _
  | with_reducible exact MemoryKept.pure_rule _
  | with_reducible exact MemoryKept.throw_rule _
  | with_reducible exact MemoryKept.get_rule
  | with_reducible exact MemoryKept.readReg_rule _
  | with_reducible exact MemoryKept.writeReg_rule _ _
  | with_reducible exact MemoryKept.arch_pc_rule
  | with_reducible exact MemoryKept.jump_rule _
  | with_reducible exact MemoryKept.load_doubleword_rule _
  | with_reducible exact MemoryKept.store_doubleword_rule _ _
  | with_reducible exact MemoryKept.execHostIO_rule
  | split
  | refine MemoryKept.bind_rule ?_ (fun _ => ?_))

-- Executing an instruction never removes a byte from memory.
theorem execInstr_keeps_memory (instruction : JoltISA.Instr) (state after : SailJoltState)
    (result : ExecutionResult) (runs : JoltISA.execInstr instruction state = .ok result after)
    (address : Nat) (present : address ∈ state.sail.mem) : address ∈ after.sail.mem := by
  have keeps : MemoryKept.Preserves (JoltISA.execInstr instruction) := by
    cases instruction
    case VirtualAdviceLoad destination byteCount =>
      -- reading the advice tape changes only the tape, then the value is written
      intro before afterLoad value loadRuns
      simp only [JoltISA.execInstr] at loadRuns
      cases tapeRead : JoltISA.readAdviceTape before.adviceTape byteCount with
      | none =>
        simp only [tapeRead] at loadRuns
        cases loadRuns
      | some pair =>
        obtain ⟨adviceValue, tape⟩ := pair
        simp only [tapeRead] at loadRuns
        exact MemoryKept.bind_rule (MemoryKept.write_rule destination adviceValue)
          (fun _ => MemoryKept.pure_rule _)
          { before with adviceTape := tape } afterLoad value loadRuns
    all_goals simp only [JoltISA.execInstr]
    all_goals memory_kept_auto
  exact keeps state after result runs address present

-- Inserting bytes at RAM_START plus their positions keeps what memory had and adds
-- every position.
theorem fold_insert_mem
    (insertByte : Std.ExtHashMap Nat (BitVec 8) → BitVec 8 × Nat → Std.ExtHashMap Nat (BitVec 8))
    (inserts : ∀ mem byte offset,
      insertByte mem (byte, offset) = mem.insert (JoltISA.RAM_START_ADDRESS + offset) byte) :
    ∀ (bytes : List (BitVec 8)) (start : Nat) (mem : Std.ExtHashMap Nat (BitVec 8)),
      (∀ address ∈ mem, address ∈ (bytes.zipIdx start).foldl insertByte mem) ∧
      (∀ offset, start ≤ offset → offset < start + bytes.length →
        JoltISA.RAM_START_ADDRESS + offset ∈ (bytes.zipIdx start).foldl insertByte mem) := by
  intro bytes
  induction bytes with
  | nil =>
    intro start mem
    refine ⟨fun address present => present, fun offset low high => ?_⟩
    simp only [List.length_nil, Nat.add_zero] at high
    omega
  | cons byte rest ih =>
    intro start mem
    obtain ⟨keeps, adds⟩ := ih (start + 1) (insertByte mem (byte, start))
    simp only [List.zipIdx_cons, List.foldl_cons]
    refine ⟨fun address present => keeps address ?_, fun offset low high => ?_⟩
    · rw [inserts]
      exact Std.ExtHashMap.mem_insert.mpr (Or.inr present)
    · by_cases first : offset = start
      · subst first
        apply keeps
        rw [inserts]
        exact Std.ExtHashMap.mem_insert.mpr (Or.inl (by simp))
      · simp only [List.length_cons] at high
        exact adds offset (by omega) (by omega)

-- Writing the ELF bytes into the zeroed RAM keeps its size: every write is in bounds or
-- skipped.
theorem initialRam_size (layout : MemoryLayout) (memory_init : List (BitVec 64 × BitVec 8)) :
    (initialRam layout memory_init).size =
      8 * ((layout.get_total_memory_size.toNat + 7) / 8) := by
  unfold initialRam
  dsimp only
  suffices sameSize : ∀ (entries : List (BitVec 64 × BitVec 8)) (ram : Array (BitVec 8)),
      (entries.foldl (fun ram (address, byte) =>
        if JoltISA.RAM_START_ADDRESS ≤ address.toNat then
          ram.setIfInBounds (address.toNat - JoltISA.RAM_START_ADDRESS) byte
        else ram) ram).size = ram.size by
    rw [sameSize, Array.size_replicate]
  intro entries
  induction entries with
  | nil => intro ram; rfl
  | cons entry rest ih =>
    intro ram
    rw [List.foldl_cons, ih]
    obtain ⟨address, byte⟩ := entry
    dsimp only
    split
    · exact Array.size_setIfInBounds
    · rfl

-- The starting memory holds every byte of Rust's RAM: from RAM_START up to heap_end,
-- rounded up to whole 64-bit units.
-- See : jolt/tracer/src/emulator/mod.rs:242-248 (init_memory)
theorem initial_state_memory {Source : Type} (joltInstance : JoltInstance Source)
    (privateInputs : JoltPrivateInputs) (initialState : SailJoltState)
    (built : joltInstance.initial_state privateInputs = some initialState) (offset : Nat)
    (inRam : offset <
      8 * ((initialState.jolt_device.memory_layout.get_total_memory_size.toNat + 7) / 8)) :
    JoltISA.RAM_START_ADDRESS + offset ∈ initialState.sail.mem := by
  unfold JoltInstance.initial_state at built
  rw [bind_some_iff] at built
  obtain ⟨layout, _, built⟩ := built
  dsimp only at built
  -- create_emulator's three size checks: trusted advice, untrusted advice, inputs
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  split at built
  · cases built
  rw [bind_some_iff] at built
  obtain ⟨_, _, built⟩ := built
  -- the memory holds every byte of the zeroed RAM
  cases built
  rw [init_state_jolt_device] at inRam
  unfold init_state
  dsimp only
  apply (fold_insert_mem _ (fun _ _ _ => rfl) _ 0 {}).2 offset (by omega)
  rw [Array.length_toList, initialRam_size]
  simpa using inRam

namespace JoltConstraints

open JoltIOSetupFrame

/-- Every recorded pre-state has the program's initial device setup. -/
theorem trace_preState_ioSame {joltInstance : JoltInstance SourceInstruction} {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (hi : i < trace.rows.size) :
    Same trace.initialState.jolt_device (getElem trace.rows i hi).preState.jolt_device := by
  induction i with
  | zero =>
    rw [trace.startsAtInitial (by omega)]
    exact Same.refl _
  | succ i ih =>
    have hprev := ih (by omega)
    have hexec := execInstr_rule _ _ _ _ (getElem trace.rows i (by omega)).executes
    have hlink := trace.linkedState i (by omega) hi
    rw [hlink]
    split
    · exact hprev.trans hexec
    · exact hprev.trans hexec

end JoltConstraints

-- Every row starts with all of Rust's RAM in memory: execution only adds bytes, and
-- moving to the next instruction changes only the PC registers.
theorem HonestTrace.preState_memory {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (offset : Nat)
    (inRam : offset <
      8 * ((trace.initialState.jolt_device.memory_layout.get_total_memory_size.toNat + 7) / 8)) :
    JoltISA.RAM_START_ADDRESS + offset ∈ (getElem trace.rows i inTrace).preState.sail.mem := by
  induction i with
  | zero =>
    rw [trace.startsAtInitial (by omega)]
    exact initial_state_memory joltInstance privateInputs trace.initialState trace.initialized
      offset inRam
  | succ i ih =>
    have before := ih (by omega)
    have kept := execInstr_keeps_memory _ _ _ _ (getElem trace.rows i (by omega)).executes _ before
    rw [trace.linkedState i (by omega) inTrace]
    split
    · exact kept
    · exact kept

-- An SD that retires ran its 64-bit store at the address it computed.
theorem execInstr_store_runs (base value : JoltISA.Src) (imm : BitVec 64)
    (state after : SailJoltState)
    (runs : JoltISA.execInstr (.SD base value imm) state = .ok (.Retire_Success ()) after) :
    ∃ stored result final, JoltISA.Mmu.store_doubleword
      (JoltISA.sourceValue base state + imm) stored state = .ok result final := by
  simp only [JoltISA.execInstr] at runs
  cases baseRead : JoltISA.readSrc base state with
  | error failure middle =>
    simp only [bind, EStateM.bind, baseRead] at runs
    cases runs
  | ok baseValue middle =>
    obtain ⟨middleSame, baseIs⟩ := readSrc_value base state middle baseValue baseRead
    simp only [bind, EStateM.bind, baseRead] at runs
    rw [middleSame] at runs
    cases valueRead : JoltISA.readSrc value state with
    | error failure middle =>
      rw [valueRead] at runs
      cases runs
    | ok storedValue middle =>
      obtain ⟨storedSame, _⟩ := readSrc_value value state middle storedValue valueRead
      rw [valueRead] at runs
      dsimp only at runs
      rw [storedSame, baseIs] at runs
      split at runs
      · -- the address is aligned, and the store ran
        rw [EStateM.bind] at runs
        cases stores : JoltISA.Mmu.store_doubleword (JoltISA.sourceValue base state + imm)
            storedValue state with
        | error failure final =>
          rw [stores] at runs
          cases runs
        | ok result final => exact ⟨_, _, _, stores⟩
      · cases runs

-- 64 bits read one byte at a time are there when each of the 8 bytes is.
theorem read_doubleword_isSome (byte : Nat → Option (BitVec 8)) (address : Nat)
    (present : ∀ offset < 8, (byte (address + offset)).isSome) :
    (JoltISA.read_doubleword? byte address).isSome := by
  obtain ⟨byte0, is0⟩ := Option.isSome_iff_exists.mp (present 0 (by decide))
  obtain ⟨byte1, is1⟩ := Option.isSome_iff_exists.mp (present 1 (by decide))
  obtain ⟨byte2, is2⟩ := Option.isSome_iff_exists.mp (present 2 (by decide))
  obtain ⟨byte3, is3⟩ := Option.isSome_iff_exists.mp (present 3 (by decide))
  obtain ⟨byte4, is4⟩ := Option.isSome_iff_exists.mp (present 4 (by decide))
  obtain ⟨byte5, is5⟩ := Option.isSome_iff_exists.mp (present 5 (by decide))
  obtain ⟨byte6, is6⟩ := Option.isSome_iff_exists.mp (present 6 (by decide))
  obtain ⟨byte7, is7⟩ := Option.isSome_iff_exists.mp (present 7 (by decide))
  rw [Nat.add_zero] at is0
  unfold JoltISA.read_doubleword?
  rw [is0, is1, is2, is3, is4, is5, is6, is7]
  rfl

-- A byte below RAM that a store can write is one the device can read: an output, panic
-- or termination byte. Both checks look only at the layout.
-- See : jolt/tracer/src/emulator/mmu.rs:644-667 (store_raw), 120-184 (assert_effective_address)
--       jolt/common/src/jolt_device.rs:121-148 (JoltDevice::load)
theorem store_raw_device_readable {state after : SailJoltState} {address : Nat}
    {value : BitVec 8} (belowRam : address < JoltISA.RAM_START_ADDRESS)
    (stored : JoltISA.Mmu.store_raw? state address value = some after)
    (device : JoltDevice) (sameLayout : device.memory_layout = state.jolt_device.memory_layout) :
    (device.load? address).isSome := by
  unfold JoltISA.Mmu.store_raw? at stored
  rw [if_neg (by omega)] at stored
  split at stored
  · cases stored
  split at stored
  · cases stored
  rename_i writable
  have writableTrue : JoltISA.Mmu.effective_address_ok state.jolt_device address true = true := by
    cases checked : JoltISA.Mmu.effective_address_ok state.jolt_device address true
    · rw [checked] at writable
      exact absurd rfl writable
    · rfl
  unfold JoltISA.Mmu.effective_address_ok at writableTrue
  rw [if_pos belowRam, if_pos rfl] at writableTrue
  simp only [Bool.and_eq_true] at writableTrue
  have regions := writableTrue.2
  unfold JoltDevice.is_output JoltDevice.is_panic JoltDevice.is_termination at regions
  rw [← sameLayout] at regions
  unfold JoltDevice.load?
  simp only [JoltDevice.is_output, JoltDevice.is_panic, JoltDevice.is_termination] at *
  split_ifs <;> simp_all <;> omega

-- Once a byte store fails, the rest of a 64-bit store fails too.
theorem store_bytes_from_none (ea : Nat) (value : BitVec 64) :
    ∀ (offsets : List Nat), offsets.foldl (fun current k => current.bind fun state =>
      JoltISA.Mmu.store_raw? state (ea + k) (value.extractLsb' (8 * k) 8)) none = none := by
  intro offsets
  induction offsets with
  | nil => rfl
  | cons k rest ih => exact ih

-- A device store that succeeds wrote each of its bytes to a byte the device can read.
theorem store_bytes_device_readable (ea : Nat) (value : BitVec 64) (device : JoltDevice)
    (belowRam : ea + 7 < JoltISA.RAM_START_ADDRESS) :
    ∀ (offsets : List Nat) (start : Option SailJoltState) (after : SailJoltState),
      (∀ state, start = some state → device.memory_layout = state.jolt_device.memory_layout) →
      (∀ k ∈ offsets, k < 8) →
      offsets.foldl (fun current k => current.bind fun state =>
        JoltISA.Mmu.store_raw? state (ea + k) (value.extractLsb' (8 * k) 8)) start = some after →
      ∀ k ∈ offsets, (device.load? (ea + k)).isSome := by
  intro offsets
  induction offsets with
  | nil =>
    intro _ _ _ _ _ k member
    cases member
  | cons k rest ih =>
    intro start after sameLayout small stored
    rw [List.foldl_cons] at stored
    cases start with
    | none =>
      rw [Option.bind_none, store_bytes_from_none] at stored
      cases stored
    | some before =>
      rw [Option.bind_some] at stored
      cases stepped : JoltISA.Mmu.store_raw? before (ea + k) (value.extractLsb' (8 * k) 8) with
      | none =>
        rw [stepped, store_bytes_from_none] at stored
        cases stored
      | some middle =>
        rw [stepped] at stored
        have kSmall := small k List.mem_cons_self
        have readable := store_raw_device_readable (by omega) stepped device (sameLayout before rfl)
        intro j member
        rcases List.mem_cons.mp member with isK | inRest
        · subst isK
          exact readable
        · -- the byte store keeps the layout
          refine ih (some middle) after (fun state same => ?_)
            (fun j inRest => small j (List.mem_cons_of_mem _ inRest)) stored j inRest
          cases same
          exact (sameLayout before rfl).trans
            (JoltIOSetupFrame.store_raw_same _ _ _ _ stepped).1.symm

-- When an SD row runs, the 64 bits it overwrites are present, so the witness can record
-- the old value as Rust's tracer does. In RAM, every byte below heap_end is in memory;
-- below RAM, the store succeeds only on output, panic and termination bytes, which the
-- device always reads.
-- See : jolt/tracer/src/emulator/mmu.rs:556 (trace_store reads the old word)
theorem HonestTrace.store_word_present {joltInstance : JoltInstance SourceInstruction}
    {privateInputs : JoltPrivateInputs} (trace : HonestTrace joltInstance privateInputs)
    (i : Nat) (inTrace : i < trace.rows.size) (base value : JoltISA.Src) (imm : BitVec 64)
    (isStore : trace.bytecode[(getElem trace.rows i inTrace).rowIndex].instruction =
      .SD base value imm) :
    (JoltISA.trace_doubleword? (getElem trace.rows i inTrace).preState
      (JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm)).isSome = true := by
  have runs := (getElem trace.rows i inTrace).executes
  rw [withRuntimeAdvice_store _ base value imm isStore] at runs
  have aligned := execInstr_store_aligned base value imm _ _ runs
  obtain ⟨stored, result, final, stores⟩ := execInstr_store_runs base value imm _ _ runs
  have sameLayout := (JoltConstraints.trace_preState_ioSame trace i inTrace).1
  have ramStart : JoltISA.RAM_START_ADDRESS = 2147483648 := rfl
  unfold JoltISA.trace_doubleword?
  unfold JoltISA.Mmu.store_doubleword at stores
  rw [if_neg (by omega)] at stores
  split
  · -- below RAM: every byte is one the device reads
    rename_i belowRam
    rw [if_neg (by omega)] at stores
    dsimp only at stores
    split at stores
    · rename_i stateAfter folded
      apply read_doubleword_isSome
      intro offset small
      exact store_bytes_device_readable _ stored _ (by omega) (List.range 8) _ stateAfter
        (fun state same => by cases same; rfl) (fun k member => List.mem_range.mp member)
        folded offset (List.mem_range.mpr small)
    · cases stores
  · -- in RAM: the address is below heap_end, and every byte there is in memory
    rename_i notBelow
    rw [if_pos (by omega)] at stores
    split at stores
    · rename_i withinHeap
      unfold JoltISA.Mmu.effective_address_ok at withinHeap
      rw [if_neg (by omega), if_pos rfl] at withinHeap
      simp only [Bool.and_eq_true, decide_eq_true_eq] at withinHeap
      apply read_doubleword_isSome
      intro offset small
      -- the byte is inside Rust's RAM, which ends at heap_end rounded up to 64 bits
      have inRam : (JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm).toNat -
          JoltISA.RAM_START_ADDRESS + offset <
          8 * ((trace.initialState.jolt_device.memory_layout.get_total_memory_size.toNat + 7) / 8) := by
        rw [← sameLayout]
        unfold MemoryLayout.get_total_memory_size
        rw [BitVec.toNat_sub]
        have heapFits := (getElem trace.rows i inTrace).preState.jolt_device.memory_layout.heap_end.isLt
        have ramStartBits : (BitVec.ofNat 64 JoltISA.RAM_START_ADDRESS).toNat = 2147483648 := rfl
        have wordSize : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
        rw [ramStartBits]
        omega
      have present := trace.preState_memory i inTrace _ inRam
      rw [show JoltISA.RAM_START_ADDRESS +
          ((JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm).toNat -
            JoltISA.RAM_START_ADDRESS + offset) =
          (JoltISA.sourceValue base (getElem trace.rows i inTrace).preState + imm).toNat + offset by
        omega] at present
      rw [Std.ExtHashMap.get?_eq_getElem?]
      exact Std.ExtHashMap.mem_iff_isSome_getElem?.mp present
    · cases stores
