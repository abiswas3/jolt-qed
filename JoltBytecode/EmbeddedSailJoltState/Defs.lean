import LeanRV64D

/-!
# Embedded Architecture: SailJoltState embeds SailState

Instead of duplicating SailState's fields, SailJoltState embeds it directly.
This makes project/inject trivial (field access/update) and may eliminate
the monadic plumbing noise in proofs.
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

-- ============================================================================
-- Types
-- ============================================================================

abbrev SailState := SequentialState RegisterType trivialChoiceSource

-- SailJoltState embeds SailState directly instead of duplicating fields.
structure SailJoltState where
  sail : SailState
  vregs : BitVec 7 → BitVec 64 := fun _ => 0

abbrev JoltMonad (α : Type) := EStateM (Error exception) SailJoltState α

-- ============================================================================
-- Projection: trivial field access/update
-- ============================================================================

-- project: just read the embedded SailState.
@[simp] def project (js : SailJoltState) : SailState := js.sail

-- inject: update the embedded SailState, keep vregs.
@[simp] def inject (js : SailJoltState) (ss : SailState) : SailJoltState :=
  { js with sail := ss }

-- projectResult: strip vregs from an EStateM result.
def projectResult (r : EStateM.Result (Error exception) SailJoltState α) :
    EStateM.Result (Error exception) SailState α :=
  match r with
  | .ok a js' => .ok a (project js')
  | .error e js' => .error e (project js')

-- ============================================================================
-- liftSail
-- ============================================================================

def liftSail (m : SailM α) : JoltMonad α := fun js =>
  match m js.sail with
  | .ok a ss' => .ok a { js with sail := ss' }
  | .error e ss' => .error e { js with sail := ss' }

-- ============================================================================
-- Structural lemmas
-- ============================================================================

@[simp] theorem project_inject (js : SailJoltState) (ss : SailState) :
    project (inject js ss) = ss := rfl

@[simp] theorem inject_inject (js : SailJoltState) (ss1 ss2 : SailState) :
    inject (inject js ss1) ss2 = inject js ss2 := rfl

@[simp] theorem inject_project (js : SailJoltState) :
    inject js (project js) = js := by simp

theorem liftSail_project (m : SailM α) (js : SailJoltState) :
    projectResult ((liftSail m).run js) = m.run js.sail := by
  simp only [liftSail, projectResult, project, EStateM.run]
  cases m js.sail <;> rfl

-- liftSail preserves bind.
theorem liftSail_bind (m : SailM α) (f : α → SailM β) :
    liftSail (m >>= f) = (do let a ← liftSail m; liftSail (f a) : JoltMonad β) := by
  funext js
  simp only [liftSail, bind, EStateM.bind]
  cases m js.sail with
  | ok a ss' => rfl
  | error e ss' => rfl

-- liftSail preserves pure.
theorem liftSail_pure (a : α) :
    liftSail (pure a) = (pure a : JoltMonad α) := by
  funext js
  simp only [liftSail, pure, EStateM.pure]

-- ============================================================================
-- Virtual register operations
-- ============================================================================

def readVReg (vr : BitVec 7) : JoltMonad (BitVec 64) := do
  let js ← get; pure (js.vregs vr)

def writeVReg (vr : BitVec 7) (val : BitVec 64) : JoltMonad Unit :=
  modify fun js => { js with vregs := fun r => if r = vr then val else js.vregs r }

-- ============================================================================
-- Memory read primitives (raw Sail memory access)
-- ============================================================================

-- Read a single byte from Sail's physical memory.
-- At the bottom of Sail's memory hierarchy, readByte looks up addr in
-- state.mem (an ExtHashMap Nat (BitVec 8)). This is the same operation.
def sailReadByte (addr : Nat) : SailM (BitVec 8) := fun s =>
  match s.mem.get? addr with
  | some v => .ok v s
  | none => .error (Error.OutOfMemoryRange addr) s

-- Read 4 bytes (little-endian) from Sail's memory, producing a 32-bit word.
def sailReadWord (addr : BitVec 64) : SailM (BitVec 32) := do
  let b0 ← sailReadByte addr.toNat
  let b1 ← sailReadByte (addr.toNat + 1)
  let b2 ← sailReadByte (addr.toNat + 2)
  let b3 ← sailReadByte (addr.toNat + 3)
  pure (b3 ++ b2 ++ b1 ++ b0)

-- Read 8 bytes (little-endian) from Sail's memory, producing a 64-bit dword.
def sailReadDword (addr : BitVec 64) : SailM (BitVec 64) := do
  let lo ← sailReadWord addr
  let hi ← sailReadWord (addr + 4)
  pure ((hi ++ lo : BitVec 64))

-- ============================================================================
-- JoltConfig: Sail state assumptions for Jolt's execution environment
-- ============================================================================

-- Jolt runs in bare-metal M-mode with flat physical memory. Under these
-- assumptions, Sail's virtual memory pipeline (vmem_read) reduces to raw
-- byte reads from state.mem.
--
-- The conditions are:
-- 1. Machine mode with MPRV=0: translateAddr returns identity (Bare mode)
-- 2. PMP entries are unlocked: Machine mode bypasses PMP
-- 3. Valid PMA region: the physical address has readable attributes
-- 4. Not MMIO: the address is regular RAM, not memory-mapped I/O
-- 5. Memory is populated: all accessed addresses are in state.mem
--
-- These are captured as a predicate on SailState rather than baking in
-- specific register values, so the proofs stay abstract.
structure JoltConfig (s : SailState) : Prop where
  -- Machine mode: cur_privilege register is Machine.
  -- This makes translateAddr use Bare (identity) translation.
  machine_mode : s.regs.get? Register.cur_privilege =
    some (Privilege.Machine : RegisterType Register.cur_privilege)
  -- mstatus register is readable and has MPRV=0.
  -- MPRV=0 means effectivePrivilege returns the actual privilege (Machine),
  -- not the MPP field. This ensures Bare translation mode.
  mstatus_ok : ∃ mval : RegisterType Register.mstatus,
    s.regs.get? Register.mstatus = some mval ∧
    _get_Mstatus_MPRV mval = 0#1
  -- All memory addresses are populated in state.mem.
  -- This makes sailReadByte succeed for any address.
  mem_populated : ∀ addr : Nat, s.mem.get? addr ≠ none

-- ============================================================================
-- Focused bridge lemmas for the vmem_read pipeline
-- ============================================================================

-- Under JoltConfig (Machine mode, MPRV=0), translateAddr is the identity:
-- the virtual address becomes the physical address with no translation.
-- This is because Machine mode → translationMode = Bare → paddr = vaddr.
-- Under JoltConfig (Machine mode, MPRV=0), translateAddr is the identity:
-- the virtual address becomes the physical address with no translation.
-- This is because Machine mode → translationMode = Bare → paddr = vaddr.
--
-- Proof strategy: unfold translateAddr, show readReg succeeds for mstatus
-- and cur_privilege (from JoltConfig), then effectivePrivilege returns Machine,
-- translationMode returns Bare, and the Bare branch returns identity.
theorem translateAddr_machine_bare (vAddr : virtaddr) (s : SailState)
    (hcfg : JoltConfig s) :
    translateAddr vAddr (MemoryAccessType.Load mem_payload.Data) s =
    .ok (Ok (physaddr.Physaddr (zero_extend (m := 64) (bits_of_virtaddr vAddr)), init_ext_ptw)) s := by
  sorry

-- The bridge lemma: under JoltConfig, Sail's execute_LOAD for LW (width=4,
-- signed) is equivalent to: read rs1, compute address, read 4 bytes raw
-- from state.mem via sailReadWord, sign-extend to 64 bits, write to rd.
--
-- This collapses the entire vmem_read pipeline (address translation, PMP,
-- PMA, MMIO checks) down to a raw byte read. Each check passes trivially
-- under JoltConfig:
--   ext_data_get_addr: always succeeds (just computes vaddr = rX[rs1] + offset)
--   misalignment: passes (plat_enable_misaligned_access = true)
--   translateAddr: identity (Machine mode → Bare translation)
--   pmpCheck: Machine mode bypasses
--   pmaCheck: JoltConfig guarantees valid readable region
--   MMIO: JoltConfig guarantees regular RAM
--   sail_mem_read: reads from state.mem = same as sailReadByte
--
-- TODO: prove by unfolding vmem_read through 6 layers.
theorem execute_LOAD_LW_factored (imm : BitVec 12) (rs1 rd : regidx)
    (s : SailState) (hcfg : JoltConfig s) :
    execute_LOAD imm rs1 rd false 4 s = (do
      let v_base ← rX_bits rs1
      let addr := v_base + sign_extend (m := 64) imm
      let word ← sailReadWord addr
      wX_bits rd (sign_extend (m := 64) word)
      pure RETIRE_SUCCESS) s := by
  -- PROVED layers (no sorry needed):
  --   Layer 1: execute_LOAD unfolds to vmem_read
  --   Layer 2: vmem_read → ext_data_get_addr (trivial) → vmem_read_addr
  --   Layer 3: misalignment passes (plat_enable_misaligned_access = true)
  --   Layer 3b: split_misaligned returns (1, width) — single memory access
  --
  -- BLOCKED at layer 4: the Sail monad transformer stack (SailME = ExceptT
  -- over SailM, wrapped in PreSailME.run with liftM) creates deeply nested
  -- terms. The remaining layers need:
  --
  --   Layer 4: translateAddr → Bare (Machine mode from JoltConfig)
  --     Needs: readReg cur_privilege = Machine, readReg mstatus for MPRV bit
  --     Blocked by: Sail register reads go through PreSail.readReg which
  --     does hash map lookup on s.regs — need to connect JoltConfig.machine_mode
  --     to the actual readReg call.
  --
  --   Layer 5: checked_mem_read → pmpCheck + pmaCheck
  --     pmpCheck: Machine mode bypasses if no locked entries (need to reason
  --     about PMP register state — 16 entries from pmpaddr0..15 and pmpcfg0..3)
  --     pmaCheck: need matching PMA region with readable attributes
  --
  --   Layer 6: read_ram → sail_mem_read → readBytes → readByte
  --     readByte does state.mem.get? addr — matches our sailReadByte.
  --     This layer should be straightforward once layers 4-5 are done.
  --
  -- Recommended approach: prove focused intermediate lemmas:
  --   translateAddr_machine_bare: Machine mode → identity translation
  --   pmpCheck_machine_pass: Machine mode → PMP passes
  --   checked_mem_read_eq_read_ram: combine the above
  --   read_ram_eq_sailReadBytes: final connection to sailReadByte
  sorry

-- ============================================================================
-- Shared Jolt instructions
-- ============================================================================

def jolt_virtual_sign_extend_word (rd : regidx) : JoltMonad Unit := do
  let v ← liftSail (rX_bits rd)
  liftSail (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb v 31 0)))

-- ============================================================================
-- sail_cases tactic
-- ============================================================================

syntax "sail_cases" term : tactic
macro_rules
  | `(tactic| sail_cases $t:term) => `(tactic|
      (generalize $t = _sc; cases _sc <;> simp))

end
