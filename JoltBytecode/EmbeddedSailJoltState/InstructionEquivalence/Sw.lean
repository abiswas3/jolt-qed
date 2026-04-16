import JoltBytecode.EmbeddedSailJoltState.Defs
import JoltBytecode.EmbeddedSailJoltState.MemoryUtils
import JoltBytecode.EmbeddedSailJoltState.MemoryWriteReasoning
import JoltBytecode.EmbeddedSailJoltState.VirtualInstructions
import JoltBytecode.EmbeddedSailJoltState.RtypeW

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

/-!
# SW: Jolt store-word decomposition
-- rs2 contains the actual value to be written 
From `tracer/src/instruction/sw.rs::inline_sequence_64`:
    VirtualAssertWordAlignment rs1, imm       -- check 4-byte alignment
    ADDI  v0, rs1, imm                        -- v0 = effective address
    ANDI  v1, v0, -8                          -- v1 = dword-aligned address
    LD    v2, v1, 0                           -- v2 = current dword at aligned addr
    SLLI  v0, v0, 3                           -- v0 = byte offset * 8 (bit offset)
    ORI   v3, x0, -1                          -- v3 = 0xFFFFFFFFFFFFFFFF
    SRLI  v3, v3, 32                          -- v3 = 0x00000000FFFFFFFF (32-bit mask)
    SLL   v3, v3, v0                          -- v3 = mask shifted to target position
    SLL   v0, rs2, v0                         -- v0 = store value shifted to position
    XOR   v0, v2, v0                          -- v0 = dword ^ shifted value
    AND   v0, v0, v3                          -- v0 = (dword ^ shifted value) & mask
    XOR   v2, v2, v0                          -- v2 = dword with word replaced
    SD    v1, v2, 0                           -- store modified dword back

The XOR-AND-XOR pattern: given dword `d`, new word `w` shifted to position,
and mask `m` covering the target 32 bits:
    d ^ ((d ^ w) & m) = (d & ~m) | (w & m)
This replaces exactly the 32 bits under the mask with the new word value.
-/


/-
TODO: (CLAUDE) : Don't write code but we will start discussion on chat
THE HIGH LEVEL IDEA
What is the crux of the this proof. 
Jolt can only read 64 bits from memory from double word aligned address, 
and write 64 bits to memory at a double word aligned address. 
So how does one implement storing of 32 bits then?
Lets make a toy example with addresses 
0, 1, 2, 3, 4, 5, 6, 7 are addresses -- each store 8 bits of data
0: is double word aligned
0 and 4 are word aligned. 
So we may either want to write 32 bits at eithe raddress 0 or 4 (These are only two legal operations, 
and we will get this from our assumptions). 

The trick is to load data at address0 into a virtual-reg as 64 bits.
and then over-write address 0-3 or 4-7 based on the address value.
And then store the 64 bit value back at address 0. 
The part we did not change - is just load and store. So it's as if we did not change. 
SO the first lemma to write down is to express this at the hashmap level. 
Right now we do not want to fight the monads. 
We want to get the logic down, we'll cut through the monads with assumptions and simp lemmas later.
We need to reason about this first. 
Note that in LW we invented load_word_at or something like that. 

-/ 

/-- Jolt's SW decomposition: 13-step read-modify-write via dword-aligned access. -/
def jolt_sw (imm : BitVec 12) (rs2 rs1 : regidx) : JoltMonad ExecutionResult := do
  let base ← liftSail (rX_bits rs1)
  let ea := base + sign_extend (m := 64) imm
  -- VirtualAssertWordAlignment
  if ea &&& 3 ≠ 0 then
    throw (Error.Assertion "SW: effective address not word-aligned")
  else do
    -- ADDI v0, rs1, imm
    writeVReg 0 ea
    -- ANDI v1, v0, -8
    let _ ← vreg_ANDI 1 0 (-8 : BitVec 12)
    -- LD v2, v1, 0
    match ← vreg_LD 2 1 0 with
    | .Retire_Success () =>
        -- SLLI v0, v0, 3
        let _ ← vreg_SLLI 0 0 3
        -- ORI v3, x0, -1  (x0 = 0, imm = -1 sign-extended = allOnes)
        writeVReg 3 0
        let _ ← vreg_ORI 3 3 (-1 : BitVec 12)
        -- SRLI v3, v3, 32
        let _ ← vreg_SRLI 3 3 32
        -- SLL v3, v3, v0
        let _ ← vreg_SLL 3 3 0
        -- SLL v0, rs2, v0  (rs2 is a real register)
        let rs2_val ← liftSail (rX_bits rs2)
        let v0_shift ← readVReg 0
        writeVReg 0 (shift_bits_left rs2_val (Sail.BitVec.extractLsb v0_shift 5 0))
        -- XOR v0, v2, v0
        let _ ← vreg_XOR 0 2 0
        -- AND v0, v0, v3
        let _ ← vreg_AND 0 0 3
        -- XOR v2, v2, v0
        let _ ← vreg_XOR 2 2 0
        -- SD v1, v2, 0
        let _ ← vreg_SD 1 2 0
        pure RETIRE_SUCCESS
    | other => pure other

-- ===========================================================================
-- Call chain: execute_STORE → ... → hashmap insert
-- ===========================================================================
--
-- 1. execute_STORE (imm, rs2, rs1, width=4)           [InstsEnd.lean:66988]
--    │ let offset := sign_extend imm
--    │ assert (width ≤ xlen_bytes)                     -- width check
--    │ let data := extractLsb (← rX_bits rs2) 31 0    -- read rs2, take low 32 bits
--    │
--    ▼
-- 2. vmem_write (rs1, offset, 4, data, Store Data, false, false, false)
--    │                                                  [VmemUtils.lean:386]
--    │ Wrapped in SailME.run (ExceptT over SailM)
--    │
--    ▼
-- 3. ext_data_get_addr (rs1, offset, _, _)             [AddrChecks.lean:212]
--    │ let addr := Virtaddr (rX_bits(rs1) + offset)
--    │ pure (Ext_DataAddr_OK addr)
--    │ -- Always succeeds, just computes vaddr = base + offset
--    │
--    ├── On Ext_DataAddr_Error → SailME.throw (Err ...)  [never happens]
--    ▼
-- 4. vmem_write_addr (vaddr, 4, data, Store Data, false, false, false)
--    │                                                  [VmemUtils.lean:313]
--    │
--    ├── access_causes_misaligned_exception(vaddr, 4, false)  [VmemUtils.lean:259]
--    │   = ¬(is_aligned_vaddr vaddr 4) ∧ (¬plat_enable_misaligned_access ∨ false)
--    │   Since plat_enable_misaligned_access = true → always false → OK
--    │   (If true → Err (Memory_Exception (vaddr, E_SAMO_Addr_Align)))
--    │
--    ├── split_misaligned (vaddr, 4)                    [VmemUtils.lean:237]
--    │   Since is_aligned or allowed_misaligned → pure (1, 4)
--    │   i.e. n=1, bytes=4 → single memory access
--    │
--    ├── misaligned_order (1)                           [VmemUtils.lean:253]
--    │   = (0, 0, 1)  i.e. first=0, last=0, step=1
--    │
--    │ -- Loop body runs once (offset=0):
--    ▼
-- 5. translateAddr (Virtaddr vaddr, Store Data)         [Vmem.lean:489]
--    │ let effPriv := effectivePrivilege(Store Data, mstatus, cur_privilege)
--    │   Under JoltConfig: cur_privilege = Machine, MPRV=0
--    │   → effectivePrivilege returns Machine
--    │ let mode := translationMode(Machine)
--    │   Machine mode → Bare
--    │ if is_shadow_stack_access → no (Store Data is not shadow stack)
--    │ if mode == Bare →
--    │   pure (Ok (Physaddr (zero_extend vaddr_bits), init_ext_ptw))
--    │ -- Identity translation: paddr = vaddr
--    │
--    ├── On Err → SailME.throw (Err (Memory_Exception ...))
--    ▼
-- 6. assert (res == is_store_conditional(Store Data))   [VmemUtils.lean:336]
--    │ res=false, is_store_conditional(Store Data)=false → OK
--    │
--    │ if res ∧ ¬match_reservation → no (res=false)
--    ▼
-- 7. mem_write_ea (paddr, 4, aq=false, rl=false, con=false)  [Mem.lean:614]
--    │ if (rl ∨ con) ∧ ¬is_aligned → no (rl=false, con=false)
--    │ pure (Ok (write_ram_ea wk paddr 4))
--    │   write_ram_ea is a no-op (returns Unit)         [PhysMemInterface.lean:324]
--    │
--    ├── On Err → SailME.throw (Err (Memory_Exception ...))
--    ▼
-- 8. let write_value := extractLsb data 31 0           -- extract the 4-byte slice
--    │ (For offset=0, bytes=4: bits [31:0] of data)
--    ▼
-- 9. mem_write_value (paddr, 4, write_value, Store Data, false, false, false)
--    │                                                  [Mem.lean:662]
--    ▼
-- 10. mem_write_value_meta (paddr, 4, value, Store Data, default_meta, false, false, false)
--    │                                                  [Mem.lean:656]
--    │ let ep := effectivePrivilege(Store Data, mstatus, cur_privilege)
--    │   → Machine (same as step 5)
--    ▼
-- 11. mem_write_value_priv_meta (paddr, 4, value, Store Data, Machine, (), false, false, false)
--    │                                                  [Mem.lean:635]
--    │ if (rl ∨ con) ∧ ¬is_aligned → no (both false)
--    ▼
-- 12. checked_mem_write (paddr, 4, value, Store Data, Machine, (), false, false, false)
--    │                                                  [Mem.lean:621]
--    │ match phys_access_check(Store Data, Machine, paddr, 4, false)
--    │   Machine mode → PMP check passes → none
--    │
--    │ if within_mmio_writable(paddr, 4) → no (JoltConfig: regular RAM)
--    ▼
-- 13. write_ram (Write_plain, paddr, 4, value, ())     [PhysMemInterface.lean:287]
--    │ wk = Write_plain (from write_kind_of_flags false false false)
--    │ Build Mem_write_request with:
--    │   access_kind = AK_explicit { variety = AV_plain, strength = AS_normal }
--    │   pa = paddr bits, size = 4, value = some data
--    ▼
-- 14. sail_mem_write (request)                          [Specialization.lean:79]
--    │ → PreSail.ConcurrencyInterfaceV2.sail_mem_write
--    │ This is the Sail library primitive that writes bytes into state.mem
--    │ (an ExtHashMap Nat (BitVec 8)).
--    │
--    │ match result:
--    │   Ok _ → __WriteRAM_Meta (no-op), pure true
--    │   Err () → pure false
--    ▼
-- 15. Back in mem_write_value_priv_meta:
--    │ On Ok: mem_write_callback (logging, no state change)
--    │ pure result
--    ▼
-- 16. Back in vmem_write_addr loop:
--    │ offset == last (0==0) → finished=true
--    │ pure (Ok write_success)
--    ▼
-- 17. Back in execute_STORE:
--    │ match Ok _ → pure RETIRE_SUCCESS
--
-- Summary of checks before the hashmap write:
--   (a) width ≤ xlen_bytes assertion
--   (b) misaligned exception check → passes (plat_enable_misaligned_access=true)
--   (c) translateAddr → identity (Machine + Bare mode)
--   (d) store-conditional reservation check → skipped (not SC)
--   (e) mem_write_ea alignment check → passes (rl=false, con=false)
--   (f) phys_access_check (PMP) → passes (Machine mode)
--   (g) MMIO check → not MMIO (regular RAM from JoltConfig)
--
-- Under JoltConfig, all checks pass and the net effect is:
--   read rs1, rs2 → compute addr → write low 32 bits of rs2 into state.mem at addr
-- ===========================================================================

-- ============================================================================
-- Main theorem: Jolt SW = Sail SW
-- ============================================================================

-- Running Jolt's 13-step SW decomposition (read-modify-write via dword-aligned
-- access) and projecting onto Sail state produces exactly the same result as
-- running Sail's native `execute_STORE` at width 4.
--
-- Assumptions will be refined as we fill in the proof — for now we include
-- the same shape used by the load proofs (WellFormed, JoltConfig) plus
-- placeholders for store-specific conditions (alignment, memory pipeline).
theorem jolt_sw_eq_sail (imm : BitVec 12) (rs2 rs1 : regidx)
    (js : SailJoltState) (hwf : WellFormed js) (hcfg : JoltConfig js.sail) :
    projectResult ((jolt_sw imm rs2 rs1).run js) =
    (execute_STORE imm rs2 rs1 4).run js.sail := by
  sorry

end
