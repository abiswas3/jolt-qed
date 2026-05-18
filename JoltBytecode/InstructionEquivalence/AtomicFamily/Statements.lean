import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.InstructionEquivalence.Memory.Utils

/-!
# Atomic-family theorem statements

These are review-stage equivalence statements for the RV64 AMO programs in
`JoltISA.Expansions.Atomics`.  The assumptions separate the normal Jolt
load/store path from Sail's native atomic path; the proofs still need the
phase helpers and memory-splice math.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace AtomicFamily

structure StoreBareTranslation (addr : BitVec 64) (s : SailState) : Prop where
  translate : translateAddr (Virtaddr addr) (Store Data) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

structure FlatStoreMem (addr : BitVec 64) (width : Nat) (s : SailState) :
    Prop where
  pmp : phys_access_check (Store Data) Privilege.Machine
    (physaddr.Physaddr addr) width false s = .ok none s
  mmio : within_mmio_writable (physaddr.Physaddr addr) width s = .ok false s

structure AtomicBareTranslation (op : amoop) (addr : BitVec 64)
    (s : SailState) : Prop where
  translate : translateAddr (Virtaddr addr) (Atomic (op, Data, Data)) s =
    .ok (Ok (physaddr.Physaddr addr, init_ext_ptw)) s

structure FlatAtomicMem (op : amoop) (addr : BitVec 64) (width : Nat)
    (s : SailState) : Prop where
  pmp : phys_access_check (Atomic (op, Data, Data)) Privilege.Machine
    (physaddr.Physaddr addr) width true s = .ok none s
  readable : within_mmio_readable (physaddr.Physaddr addr) width s =
    .ok false s
  writable : within_mmio_writable (physaddr.Physaddr addr) width s =
    .ok false s

structure AmoMemoryAssumptions
    (op : amoop) (sailWidth : Nat) (joltAddr amoAddr : BitVec 64)
    (s : SailState) : Prop where
  jolt_load_translate : BareTranslation joltAddr s
  jolt_load_mem : FlatPhysMem joltAddr 8 s
  jolt_store_translate : StoreBareTranslation joltAddr s
  jolt_store_mem : FlatStoreMem joltAddr 8 s
  sail_atomic_translate : AtomicBareTranslation op amoAddr s
  sail_atomic_mem : FlatAtomicMem op amoAddr sailWidth s

theorem amoadddProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOADD 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoadddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amoaddwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOADD 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoaddwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOADD false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amoanddProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOAND 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoanddProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amoandwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOAND 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoandwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOAND false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amoordProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOOR 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amoorwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOOR 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOOR false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amoxordProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOXOR 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoxordProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOXOR false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amoxorwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOXOR 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoxorwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOXOR false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amoswapdProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amoswapwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOSWAP 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amoswapwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOSWAP false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amomindProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMIN 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomindProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMIN false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amominwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMIN 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMIN false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amominudProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amominuwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMINU 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amominuwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMINU false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amomaxdProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMAX 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxdProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAX false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amomaxwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMAX 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAX false false rs2 rs1 4 rd).run js.sail := by
  sorry

theorem amomaxudProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMAXU 8 addr addr js.sail)
    (h_no_ovf : addr.toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (7 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxudProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 8 rd).run js.sail := by
  sorry

theorem amomaxuwProgram_eq_sail_aligned
    (rs2 rs1 rd : regidx) (js : SailJoltState)
    (hcfg : JoltConfig js.sail)
    (addr rs2Val : BitVec 64)
    (hrs1 : rX_bits rs1 js.sail = .ok addr js.sail)
    (hrs2 : rX_bits rs2 js.sail = .ok rs2Val js.sail)
    (h_mem : AmoMemoryAssumptions amoop.AMOMAXU 4
      (addr &&& (-8 : BitVec 64)) addr js.sail)
    (h_no_ovf : (addr &&& (-8 : BitVec 64)).toNat + 7 < 2 ^ 64)
    (h_align : addr &&& (3 : BitVec 64) = 0) :
    projectResult ((JoltISA.execProgram
      (JoltISA.amomaxuwProgram rs2 rs1 rd)).run js) =
      (execute_AMO amoop.AMOMAXU false false rs2 rs1 4 rd).run js.sail := by
  sorry

end AtomicFamily

end
