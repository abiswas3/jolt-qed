import JoltBytecode.JoltISA.Environment
import JoltBytecode.InstructionEquivalence.Memory.Utils
import JoltBytecode.VirtualInstructions
import JoltBytecode.InstructionEquivalence.LoadDefUtils
import JoltBytecode.InstructionEquivalence.ProofSupport

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false
set_option mvcgen.warning false

open Sail PreSail LeanRV64D.Functions
open Std.Do
open virtaddr MemoryAccessType mem_payload

set_option autoImplicit true

noncomputable section

namespace InstructionEquivalence

theorem dword_load_assumptions_of_aligned_translate_phys (addr : BitVec 64) (s : SailState)
    (haligned : AlignedDwordAccess addr)
    (htranslate : BareTranslation addr s)
    (hphys : FlatPhysMem addr 8 s) :
    DwordLoadAssumptions addr s := by
  refine
    { aligned := haligned
      translate := htranslate
      phys := hphys }

end InstructionEquivalence
