import JoltBytecode.Bundles
import JoltBytecode.InstructionEquivalence.ProofSupport.Projection
import JoltBytecode.InstructionEquivalence.ProofSupport.InstructionLemmas
import JoltBytecode.InstructionEquivalence.ProofSupport.RegisterAccess

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace Natives

/-- Main native `BLT` equivalence statement. -/
def bltInstrEqSailStatement
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (_h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) : Prop :=
  System.systemProjectResult
    ((JoltISA.execInstr (.BLT (.xreg rs1) (.xreg rs2) imm)).run js) =
    ((execute_BTYPE imm rs2 rs1 bop.BLT).run js.sail)
  
theorem systemProjectResult_pure_retire
      (js : SailJoltState)
      (hlinked : LinkedCSRs js) :
      System.systemProjectResult
        (((pure RETIRE_SUCCESS : JoltMonad ExecutionResult) js))
      =
      ((pure RETIRE_SUCCESS : SailM ExecutionResult) js.sail) := by
    simp only [pure, EStateM.pure, System.systemProjectResult]
    rw [Projection.systemProject_eq_sail_of_compatible js hlinked]

-- Given Sail Monad m, and continuation function f
-- running m via 
theorem liftSail_bind
    (m : SailM α)
    (f : α → SailM β) :
    liftSail (m >>= f) =
      (liftSail m >>= fun x => liftSail (f x)) := by
  unfold liftSail 
  funext js 
  simp only [bind, EStateM.bind]
  cases hm: m js.sail <;> rfl

theorem bltInstr_eq_sail
    (imm : BitVec 13)
    (rs2 rs1 : regidx)
    (js : SailJoltState)
    (h : BinarySourceReadWithLinkedCSRs rs2 rs1 js) :
    bltInstrEqSailStatement imm rs2 rs1 js h := by
 unfold bltInstrEqSailStatement
 -- RHS 
 simp only [execute_BTYPE]
 simp only [EStateM.run, bind, EStateM.bind]
 simp only [h.rs1_read, h.rs2_read]
 simp only [pure, EStateM.pure]
 -- LHS 
 simp only [JoltISA.execInstr]
 rw [bind_after_success_of_readSrc_xreg rs1 js h.rs1_val h.rs1_read _]
 rw [bind_after_success_of_readSrc_xreg rs2 js h.rs2_val h.rs2_read _]
 cases h_taken : zopz0zI_s h.rs1_val h.rs2_val
 · -- not taken
   simp only [Bool.false_eq_true, if_false]
   exact systemProjectResult_pure_retire js h.linkedCSRs 
 · -- taken
   simp only [if_true]
   rw [← liftSail_bind]
   simp only [bind, EStateM.bind] 
   unfold liftSail 
   
   sorry





end Natives

end
