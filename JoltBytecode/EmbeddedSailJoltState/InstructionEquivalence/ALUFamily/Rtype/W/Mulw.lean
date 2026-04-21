import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Rtype.W.Family
import JoltBytecode.EmbeddedSailJoltState.InstructionEquivalence.ALUFamily.Bridges.Mul

set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULW: Jolt MUL + VirtualSignExtendWord = Sail MULW

Unlike `ADDW`/`SUBW`, Jolt's `MULW` does not go through
`execute_RTYPE rop.MUL`. It performs the multiplication inline:

```
liftSail (rX_bits rs1)
liftSail (rX_bits rs2)
liftSail (wX_bits rd (v1 * v2))
jolt_virtual_sign_extend_word rd
```

Sail's `MULW` is a standalone function `execute_MULW` (not a branch of
`execute_RTYPEW`). The uniform R-type W closer still applies because the
surface shape — read `rs1`, read `rs2`, write `rd`, return — is the same.

Bridge: `mulw32_eq_mul` (in `Bridges/Mul.lean`), connecting the Sail
`to_bits_truncate ∘ toInt` idiom to plain 32-bit `BitVec` multiply, and
`extractLsb_mul`, truncation distributing over multiply.
-/

theorem execute_MULW_factored (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = (do
      let v1 ← rX_bits rs1
      let v2 ← rX_bits rs2
      wX_bits rd (sign_extend (m := 64)
        (to_bits_truncate (l := 32)
          (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
           BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
      pure RETIRE_SUCCESS) := by
  simp [execute_MULW, bind_pure_comp, pure_bind]

def jolt_mulw (rs2 rs1 rd : regidx) : JoltMonad ExecutionResult := do
  let v1 ← liftSail (rX_bits rs1)
  let v2 ← liftSail (rX_bits rs2)
  liftSail (wX_bits rd (v1 * v2))
  jolt_virtual_sign_extend_word rd
  pure RETIRE_SUCCESS

theorem jolt_mulw_concrete (rs2 rs1 rd : regidx)
    (hrd : rd ≠ regidx.Regidx 0) (js : SailJoltState) (hwf : WellFormed js) :
    ∃ (js' : SailJoltState) (v1 v2 : BitVec 64),
      rX_bits rs1 js.sail = .ok v1 js.sail ∧
      rX_bits rs2 js.sail = .ok v2 js.sail ∧
      (jolt_mulw rs2 rs1 rd).run js = .ok RETIRE_SUCCESS js' ∧
      js'.sail = stateAfterWrite js.sail rd
        (sign_extend (m := 64)
          (to_bits_truncate (l := 32)
            (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
             BitVec.toInt (Sail.BitVec.extractLsb v2 31 0)))) := by
  unfold jolt_mulw liftSail
  simp only [bind, EStateM.bind, pure, EStateM.pure, EStateM.run]
  obtain ⟨v1, h1⟩ := hwf rs1
  obtain ⟨v2, h2⟩ := hwf rs2
  simp only [h1, h2]
  obtain ⟨s3, hw1⟩ := wX_shape rd (v1 * v2) js.sail
  simp only [hw1]
  have hrx := wX_rX_roundtrip rd _ js.sail s3 hrd hw1
  obtain ⟨js4, hvsew, hsail⟩ :=
    jolt_virtual_sign_extend_word_concrete rd { sail := s3, vregs := js.vregs } (v1 * v2) hrd hrx
  simp only [EStateM.run] at hvsew
  simp only [hvsew]
  refine ⟨js4, v1, v2, rfl, rfl, rfl, ?_⟩
  rw [hsail, show ({ sail := s3, vregs := js.vregs } : SailJoltState).sail = s3 from rfl,
      wX_bits_eq_stateAfterWrite rd (v1 * v2) js.sail s3 hw1,
      stateAfterWrite_stateAfterWrite]
  congr 1; congr 1
  rw [extractLsb_mul, ← mulw32_eq_mul]

theorem jolt_mulw_eq_sail (rs2 rs1 rd : regidx) (hrd : rd ≠ regidx.Regidx 0)
    (js : SailJoltState) (hwf : WellFormed js) :
    projectResult ((jolt_mulw rs2 rs1 rd).run js) =
    (execute_MULW rs2 rs1 rd).run js.sail :=
  rtype_eq_sail_uniform
    (f := fun v1 v2 => sign_extend (m := 64)
      (to_bits_truncate (l := 32)
        (BitVec.toInt (Sail.BitVec.extractLsb v1 31 0) *i
         BitVec.toInt (Sail.BitVec.extractLsb v2 31 0))))
    (execute_MULW_factored rs2 rs1 rd)
    (jolt_mulw_concrete rs2 rs1 rd hrd js hwf)

end
