import JoltBytecode.JoltISA.Environment

/-!
# ALU-family public theorem bundles

The ordinary ALU and advice-backed ALU public theorems need only source-register
read assumptions. Destination writes are derived from generated Sail/Jolt write
semantics; no privilege, memory, or CSR assumptions belong here.
-/

set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

set_option autoImplicit true

noncomputable section

namespace ALUFamily

/-- Public assumptions for one-source ALU instructions.

This bundles exactly one source-register read: `rs1` has value `rs1_val` in the
initial Sail state. -/
structure UnarySourceReadAssumptions (rs1 : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs1_read : XRegRead rs1 rs1_val js.sail

/-- Public assumptions for two-source ALU instructions.

This bundles exactly the two source-register reads: `rs1` and `rs2` have the
recorded values in the initial Sail state. -/
structure BinarySourceReadAssumptions
    (rs2 rs1 : regidx) (js : SailJoltState) where
  rs1_val : BitVec 64
  rs2_val : BitVec 64
  rs1_read : XRegRead rs1 rs1_val js.sail
  rs2_read : XRegRead rs2 rs2_val js.sail

end ALUFamily

end
