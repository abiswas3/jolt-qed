set_option maxHeartbeats 1_000_000_000
set_option linter.unusedVariables false

open Sail PreSail LeanRV64D.Functions

noncomputable section

/-!
# MULH: Jolt's 7-step decomposition = Sail MULH

*Not yet implemented.* The decomposition structure is noted below so the
file has a durable home.

Jolt decomposes MULH as:
1. `VirtualMovSign v_sx, rs1` — extract sign of rs1
2. `VirtualMovSign v_sy, rs2` — extract sign of rs2
3. `MUL v_sx, v_sx, rs2`      — `s_x * y`
4. `MUL v_sy, v_sy, rs1`      — `s_y * x`
5. `MULHU v_tmp, rs1, rs2`    — unsigned high multiply
6. `ADD v_tmp, v_tmp, v_sx`   — add `s_x * y`
7. `ADD rd, v_tmp, v_sy`      — add `s_y * x`

Key insight for the bridge: signed high multiply = unsigned high
multiply plus sign corrections.
-/

end
