import JoltBytecode.JoltISA.Expansions.ALU
import JoltBytecode.JoltISA.Expansions.Mul
import JoltBytecode.JoltISA.Expansions.DivRem
import JoltBytecode.JoltISA.Expansions.Load
import JoltBytecode.JoltISA.Expansions.Store
import JoltBytecode.JoltISA.Expansions.Atomics
import JoltBytecode.JoltISA.Expansions.Advice
import JoltBytecode.JoltISA.ExpansionsAutomated

/-!
# Hand-written vs auto-generated expansion equivalence

Each theorem shows a hand-written `…Program` (in `JoltISA/Expansions/`) equals
the auto-generated `…ProgramAuto` (in `JoltISA/ExpansionsAutomated.lean`,
produced by `jolt-lean-gen --lean`). The argument order differs between the two
(hand: `rs2 rs1 rd`; auto: `rd rs1 rs2`), so each statement maps the arguments
across.

Shift-immediate instructions are specialised in the generator to the sentinel
shift amount 37, so those equivalences are stated at `shamt = 37`.

Starting set: easy ALU cases, including block-using ones (`slliBlock`, and the
`inlineTmp0` scratch in `sll`/`srl`) to confirm block/wrapper unfolding closes
by `rfl`.
-/

open Sail PreSail LeanRV64D.Functions

-- The atomic proofs feed a deliberately broad unfold set (all AMO scratch-slot
-- and block helpers) to one uniform tactic; not every entry fires per instruction.
set_option linter.unusedSimpArgs false

namespace JoltISA

theorem addw_auto_eq (rs2 rs1 rd : regidx) :
    addwProgram rs2 rs1 rd = addwProgramAuto rd rs1 rs2 := by rfl

theorem subw_auto_eq (rs2 rs1 rd : regidx) :
    subwProgram rs2 rs1 rd = subwProgramAuto rd rs1 rs2 := by rfl

theorem mulw_auto_eq (rs2 rs1 rd : regidx) :
    mulwProgram rs2 rs1 rd = mulwProgramAuto rd rs1 rs2 := by rfl

theorem sll_auto_eq (rs2 rs1 rd : regidx) :
    sllProgram rs2 rs1 rd = sllProgramAuto rd rs1 rs2 := by rfl

theorem srl_auto_eq (rs2 rs1 rd : regidx) :
    srlProgram rs2 rs1 rd = srlProgramAuto rd rs1 rs2 := by rfl

theorem slli_auto_eq (rs1 rd : regidx) :
    slliProgram 37 rs1 rd = slliProgramAuto rd rs1 := by rfl

theorem srli_auto_eq (rs1 rd : regidx) :
    srliProgram 37 rs1 rd = srliProgramAuto rd rs1 := by rfl

theorem srai_auto_eq (rs1 rd : regidx) :
    sraiProgram 37 rs1 rd = sraiProgramAuto rd rs1 := by rfl

theorem sra_auto_eq (rs2 rs1 rd : regidx) :
    sraProgram rs2 rs1 rd = sraProgramAuto rd rs1 rs2 := by rfl

/-! ## Word ALU -/

theorem sllw_auto_eq (rs2 rs1 rd : regidx) :
    sllwProgram rs2 rs1 rd = sllwProgramAuto rd rs1 rs2 := by rfl

theorem srlw_auto_eq (rs2 rs1 rd : regidx) :
    srlwProgram rs2 rs1 rd = srlwProgramAuto rd rs1 rs2 := by rfl

theorem sraw_auto_eq (rs2 rs1 rd : regidx) :
    srawProgram rs2 rs1 rd = srawProgramAuto rd rs1 rs2 := by rfl

theorem addiw_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    addiwProgram imm rs1 rd = addiwProgramAuto rd rs1 imm := by rfl

theorem slliw_auto_eq (rs1 rd : regidx) :
    slliwProgram 5 rs1 rd = slliwProgramAuto rd rs1 := by rfl

theorem srliw_auto_eq (rs1 rd : regidx) :
    srliwProgram 5 rs1 rd = srliwProgramAuto rd rs1 := by rfl

theorem sraiw_auto_eq (rs1 rd : regidx) :
    sraiwProgram 5 rs1 rd = sraiwProgramAuto rd rs1 := by rfl

/-! ## Multiply-high -/

theorem mulh_auto_eq (rs2 rs1 rd : regidx) :
    mulhProgram rs2 rs1 rd = mulhProgramAuto rd rs1 rs2 := by rfl

theorem mulhsu_auto_eq (rs2 rs1 rd : regidx) :
    mulhsuProgram rs2 rs1 rd = mulhsuProgramAuto rd rs1 rs2 := by rfl

/-! ## DivRem — general over the advice values -/

theorem div_auto_eq (rs2 rs1 rd : regidx) (a0 a1 : BitVec 64) :
    divProgram rs2 rs1 rd a0 a1 = divProgramAuto rd rs1 rs2 a0 a1 := by rfl

theorem divu_auto_eq (rs2 rs1 rd : regidx) (a0 : BitVec 64) :
    divuProgram rs2 rs1 rd a0 = divuProgramAuto rd rs1 rs2 a0 := by rfl

theorem divw_auto_eq (rs2 rs1 rd : regidx) (a0 a1 : BitVec 64) :
    divwProgram rs2 rs1 rd a0 a1 = divwProgramAuto rd rs1 rs2 a0 a1 := by rfl

theorem divuw_auto_eq (rs2 rs1 rd : regidx) (a0 : BitVec 64) :
    divuwProgram rs2 rs1 rd a0 = divuwProgramAuto rd rs1 rs2 a0 := by rfl

theorem rem_auto_eq (rs2 rs1 rd : regidx) (a0 a1 : BitVec 64) :
    remProgram rs2 rs1 rd a0 a1 = remProgramAuto rd rs1 rs2 a0 a1 := by rfl

theorem remu_auto_eq (rs2 rs1 rd : regidx) (a0 : BitVec 64) :
    remuProgram rs2 rs1 rd a0 = remuProgramAuto rd rs1 rs2 a0 := by rfl

theorem remw_auto_eq (rs2 rs1 rd : regidx) (a0 a1 : BitVec 64) :
    remwProgram rs2 rs1 rd a0 a1 = remwProgramAuto rd rs1 rs2 a0 a1 := by rfl

theorem remuw_auto_eq (rs2 rs1 rd : regidx) (a0 : BitVec 64) :
    remuwProgram rs2 rs1 rd a0 = remuwProgramAuto rd rs1 rs2 a0 := by rfl

/-! ## Advice loads -/

theorem advicelb_auto_eq (rd : regidx) (advice : BitVec 8) :
    advicelbProgram rd advice = advicelbProgramAuto rd (advice.setWidth 64) := by
  unfold advicelbProgram advicelbProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem advicelh_auto_eq (rd : regidx) (advice : BitVec 16) :
    advicelhProgram rd advice = advicelhProgramAuto rd (advice.setWidth 64) := by
  unfold advicelhProgram advicelhProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem advicelw_auto_eq (rd : regidx) (advice : BitVec 32) :
    advicelwProgram rd advice = advicelwProgramAuto rd (advice.setWidth 64) := by
  unfold advicelwProgram advicelwProgramAuto adviceLoadDstFor adviceLoadSrcFor
    sideEffectingRdZeroDst rdZeroRewriteVReg slliBlock
  cases isX0 rd <;> rfl

theorem adviceld_auto_eq (rd : regidx) (advice : BitVec 64) :
    adviceldProgram rd advice = adviceldProgramAuto rd advice := by
  unfold adviceldProgram adviceldProgramAuto adviceLoadDstFor sideEffectingRdZeroDst
    rdZeroRewriteVReg
  cases isX0 rd <;> rfl

/-! ## Stores (no rd branch; imm pass-through) -/

theorem sb_auto_eq (imm : BitVec 12) (rs2 rs1 : regidx) :
    sbProgram imm rs2 rs1 = sbProgramAuto rs1 rs2 imm := by rfl

theorem sh_auto_eq (imm : BitVec 12) (rs2 rs1 : regidx) :
    shProgram imm rs2 rs1 = shProgramAuto rs1 rs2 imm := by rfl

theorem sw_auto_eq (imm : BitVec 12) (rs2 rs1 : regidx) :
    swProgram imm rs2 rs1 = swProgramAuto rs1 rs2 imm := by rfl

/-! ## Loads

Side-effecting: the hand def threads the rd==x0 branch through each temporary
(`loadV0For`/`loadDstFor`/…), while the generated def has a single outer
`if isX0 rd`. Not definitionally equal, so we split on `isX0 rd` and let `simp`
resolve the per-operand branches against the outer one. -/

theorem lb_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lbProgram imm rs1 rd = lbProgramAuto rd rs1 imm := by
  unfold lbProgram lbProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

theorem lbu_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lbuProgram imm rs1 rd = lbuProgramAuto rd rs1 imm := by
  unfold lbuProgram lbuProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

theorem lh_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lhProgram imm rs1 rd = lhProgramAuto rd rs1 imm := by
  unfold lhProgram lhProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

theorem lhu_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lhuProgram imm rs1 rd = lhuProgramAuto rd rs1 imm := by
  unfold lhuProgram lhuProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

theorem lw_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lwProgram imm rs1 rd = lwProgramAuto rd rs1 imm := by
  unfold lwProgram lwProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

theorem lwu_auto_eq (imm : BitVec 12) (rs1 rd : regidx) :
    lwuProgram imm rs1 rd = lwuProgramAuto rd rs1 imm := by
  unfold lwuProgram lwuProgramAuto loadV0For loadV1For loadInlineTmpFor loadDstFor
    sideEffectingRdZeroDst
  cases isX0 rd <;> rfl

/-! ## Atomics

Same side-effecting shape as loads, but the branch is threaded through the AMO
scratch-slot helpers (all bottoming out in `amoVRegFor rd n = if isX0 rd then
inlineTmp (n+1) else inlineTmp n`) and the block builders. Unfold the lot, split
on `isX0 rd`, and let `rfl` finish. -/

-- Uniform tactic: split on `isX0 rd`, unfold the AMO scratch-slot and block
-- helpers (deliberately broad — not all fire per instruction), and let `rfl`
-- close the residual definitional equality.
local macro "amo_equiv " r:ident p:ident pa:ident : tactic =>
  `(tactic|
    (dsimp only [$p:ident, $pa:ident, amoDoubleBinopProgram, amoDoubleSelectProgram,
        amoWordBinopProgram, amoWordSelectProgram, amoWordSelectRustProgram,
        amoPre64Program, amoPre64ProgramWithScratch, amoPost64Program,
        amoPost64ProgramWithScratch, amoDstFor, sideEffectingRdZeroDst,
        rdZeroRewriteVReg, amoVRegFor, amoOldVRegFor, amoNewVRegFor, amoTmpVRegFor,
        amoMaskVRegFor, amoDwordVRegFor, amoShiftVRegFor, amoInlineTmpVRegFor,
        amoDoubleBinopNewVRegFor, amoDoubleBinopOldVRegFor, amoWordSwapMaskVRegFor,
        amoWordSwapDwordVRegFor, amoWordSwapShiftVRegFor, amoWordSwapOldVRegFor,
        amoWordSwapInlineTmpVRegFor, amoWordSelectOldVRegFor, amoWordSelectDwordVRegFor,
        amoWordSelectShiftVRegFor, amoWordSelectNewVRegFor, amoWordSelectMaskVRegFor,
        amoWordSelectInlineTmpVRegFor, slliBlock, sllBlock, srlBlock, sraiBlock,
        srliBlock] <;> cases isX0 $r <;> rfl))

theorem amoaddd_auto_eq (rs2 rs1 rd : regidx) :
    amoadddProgram rs2 rs1 rd = amoadddProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoadddProgram amoadddProgramAuto

theorem amoandd_auto_eq (rs2 rs1 rd : regidx) :
    amoanddProgram rs2 rs1 rd = amoanddProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoanddProgram amoanddProgramAuto

theorem amoord_auto_eq (rs2 rs1 rd : regidx) :
    amoordProgram rs2 rs1 rd = amoordProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoordProgram amoordProgramAuto

theorem amoxord_auto_eq (rs2 rs1 rd : regidx) :
    amoxordProgram rs2 rs1 rd = amoxordProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoxordProgram amoxordProgramAuto

theorem amoswapd_auto_eq (rs2 rs1 rd : regidx) :
    amoswapdProgram rs2 rs1 rd = amoswapdProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoswapdProgram amoswapdProgramAuto

theorem amomind_auto_eq (rs2 rs1 rd : regidx) :
    amomindProgram rs2 rs1 rd = amomindProgramAuto rd rs1 rs2 := by
  amo_equiv rd amomindProgram amomindProgramAuto

theorem amomaxd_auto_eq (rs2 rs1 rd : regidx) :
    amomaxdProgram rs2 rs1 rd = amomaxdProgramAuto rd rs1 rs2 := by
  amo_equiv rd amomaxdProgram amomaxdProgramAuto

theorem amominud_auto_eq (rs2 rs1 rd : regidx) :
    amominudProgram rs2 rs1 rd = amominudProgramAuto rd rs1 rs2 := by
  amo_equiv rd amominudProgram amominudProgramAuto

theorem amomaxud_auto_eq (rs2 rs1 rd : regidx) :
    amomaxudProgram rs2 rs1 rd = amomaxudProgramAuto rd rs1 rs2 := by
  amo_equiv rd amomaxudProgram amomaxudProgramAuto

theorem amoaddw_auto_eq (rs2 rs1 rd : regidx) :
    amoaddwProgram rs2 rs1 rd = amoaddwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoaddwProgram amoaddwProgramAuto

theorem amoandw_auto_eq (rs2 rs1 rd : regidx) :
    amoandwProgram rs2 rs1 rd = amoandwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoandwProgram amoandwProgramAuto

theorem amoorw_auto_eq (rs2 rs1 rd : regidx) :
    amoorwProgram rs2 rs1 rd = amoorwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoorwProgram amoorwProgramAuto

theorem amoxorw_auto_eq (rs2 rs1 rd : regidx) :
    amoxorwProgram rs2 rs1 rd = amoxorwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoxorwProgram amoxorwProgramAuto

theorem amoswapw_auto_eq (rs2 rs1 rd : regidx) :
    amoswapwProgram rs2 rs1 rd = amoswapwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amoswapwProgram amoswapwProgramAuto

theorem amominw_auto_eq (rs2 rs1 rd : regidx) :
    amominwProgram rs2 rs1 rd = amominwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amominwProgram amominwProgramAuto

theorem amomaxw_auto_eq (rs2 rs1 rd : regidx) :
    amomaxwProgram rs2 rs1 rd = amomaxwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amomaxwProgram amomaxwProgramAuto

theorem amominuw_auto_eq (rs2 rs1 rd : regidx) :
    amominuwProgram rs2 rs1 rd = amominuwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amominuwProgram amominuwProgramAuto

theorem amomaxuw_auto_eq (rs2 rs1 rd : regidx) :
    amomaxuwProgram rs2 rs1 rd = amomaxuwProgramAuto rd rs1 rs2 := by
  amo_equiv rd amomaxuwProgram amomaxuwProgramAuto

end JoltISA
