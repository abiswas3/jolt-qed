
# Jolt-QED: State of the World

**DONE: 24 | INPROGRESS: 7 | TODO: 34**

This is an effort to prove that Jolt bytecode expansions are equivalent to the RiscV instructions they replace.
There are few classes of instructions 

## ALU Instructions (DONE: 14 | INPROGRESS: 2 | TODO: 2)

These are often called FormatR and FormatI instructions, and their RISCV counterparts just read registers (which does not change state), and writes to a single destination register `rd`. 

- DONE: ADDW (Format R) — `Addw.lean`
- DONE: SUBW (Format R) — `Subw.lean`
- DONE: ADDIW (Format I) — `Addiw.lean`
- DONE: MULW (Format R) — `Mulw.lean`
- TODO: MULH (Format R) — `Mulh.lean` (stub only, no proofs)
- TODO: MULHSU (Format R)
- INPROGRESS: SLLW (Format R) — `Sllw.lean` (1 sorry: `sll_32_eq_mul_trunc`)
- INPROGRESS: SRLW (Format R) — `Srlw.lean` (1 sorry: `ctz_srlw_bitmask`)
- DONE: SRAW (Format R) — `Sraw.lean`
- DONE: SLL (Format R) — `Sll.lean`
- DONE: SRL (Format R) — `Srl.lean`
- DONE: SRA (Format R) — `Sra.lean`
- DONE: SRAI (Format I) — `Srai.lean`
- DONE: SRAIW (Format I) — `Sraiw.lean`
- DONE: SLLI (Format I) — `Slli.lean`
- DONE: SLLIW (Format I) — `Slliw.lean`
- DONE: SRLI (Format I) — `Srli.lean`
- DONE: SRLIW (Format I) — `Srliw.lean`

There is a general strategy for this group of instructions, ill put this in.

## ALU Instructions With Advice (DONE: 0 | INPROGRESS: 0 | TODO: 8)

This is the DIV, REM, class of formatR and formatI instructions which do the same as above but they also use an advice string in jolt. 
So here the proofs are different: We do not necessarily step through both monads and say sail state is the same. 
Here we have to do soundness and completeness proofs. 
If advice is right, then the jolt-expansion goes through cleanly without panics.
Otherwise it does not. 
So will have to prove completeness and soundness lemmas here. 
We have not started this type of instructions. 

- TODO: DIV, DIVU, DIVW, DIVUW
- TODO: REM, REMU, REMW, REMUW

Helper: `Advice.lean` — shared advice collapse theorem, SLLI/SRAI step lemmas, projectResult lifting

## Load (DONE: 10 | INPROGRESS: 0 | TODO: 0)

These are fully complete. They load values from memory into a destination `rd`.

- DONE: LB — `Lb.lean` (signed byte)
- DONE: LBU — `Lbu.lean` (unsigned byte)
- DONE: LH — `Lh.lean` (signed halfword)
- DONE: LHU — `Lhu.lean` (unsigned halfword)
- DONE: LW — `Lw.lean` (signed word)
- DONE: LWU — `Lwu.lean` (unsigned word)
- DONE: ADVICELB — `Advicelb.lean`
- DONE: ADVICELD — `Adviceld.lean`
- DONE: ADVICELH — `Advicelh.lean`
- DONE: ADVICELW — `Advicelw.lean`

Helper: `LoadDefUtils.lean` — shared load definitions

## Store Instructions (DONE: 0 | INPROGRESS: 3 | TODO: 0)

These write register values to memory. SB/SH/SW have inline sequences; SD does not.

- INPROGRESS: SB — `Sb.lean` (Jolt def + main theorem stub, proof sorry'd, `vreg_SD` sorry'd)
- INPROGRESS: SH — `Sh.lean` (Jolt def + main theorem stub, proof sorry'd, `vreg_SD` sorry'd)
- INPROGRESS: SW — `Sw.lean` (Jolt def + main theorem stub, proof sorry'd, `vreg_SD` sorry'd)

## Atomic Instructions (DONE: 0 | INPROGRESS: 2 | TODO: 20)

Load-reserved / store-conditional pairs and AMO (atomic memory operations).
All have inline sequences in the Rust implementation.

**Load-reserved / Store-conditional:**
- INPROGRESS: LRD — `Lrd.lean` (not in build)
- INPROGRESS: LRW — `Lrw.lean` (not in build)
- TODO: SCD — store conditional dword
- TODO: SCW — store conditional word

**AMO (read-modify-write):**
- TODO: AMOADDD, AMOADDW
- TODO: AMOANDD, AMOANDW
- TODO: AMOMAXD, AMOMAXUD, AMOMAXUW, AMOMAXW
- TODO: AMOMIND, AMOMINUD, AMOMINUW, AMOMINW
- TODO: AMOORD, AMOORW
- TODO: AMOSWAPD, AMOSWAPW
- TODO: AMOXORD, AMOXORW

## System Instructions (DONE: 0 | INPROGRESS: 0 | TODO: 4)

- TODO: ECALL
- TODO: CSRRS
- TODO: CSRRW
- TODO: MRET

