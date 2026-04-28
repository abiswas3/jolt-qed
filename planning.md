
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

## ALU Instructions With Advice (DONE: 1 | INPROGRESS: 3 | TODO: 4)

The general strategy to close these proofs can be found [here](https://randomwalks.xyz/blog/bytecode-expansions/chainsmokers/).
Most of the blog focuses on closing the top level lemmas. 
We found that in order to close the phase lemmas -- we had to implement existential lemmas along with `run_ok` and `run_err` lemmas for individual instruction.
The issue was that `vregs` was a function, and each write had an if `vd = x` then vregs[x] = v else vregs = vregs (I paraphrase, i forget the syntax).
This means a sequence of 4 or more writes was leading to a bit of a blow up in cases. 
Instead we say at the end of the write, there exists some jolt state `js'` such that the following holds. 
When chaining in the main lemmas we can easily find a value that satisfies this existential. 

Note that the above helps characterise the monadic step functions using `EStateM`. 
The pure math lemmas of div are proven but quite a handful.
They will be modularised later. 
For now we focus on the remaining. 
- DONE: DIV

These will mostly follow div, we will just have to close out some differences.
- TODO:  DIVU, DIVW, DIVUW
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

