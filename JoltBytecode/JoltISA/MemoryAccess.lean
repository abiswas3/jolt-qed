/-
Just like Register Acess which helps define Instruction semantics i.e how to step the JoltCPU. 
We need MemoryAccess unified. This file contains all the helpers needed to access memory and helper theorems,
and abbreviations. 
Memory is currently, all over the place.

Here's the lay of the land, and why this one is different from the register cleanups.

  What I found

  Memory genuinely is scattered, across three kinds of thing:

  1. Address vocabulary — JoltBytecode/Memory.lean (effectiveAddr12, dwordBase, compute_aligned_dword_base_address, …). Pure abbrevs. Imported by 3 files.
  2. Inlined access — execInstr's LD/SD (Semantics.lean:304/316) inline everything: address math, the addr &&& 7 = 0 alignment check, and raw liftSail 
  (vmem_read_addr …) / liftSail (vmem_write_addr …). There is no readMem/writeMem helper — no memory analogue of readSrc/writeDst exists anywhere (grep for
  memory-access defs is empty).
  3. Proof theory — InstructionEquivalence/Memory/* (Read/Write/Basic/Alignment/StoreExec/Windows, ~2900 lines), plus raw vmem_* reasoning spread across
  ~10 load/store/atomic proof files.

  What MemoryAccess.lean should — and shouldn't — be

  To be the true RegisterAccess analogue, it's the access-definition layer: the address abbreviations (#1) + new memRead/memWrite helpers wrapping the
  liftSail (vmem_*_addr …) pattern (#2), living in JoltISA root, used by execInstr.

  It should not absorb #3. The memory proof theory is the analogue of the RegisterOps/stateAfterWrite lemmas — equivalence-layer machinery that correctly
  lives in InstructionEquivalence/Memory/. (Same call we made for registers: access defs in root, proof lemmas stay put.)

  The catch that makes this bigger than the register work

  RegisterAccess already existed; here you'd be introducing the abstraction. The moment you define memReadDword/memWriteDword and rewire execInstr's LD/SD
  to use them, every proof that currently reasons about the inlined liftSail (vmem_read_addr …) — the LD/SD/store/atomic equivalence proofs across those
  ~10 files — now faces memReadDword instead, and needs an unfold lemma or rewrite. So the execInstr-rewire step has a real proof ripple; it's not
  mechanical.

  Recommended phasing (each bisectable, lake build-checked)

  - Phase 1 (safe, high value, no proof ripple): consolidate the address vocabulary — move JoltBytecode/Memory.lean's abbrevs into
  JoltISA/MemoryAccess.lean, repoint its 3 importers, delete Memory.lean. This makes MemoryAccess.lean real and kills the Memory.lean-vs-Memory/\-dir name
  collision in one shot. Pure relocation.
  - Phase 2 (deliberate, has ripple): define memReadDword/memWriteDword (wrapping vmem_*_addr + alignment), rewire execInstr LD/SD, and add the
  unfold/run-lemmas the load/store proofs need. This is the part that earns the "unified access" framing — but it touches the proofs and deserves its own
  focused pass.

  My suggestion: do Phase 1 now (clean, immediate payoff), and treat Phase 2 as the real design task to do together — since defining the right
  memRead/memWrite shape (dword-only? width-parametric? alignment baked in or separate?) is a decision worth making explicitly, like we did with
  writeSingleVReg_ex.

  Want me to do Phase 1 now, and then we design the Phase 2 helper interface together?

-/ 
