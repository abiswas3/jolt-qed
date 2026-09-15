import JoltBytecode.JoltISA.Semantics

/-!
# Foundational Jolt witness and execution-trace types

This file fixes the proof dimensions, exact proof-facing instruction/bytecode
rows, public RAM metadata, and the semantic execution trace used by the
constraint layer. Correct execution is defined exclusively by the existing
`JoltISA.execInstr`; the proof-facing row is data linked to that interpreter,
not a second instruction semantics.
-/

open Sail PreSail LeanRV64D.Functions

namespace JoltConstraints

universe u

/-- A vector of length T where coordinate has type α-/
abbrev Column (T : Nat) (α : Type u) : Type u :=
  Fin T → α

/-- Register width of the current Jolt ISA. -/
abbrev Xlen : Nat := 64

/-- Number of bits in Jolt's combined two-operand lookup address. -/
abbrev InstructionLookupAddressBits : Nat := 2 * Xlen

/-- Number of bits needed to index into Jolt Virtual Reg File -/
abbrev RegisterAddressBits : Nat := 7
abbrev RegisterAddressCount : Nat := 2 ^ RegisterAddressBits
abbrev RegisterAddress : Type := Fin RegisterAddressCount

/-- Rust switches from `(4, 16)` to `(8, 32)` one-hot chunks at this `logT`. 
TODO: Find rust source code evidence
-/
abbrev OneHotChunkThresholdLogT : Nat := 25

/--Parameters for the NP witnes
TODO: Find Rust code source
-/
structure JoltWitnessParams where
  logT : Nat
  ramK : Nat
  bytecodeK : Nat
  committedChunkBits : Nat
  lookupVirtualChunkBits : Nat
  includeTrustedAdvice : Bool
  includeUntrustedAdvice : Bool
  maxTrustedAdviceSize : Nat
  maxUntrustedAdviceSize : Nat
  deriving DecidableEq, Repr

/-- The three committed read-address chunk counts (`D`) in Rust's canonical
instruction, bytecode, RAM order.
TODO: <Link> to my blog writeup of this.
TODO: Also link Rust source
-/
structure JoltRaPolynomialLayout where
  instructionD : Nat
  bytecodeD : Nat
  ramD : Nat
  deriving DecidableEq, Repr

namespace JoltRaPolynomialLayout

/-- TODO: Find a better name eventually. Eegiot-/
def total (layout : JoltRaPolynomialLayout) : Nat :=
  layout.instructionD + layout.bytecodeD + layout.ramD

end JoltRaPolynomialLayout

/-- Rust's `RaChunkSelector`, with the range check on `index` represented by
the type.  Chunk zero is the most-significant chunk.
TODO: Not a scooby what is going on here.-/
structure JoltRaChunkSelector (chunks chunkBits : Nat) where
  index : Fin chunks

namespace JoltRaChunkSelector

/-- Number of low bits skipped before selecting this MSB-first chunk. -/
def shift {chunks chunkBits : Nat}
    (selector : JoltRaChunkSelector chunks chunkBits) : Nat :=
  (chunks - (selector.index.val + 1)) * chunkBits

/-- Rust's `(value >> shift) & (2^chunkBits - 1)`, expressed using natural
division and remainder. -/
def chunkNat {chunks chunkBits : Nat}
    (selector : JoltRaChunkSelector chunks chunkBits) (value : Nat) : Nat :=
  (value / 2 ^ selector.shift) % 2 ^ chunkBits

/-- The selected value, typed in the one-hot address domain. -/
def chunk {chunks chunkBits : Nat}
    (selector : JoltRaChunkSelector chunks chunkBits) (value : Nat) :
    Fin (2 ^ chunkBits) :=
  ⟨selector.chunkNat value, Nat.mod_lt _ (by positivity)⟩

end JoltRaChunkSelector

namespace JoltWitnessParams

/-- Unlike `Nat.nextPowerOfTwo`, this predicate excludes zero. -/
def IsPowerOfTwo (value : Nat) : Prop :=
  ∃ logValue : Nat, value = 2 ^ logValue

def traceLength (params : JoltWitnessParams) : Nat :=
  2 ^ params.logT

/-- `ProverConfig::derive` pads an unpadded Rust trace past its last real row,
with a production minimum of 256 cycles. -/
def paddedTraceLength (unpaddedLength : Nat) : Nat :=
  if unpaddedLength < 256 then
    256
  else
    Nat.nextPowerOfTwo (unpaddedLength + 1)

def ceilDiv (n d : Nat) : Nat :=
  (n + d - 1) / d

/--Show that n ≤ ⌈n/d⌉* d-/
theorem le_ceilDiv_mul (n d : Nat) (dPositive : 0 < d) :
    n ≤ ceilDiv n d * d := by
  let q := (n + d - 1) / d 
  let r := (n + d - 1) % d
  have h_div_fact : (n + d - 1) = q * d + r := by 
    simpa only [q, r] using (Nat.div_add_mod' (n + d - 1) d).symm
  have h_rem_smaller_than_divisor : r < d := by 
    simpa only [r] using Nat.mod_lt (n + d - 1) dPositive
  rw [← Nat.le_sub_one_iff_lt dPositive] at h_rem_smaller_than_divisor
  calc
      n = n + d - 1 - (d - 1) := by omega
      _ = q * d + r - (d - 1) := by rw [h_div_fact]
      _ ≤ q * d + r - r := by gcongr
      _ = q * d := by omega
      _ = ceilDiv n d * d := by rfl

def committedChunkSize (params : JoltWitnessParams) : Nat :=
  2 ^ params.committedChunkBits

def lookupVirtualChunkSize (params : JoltWitnessParams) : Nat :=
  2 ^ params.lookupVirtualChunkBits

def productionCommittedChunkBits (logT : Nat) : Nat :=
  if logT < OneHotChunkThresholdLogT then 4 else 8

def productionLookupVirtualChunkBits (logT : Nat) : Nat :=
  if logT < OneHotChunkThresholdLogT then 16 else 32

/-- Address-bit width of the padded public bytecode table. -/
def bytecodeAddressBits (params : JoltWitnessParams) : Nat :=
  Nat.clog 2 params.bytecodeK

/-- Address-bit width of the remapped RAM table. -/
def ramAddressBits (params : JoltWitnessParams) : Nat :=
  Nat.clog 2 params.ramK

/-- Rust's committed RA polynomial layout.  Committed chunks use ceiling
division because the most-significant chunk may be left-zero-padded. -/
def raPolynomialLayout (params : JoltWitnessParams) : JoltRaPolynomialLayout where
  instructionD := ceilDiv InstructionLookupAddressBits params.committedChunkBits
  bytecodeD := ceilDiv params.bytecodeAddressBits params.committedChunkBits
  ramD := ceilDiv params.ramAddressBits params.committedChunkBits

def instructionCommittedRaCount (params : JoltWitnessParams) : Nat :=
  params.raPolynomialLayout.instructionD

def bytecodeCommittedRaCount (params : JoltWitnessParams) : Nat :=
  params.raPolynomialLayout.bytecodeD

def ramCommittedRaCount (params : JoltWitnessParams) : Nat :=
  params.raPolynomialLayout.ramD

/-- Number of virtual instruction-RA polynomials.  Valid dimensions make this
an exact quotient whose chunks tile all 128 lookup-address bits. -/
def instructionVirtualRaCount (params : JoltWitnessParams) : Nat :=
  InstructionLookupAddressBits / params.lookupVirtualChunkBits

/-- Number of committed instruction-RA chunks represented by one virtual
instruction-RA chunk. -/
def instructionCommittedRaPerVirtual (params : JoltWitnessParams) : Nat :=
  params.lookupVirtualChunkBits / params.committedChunkBits

/-- Leading zero bits in a ceiling-divided committed address layout. -/
def committedAddressPadding (addressBits chunkBits : Nat) : Nat :=
  ceilDiv addressBits chunkBits * chunkBits - addressBits

def instructionCommittedAddressPadding (params : JoltWitnessParams) : Nat :=
  committedAddressPadding InstructionLookupAddressBits params.committedChunkBits

def bytecodeCommittedAddressPadding (params : JoltWitnessParams) : Nat :=
  committedAddressPadding params.bytecodeAddressBits params.committedChunkBits

def ramCommittedAddressPadding (params : JoltWitnessParams) : Nat :=
  committedAddressPadding params.ramAddressBits params.committedChunkBits

def adviceLength (maxSizeBytes : Nat) : Nat :=
  max 1 (Nat.nextPowerOfTwo (maxSizeBytes / 8))

def trustedAdviceLength (params : JoltWitnessParams) : Nat :=
  adviceLength params.maxTrustedAdviceSize

def untrustedAdviceLength (params : JoltWitnessParams) : Nat :=
  adviceLength params.maxUntrustedAdviceSize

/-- Number of words occupied by the trusted-advice region in Rust memory.
Unlike the commitment length, this is zero when the configured byte capacity
is zero. -/
def trustedAdviceWords (params : JoltWitnessParams) : Nat :=
  params.maxTrustedAdviceSize / 8

/-- Number of words occupied by the untrusted-advice region in Rust memory. -/
def untrustedAdviceWords (params : JoltWitnessParams) : Nat :=
  params.maxUntrustedAdviceSize / 8

def instructionCommittedSelector (params : JoltWitnessParams)
    (chunk : Fin params.instructionCommittedRaCount) :
    JoltRaChunkSelector params.instructionCommittedRaCount
      params.committedChunkBits :=
  ⟨chunk⟩

def bytecodeCommittedSelector (params : JoltWitnessParams)
    (chunk : Fin params.bytecodeCommittedRaCount) :
    JoltRaChunkSelector params.bytecodeCommittedRaCount
      params.committedChunkBits :=
  ⟨chunk⟩

def ramCommittedSelector (params : JoltWitnessParams)
    (chunk : Fin params.ramCommittedRaCount) :
    JoltRaChunkSelector params.ramCommittedRaCount params.committedChunkBits :=
  ⟨chunk⟩

def instructionVirtualSelector (params : JoltWitnessParams)
    (chunk : Fin params.instructionVirtualRaCount) :
    JoltRaChunkSelector params.instructionVirtualRaCount
      params.lookupVirtualChunkBits :=
  ⟨chunk⟩

/-- Rust groups the committed instruction-RA chunks contiguously underneath
each virtual instruction-RA chunk. -/
def instructionCommittedChunkIndex (params : JoltWitnessParams)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) : Nat :=
  virtualChunk.val * params.instructionCommittedRaPerVirtual + localChunk.val

/-- Checked form of Rust's contiguous committed-chunk index. Arbitrary raw
parameters may be invalid, so the foundational map is total via `Option`;
`JoltWitnessParams.Valid` proves that production dimensions always succeed. -/
def instructionCommittedChunk? (params : JoltWitnessParams)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    Option (Fin params.instructionCommittedRaCount) :=
  let index := params.instructionCommittedChunkIndex virtualChunk localChunk
  if inBounds : index < params.instructionCommittedRaCount then
    some ⟨index, inBounds⟩
  else
    none

/-- Selector for one committed subchunk inside a virtual instruction chunk. -/
def instructionCommittedLocalSelector (params : JoltWitnessParams)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    JoltRaChunkSelector params.instructionCommittedRaPerVirtual
      params.committedChunkBits :=
  ⟨localChunk⟩

/-- Rust-valid proof dimensions and advice capacities.

This is the proposition-level counterpart of the checks performed by
`JoltFormulaDimensions::try_from`, `BytecodePreprocessing::preprocess`,
`ProverConfig::derive`, and `MemoryLayout::new`.  Raw parameters remain data so
arbitrary witness arrays can still be discussed; an honest Rust-aligned trace
will carry a proof of this predicate. -/
structure Valid (params : JoltWitnessParams) : Prop where
  /-- Production Rust traces are padded to at least `2^8 = 256` cycles. -/
  logTAtLeastEight : 8 ≤ params.logT
  /-- `checked_pow2` rejects a shift by `usize::BITS`; the supported Rust
  prover targets are 64-bit. -/
  logTLessThanRustUsizeBits : params.logT < 64
  /-- Rust inserts a no-op bytecode row and pads the table to a power of two. -/
  bytecodeKAtLeastTwo : 2 ≤ params.bytecodeK
  bytecodeKPowerOfTwo : IsPowerOfTwo params.bytecodeK
  /-- Proof-facing rows store the bytecode index in a `u32`. -/
  bytecodeKFitsU32 : params.bytecodeK ≤ 2 ^ 32
  /-- Production `MemoryLayout` always reserves the panic and termination
  words. Rust's generic formula dimensions accept `ram_k = 1`, but the
  prover/verifier-derived RAM domain therefore starts at two words. -/
  ramKAtLeastTwo : 2 ≤ params.ramK
  ramKPowerOfTwo : IsPowerOfTwo params.ramK
  committedChunkBitsPositive : 0 < params.committedChunkBits
  lookupVirtualChunkBitsPositive : 0 < params.lookupVirtualChunkBits
  /-- This check is explicit in `JoltFormulaDimensions::try_from`. -/
  committedChunkBitsLeLookupVirtualChunkBits :
    params.committedChunkBits ≤ params.lookupVirtualChunkBits
  /-- A virtual lookup chunk is made from whole committed chunks. -/
  committedChunkBitsDvdLookupVirtualChunkBits :
    params.committedChunkBits ∣ params.lookupVirtualChunkBits
  /-- Virtual chunks tile the complete `2 * XLEN` instruction address. -/
  lookupVirtualChunkBitsDvdInstructionAddress :
    params.lookupVirtualChunkBits ∣ InstructionLookupAddressBits
  /-- `ProverConfig::derive` has exactly these two production policies. -/
  productionChunkPolicy :
    params.committedChunkBits = productionCommittedChunkBits params.logT ∧
      params.lookupVirtualChunkBits =
        productionLookupVirtualChunkBits params.logT
  /-- `MemoryLayout::new` stores already-aligned advice capacities. -/
  trustedAdviceSizeAligned : params.maxTrustedAdviceSize % 8 = 0
  untrustedAdviceSizeAligned : params.maxUntrustedAdviceSize % 8 = 0
  trustedAdviceSizePowerOfTwoOrZero :
    params.maxTrustedAdviceSize = 0 ∨
      IsPowerOfTwo params.maxTrustedAdviceSize
  untrustedAdviceSizePowerOfTwoOrZero :
    params.maxUntrustedAdviceSize = 0 ∨
      IsPowerOfTwo params.maxUntrustedAdviceSize
  /-- A present advice commitment must have a nonempty configured region. -/
  trustedAdvicePresentOnlyIfNonempty :
    params.includeTrustedAdvice = true → 0 < params.maxTrustedAdviceSize
  untrustedAdvicePresentOnlyIfNonempty :
    params.includeUntrustedAdvice = true → 0 < params.maxUntrustedAdviceSize

theorem Valid.instructionVirtualChunksTile
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.instructionVirtualRaCount * params.lookupVirtualChunkBits =
      InstructionLookupAddressBits := by
  exact Nat.div_mul_cancel valid.lookupVirtualChunkBitsDvdInstructionAddress

theorem Valid.ramKPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.ramK :=
  lt_of_lt_of_le (by omega) valid.ramKAtLeastTwo

theorem Valid.ramAddressBitsPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.ramAddressBits := by
  exact Nat.clog_pos (by omega) valid.ramKAtLeastTwo

theorem Valid.ramK_eq_two_pow_addressBits
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.ramK = 2 ^ params.ramAddressBits := by
  rcases valid.ramKPowerOfTwo with ⟨logRamK, ramK_eq⟩
  simp [ramAddressBits, ramK_eq, Nat.clog_pow, show 1 < 2 by omega]

theorem Valid.ramAddressBits_le_committedChunks
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.ramAddressBits ≤
      params.ramCommittedRaCount * params.committedChunkBits := by
  exact le_ceilDiv_mul params.ramAddressBits params.committedChunkBits
    valid.committedChunkBitsPositive

theorem Valid.ramCommittedRaCountPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.ramCommittedRaCount := by
  unfold ramCommittedRaCount raPolynomialLayout ceilDiv
  apply Nat.div_pos
  · have addressBitsPositive := valid.ramAddressBitsPositive
    omega
  · exact valid.committedChunkBitsPositive

theorem Valid.bytecodeKPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.bytecodeK :=
  lt_of_lt_of_le (by omega) valid.bytecodeKAtLeastTwo

theorem Valid.bytecodeAddressBitsPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.bytecodeAddressBits := by
  exact Nat.clog_pos (by omega) valid.bytecodeKAtLeastTwo

theorem Valid.bytecodeK_eq_two_pow_addressBits
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.bytecodeK = 2 ^ params.bytecodeAddressBits := by
  rcases valid.bytecodeKPowerOfTwo with ⟨logBytecodeK, bytecodeK_eq⟩
  simp [bytecodeAddressBits, bytecodeK_eq, Nat.clog_pow,
    show 1 < 2 by omega]

theorem Valid.bytecodeAddressBits_le_committedChunks
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.bytecodeAddressBits ≤
      params.bytecodeCommittedRaCount * params.committedChunkBits := by
  exact le_ceilDiv_mul params.bytecodeAddressBits params.committedChunkBits
    valid.committedChunkBitsPositive

theorem Valid.bytecodeCommittedRaCountPositive
    {params : JoltWitnessParams} (valid : params.Valid) :
    0 < params.bytecodeCommittedRaCount := by
  unfold bytecodeCommittedRaCount raPolynomialLayout ceilDiv
  apply Nat.div_pos
  · have addressBitsPositive := valid.bytecodeAddressBitsPositive
    omega
  · exact valid.committedChunkBitsPositive

theorem Valid.committedChunksTileVirtualChunk
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.instructionCommittedRaPerVirtual * params.committedChunkBits =
      params.lookupVirtualChunkBits := by
  exact Nat.div_mul_cancel valid.committedChunkBitsDvdLookupVirtualChunkBits

/-- The production chunk policy makes the committed instruction chunks an
exact contiguous partition of the virtual instruction chunks. -/
theorem Valid.instructionCommittedRaCount_eq
    {params : JoltWitnessParams} (valid : params.Valid) :
    params.instructionCommittedRaCount =
      params.instructionVirtualRaCount *
        params.instructionCommittedRaPerVirtual := by
  simp only [instructionCommittedRaCount, instructionVirtualRaCount,
    instructionCommittedRaPerVirtual, raPolynomialLayout]
  rw [valid.productionChunkPolicy.1, valid.productionChunkPolicy.2]
  by_cases small : params.logT < OneHotChunkThresholdLogT
  · norm_num [ceilDiv, productionCommittedChunkBits,
      productionLookupVirtualChunkBits, small, InstructionLookupAddressBits,
      Xlen]
  · norm_num [ceilDiv, productionCommittedChunkBits,
      productionLookupVirtualChunkBits, small, InstructionLookupAddressBits,
      Xlen]

/-- Proof-indexed form of `instructionCommittedChunk?`, useful after the
production dimension checks have been established. -/
def Valid.instructionCommittedChunk
    {params : JoltWitnessParams} (valid : params.Valid)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    Fin params.instructionCommittedRaCount :=
  ⟨params.instructionCommittedChunkIndex virtualChunk localChunk, by
    rw [valid.instructionCommittedRaCount_eq]
    calc
      virtualChunk.val * params.instructionCommittedRaPerVirtual +
            localChunk.val <
          virtualChunk.val * params.instructionCommittedRaPerVirtual +
            params.instructionCommittedRaPerVirtual :=
        Nat.add_lt_add_left localChunk.isLt _
      _ = (virtualChunk.val + 1) *
            params.instructionCommittedRaPerVirtual := by
        simp [Nat.add_mul]
      _ ≤ params.instructionVirtualRaCount *
            params.instructionCommittedRaPerVirtual :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr virtualChunk.isLt)⟩

theorem Valid.instructionCommittedChunk?_eq_some
    {params : JoltWitnessParams} (valid : params.Valid)
    (virtualChunk : Fin params.instructionVirtualRaCount)
    (localChunk : Fin params.instructionCommittedRaPerVirtual) :
    params.instructionCommittedChunk? virtualChunk localChunk =
      some (valid.instructionCommittedChunk virtualChunk localChunk) := by
  have inBounds :=
    (valid.instructionCommittedChunk virtualChunk localChunk).isLt
  change params.instructionCommittedChunkIndex virtualChunk localChunk <
    params.instructionCommittedRaCount at inBounds
  unfold instructionCommittedChunk?
  rw [dif_pos inBounds]
  congr

end JoltWitnessParams

structure JoltTraceRowMetadata where
  pc : Nat
  unexpandedPC : BitVec Xlen
  virtualSequenceRemaining : Option Nat
  isFirstInSequence : Bool
  isCompressed : Bool

/-- Stable identity of every final instruction in Rust's base Jolt profile.
Unlike `JoltISA.Instr`, this deliberately contains no execution-time values.
TODO: This should not be there. It should use the ISA.
-/
inductive JoltInstructionKind where
  | NoOp
  | ADDI | ANDI | ORI | XORI | SLTI | SLTIU | LUI | AUIPC | JAL | JALR
  | BEQ | BNE | BLT | BGE | BLTU | BGEU | FENCE
  | ADD | SUB | MUL | MULHU | ANDN | VirtualMULI
  | VirtualPow2 | VirtualPow2W | VirtualPow2I | VirtualPow2IW
  | VirtualShiftRightBitmask | VirtualShiftRightBitmaskI
  | VirtualSRLI | VirtualSRAI | VirtualSRL | VirtualSRA
  | VirtualROTRI | VirtualROTRIW | VirtualRev8W
  | VirtualXORROT32 | VirtualXORROT24 | VirtualXORROT16 | VirtualXORROT63
  | VirtualXORROTW16 | VirtualXORROTW12 | VirtualXORROTW8 | VirtualXORROTW7
  | OR | XOR | AND | SLT | SLTU
  | VirtualSignExtendWord | VirtualZeroExtendWord | VirtualMovsign
  | VirtualAssertHalfwordAlignment | VirtualAssertWordAlignment
  | LD | SD
  | VirtualAdvice | VirtualAdviceLoad | VirtualAdviceLen | VirtualHostIO
  | VirtualAssertEQ | VirtualAssertValidDiv0
  | VirtualChangeDivisor | VirtualChangeDivisorW
  | VirtualAssertValidUnsignedRemainder | VirtualAssertMulUNoOverflow
  | VirtualAssertLTE
  deriving DecidableEq, Repr

namespace JoltInstructionKind

/-- Erase execution operands while retaining Rust's final instruction kind.
This exhaustive match is the central compile-time guard against ISA drift. -/
def ofInstr : JoltISA.Instr → JoltInstructionKind
  | .NoOp => .NoOp
  | .ADDI .. => .ADDI
  | .ANDI .. => .ANDI
  | .ORI .. => .ORI
  | .XORI .. => .XORI
  | .SLTI .. => .SLTI
  | .SLTIU .. => .SLTIU
  | .LUI .. => .LUI
  | .AUIPC .. => .AUIPC
  | .JAL .. => .JAL
  | .JALR .. => .JALR
  | .BEQ .. => .BEQ
  | .BNE .. => .BNE
  | .BLT .. => .BLT
  | .BGE .. => .BGE
  | .BLTU .. => .BLTU
  | .BGEU .. => .BGEU
  | .FENCE => .FENCE
  | .ADD .. => .ADD
  | .SUB .. => .SUB
  | .MUL .. => .MUL
  | .MULHU .. => .MULHU
  | .ANDN .. => .ANDN
  | .VirtualMULI .. => .VirtualMULI
  | .VirtualPow2 .. => .VirtualPow2
  | .VirtualPow2W .. => .VirtualPow2W
  | .VirtualPow2I .. => .VirtualPow2I
  | .VirtualPow2IW .. => .VirtualPow2IW
  | .VirtualShiftRightBitmask .. => .VirtualShiftRightBitmask
  | .VirtualShiftRightBitmaskI .. => .VirtualShiftRightBitmaskI
  | .VirtualSRLI .. => .VirtualSRLI
  | .VirtualSRAI .. => .VirtualSRAI
  | .VirtualSRL .. => .VirtualSRL
  | .VirtualSRA .. => .VirtualSRA
  | .VirtualROTRI .. => .VirtualROTRI
  | .VirtualROTRIW .. => .VirtualROTRIW
  | .VirtualRev8W .. => .VirtualRev8W
  | .VirtualXORROT32 .. => .VirtualXORROT32
  | .VirtualXORROT24 .. => .VirtualXORROT24
  | .VirtualXORROT16 .. => .VirtualXORROT16
  | .VirtualXORROT63 .. => .VirtualXORROT63
  | .VirtualXORROTW16 .. => .VirtualXORROTW16
  | .VirtualXORROTW12 .. => .VirtualXORROTW12
  | .VirtualXORROTW8 .. => .VirtualXORROTW8
  | .VirtualXORROTW7 .. => .VirtualXORROTW7
  | .OR .. => .OR
  | .XOR .. => .XOR
  | .AND .. => .AND
  | .SLT .. => .SLT
  | .SLTU .. => .SLTU
  | .VirtualSignExtendWord .. => .VirtualSignExtendWord
  | .VirtualZeroExtendWord .. => .VirtualZeroExtendWord
  | .VirtualMovsign .. => .VirtualMovsign
  | .VirtualAssertHalfwordAlignment .. => .VirtualAssertHalfwordAlignment
  | .VirtualAssertWordAlignment .. => .VirtualAssertWordAlignment
  | .LD .. => .LD
  | .SD .. => .SD
  | .VirtualAdvice .. => .VirtualAdvice
  | .VirtualAdviceLoad .. => .VirtualAdviceLoad
  | .VirtualAdviceLen .. => .VirtualAdviceLen
  | .VirtualHostIO => .VirtualHostIO
  | .VirtualAssertEQ .. => .VirtualAssertEQ
  | .VirtualAssertValidDiv0 .. => .VirtualAssertValidDiv0
  | .VirtualChangeDivisor .. => .VirtualChangeDivisor
  | .VirtualChangeDivisorW .. => .VirtualChangeDivisorW
  | .VirtualAssertValidUnsignedRemainder .. =>
      .VirtualAssertValidUnsignedRemainder
  | .VirtualAssertMulUNoOverflow .. => .VirtualAssertMulUNoOverflow
  | .VirtualAssertLTE .. => .VirtualAssertLTE

end JoltInstructionKind

/-- Rust's normalized proof-facing operands.  Register IDs are typed directly
in the 128-address read/write domain; `imm` is the exact normalized `i128`
value, which is intentionally distinct from an execution-time advice value. -/
structure JoltInstructionOperands where
  rs1 : Option RegisterAddress
  rs2 : Option RegisterAddress
  rd : Option RegisterAddress
  imm : Int
  deriving DecidableEq, Repr

namespace JoltInstructionOperands

/-- Storage condition enforced by `JoltTraceRow::from_components`: the signed
magnitude of an `i128` immediate must fit in its packed `u64` slot.  Register
IDs need no separate predicate because `RegisterAddress = Fin 128`. -/
def Packable (operands : JoltInstructionOperands) : Prop :=
  operands.imm.natAbs < 2 ^ Xlen

end JoltInstructionOperands

/-- Static identity-and-operands component of Rust's `JoltInstructionRow`.
Lean keeps its address and virtual-sequence metadata in `JoltBytecodeRow` so
the same fields remain available through the pre-existing row accessors. -/
structure JoltInstructionRow where
  kind : JoltInstructionKind
  operands : JoltInstructionOperands
  deriving DecidableEq, Repr

namespace JoltInstructionRow

def noOp : JoltInstructionRow where
  kind := .NoOp
  operands := { rs1 := none, rs2 := none, rd := none, imm := 0 }

end JoltInstructionRow

/-- One row of Rust's padded, fixed/public `BytecodePreprocessing.bytecode`
table.  The compact bytecode index is the array address and is therefore not
duplicated inside the row. -/
structure JoltBytecodeRow where
  instruction : JoltInstructionRow
  unexpandedPC : BitVec Xlen
  virtualSequenceRemaining : Option Nat
  isFirstInSequence : Bool
  isCompressed : Bool
  deriving Repr

namespace JoltBytecodeRow

/-- Rust inserts this row at bytecode index zero and uses it for padding. -/
def noOp : JoltBytecodeRow where
  instruction := JoltInstructionRow.noOp
  unexpandedPC := 0
  virtualSequenceRemaining := none
  isFirstInSequence := false
  isCompressed := false

/-- Conditions needed to materialize this logical bytecode entry in Rust's
compact proof-facing row. -/
def Packable (row : JoltBytecodeRow) : Prop :=
  row.instruction.operands.Packable ∧
    ∀ remaining,
      row.virtualSequenceRemaining = some remaining → remaining < 2 ^ 16

end JoltBytecodeRow

/-- The three mutually exclusive row classes used by Rust's proof-facing
`JoltTraceRow`. -/
inductive JoltTraceRowClass where
  | nonMemory
  | load
  | store
  deriving DecidableEq, Repr

/-- Classify a final Jolt instruction exactly as Rust classifies its captured
state before constructing a proof-facing trace row. -/
def JoltTraceRowClass.ofInstr : JoltISA.Instr → JoltTraceRowClass
  | instruction =>
      match JoltInstructionKind.ofInstr instruction with
      | .LD => .load
      | .SD => .store
      | _ => .nonMemory

attribute [simp] JoltInstructionKind.ofInstr JoltTraceRowClass.ofInstr

/-- Independent witness values stored for a non-memory row. -/
structure NonMemoryState where
  rs1Value : BitVec Xlen
  rs2Value : BitVec Xlen
  rdPreValue : BitVec Xlen
  rdWriteValue : BitVec Xlen
  deriving Repr

/-- Independent witness values stored for a load row.  As in Rust,
`rdWriteValue` is also the logical RAM read and RAM write value. -/
structure LoadState where
  rs1Value : BitVec Xlen
  ramAddress : BitVec Xlen
  rdPreValue : BitVec Xlen
  rdWriteValue : BitVec Xlen
  deriving Repr

/-- Independent witness values stored for a store row.  As in Rust,
`rs2Value` is also the logical RAM write value. -/
structure StoreState where
  rs1Value : BitVec Xlen
  rs2Value : BitVec Xlen
  ramReadValue : BitVec Xlen
  ramAddress : BitVec Xlen
  deriving Repr

/-- Rust's `CapturedState`, indexed in Lean by the final row class.  The index
is the type-level counterpart of Rust's checked `from_components` constructor:
a load instruction cannot be paired with non-memory or store values. -/
inductive CapturedState : JoltTraceRowClass → Type where
  | nonMemory (state : NonMemoryState) : CapturedState .nonMemory
  | load (state : LoadState) : CapturedState .load
  | store (state : StoreState) : CapturedState .store

/-- The logical proof-facing trace row.  Rust packs this information into 64
bytes; Lean keeps the semantic components explicit. -/
structure JoltTraceRow where
  instruction : JoltISA.Instr
  /-- Exact proof-facing identity and normalized operands carried by Rust. -/
  instructionRow : JoltInstructionRow
  metadata : JoltTraceRowMetadata
  capturedState : CapturedState (JoltTraceRowClass.ofInstr instruction)

namespace CapturedState

def rs1Value {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rs1Value
  | .load state => state.rs1Value
  | .store state => state.rs1Value

def rs2Value {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rs2Value
  | .load _ => 0
  | .store state => state.rs2Value

def rdPreValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rdPreValue
  | .load state => state.rdPreValue
  | .store _ => 0

def rdWriteValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory state => state.rdWriteValue
  | .load state => state.rdWriteValue
  | .store _ => 0

def ramAddress {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.ramAddress
  | .store state => state.ramAddress

def ramReadValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.rdWriteValue
  | .store state => state.ramReadValue

def ramWriteValue {kind : JoltTraceRowClass} : CapturedState kind → BitVec Xlen
  | .nonMemory _ => 0
  | .load state => state.rdWriteValue
  | .store state => state.rs2Value

end CapturedState

namespace JoltTraceRow

/-- Forget dynamic captured values and the bytecode index itself, retaining
the fixed/public bytecode row selected by that index. -/
def bytecodeRow (row : JoltTraceRow) : JoltBytecodeRow where
  instruction := row.instructionRow
  unexpandedPC := row.metadata.unexpandedPC
  virtualSequenceRemaining := row.metadata.virtualSequenceRemaining
  isFirstInSequence := row.metadata.isFirstInSequence
  isCompressed := row.metadata.isCompressed

def rs1Value (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rs1Value

def rs2Value (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rs2Value

def rdPreValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rdPreValue

def rdWriteValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.rdWriteValue

def ramAddress (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramAddress

def ramReadValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramReadValue

def ramWriteValue (row : JoltTraceRow) : BitVec Xlen :=
  row.capturedState.ramWriteValue

end JoltTraceRow

/-! Public values used by constraints but not committed as witness columns. -/

/-- A contiguous word region inside the remapped RAM domain.

Rust's `MemoryLayout` stores byte addresses.  Stage-4 RAM relations use the
corresponding word indices relative to `get_lowest_address`; this bounded form
makes it impossible for an advice contribution to extend past `ramK`. -/
structure JoltRamRegion (ramK length : Nat) where
  start : Nat
  endLe : start + length ≤ ramK

namespace JoltRamRegion

/-- The RAM address at one in-region offset. -/
def address {ramK length : Nat}
    (region : JoltRamRegion ramK length) (offset : Fin length) : Fin ramK :=
  ⟨region.start + offset.val,
    lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt region.start) region.endLe⟩

/-- Recover the region-relative word index of a RAM address, when present. -/
def index? {ramK length : Nat}
    (region : JoltRamRegion ramK length) (address : Fin ramK) : Option (Fin length) :=
  if lower : region.start ≤ address.val then
    if upper : address.val < region.start + length then
      some ⟨address.val - region.start, by omega⟩
    else
      none
  else
    none

/-- Two bounded word regions do not overlap. -/
def Disjoint {ramK leftLength rightLength : Nat}
    (left : JoltRamRegion ramK leftLength)
    (right : JoltRamRegion ramK rightLength) : Prop :=
  left.start + leftLength ≤ right.start ∨
    right.start + rightLength ≤ left.start

end JoltRamRegion

/-- Verifier-known data used by witness constraints.

`publicInitialRam` is the dense semantic form of Rust's `PublicInitialRam`: in
the current fixed-program scope it contains the program image and public input
words, but deliberately excludes trusted and untrusted advice.  The two advice
regions locate the separately committed advice columns in the same remapped
RAM domain. -/
structure JoltPublicInputs (params : JoltWitnessParams) where
  lowestMemoryAddress : BitVec Xlen
  /-- The padded fixed/public bytecode table. -/
  bytecode : Column params.bytecodeK JoltBytecodeRow
  /-- Number of rows after inserting index-zero no-op and before padding. -/
  bytecodeActiveLength : Nat
  /-- Compact bytecode index of the ELF entry instruction. -/
  entryBytecodeIndex : Fin params.bytecodeK
  publicInitialRam : Column params.ramK (BitVec Xlen)
  trustedAdviceRegion :
    JoltRamRegion params.ramK params.trustedAdviceWords
  untrustedAdviceRegion :
    JoltRamRegion params.ramK params.untrustedAdviceWords
  ramOutputMask : Column params.ramK Bool
  ramOutputValue : Column params.ramK (BitVec Xlen)

namespace JoltPublicInputs

/-- Native memory-layout facts checked before Rust constructs the witness. -/
structure Valid {params : JoltWitnessParams}
    (publicInputs : JoltPublicInputs params) : Prop where
  bytecodeActiveLengthPositive : 0 < publicInputs.bytecodeActiveLength
  /-- Exact `BytecodePreprocessing::preprocess` padding policy. -/
  bytecodeK_eq :
    params.bytecodeK =
      max 2 (Nat.nextPowerOfTwo publicInputs.bytecodeActiveLength)
  bytecodeActiveLengthBound :
    publicInputs.bytecodeActiveLength ≤ params.bytecodeK
  entryBytecodeIndexActive :
    publicInputs.entryBytecodeIndex.val < publicInputs.bytecodeActiveLength
  /-- `BytecodePreprocessing::preprocess` reserves index zero for no-op. -/
  bytecodeZeroIsNoOp : ∀ index : Fin params.bytecodeK,
    index.val = 0 → publicInputs.bytecode index = JoltBytecodeRow.noOp
  /-- `BytecodePreprocessing::preprocess` pads unused table rows with no-op. -/
  bytecodePaddingIsNoOp : ∀ index : Fin params.bytecodeK,
    publicInputs.bytecodeActiveLength ≤ index.val →
      publicInputs.bytecode index = JoltBytecodeRow.noOp
  bytecodeRowsPackable : ∀ index : Fin params.bytecodeK,
    (publicInputs.bytecode index).Packable
  lowestMemoryAddressAligned :
    publicInputs.lowestMemoryAddress.toNat % 8 = 0
  /-- Every remapped word address fits in one RV64 address. -/
  ramAddressSpaceBound :
    publicInputs.lowestMemoryAddress.toNat + 8 * params.ramK ≤ 2 ^ Xlen
  /-- `MemoryLayout::new` places the larger advice block first and defines the
  remapping origin as the lower of the two starts. -/
  adviceRegionPlacement :
    if params.trustedAdviceWords ≥ params.untrustedAdviceWords then
      publicInputs.trustedAdviceRegion.start = 0 ∧
        publicInputs.untrustedAdviceRegion.start = params.trustedAdviceWords
    else
      publicInputs.untrustedAdviceRegion.start = 0 ∧
        publicInputs.trustedAdviceRegion.start = params.untrustedAdviceWords
  adviceRegionsDisjoint :
    JoltRamRegion.Disjoint publicInputs.trustedAdviceRegion
      publicInputs.untrustedAdviceRegion
  /-- `PublicInitialRam` omits committed advice contributions. -/
  publicInitialRamZeroOnTrustedAdvice :
    ∀ offset : Fin params.trustedAdviceWords,
      publicInputs.publicInitialRam
        (publicInputs.trustedAdviceRegion.address offset) = 0
  publicInitialRamZeroOnUntrustedAdvice :
    ∀ offset : Fin params.untrustedAdviceWords,
      publicInputs.publicInitialRam
        (publicInputs.untrustedAdviceRegion.address offset) = 0

end JoltPublicInputs

structure JoltTraceMetadata (params : JoltWitnessParams)
    extends JoltPublicInputs params where
  trustedAdvice : Column params.trustedAdviceLength (BitVec Xlen)
  untrustedAdvice : Column params.untrustedAdviceLength (BitVec Xlen)

namespace JoltTraceMetadata

/-- Read the padded trusted-advice commitment by a natural word index. -/
def trustedAdviceWord
    {params : JoltWitnessParams} (metadata : JoltTraceMetadata params)
    (index : Nat) : BitVec Xlen :=
  if inBounds : index < params.trustedAdviceLength then
    metadata.trustedAdvice ⟨index, inBounds⟩
  else
    0

/-- Read the padded untrusted-advice commitment by a natural word index. -/
def untrustedAdviceWord
    {params : JoltWitnessParams} (metadata : JoltTraceMetadata params)
    (index : Nat) : BitVec Xlen :=
  if inBounds : index < params.untrustedAdviceLength then
    metadata.untrustedAdvice ⟨index, inBounds⟩
  else
    0

/-- The trusted-advice word occupying `address`, if that committed stream is
present and the address lies in its Rust memory-layout region. -/
def trustedAdviceAt?
    {params : JoltWitnessParams} (metadata : JoltTraceMetadata params)
    (address : Fin params.ramK) : Option (BitVec Xlen) :=
  if params.includeTrustedAdvice then
    (metadata.trustedAdviceRegion.index? address).map
      (fun index => metadata.trustedAdviceWord index.val)
  else
    none

/-- The untrusted-advice analogue of `trustedAdviceAt?`. -/
def untrustedAdviceAt?
    {params : JoltWitnessParams} (metadata : JoltTraceMetadata params)
    (address : Fin params.ramK) : Option (BitVec Xlen) :=
  if params.includeUntrustedAdvice then
    (metadata.untrustedAdviceRegion.index? address).map
      (fun index => metadata.untrustedAdviceWord index.val)
  else
    none

/-- Rust's full initial RAM word in fixed/public-program mode: public program
and input memory, overlaid by the separately committed advice blocks.  Valid
Rust layouts make all three regions disjoint. -/
def initialRamValue
    {params : JoltWitnessParams} (metadata : JoltTraceMetadata params)
    (address : Fin params.ramK) : BitVec Xlen :=
  match metadata.untrustedAdviceAt? address with
  | some value => value
  | none =>
      match metadata.trustedAdviceAt? address with
      | some value => value
      | none => metadata.publicInitialRam address

/-- Rust-valid metadata.  Advice arrays remain total padded columns, while an
absent commitment denotes an empty byte stream and therefore must be zero. -/
structure Valid {params : JoltWitnessParams}
    (metadata : JoltTraceMetadata params) : Prop where
  paramsValid : params.Valid
  publicInputsValid : metadata.toJoltPublicInputs.Valid
  trustedAdviceRegionCovered :
    params.trustedAdviceWords ≤ params.trustedAdviceLength
  untrustedAdviceRegionCovered :
    params.untrustedAdviceWords ≤ params.untrustedAdviceLength
  trustedAdviceZeroPastCapacity : ∀ index : Fin params.trustedAdviceLength,
    params.trustedAdviceWords ≤ index.val → metadata.trustedAdvice index = 0
  untrustedAdviceZeroPastCapacity : ∀ index : Fin params.untrustedAdviceLength,
    params.untrustedAdviceWords ≤ index.val → metadata.untrustedAdvice index = 0
  trustedAdviceZeroIfAbsent :
    params.includeTrustedAdvice = false →
      ∀ index, metadata.trustedAdvice index = 0
  untrustedAdviceZeroIfAbsent :
    params.includeUntrustedAdvice = false →
      ∀ index, metadata.untrustedAdvice index = 0

end JoltTraceMetadata

/-- Index of the machine state immediately before row `i`. -/
def currentStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i, Nat.lt_trans i.isLt (Nat.lt_succ_self T)⟩

/-- Index of the machine state immediately after row `i`. -/
def nextStateIndex {T : Nat} (i : Fin T) : Fin (T + 1) :=
  ⟨i + 1, Nat.succ_lt_succ i.isLt⟩

structure ExecutionTrace (params : JoltWitnessParams) where
  rows : Column params.traceLength JoltTraceRow
  state : Column (params.traceLength + 1) SailJoltState
  executes : ∀ i : Fin params.traceLength,
    (JoltISA.execInstr (rows i).instruction).run (state (currentStateIndex i)) =
      .ok RETIRE_SUCCESS (state (nextStateIndex i))
  metadata : JoltTraceMetadata params

/-- The final instruction column, derived from the proof-facing rows. -/
def ExecutionTrace.instrList {params : JoltWitnessParams}
    (trace : ExecutionTrace params) : Column params.traceLength JoltISA.Instr :=
  fun i => (trace.rows i).instruction

/-- Per-row instruction metadata, derived from the proof-facing rows. -/
def ExecutionTrace.rowMetadata {params : JoltWitnessParams}
    (trace : ExecutionTrace params) : Column params.traceLength JoltTraceRowMetadata :=
  fun i => (trace.rows i).metadata


/-- State immediately before execution row `i`. -/
def ExecutionTrace.preState {params : JoltWitnessParams}
    (trace : ExecutionTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (currentStateIndex i)

/-- State immediately after execution row `i`. -/
def ExecutionTrace.postState {params : JoltWitnessParams}
    (trace : ExecutionTrace params) (i : Fin params.traceLength) : SailJoltState :=
  trace.state (nextStateIndex i)

end JoltConstraints
