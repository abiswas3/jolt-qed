import JoltBytecode.JoltISA.SystemCSR
import JoltBytecode.InstructionEquivalence.ProofSupport.VirtualRegisters

/-!
# Shim laws for the System CSR whitelist

`@[simp]` rfl-projection lemmas for the `SystemCSR` whitelist defined in
`JoltBytecode/JoltISA/SystemCSR.lean`.  These characterise the layout against
the underlying virtual-register projectors and live with the rest of the
proof-side machinery.
-/

namespace JoltISA
namespace SystemCSR

@[simp] theorem vreg_sailTarget? (csr : SystemCSR) :
    joltRegisterSailTarget? (vreg csr) = some (sailRegister csr) := by
  cases csr <;> rfl

@[simp] theorem vreg_csrAddress? (csr : SystemCSR) :
    joltRegisterCsrAddress? (vreg csr) = some (address csr) := by
  cases csr <;> rfl

end SystemCSR
end JoltISA
