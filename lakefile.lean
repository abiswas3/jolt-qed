import Lake
open Lake DSL

package «JoltBytecode» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "5e050d47562fa4938a5f9afbc006c7f02f4544aa"

@[default_target]
lean_lib «JoltBytecode» where
  srcDir := "."
