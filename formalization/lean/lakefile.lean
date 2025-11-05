import Lake
open Lake DSL

package f0derivation where
  -- Project metadata
  version := v!"0.1.0"
  keywords := #["mathematics", "physics", "zeta-function", "golden-ratio"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib F0Derivation where
  -- Source files
  roots := #[`F0Derivation]
  globs := #[.submodules `F0Derivation]
