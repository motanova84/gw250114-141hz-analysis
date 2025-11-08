import Lake
open Lake DSL

package «f0derivation» where
  version := "1.0.0"
  keywords := #["number-theory", "zeta-function", "frequency"]
  description := "Formal derivation of f₀ = 141.7001 Hz from primes"

lean_lib «F0Derivation» where
  globs := #[.submodules `F0Derivation]
package «f0-formalization» where
package «f0derivation» where
  -- add package configuration options here

lean_lib «F0Derivation» where
  -- add library configuration options here

@[default_target]
lean_exe «f0derivation» where
  root := `Main
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
