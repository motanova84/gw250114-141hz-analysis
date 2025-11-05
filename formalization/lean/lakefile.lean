import Lake
open Lake DSL

package «f0-formalization» where
package «f0derivation» where
  -- add package configuration options here

lean_lib «F0Derivation» where
  -- add library configuration options here

@[default_target]
lean_exe «f0derivation» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
