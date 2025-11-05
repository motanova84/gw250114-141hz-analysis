import Lake
open Lake DSL

package «f0-formalization» where
  -- add package configuration options here

lean_lib «F0Derivation» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
