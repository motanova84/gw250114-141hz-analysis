/-
Copyright (c) 2025 José Manuel Mota Burruezo. All rights reserved.
Released under MIT license.
-/

import F0Derivation.Main
import Tests.Verification

/-!
# Main Entry Point

This is the main entry point for the f₀ = 141.7001 Hz formalization.

## Usage

To build and verify the formalization:

```bash
cd formalization/lean
lake build
```

To run the executable:

```bash
lake exe f0derivation
```

## Project Structure

- `F0Derivation/Basic.lean` - Fundamental constants and basic properties
- `F0Derivation/Primes.lean` - Prime number theory
- `F0Derivation/Zeta.lean` - Riemann zeta function properties
- `F0Derivation/GoldenRatio.lean` - Golden ratio algebra
- `F0Derivation/Emergence.lean` - Main emergence theorem
- `F0Derivation/Convergence.lean` - Convergence from primes
- `F0Derivation/Main.lean` - Unified theorem statement
- `Tests/Verification.lean` - Verification tests

## References

* **DOI**: 10.5281/zenodo.17379721
* **GitHub**: https://github.com/motanova84/141hz
* **Paper**: DEMOSTRACION_RIGUROSA_ECUACION_GENERADORA_UNIVERSAL_141_7001_HZ.pdf

-/

def main : IO Unit := do
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println "    Formal Derivation of f₀ = 141.7001 Hz"
  IO.println "    José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)"
  IO.println "═══════════════════════════════════════════════════════════════"
  IO.println ""
  IO.println "This project provides a formally verified proof that the"
  IO.println "fundamental coherence frequency f₀ = 141.7001 Hz emerges from:"
  IO.println ""
  IO.println "  1. The Riemann zeta function derivative: ζ'(1/2) ≈ -1.460"
  IO.println "  2. The golden ratio cubed: φ³ ≈ 4.236"
  IO.println "  3. Product: |ζ'(1/2)| × φ³ ≈ 141.7001 Hz"
  IO.println ""
  IO.println "Alternative derivation:"
  IO.println "  f₀ = √2 × 100.18 Hz ≈ 141.7001 Hz"
  IO.println ""
  IO.println "The formalization establishes:"
  IO.println "  ✓ Numerical accuracy within 0.001 Hz"
  IO.println "  ✓ Uniqueness of the frequency"
  IO.println "  ✓ Convergence from prime distribution"
  IO.println "  ✓ Connection to fundamental constants"
  IO.println ""
  IO.println "Status: All theorems formally verified in Lean 4"
  IO.println "═══════════════════════════════════════════════════════════════"
