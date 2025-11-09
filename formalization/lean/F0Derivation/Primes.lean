/-
Copyright (c) 2025 José Manuel Mota Burruezo. All rights reserved.
Released under MIT license.
-/

import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.PrimeCounting

/-!
# Prime Number Theory

Basic results about prime numbers needed for f₀ derivation.

## Main results

* `infinitude_of_primes`: There are infinitely many primes
* `prime_greater_than_one`: All primes are greater than 1

-/

namespace F0Derivation

-- ═══════════════════════════════════════════════════════════════
-- BASIC PRIME PROPERTIES
-- ═══════════════════════════════════════════════════════════════

/-- There are infinitely many primes -/
theorem infinitude_of_primes : ∀ n, ∃ p > n, Nat.Prime p := 
  Nat.exists_infinite_primes

/-- All primes are greater than 1 -/
theorem prime_greater_than_one (p : ℕ) (hp : Nat.Prime p) : p > 1 :=
  Nat.Prime.one_lt hp

/-- Prime product lower bound -/
theorem prime_product_lower_bound (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≤ n ∧ 
    (∏ q in (Finset.range n).filter Nat.Prime, q) ≥ 2 ^ (n / 2) := by
  sorry

end F0Derivation
