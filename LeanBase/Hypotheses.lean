module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false

/-!
# Published theorems on the primes, as explicit hypotheses

Each statement is a `Prop`-valued definition, to be passed as a hypothesis of the theorems that
use it; none is an axiom. The consequences of the prime number theorem along the primes are in
`LeanBase.PrimeSums.PNTcons`.

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file
ArcsAlgo/Classical/LemmaK.lean), same author and licence.

* `RosserSchoenfeld`: `π(n) > n/ln n` for `n ≥ 17` and `π(n) < 1.25506 n/ln n` for `n ≥ 2`.
-/

open Real

@[expose] public section

namespace LeanBase

open scoped Nat.Prime

/-- **Rosser–Schoenfeld bounds** [J. B. Rosser, L. Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois J. Math. 6 (1962), Cor. 1, (3.2) and (3.5)], at the integers:
`π(n) > n/ln n` for `n ≥ 17` and `π(n) < 1.25506 n/ln n` for `n > 1`. An explicit hypothesis,
never an axiom. -/
def RosserSchoenfeld : Prop :=
  (∀ n : ℕ, 17 ≤ n → (n : ℝ) / log n < π n) ∧ (∀ n : ℕ, 2 ≤ n → (π n : ℝ) < 1.25506 * n / log n)

end LeanBase
