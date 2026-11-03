module

public import LeanBase.Classical.Prop30
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
set_option autoImplicit false

/-!
# Published theorems on the primes, as explicit hypotheses

Each statement is a `Prop`-valued definition, to be passed as a hypothesis of the theorems that
use it; none is an axiom. The consequences of the prime number theorem along the primes are in
`LeanBase.PrimeSums.PNTcons`.

* `RosserSchoenfeld`: `π(n) > n/ln n` for `n ≥ 17` and `π(n) < 1.25506 n/ln n` for `n ≥ 2`.
  Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file
  ArcsAlgo/Classical/LemmaK.lean), same author and licence.
* `VonKochPi`: under the Riemann hypothesis, `|π(x) − Li(x)| ≤ C √x log x` for `x ≥ 2`. The statement
  of `ArcsAlgo.Classical.VonKoch` (arcs-algo, commit 372ba68, file ArcsAlgo/Classical/Prop3One.lean),
  copied verbatim with the namespace changed.
* `VonKochPsi`: under the Riemann hypothesis, `ψ(x) = x + O(√x log² x)` as `x → ∞`.
-/

open Real Filter Asymptotics

@[expose] public section

namespace LeanBase

open scoped Nat.Prime

/-- **Rosser–Schoenfeld bounds** [J. B. Rosser, L. Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois J. Math. 6 (1962), Cor. 1, (3.2) and (3.5)], at the integers:
`π(n) > n/ln n` for `n ≥ 17` and `π(n) < 1.25506 n/ln n` for `n > 1`. An explicit hypothesis,
never an axiom. -/
def RosserSchoenfeld : Prop :=
  (∀ n : ℕ, 17 ≤ n → (n : ℝ) / log n < π n) ∧ (∀ n : ℕ, 2 ≤ n → (π n : ℝ) < 1.25506 * n / log n)

/-- **von Koch's theorem, form with `π`** [H. von Koch, *Sur la distribution des nombres premiers*,
Acta Math. 24 (1901); H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Ch. 18]: under
the Riemann hypothesis, `π(x) − ∫_2^x dt/log t = O(√x log x)`, stated for every `x ≥ 2` with a
constant `C` (whose value is not given). The Riemann hypothesis is only its antecedent. An explicit
hypothesis, never an axiom. -/
def VonKochPi : Prop :=
  RiemannHypothesis → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |LeanBase.Classical.momentError 0 x| ≤ C * √x * log x

/-- **von Koch's theorem, form with `ψ`** [H. von Koch, *Sur la distribution des nombres premiers*,
Acta Math. 24 (1901); H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Ch. 18;
H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge 2007, Thm. 13.1]: under
the Riemann hypothesis, `ψ(x) = x + O(√x log² x)` as `x → ∞` (implied constant not given). The
Riemann hypothesis is only its antecedent. An explicit hypothesis, never an axiom. -/
def VonKochPsi : Prop :=
  RiemannHypothesis →
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] (fun x : ℝ => √x * log x ^ 2)

end LeanBase
