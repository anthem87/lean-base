module

public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false

/-!
# The prime powers `p^k`, `k ≥ 2`, on `Re s > 1/2` (ARCS paper §4)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/PrimePowers.lean), same author and licence.

`summable_vonMangoldt_nonprime_rpow`: `Σ_{n not prime} Λ(n) n^{−σ} < ∞` for `σ > 1/2`. Proof as in
Mathlib's `summable_residueClass_non_primes_div` (the case `σ = 1`): reindex the prime powers
`p^{k+2}` by `(p, k)` and sum a geometric series in `k`.
-/

@[expose] public section

namespace LeanBase.Classical

open ArithmeticFunction

/-- `p^(k+2)` is never prime. -/
theorem not_prime_pow_add_two {p : ℕ} (hp : p.Prime) (k : ℕ) : ¬ (p ^ (k + 2)).Prime := by
  rw [pow_succ']
  exact Nat.not_prime_mul hp.one_lt.ne' (Nat.one_lt_pow (by omega) hp.one_lt).ne'

/-- **The prime powers `p^k`, `k ≥ 2`, converge absolutely on `Re s > 1/2`**:
`Σ_{n not prime} Λ(n) n^{−σ} < ∞` for `σ > 1/2`. This is what makes
`D(s) − Σ_χ A_χ log L(s, χ)` holomorphic on `Re s > 1/2` (ARCS paper §4). -/
theorem summable_vonMangoldt_nonprime_rpow {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun n : ℕ => (if n.Prime then 0 else Λ n) * (n : ℝ) ^ (-σ) := by
  set f : ℕ → ℝ := fun n => (if n.Prime then 0 else Λ n) * (n : ℝ) ^ (-σ)
  set φ : Nat.Primes × ℕ → ℕ := fun pk => (pk.1 : ℕ) ^ (pk.2 + 2)
  have hφ : Function.Injective φ := by
    rintro ⟨p, k⟩ ⟨p', k'⟩ h
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj p.prop p'.prop (show (p : ℕ) ^ ((k + 1) + 1) =
      (p' : ℕ) ^ ((k' + 1) + 1) from h)
    exact Prod.ext (Subtype.ext h1) (by simp only; omega)
  have hrange : ∀ n ∉ Set.range φ, f n = 0 := by
    intro n hn
    simp only [f]
    by_cases hnp : n.Prime
    · simp [hnp]
    rw [if_neg hnp]
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        subst this; simp [hp] at hnp
      · exact absurd ⟨(⟨p, hp⟩, k - 2), by simp only [φ]; congr 1; omega⟩ hn
    · simp [vonMangoldt_eq_zero_iff.2 hpp]
  refine (hφ.summable_iff hrange).1 ?_
  -- on the pairs: `log p · p^{−(k+2)σ}`
  set δ : ℝ := σ - 1 / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hσ0 : 0 < σ := by linarith
  have hval : ∀ pk : Nat.Primes × ℕ, (f ∘ φ) pk =
      Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ 2 * ((pk.1 : ℝ) ^ (-σ)) ^ pk.2 := by
    rintro ⟨p, k⟩
    simp only [Function.comp_apply, f, φ, if_neg (not_prime_pow_add_two p.prop k)]
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime p.prop]
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_mul (Nat.cast_nonneg _), mul_assoc, ← Real.rpow_add (by exact_mod_cast p.prop.pos)]
    congr 2
    push_cast; ring
  rw [show f ∘ φ = _ from funext hval]
  have hp0 : ∀ p : Nat.Primes, 0 < (p : ℝ) ^ (-σ) := fun p =>
    Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _
  have hp1 : ∀ p : Nat.Primes, (p : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := fun p =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith)
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlt1 : ∀ p : Nat.Primes, (p : ℝ) ^ (-σ) < 1 := fun p => (hp1 p).trans_lt h2
  have hlog0 : ∀ p : Nat.Primes, 0 ≤ Real.log p := fun p =>
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hnn : ∀ pk : Nat.Primes × ℕ,
      0 ≤ Real.log pk.1 * ((pk.1 : ℝ) ^ (-σ)) ^ 2 * ((pk.1 : ℝ) ^ (-σ)) ^ pk.2 :=
    fun pk => mul_nonneg (mul_nonneg (hlog0 pk.1) (sq_nonneg _)) (pow_nonneg (hp0 pk.1).le _)
  refine (summable_prod_of_nonneg hnn).2 ⟨fun p => ?_, ?_⟩
  · show Summable fun k : ℕ => Real.log p * ((p : ℝ) ^ (-σ)) ^ 2 * ((p : ℝ) ^ (-σ)) ^ k
    exact (summable_geometric_of_lt_one (hp0 p).le (hlt1 p)).mul_left _
  show Summable fun p : Nat.Primes =>
    ∑' k : ℕ, Real.log p * ((p : ℝ) ^ (-σ)) ^ 2 * ((p : ℝ) ^ (-σ)) ^ k
  have hts : ∀ p : Nat.Primes,
      ∑' k : ℕ, Real.log p * ((p : ℝ) ^ (-σ)) ^ 2 * ((p : ℝ) ^ (-σ)) ^ k =
        Real.log p * ((p : ℝ) ^ (-σ)) ^ 2 * (1 - (p : ℝ) ^ (-σ))⁻¹ := fun p => by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (hp0 p).le (hlt1 p)]
  refine (summable_congr hts).2 ?_
  -- `log p · p^{−2σ} / (1 − p^{−σ}) ≤ (δ (1 − 2^{−σ}))⁻¹ p^{δ − 2σ}`, and `δ − 2σ < −1`
  set K : ℝ := (δ * (1 - (2 : ℝ) ^ (-σ)))⁻¹
  have hK : 0 < K := inv_pos.2 (mul_pos hδ (by linarith))
  refine ((Nat.Primes.summable_rpow.2 (show δ - 2 * σ < -1 by simp only [δ]; linarith)).mul_left K
    |>.of_nonneg_of_le (fun p => ?_) (fun p => ?_))
  · have := hp0 p; have := hlog0 p; have := hlt1 p
    have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith
    positivity
  · have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
    have hlog : Real.log p ≤ (p : ℝ) ^ δ / δ := Real.log_le_rpow_div hp.le hδ
    have hden : 1 - (2 : ℝ) ^ (-σ) ≤ 1 - (p : ℝ) ^ (-σ) := by linarith [hp1 p]
    have hden0 : 0 < 1 - (2 : ℝ) ^ (-σ) := by linarith
    have hsq : ((p : ℝ) ^ (-σ)) ^ 2 = (p : ℝ) ^ (-2 * σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; congr 1; push_cast; ring
    rw [hsq]
    have hpow : (p : ℝ) ^ δ * (p : ℝ) ^ (-2 * σ) = (p : ℝ) ^ (δ - 2 * σ) := by
      rw [← Real.rpow_add hp]; congr 1; ring
    have h3 : 0 < (p : ℝ) ^ (-2 * σ) := Real.rpow_pos_of_pos hp _
    calc Real.log p * (p : ℝ) ^ (-2 * σ) * (1 - (p : ℝ) ^ (-σ))⁻¹
        ≤ ((p : ℝ) ^ δ / δ) * (p : ℝ) ^ (-2 * σ) * (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
          have : 0 < 1 - (p : ℝ) ^ (-σ) := by linarith [hlt1 p]
          gcongr
      _ = K * (p : ℝ) ^ (δ - 2 * σ) := by
          rw [← hpow]; simp only [K]; field_simp

end LeanBase.Classical
