module

public import LeanBase.Classical.LandauZeros
public import LeanBase.Classical.PrimePowers
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.Floor
set_option autoImplicit false

/-!
# Proposition 3, directions (2) ⇒ (1) and (3) ⇒ (1) (ARCS paper §4.2)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/ArcProp3.lean), same author and licence.

* `primeRace c x = Σ_{p ≤ x} c_p` is the height `H_{a/q}`; `IsCharCombination X A c` says
  `c_p = Σ_{χ∈X} A_χ χ(p)` (the expansion of §4.1).
* `raceGap_mellin`: `∫_1^∞ (C x^θ − H(x)) x^{−s−1} dx = C/(s − θ) − D(s)/s` (Abel summation).
* `deriv_primeSeries_eq`: `D′ = Σ_χ A_χ L′/L(s, χ) + h′`, with `h′` the L-series of the prime powers
  `p^k`, `k ≥ 2`, absolutely convergent on `Re s > 1/2` (`abscissaOfAbsConv_primePowerTail_le`).
* `prop3_orders_of_upper_bound`: from `H(N) ≤ C N^θ` (`θ ≥ 1/2`) and (R) on `(θ, 1]`,
  `Σ_χ A_χ m_χ(ρ) = 0` at every `ρ` with `Re ρ > θ` (via `landau_zero_engine`).
* `prop3_zeroFree_of_upper_bound` (the last sentence of Proposition 3), `prop3_two_imp_zeroFree`,
  `prop3_three_imp_zeroFree`: under (R) and (N), the one-sided bounds give that no `L(s, χ)`,
  `χ ∈ X`, vanishes on `Re s > θ`, resp. `Re s > 1/2`.

Elsewhere: the step "β ≥ 1/2 by the functional equation", which turns the zero-free half-plane
into the statement on the critical line, is proved in `FunctionalEquation` (`grhFor_of_zeroFree`,
`prop3_arc_two_imp_GRH`, `prop3_arc_three_imp_GRH`); the directions (1) ⇒ (2), (3) are in
`Prop3One` (`prop3_one_imp_two_three`), with the GRH bound `π(x, χ) = O(√x log x)` as the cited
hypothesis `GRHPrimeBound`. The ARCS paper's `log L` and Möbius identity
`P(w) = Σ_j μ(j) j^{−1} log ζ(jw)` are replaced by logarithmic derivatives: `−L′/L = Σ χΛ n^{−s}`
is in Mathlib, and the difference with `D′` is the prime-power tail.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set MeasureTheory Asymptotics LSeries

/-- The weights on the primes: `c_p` at primes, `0` elsewhere. -/
noncomputable def primeCoeff (c : ℕ → ℝ) (n : ℕ) : ℝ := if n.Prime then c n else 0

/-- The weighted prime count `H(x) = Σ_{p ≤ x} c_p` (ARCS paper §3.2, the height of an arc). -/
noncomputable def primeRace (c : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoeff c n

/-- The gap `C x^θ − H(x)` on `x > 1`, extended by `0`. -/
noncomputable def raceGap (C θ : ℝ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  if 1 < t then C * t ^ θ - primeRace c t else 0

theorem primeRace_neg (c : ℕ → ℝ) (x : ℝ) : primeRace (fun n => -c n) x = -primeRace c x := by
  simp only [primeRace, primeCoeff, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

theorem primeRace_natCast (c : ℕ → ℝ) (N : ℕ) : primeRace c N = ∑ n ∈ Finset.Icc 1 N, primeCoeff c n := by
  simp [primeRace]

theorem abs_primeRace_le (c : ℕ → ℝ) {K : ℝ} (hK : ∀ n, |primeCoeff c n| ≤ K) {x : ℝ} (hx : 0 ≤ x) :
    |primeRace c x| ≤ K * x := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  calc |primeRace c x| ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, |primeCoeff c n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, K := Finset.sum_le_sum fun n _ => hK n
    _ = K * ⌊x⌋₊ := by simp [mul_comm]
    _ ≤ K * x := by gcongr; exact Nat.floor_le hx

theorem measurable_primeRace (c : ℕ → ℝ) : Measurable (primeRace c) :=
  (measurable_from_nat (f := fun N => ∑ n ∈ Finset.Icc 1 N, primeCoeff c n)).comp Nat.measurable_floor

theorem primeRace_of_lt_two (c : ℕ → ℝ) {x : ℝ} (hx : x < 2) : primeRace c x = 0 := by
  have : ⌊x⌋₊ ≤ 1 := by
    have := Nat.floor_lt' (show (2 : ℕ) ≠ 0 by norm_num) |>.2 (by exact_mod_cast hx); omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> simp [primeRace, primeCoeff, h, Nat.not_prime_one]

/-- `|g(t)| ≤ (|C| + K) t^{max(θ,1)}` for `t > 1`. -/
theorem abs_raceGap_le (C θ : ℝ) (c : ℕ → ℝ) {K R : ℝ} (hK : ∀ n, |primeCoeff c n| ≤ K) (hθ : 0 ≤ θ)
    {t : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) (hR : 1 ≤ R) :
    |raceGap C θ c t| ≤ |C| * R ^ θ + K * R := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  simp only [raceGap]
  split_ifs with h
  · calc |C * t ^ θ - primeRace c t| ≤ |C * t ^ θ| + |primeRace c t| := abs_sub _ _
      _ ≤ |C| * R ^ θ + K * R := by
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht _)]
        gcongr
        · exact (abs_primeRace_le c hK ht).trans (by gcongr)
  · simp only [abs_zero]; positivity

theorem locallyIntegrableOn_raceGap (C θ : ℝ) (c : ℕ → ℝ) {K : ℝ}
    (hK : ∀ n, |primeCoeff c n| ≤ K) (hθ : 0 ≤ θ) :
    LocallyIntegrableOn (fun t => (raceGap C θ c t : ℂ)) (Ioi 0) := by
  have hmeas : Measurable fun t => (raceGap C θ c t : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact Measurable.ite measurableSet_Ioi
      ((measurable_const.mul (measurable_id.pow_const θ)).sub (measurable_primeRace c))
      measurable_const
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun k hk hkc => ?_
  obtain ⟨R, hR⟩ := hkc.isBounded.subset_closedBall_lt 0 0
  refine Measure.integrableOn_of_bounded (M := |C| * (max R 1) ^ θ + K * max R 1)
    hkc.measure_lt_top.ne hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_mem hkc.measurableSet).mono fun t ht => ?_
  have ht0 : 0 < t := hk ht
  have htR : t ≤ max R 1 := by
    have := hR.2 ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos ht0] at this
    exact this.trans (le_max_left _ _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_raceGap_le C θ c hK hθ ht0.le htR (le_max_right _ _)

theorem raceGap_isBigO (C θ : ℝ) (c : ℕ → ℝ) {K : ℝ} (hK : ∀ n, |primeCoeff c n| ≤ K)
    (hθ : 0 ≤ θ) :
    (fun t => (raceGap C θ c t : ℂ)) =O[atTop] (· ^ (-(-(max θ 1)))) := by
  refine IsBigO.of_bound (|C| + K) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  rw [Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.norm_of_nonneg (by positivity)]
  have h := abs_raceGap_le C θ c hK hθ (zero_le_one.trans ht) le_rfl ht
  have h1 : t ^ θ ≤ t ^ (max θ 1) := Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)
  have h2 : t ≤ t ^ (max θ 1) := by
    conv_lhs => rw [← Real.rpow_one t]
    exact Real.rpow_le_rpow_of_exponent_le ht (le_max_right _ _)
  calc |raceGap C θ c t| ≤ |C| * t ^ θ + K * t := h
    _ ≤ |C| * t ^ (max θ 1) + K * t ^ (max θ 1) := by gcongr
    _ = (|C| + K) * t ^ (max θ 1) := by ring

/-- The integrand of the Mellin transform of the gap, on `t > 0`. -/
theorem raceGap_mellin_integrand (C θ : ℝ) (c : ℕ → ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-s - 1) • (raceGap C θ c t : ℂ) = (Ioi (1 : ℝ)).indicator (fun t : ℝ =>
      C * (t : ℂ) ^ ((θ : ℂ) - s - 1) -
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (primeCoeff c k : ℂ)) * (t : ℂ) ^ (-(s + 1))) t := by
  simp only [raceGap, Set.indicator, mem_Ioi, smul_eq_mul]
  split_ifs with h
  · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have e1 : (t : ℂ) ^ (-s - 1) * (t : ℂ) ^ (θ : ℂ) = (t : ℂ) ^ ((θ : ℂ) - s - 1) := by
      rw [← Complex.cpow_add _ _ ht']; ring_nf
    have e2 : -(s + 1) = -s - 1 := by ring
    simp only [primeRace]
    push_cast
    rw [Complex.ofReal_cpow ht.le, e2]
    linear_combination (C : ℂ) * e1
  · simp

theorem integrableOn_primeRace_cpow (c : ℕ → ℝ) {K : ℝ} (hK : ∀ n, |primeCoeff c n| ≤ K) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (primeCoeff c k : ℂ)) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => K * t ^ (-s.re)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul K
  refine hint.mono' ?_ ?_
  · refine (((measurable_from_nat (f := fun N => ∑ k ∈ Finset.Icc 1 N, (primeCoeff c k : ℂ))).comp
      Nat.measurable_floor).aestronglyMeasurable).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (by simp only [mem_Ioi] at ht; linarith))).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have hsum : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (primeCoeff c k : ℂ)‖ ≤ K * t := by
      have := abs_primeRace_le c hK ht0.le
      simp only [primeRace] at this
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
      exact this
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (primeCoeff c k : ℂ)‖ * t ^ (-(s.re + 1))
        ≤ K * t * t ^ (-(s.re + 1)) := by gcongr
      _ = K * t ^ (-s.re) := by
        rw [mul_assoc, ← Real.rpow_one_add' ht0.le (by linarith)]; congr 2; ring

/-- **The Mellin transform of the gap** (ARCS paper §4, proof of Proposition 3): for `Re s > max(θ, 1)`,
`∫_1^∞ (C x^θ − H(x)) x^{−s−1} dx` converges and equals `C/(s − θ) − D(s)/s`, `D = Σ_p c_p p^{−s}`.
The second term is Abel summation (Mathlib's `LSeries_eq_mul_integral`). -/
theorem raceGap_mellin (C θ : ℝ) (c : ℕ → ℝ) {K : ℝ} (hK : ∀ n, |primeCoeff c n| ≤ K) {s : ℂ}
    (hsθ : θ < s.re) (hs1 : 1 < s.re) :
    MellinConvergent (fun t => (raceGap C θ c t : ℂ)) (-s) ∧
      mellin (fun t => (raceGap C θ c t : ℂ)) (-s) =
        C / (s - θ) - LSeries (fun n => (primeCoeff c n : ℂ)) s / s := by
  set b : ℕ → ℂ := fun n => (primeCoeff c n : ℂ)
  set F : ℝ → ℂ := fun t : ℝ => C * (t : ℂ) ^ ((θ : ℂ) - s - 1) -
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * (t : ℂ) ^ (-(s + 1))
  have hre : ((θ : ℂ) - s - 1).re < -1 := by simp; linarith
  have h1 : IntegrableOn (fun t : ℝ => (C : ℂ) * (t : ℂ) ^ ((θ : ℂ) - s - 1)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hre zero_lt_one).const_mul _
  have h2 := integrableOn_primeRace_cpow c hK hs1
  have hF : IntegrableOn F (Ioi 1) := h1.sub h2
  have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • (raceGap C θ c t : ℂ)) ((Ioi (1 : ℝ)).indicator F)
      (Ioi 0) := fun t ht => raceGap_mellin_integrand C θ c s ht
  have hind : IntegrableOn ((Ioi (1 : ℝ)).indicator F) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 hF).integrableOn
  refine ⟨(hind.congr_fun heq.symm measurableSet_Ioi), ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, show max (0 : ℝ) 1 = 1 by norm_num, integral_sub h1 h2, integral_const_mul,
    integral_Ioi_cpow_of_lt hre zero_lt_one]
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1; linarith
  have hsθ' : s - θ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hab : LSeries b s = s * ∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, b k) * t ^ (-(s + 1)) := by
    refine LSeries_eq_mul_integral b zero_le_one hs1 ?_ ?_
    · refine LSeriesSummable_of_le_const_mul_rpow (x := 1) hs1 ⟨K, fun n _ => ?_⟩
      simp only [b, Complex.norm_real, Real.norm_eq_abs, sub_self, Real.rpow_zero, mul_one]
      exact hK n
    · refine IsBigO.of_bound K (Eventually.of_forall fun n => ?_)
      have := abs_primeRace_le c hK (Nat.cast_nonneg n)
      rw [primeRace_natCast] at this
      simp only [b]
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), Real.rpow_one]
      exact this
  rw [hab, mul_div_cancel_left₀ _ hs0]
  have hθs : (θ : ℂ) - s ≠ 0 := fun h => hsθ' (by linear_combination -h)
  congr 1
  simp only [Complex.ofReal_one, Complex.one_cpow, show (θ : ℂ) - s - 1 + 1 = θ - s by ring]
  field_simp
  ring

section Prop3

open ArithmeticFunction DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- The weights of an arc on the primes are a combination of characters:
`c_p = Σ_{χ∈X} A_χ χ(p)` for every prime `p` (ARCS paper §4.1, `A_χ = φ(q)^{−1} Σ_r c_r χ̄(r)`; the
hypothesis forces `c_p = 0` for `p ∣ q`, as in `H_{a/q}`). -/
def IsCharCombination (X : Finset (DirichletCharacter ℂ q)) (A : DirichletCharacter ℂ q → ℂ)
    (c : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → (c p : ℂ) = ∑ χ ∈ X, A χ * χ p

/-- The prime-power tail `Σ_χ A_χ χΛ − log · c`: on primes the two terms cancel, so only the `p^k`,
`k ≥ 2`, remain. Its L-series is `h′` in the ARCS paper's `D = Σ_χ A_χ log L(s, χ) + h`. -/
noncomputable def primePowerTail (X : Finset (DirichletCharacter ℂ q))
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) : ℕ → ℂ :=
  (∑ χ ∈ X, A χ • ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ))) -
    logMul (fun n => (primeCoeff c n : ℂ))

theorem abs_primeCoeff_le {X : Finset (DirichletCharacter ℂ q)} {A : DirichletCharacter ℂ q → ℂ}
    {c : ℕ → ℝ} (hc : IsCharCombination X A c) (n : ℕ) :
    |primeCoeff c n| ≤ ∑ χ ∈ X, ‖A χ‖ := by
  simp only [primeCoeff]
  split_ifs with hn
  · rw [← Real.norm_eq_abs, ← Complex.norm_real, hc n hn]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
  · simp only [abs_zero]; positivity

theorem norm_primePowerTail_le {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c) (n : ℕ) :
    ‖primePowerTail X A c n‖ ≤ (∑ χ ∈ X, ‖A χ‖) * (if n.Prime then 0 else Λ n) := by
  simp only [primePowerTail, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, logMul, primeCoeff]
  split_ifs with hn
  · rw [vonMangoldt_apply_prime hn, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
    have : ∑ χ ∈ X, A χ * ((χ n : ℂ) * Complex.log n) - Complex.log n * (c n : ℂ) = 0 := by
      rw [hc n hn, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_eq_zero fun χ _ => by ring
    rw [this, norm_zero, mul_zero]
  · simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun χ _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    gcongr
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)

/-- The prime-power tail converges absolutely on `Re s > 1/2`. -/
theorem abscissaOfAbsConv_primePowerTail_le {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c) :
    abscissaOfAbsConv (primePowerTail X A c) ≤ ((1 / 2 : ℝ) : EReal) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  set K := ∑ χ ∈ X, ‖A χ‖
  refine Summable.of_norm_bounded ((summable_vonMangoldt_nonprime_rpow hy).mul_left K) fun n => ?_
  have hnn : 0 ≤ (if n.Prime then 0 else Λ n) := by
    split_ifs
    exacts [le_rfl, vonMangoldt_nonneg]
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl]
    exact mul_nonneg hK0 (mul_nonneg hnn (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rw [if_neg hn]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_primePowerTail_le hc n) (Real.rpow_nonneg hn0.le _)

/-- **`D′ = Σ_χ A_χ L′/L(s, χ) + h′` on `Re s > 1`** (ARCS paper §4, proof of Proposition 3, in the
derivative form): `D(s) = Σ_p c_p p^{−s}`, `−L′/L(s, χ) = Σ χ(n)Λ(n) n^{−s}`, and `h′` is the
L-series of the prime-power tail. -/
theorem deriv_primeSeries_eq {X : Finset (DirichletCharacter ℂ q)}
    {A : DirichletCharacter ℂ q → ℂ} {c : ℕ → ℝ} (hc : IsCharCombination X A c) {s : ℂ}
    (hs : 1 < s.re) :
    deriv (LSeries fun n => (primeCoeff c n : ℂ)) s =
      ∑ χ ∈ X, A χ * logDeriv (LFunction χ) s + LSeries (primePowerTail X A c) s := by
  set b : ℕ → ℂ := fun n => (primeCoeff c n : ℂ)
  have hb1 : abscissaOfAbsConv b ≤ 1 := by
    refine abscissaOfAbsConv_le_one_of_isBigO_one (IsBigO.of_bound (∑ χ ∈ X, ‖A χ‖)
      (Eventually.of_forall fun n => ?_))
    simp only [b, Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one]
    exact abs_primeCoeff_le hc n
  have hb : abscissaOfAbsConv b < s.re := hb1.trans_lt (by exact_mod_cast hs)
  rw [LSeries_deriv hb]
  have hlog : ∀ χ ∈ X, logDeriv (LFunction χ) s =
      -LSeries ((fun n : ℕ => (χ n : ℂ)) * fun n : ℕ => (Λ n : ℂ)) s := by
    intro χ _
    rw [logDeriv_apply, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
    have := LSeries_twist_vonMangoldt_eq χ hs
    rw [this, neg_div, neg_neg]
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hlog χ hχ], primePowerTail,
    LSeries_sub (LSeriesSummable.sum fun χ _ => (LSeriesSummable_twist_vonMangoldt χ hs).smul _)
      (LSeriesSummable_logMul_of_lt_re hb),
    LSeries_sum fun χ _ => (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  simp only [LSeries_smul, mul_neg, Finset.sum_neg_distrib]
  ring

/-- **Proposition 3, direction (2) ⇒ (1), at one exponent** (ARCS paper §4.2). Let
`c_p = Σ_{χ∈X} A_χ χ(p)` with every `χ ∈ X` non-principal, and suppose the one-sided bound
`H(N) ≤ C N^θ` for all `N ≥ 2`, with `θ ≥ 1/2`, and condition (R) on `(θ, 1]`. Then at every `ρ`
with `Re ρ > θ` the multiplicities `m_χ(ρ)` of the zeros of the `L(s, χ)` satisfy
`Σ_χ A_χ m_χ(ρ) = 0`. -/
theorem prop3_orders_of_upper_bound (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ)
    (hc : IsCharCombination X A c) {θ C : ℝ} (hθ : 1 / 2 ≤ θ)
    (hbound : ∀ N : ℕ, 2 ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, θ < σ → σ ≤ 1 → LFunction χ σ ≠ 0) {ρ : ℂ} (hρ : θ < ρ.re) :
    ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) = 0 := by
  classical
  have hK := abs_primeCoeff_le hc
  have hθ0 : 0 ≤ θ := by linarith
  set C' := max C 0
  set g := raceGap C' θ c
  have hg0 : ∀ t, 0 ≤ g t := by
    intro t
    simp only [g, raceGap]
    split_ifs with ht
    · have hC' : 0 ≤ C' := le_max_right _ _
      have htθ : 0 ≤ t ^ θ := Real.rpow_nonneg (by linarith) _
      rcases lt_or_ge t 2 with h2 | h2
      · rw [primeRace_of_lt_two c h2, sub_zero]; positivity
      · set N := ⌊t⌋₊
        have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast h2)
        have hHN : primeRace c t = primeRace c N := by simp [primeRace, N]
        rw [hHN]
        have h1 := hbound N hN
        have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h2' : (N : ℝ) ^ θ ≤ t ^ θ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) hθ0
        have h3 : C * (N : ℝ) ^ θ ≤ C' * (N : ℝ) ^ θ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ
        have h4 : C' * (N : ℝ) ^ θ ≤ C' * t ^ θ := mul_le_mul_of_nonneg_left h2' hC'
        linarith
    · exact le_rfl
  have hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0 := fun t ht => by
    simp only [g, raceGap, if_neg (not_lt.2 ht.2.le)]
  have hLan : ∀ χ ∈ X, AnalyticOnNhd ℂ (LFunction χ) univ := fun χ hχ s _ =>
    (differentiable_LFunction (hX1 χ hχ)).analyticAt s
  have hreal : ∀ χ ∈ X, ∀ σ : ℝ, θ < σ → LFunction χ σ ≠ 0 := by
    intro χ hχ σ hσ
    rcases le_or_gt σ 1 with h | h
    · exact hR χ hχ σ hσ h
    · exact LFunction_ne_zero_of_one_le_re χ (Or.inl (hX1 χ hχ)) (by simp; linarith)
  have hfin : ∀ χ ∈ X, analyticOrderAt (LFunction χ) ρ ≠ ⊤ := by
    intro χ hχ
    refine (hLan χ hχ).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := ((θ + 1 : ℝ) : ℂ)) trivial trivial ?_
    rw [analyticOrderAt_eq_zero.2 (Or.inr (hreal χ hχ _ (by linarith)))]
    exact ENat.zero_ne_top
  have hh : AnalyticOnNhd ℂ (LSeries (primePowerTail X A c)) {s | θ < s.re} :=
    (LSeries_analyticOnNhd _).mono fun s hs =>
      (abscissaOfAbsConv_primePowerTail_le hc).trans_lt (by
        have : (1 / 2 : ℝ) < s.re := lt_of_le_of_lt hθ hs
        exact_mod_cast this)
  exact landau_zero_engine X A (fun χ => LFunction χ) (LSeries (primePowerTail X A c)) θ (θ + 1)
    hθ0 (by linarith) g hg0 hg1 (locallyIntegrableOn_raceGap C' θ c hK hθ0) (-(max θ 1))
    (raceGap_isBigO C' θ c hK hθ0) C' (LSeries fun n => (primeCoeff c n : ℂ))
    (fun σ hσ => (raceGap_mellin C' θ c hK (s := σ) (by simp; linarith) (by simp; linarith)).1)
    (fun s hs => (raceGap_mellin C' θ c hK (by linarith) (by linarith)).2)
    (fun χ hχ => (hLan χ hχ).mono (subset_univ _)) hreal hh
    (fun s hs => deriv_primeSeries_eq hc (by linarith)) hρ
    (fun χ => analyticOrderNatAt (LFunction χ) ρ)
    (fun χ hχ => (Nat.cast_analyticOrderNatAt (hfin χ hχ)).symm)

/-- Condition (N) of Proposition 3 on the half-plane `Re s > σ₀`: at every zero of some
`L(s, χ)`, `χ ∈ X`, the multiplicities do not cancel. -/
def ConditionN (X : Finset (DirichletCharacter ℂ q)) (A : DirichletCharacter ℂ q → ℂ) (σ₀ : ℝ) :
    Prop :=
  ∀ ρ : ℂ, σ₀ < ρ.re → (∃ χ ∈ X, LFunction χ ρ = 0) →
    ∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) ≠ 0

/-- **Proposition 3, last sentence**: if (2) holds for one `θ ≥ 1/2`, then under (R) and (N) every
zero of every `L(s, χ)`, `χ ∈ X`, has `Re ρ ≤ θ`. -/
theorem prop3_zeroFree_of_upper_bound (X : Finset (DirichletCharacter ℂ q))
    (hX1 : ∀ χ ∈ X, χ ≠ 1) (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ)
    (hc : IsCharCombination X A c) {θ C : ℝ} (hθ : 1 / 2 ≤ θ)
    (hbound : ∀ N : ℕ, 2 ≤ N → primeRace c N ≤ C * (N : ℝ) ^ θ)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, θ < σ → σ ≤ 1 → LFunction χ σ ≠ 0) (hN : ConditionN X A θ) :
    ∀ χ ∈ X, ∀ ρ : ℂ, θ < ρ.re → LFunction χ ρ ≠ 0 := by
  intro χ hχ ρ hρ h0
  exact hN ρ hρ ⟨χ, hχ, h0⟩ (prop3_orders_of_upper_bound X hX1 A c hc hθ hbound hR hρ)

/-- **Proposition 3, (2) ⇒ (1), zero-free form** (ARCS paper §4.2): under (R) on `(1/2, 1]` and (N) on
`Re s > 1/2`, if for every `ε > 0` there is `C_ε` with `H(N) ≤ C_ε N^{1/2+ε}` for all `N ≥ 2`, then
no `L(s, χ)`, `χ ∈ X`, vanishes on `Re s > 1/2`. (The step "the functional equation gives
`β ≥ 1/2`", which reaches the statement on the critical line, is `prop3_arc_two_imp_GRH` in
`FunctionalEquation`.) -/
theorem prop3_two_imp_zeroFree (X : Finset (DirichletCharacter ℂ q)) (hX1 : ∀ χ ∈ X, χ ≠ 1)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0) (hN : ConditionN X A (1 / 2))
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → primeRace c N ≤ C * (N : ℝ) ^ (1 / 2 + ε)) :
    ∀ χ ∈ X, ∀ ρ : ℂ, 1 / 2 < ρ.re → LFunction χ ρ ≠ 0 := by
  intro χ hχ ρ hρ
  set ε := (ρ.re - 1 / 2) / 2
  obtain ⟨C, hC⟩ := h2 ε (by simp only [ε]; linarith)
  refine prop3_zeroFree_of_upper_bound X hX1 A c hc (by simp only [ε]; linarith) hC
    (fun χ hχ σ hσ h1 => hR χ hχ σ (by simp only [ε] at hσ; linarith) h1)
    (fun ρ' hρ' => hN ρ' (by simp only [ε] at hρ'; linarith)) χ hχ ρ (by simp only [ε]; linarith)

/-- **Proposition 3, (3) ⇒ (1), zero-free form**: the same with the lower bound
`H(N) ≥ −C_ε N^{1/2+ε}` (apply the upper case to `−c`, `−A`). -/
theorem prop3_three_imp_zeroFree (X : Finset (DirichletCharacter ℂ q)) (hX1 : ∀ χ ∈ X, χ ≠ 1)
    (A : DirichletCharacter ℂ q → ℂ) (c : ℕ → ℝ) (hc : IsCharCombination X A c)
    (hR : ∀ χ ∈ X, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → LFunction χ σ ≠ 0) (hN : ConditionN X A (1 / 2))
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → -(C * (N : ℝ) ^ (1 / 2 + ε)) ≤ primeRace c N) :
    ∀ χ ∈ X, ∀ ρ : ℂ, 1 / 2 < ρ.re → LFunction χ ρ ≠ 0 := by
  refine prop3_two_imp_zeroFree X hX1 (fun χ => -A χ) (fun n => -c n) ?_ hR ?_ ?_
  · intro p hp
    push_cast
    rw [hc p hp, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun χ _ => by ring
  · intro ρ hρ hz h
    refine hN ρ hρ hz ?_
    have : ∑ χ ∈ X, -A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) =
        -∑ χ ∈ X, A χ * (analyticOrderNatAt (LFunction χ) ρ : ℂ) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun χ _ => by ring
    rw [this] at h
    exact neg_eq_zero.1 h
  · intro ε hε
    obtain ⟨C, hC⟩ := h3 ε hε
    exact ⟨C, fun N hN => by rw [primeRace_neg]; linarith [hC N hN]⟩

end Prop3

end LeanBase.Classical
