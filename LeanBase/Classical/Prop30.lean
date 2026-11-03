module

public import LeanBase.Classical.ZetaNegative
public import LeanBase.Classical.LogIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
set_option autoImplicit false

/-!
# Proposition 3₀, directions (2) ⇒ (1) and (3) ⇒ (1) (ARCS paper §4.4)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/Prop30.lean), same author and licence.

* `momentError k x = E_k(x) = Σ_{p≤x} p^k − Li_k(x)`, with `Li_k(x) = li(x^{k+1}) − li(2^{k+1})`
  (the constant does not affect bounds `O(x^{k+1/2+ε})`); `momentGap` is `C x^θ − η E_k(x)`,
  `η = ±1`, which is `≥ 0` under the one-sided bounds (`momentGap_nonneg_upper`, `_lower`).
* `momentGap_mellin`: its Mellin transform is `C/(s − θ) − η (D_k(s) − J(s))/s` on
  `Re s > max(θ, k + 1)`, with `D_k(s) = Σ_p p^{k−s}` (Abel summation, `primeRace_pow_mellin`) and
  `J(s) = ∫_2^∞ t^{k−s} dt / log t` (`liK_mellin`).
* In derivative form, `D_k′ − J′ = ζ₁′/ζ₁(s − k) + h(s)` with `ζ₁(w) = (w − 1) ζ(w)` (Mathlib's
  `riemannZeta₁`, entire), `h = L(prime-power tail) − (2^u − 1)/u`, `u = k + 1 − s`, analytic on
  `Re s > k + 1/2`: the ARCS paper's `P(w) = Σ_j μ(j) j^{−1} log ζ(jw)` and
  `∫_2^∞ t^{k−s} dt / log t = −log(s − k − 1) + (entire)` after differentiation.
* `prop30_zeroFree_of_gap`: by `landau_zero_engine`, `ζ(ρ − k) ≠ 0` for `Re ρ > θ`; the real segment
  is handled by `riemannZeta_neg_of_mem_Ioo` (`ζ(σ) < 0` on `(0, 1)`, proved via `η`).
* `riemannHypothesis_of_zeroFree`: the functional equation (`riemannZeta_one_sub`) turns
  "no zero on `Re s > 1/2`" into Mathlib's `RiemannHypothesis`.
* `prop30_two_imp_RH`, `prop30_three_imp_RH`: the one-sided bounds on `E_k` for every `ε > 0`
  imply `RiemannHypothesis`, for every `k ≥ 0`.

The directions (1) ⇒ (2), (3) are in `Prop3One` (`prop30_one_imp_two_three`), with von Koch's
theorem (RH ⇒ `π(x) = li(x) + O(√x log x)`) as the cited hypothesis `VonKoch`.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set MeasureTheory Asymptotics LSeries ArithmeticFunction

/-- The weights `p^k`. -/
noncomputable def powWeight (k : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ k

/-- `E_k(x) = M_k(x) − Li_k(x)`, with `M_k(x) = Σ_{p ≤ x} p^k` (ARCS paper §4.4; `li(x^{k+1})` replaced by
`Li_k(x) = li(x^{k+1}) − li(2^{k+1})`). -/
noncomputable def momentError (k : ℕ) (x : ℝ) : ℝ := primeRace (powWeight k) x - liK k x

/-- The gap `C x^θ − η E_k(x)` on `x > 1` (`η = ±1`), extended by `0`. -/
noncomputable def momentGap (C θ η : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if 1 < t then C * t ^ θ - η * momentError k t else 0

theorem primeCoeff_pow_nonneg (k n : ℕ) : 0 ≤ primeCoeff (powWeight k) n := by
  simp only [primeCoeff, powWeight]; split_ifs <;> positivity

theorem primeCoeff_pow_le (k n : ℕ) : primeCoeff (powWeight k) n ≤ (n : ℝ) ^ k := by
  simp only [primeCoeff, powWeight]; split_ifs <;> [exact le_rfl; positivity]

theorem primeRace_pow_nonneg (k : ℕ) (x : ℝ) : 0 ≤ primeRace (powWeight k) x :=
  Finset.sum_nonneg fun n _ => primeCoeff_pow_nonneg k n

theorem primeRace_pow_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : primeRace (powWeight k) x ≤ x ^ (k + 1) := by
  calc primeRace (powWeight k) x ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, x ^ k := by
        refine Finset.sum_le_sum fun n hn => (primeCoeff_pow_le k n).trans ?_
        have : (n : ℝ) ≤ x := (Nat.cast_le.2 (Finset.mem_Icc.1 hn).2).trans (Nat.floor_le hx)
        exact pow_le_pow_left₀ (Nat.cast_nonneg n) this k
    _ = ⌊x⌋₊ * x ^ k := by simp
    _ ≤ x * x ^ k := by gcongr; exact Nat.floor_le hx
    _ = x ^ (k + 1) := by ring

theorem liK_sub_le (k : ℕ) {N t : ℝ} (hN : N ≤ t) (ht : 0 ≤ t) :
    liK k t - liK k N ≤ (t - N) * (t ^ k / Real.log 2) := by
  rw [liK, liK, intervalIntegral.integral_interval_sub_left (intervalIntegrable_liIntegrand k 0 t)
    (intervalIntegrable_liIntegrand k 0 N)]
  have h := intervalIntegral.integral_mono_on hN (intervalIntegrable_liIntegrand k N t)
    (intervalIntegrable_const (c := |t| ^ k / Real.log 2)) fun u hu => liIntegrand_le k hu.2
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_nonneg ht] at h
  exact h

theorem abs_momentGap_le (C θ η : ℝ) (hη : |η| = 1) (k : ℕ) (hθ : 0 ≤ θ) {t R : ℝ} (ht : 0 ≤ t)
    (htR : t ≤ R) (hR : 1 ≤ R) :
    |momentGap C θ η k t| ≤ |C| * R ^ θ + (R ^ (k + 1) + R ^ (k + 1) / Real.log 2) := by
  have hl := log_two_pos'
  simp only [momentGap]
  split_ifs with h
  · have h1 : |momentError k t| ≤ R ^ (k + 1) + R ^ (k + 1) / Real.log 2 := by
      have a1 := primeRace_pow_nonneg k t
      have a2 := primeRace_pow_le k ht
      have a3 := liK_nonneg k t
      have a4 := liK_le k ht
      have b1 : t ^ (k + 1) ≤ R ^ (k + 1) := pow_le_pow_left₀ ht htR _
      have b2 : t ^ (k + 1) / Real.log 2 ≤ R ^ (k + 1) / Real.log 2 := by gcongr
      rw [momentError, abs_le]; constructor <;> linarith [div_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ R) (k+1)) hl.le]
    calc |C * t ^ θ - η * momentError k t| ≤ |C * t ^ θ| + |η * momentError k t| := abs_sub _ _
      _ ≤ |C| * R ^ θ + (R ^ (k + 1) + R ^ (k + 1) / Real.log 2) := by
        rw [abs_mul, abs_mul, hη, one_mul, abs_of_nonneg (Real.rpow_nonneg ht _)]
        gcongr
  · simp only [abs_zero]; have : 0 ≤ R := by linarith
    positivity

theorem measurable_momentGap (C θ η : ℝ) (k : ℕ) : Measurable (momentGap C θ η k) :=
  Measurable.ite measurableSet_Ioi ((measurable_const.mul (measurable_id.pow_const θ)).sub
    (measurable_const.mul ((measurable_primeRace _).sub (continuous_liK k).measurable)))
    measurable_const

theorem locallyIntegrableOn_momentGap (C θ η : ℝ) (hη : |η| = 1) (k : ℕ) (hθ : 0 ≤ θ) :
    LocallyIntegrableOn (fun t => (momentGap C θ η k t : ℂ)) (Ioi 0) := by
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc => ?_
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall_lt 0 0
  refine Measure.integrableOn_of_bounded hKc.measure_lt_top.ne
    (Complex.measurable_ofReal.comp (measurable_momentGap C θ η k)).aestronglyMeasurable
    (M := |C| * (max R 1) ^ θ + ((max R 1) ^ (k + 1) + (max R 1) ^ (k + 1) / Real.log 2)) ?_
  refine (ae_restrict_mem hKc.measurableSet).mono fun t ht => ?_
  have ht0 : 0 < t := hK ht
  have htR : t ≤ max R 1 := by
    have := hR.2 ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos ht0] at this
    exact this.trans (le_max_left _ _)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_momentGap_le C θ η hη k hθ ht0.le htR (le_max_right _ _)

theorem momentGap_isBigO (C θ η : ℝ) (hη : |η| = 1) (k : ℕ) (hθ : 0 ≤ θ) :
    (fun t => (momentGap C θ η k t : ℂ)) =O[atTop] (· ^ (-(-(max θ (k + 1))))) := by
  refine IsBigO.of_bound (|C| + (1 + 1 / Real.log 2)) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have hl := log_two_pos'
  rw [Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.norm_of_nonneg (by positivity)]
  have h := abs_momentGap_le C θ η hη k hθ (zero_le_one.trans ht) le_rfl ht
  have h1 : t ^ θ ≤ t ^ (max θ (k + 1)) := Real.rpow_le_rpow_of_exponent_le ht (le_max_left _ _)
  have h2 : t ^ (k + 1) ≤ t ^ (max θ (k + 1)) := by
    rw [← Real.rpow_natCast]; push_cast
    exact Real.rpow_le_rpow_of_exponent_le ht (le_max_right _ _)
  have h3 : 0 ≤ t ^ (k + 1) := by positivity
  calc |momentGap C θ η k t| ≤ |C| * t ^ θ + (t ^ (k + 1) + t ^ (k + 1) / Real.log 2) := h
    _ ≤ |C| * t ^ (max θ (k + 1)) + (t ^ (max θ (k + 1)) + t ^ (max θ (k + 1)) / Real.log 2) := by
        gcongr
    _ = (|C| + (1 + 1 / Real.log 2)) * t ^ (max θ (k + 1)) := by ring

theorem momentGap_nonneg_upper (k : ℕ) {θ C : ℝ} (hθ : 0 ≤ θ)
    (hbound : ∀ N : ℕ, 2 ≤ N → momentError k N ≤ C * (N : ℝ) ^ θ) (t : ℝ) :
    0 ≤ momentGap (max C 0) θ 1 k t := by
  simp only [momentGap, one_mul]
  split_ifs with ht
  · have hC' : 0 ≤ max C 0 := le_max_right _ _
    have htθ : 0 ≤ t ^ θ := Real.rpow_nonneg (by linarith) _
    rcases lt_or_ge t 2 with h2 | h2
    · rw [momentError, primeRace_of_lt_two _ h2, liK_of_le_two k h2.le]; simp; positivity
    · set N := ⌊t⌋₊
      have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast h2)
      have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hHN : primeRace (powWeight k) t = primeRace (powWeight k) N := by simp [primeRace, N]
      have hli : liK k N ≤ liK k t := liK_mono k hNt
      have h1 := hbound N hN
      rw [momentError] at h1 ⊢
      have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h3 : C * (N : ℝ) ^ θ ≤ max C 0 * (N : ℝ) ^ θ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ
      have h4 : max C 0 * (N : ℝ) ^ θ ≤ max C 0 * t ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hNt hθ) hC'
      linarith
  · exact le_rfl

theorem momentGap_nonneg_lower (k : ℕ) {θ C : ℝ} (hθ : (k : ℝ) ≤ θ)
    (hbound : ∀ N : ℕ, 2 ≤ N → -(C * (N : ℝ) ^ θ) ≤ momentError k N) (t : ℝ) :
    0 ≤ momentGap (max C 0 + 1 / Real.log 2) θ (-1) k t := by
  have hl := log_two_pos'
  have hθ0 : 0 ≤ θ := le_trans (Nat.cast_nonneg k) hθ
  simp only [momentGap, neg_mul, one_mul, sub_neg_eq_add]
  split_ifs with ht
  · have hC' : 0 ≤ max C 0 := le_max_right _ _
    have htθ : 0 ≤ t ^ θ := Real.rpow_nonneg (by linarith) _
    rcases lt_or_ge t 2 with h2 | h2
    · rw [momentError, primeRace_of_lt_two _ h2, liK_of_le_two k h2.le]; simp; positivity
    · set N := ⌊t⌋₊
      have hN : 2 ≤ N := Nat.le_floor (by exact_mod_cast h2)
      have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hNt1 : t - N < 1 := by
        have := Nat.lt_floor_add_one t; simp only [N]; linarith
      have hHN : primeRace (powWeight k) t = primeRace (powWeight k) N := by simp [primeRace, N]
      have hli := liK_sub_le k hNt (by linarith)
      have h1 := hbound N hN
      rw [momentError] at h1 ⊢
      have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have h3 : C * (N : ℝ) ^ θ ≤ max C 0 * t ^ θ :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hNθ).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hNt hθ0) hC')
      have hk : t ^ k ≤ t ^ θ := by
        rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hθ
      have h5 : (t - N) * (t ^ k / Real.log 2) ≤ 1 / Real.log 2 * t ^ θ := by
        have : 0 ≤ t ^ k / Real.log 2 := by positivity
        calc (t - N) * (t ^ k / Real.log 2) ≤ 1 * (t ^ k / Real.log 2) := by gcongr
          _ = 1 / Real.log 2 * t ^ k := by ring
          _ ≤ 1 / Real.log 2 * t ^ θ := by gcongr
      rw [hHN]
      nlinarith
  · exact le_rfl

/-- `D_k(s) = Σ_p p^k p^{−s}`, coefficients. -/
noncomputable def powCoeff (k : ℕ) (n : ℕ) : ℂ := (primeCoeff (powWeight k) n : ℂ)

theorem norm_powCoeff_le (k n : ℕ) : ‖powCoeff k n‖ ≤ (n : ℝ) ^ k := by
  rw [powCoeff, Complex.norm_real, Real.norm_of_nonneg (primeCoeff_pow_nonneg k n)]
  exact primeCoeff_pow_le k n

theorem integrableOn_primeRace_pow_cpow (k : ℕ) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    IntegrableOn (fun t : ℝ => (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, powCoeff k j) * (t : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ ((k : ℝ) - s.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  refine hint.mono' ?_ ?_
  · refine (((measurable_from_nat (f := fun N => ∑ j ∈ Finset.Icc 1 N, powCoeff k j)).comp
      Nat.measurable_floor).aestronglyMeasurable).mul ?_
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (by simp only [mem_Ioi] at ht; linarith))).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    have hsum : ‖∑ j ∈ Finset.Icc 1 ⌊t⌋₊, powCoeff k j‖ ≤ t ^ (k + 1) := by
      simp only [powCoeff]
      rw [← Complex.ofReal_sum, Complex.norm_real,
        Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => primeCoeff_pow_nonneg k j)]
      exact primeRace_pow_le k ht0.le
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc ‖∑ j ∈ Finset.Icc 1 ⌊t⌋₊, powCoeff k j‖ * t ^ (-(s.re + 1))
        ≤ t ^ (k + 1) * t ^ (-(s.re + 1)) := by gcongr
      _ = t ^ ((k : ℝ) - s.re) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; congr 1; push_cast; ring

theorem abscissa_powCoeff_le (k : ℕ) : abscissaOfAbsConv (powCoeff k) ≤ ((k : ℝ) + 1 : ℝ) := by
  have := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (f := powCoeff k) (x := (k : ℝ))
    (IsBigO.of_bound 1 (Eventually.of_forall fun n => by
      rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), Real.rpow_natCast]
      exact norm_powCoeff_le k n))
  exact_mod_cast this

/-- Abel summation for `M_k`: `∫_1^∞ M_k(x) x^{−s−1} dx = D_k(s)/s` on `Re s > k + 1`. -/
theorem primeRace_pow_mellin (k : ℕ) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (∑ j ∈ Finset.Icc 1 ⌊t⌋₊, powCoeff k j) * (t : ℂ) ^ (-(s + 1)) =
      LSeries (powCoeff k) s / s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hr : (0 : ℝ) ≤ k + 1 := by positivity
  have hab := LSeries_eq_mul_integral (powCoeff k) hr hs ?_ ?_
  · rw [hab]; field_simp
  · refine LSeriesSummable_of_le_const_mul_rpow (x := (k : ℝ) + 1) hs ⟨1, fun n _ => ?_⟩
    rw [one_mul, show (k : ℝ) + 1 - 1 = k by ring, Real.rpow_natCast]
    exact norm_powCoeff_le k n
  · refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
    have h := primeRace_pow_le k (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    rw [primeRace_natCast] at h
    simp only [powCoeff]
    rw [← Complex.ofReal_sum, Complex.norm_real, one_mul,
      Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => primeCoeff_pow_nonneg k j),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    exact h

/-- **The Mellin transform of the gap `C x^θ − η E_k(x)`**: for `Re s > max(θ, k + 1)`,
`= C/(s − θ) − η (D_k(s) − J(s))/s`. -/
theorem momentGap_mellin (C θ η : ℝ) (k : ℕ) {s : ℂ} (hsθ : θ < s.re) (hsk : (k : ℝ) + 1 < s.re) :
    MellinConvergent (fun t => (momentGap C θ η k t : ℂ)) (-s) ∧
      mellin (fun t => (momentGap C θ η k t : ℂ)) (-s) =
        C / (s - θ) - (η : ℂ) * (LSeries (powCoeff k) s - liMellin k s) / s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hsk; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  set F₁ : ℝ → ℂ := fun t : ℝ => C * (t : ℂ) ^ ((θ : ℂ) - s - 1) -
    η * ((∑ j ∈ Finset.Icc 1 ⌊t⌋₊, powCoeff k j) * (t : ℂ) ^ (-(s + 1)))
  set F₂ : ℝ → ℂ := fun t : ℝ => η * ((liK k t : ℂ) * (t : ℂ) ^ (-s - 1))
  have hre : ((θ : ℂ) - s - 1).re < -1 := by simp; linarith
  have h1 : IntegrableOn (fun t : ℝ => (C : ℂ) * (t : ℂ) ^ ((θ : ℂ) - s - 1)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hre zero_lt_one).const_mul _
  have h2 := integrableOn_primeRace_pow_cpow k hsk
  have hF₁ : IntegrableOn F₁ (Ioi 1) := h1.sub (h2.const_mul _)
  obtain ⟨h3, h3v⟩ := liK_mellin k hsk
  have hF₂ : IntegrableOn F₂ (Ioi 2) := h3.const_mul _
  have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) • (momentGap C θ η k t : ℂ))
      ((Ioi (1 : ℝ)).indicator F₁ + (Ioi (2 : ℝ)).indicator F₂) (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [momentGap, Pi.add_apply, Set.indicator, mem_Ioi, smul_eq_mul, F₁, F₂]
    split_ifs with h1' h2'
    · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have e1 : (t : ℂ) ^ (-s - 1) * (t : ℂ) ^ (θ : ℂ) = (t : ℂ) ^ ((θ : ℂ) - s - 1) := by
        rw [← Complex.cpow_add _ _ ht']; ring_nf
      have e2 : -(s + 1) = -s - 1 := by ring
      simp only [momentError, primeRace, powCoeff]
      push_cast
      rw [Complex.ofReal_cpow ht0.le, e2]
      linear_combination (C : ℂ) * e1
    · have hli : liK k t = 0 := liK_of_le_two k (not_lt.1 h2')
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      have e1 : (t : ℂ) ^ (-s - 1) * (t : ℂ) ^ (θ : ℂ) = (t : ℂ) ^ ((θ : ℂ) - s - 1) := by
        rw [← Complex.cpow_add _ _ ht']; ring_nf
      have e2 : -(s + 1) = -s - 1 := by ring
      simp only [momentError, primeRace, powCoeff, hli]
      push_cast
      rw [Complex.ofReal_cpow ht0.le, e2]
      linear_combination (C : ℂ) * e1
    · exact absurd (by linarith : (1 : ℝ) < t) h1'
    · simp
  have hind₁ : IntegrableOn ((Ioi (1 : ℝ)).indicator F₁) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 hF₁).integrableOn
  have hind₂ : IntegrableOn ((Ioi (2 : ℝ)).indicator F₂) (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioi).2 hF₂).integrableOn
  refine ⟨(hind₁.add hind₂).congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi heq, Pi.add_def, integral_add hind₁ hind₂,
    setIntegral_indicator measurableSet_Ioi, setIntegral_indicator measurableSet_Ioi,
    Ioi_inter_Ioi, Ioi_inter_Ioi, show max (0 : ℝ) 1 = 1 by norm_num,
    show max (0 : ℝ) 2 = 2 by norm_num, integral_sub h1 (h2.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_Ioi_cpow_of_lt hre zero_lt_one,
    primeRace_pow_mellin k hsk, h3v]
  have hsθ : s - (θ : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have e1 : ((1 : ℝ) : ℂ) ^ ((θ : ℂ) - s - 1 + 1) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  have e2 : -(1 : ℂ) / ((θ : ℂ) - s - 1 + 1) = 1 / (s - θ) := by
    rw [show (θ : ℂ) - s - 1 + 1 = -(s - θ) by ring, div_neg, neg_div, neg_neg]
  rw [e1, e2, mul_one_div, mul_div_assoc, sub_div]
  ring

/-- `L(f, s − k) = L(n^k f, s)`. -/
theorem LSeries_sub_natCast (f : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries f (s - k) = LSeries (fun n => f n * (n : ℂ) ^ k) s := by
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_of_ne_zero hn, term_of_ne_zero hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_sub _ _ hn', Complex.cpow_natCast, div_div_eq_mul_div]

/-- The prime-power tail for `ζ`: `Λ(n) n^k − log n · [n prime] n^k`. -/
noncomputable def zetaTail (k : ℕ) : ℕ → ℂ :=
  (fun n => (Λ n : ℂ) * (n : ℂ) ^ k) - logMul (powCoeff k)

theorem norm_zetaTail_le (k n : ℕ) :
    ‖zetaTail k n‖ ≤ (if n.Prime then 0 else Λ n) * (n : ℝ) ^ k := by
  simp only [zetaTail, Pi.sub_apply, logMul, powCoeff, primeCoeff, powWeight]
  split_ifs with hn
  · rw [vonMangoldt_apply_prime hn, Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
    push_cast; simp
  · simp only [Complex.ofReal_zero, mul_zero, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg vonMangoldt_nonneg, norm_pow, Complex.norm_natCast, le_refl]

theorem abscissa_zetaTail_le (k : ℕ) :
    abscissaOfAbsConv (zetaTail k) ≤ ((k : ℝ) + 1 / 2 : ℝ) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  have hy' : 1 / 2 < y - k := by linarith
  refine Summable.of_norm_bounded (summable_vonMangoldt_nonprime_rpow hy') fun n => ?_
  have hnn : 0 ≤ (if n.Prime then 0 else Λ n) := by
    split_ifs
    exacts [le_rfl, vonMangoldt_nonneg]
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [if_pos rfl]; exact mul_nonneg hnn (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [if_neg hn]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [Complex.ofReal_re]
    calc ‖zetaTail k n‖ / (n : ℝ) ^ y ≤ (if n.Prime then 0 else Λ n) * (n : ℝ) ^ k / (n : ℝ) ^ y := by
          gcongr; exact norm_zetaTail_le k n
      _ = (if n.Prime then 0 else Λ n) * (n : ℝ) ^ (-(y - k)) := by
          rw [mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_sub hn0]
          congr 2; ring

theorem riemannZeta₁_eq {w : ℂ} (hw : w ≠ 1) : riemannZeta₁ w = (w - 1) * riemannZeta w := by
  rw [riemannZeta_eq_inv_sub_mul hw, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hw), one_mul]

/-- `ζ₁(σ) = (σ − 1) ζ(σ) ≠ 0` for real `σ > 1/2` (with `ζ(σ) < 0` on `(1/2, 1)`). -/
theorem riemannZeta₁_real_ne_zero {σ : ℝ} (hσ : 1 / 2 < σ) : riemannZeta₁ σ ≠ 0 := by
  rcases lt_trichotomy σ 1 with h | h | h
  · have h1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h.ne
    rw [riemannZeta₁_eq h1]
    exact mul_ne_zero (sub_ne_zero.2 h1) (riemannZeta_ne_zero_of_mem_Ioo (by linarith) h)
  · rw [h, Complex.ofReal_one, riemannZeta₁_one]; exact one_ne_zero
  · have h1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h.ne'
    rw [riemannZeta₁_eq h1]
    exact mul_ne_zero (sub_ne_zero.2 h1) (riemannZeta_ne_zero_of_one_lt_re (by simpa using h))

/-- `ζ₁′/ζ₁(w) = 1/(w − 1) − Σ Λ(n) n^{−w}` on `Re w > 1`. -/
theorem logDeriv_riemannZeta₁ {w : ℂ} (hw : 1 < w.re) :
    logDeriv riemannZeta₁ w = 1 / (w - 1) - LSeries (fun n => (Λ n : ℂ)) w := by
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have hev : riemannZeta₁ =ᶠ[𝓝 w] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hw1] with z hz using riemannZeta₁_eq hz
  have hz := riemannZeta_ne_zero_of_one_lt_re hw
  have hd : HasDerivAt (fun z => (z - 1) * riemannZeta z)
      (1 * riemannZeta w + (w - 1) * deriv riemannZeta w) w :=
    ((hasDerivAt_id w).sub_const 1).mul (differentiableAt_riemannZeta hw1).hasDerivAt
  rw [logDeriv_apply, hev.deriv_eq, hd.deriv, hev.eq_of_nhds,
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  have h1 : w - 1 ≠ 0 := sub_ne_zero.2 hw1
  field_simp
  ring

/-- **Proposition 3₀, (2) ⇒ zero-free and (3) ⇒ zero-free, at one exponent** (ARCS paper §4.4): if the
gap `C x^θ − η E_k(x)` (`η = ±1`, `θ ≥ k + 1/2`) is non-negative, then `ζ(ρ − k) ≠ 0` whenever
`Re ρ > θ`. -/
theorem prop30_zeroFree_of_gap (k : ℕ) {θ C η : ℝ} (hη : η = 1 ∨ η = -1)
    (hθ : (k : ℝ) + 1 / 2 ≤ θ) (hg0 : ∀ t, 0 ≤ momentGap C θ η k t) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta (ρ - k) ≠ 0 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hθ0 : 0 ≤ θ := by linarith
  have habs : |η| = 1 := by rcases hη with rfl | rfl <;> simp
  have hη0 : (η : ℂ) ≠ 0 := by rcases hη with rfl | rfl <;> simp
  set f : Unit → ℂ → ℂ := fun _ s => riemannZeta₁ (s - k)
  set Φ : ℂ → ℂ := fun s => (η : ℂ) * (LSeries (powCoeff k) s - liMellin k s)
  set h : ℂ → ℂ := fun s => (η : ℂ) * (LSeries (zetaTail k) s -
    dslope (fun u : ℂ => (2 : ℂ) ^ u) 0 ((k : ℂ) + 1 - s))
  have hfan : ∀ i, AnalyticOnNhd ℂ (f i) univ := fun _ z _ =>
    (differentiable_riemannZeta₁.comp (differentiable_id.sub_const _)).analyticAt z
  have hreal : ∀ i ∈ (Finset.univ : Finset Unit), ∀ σ : ℝ, θ < σ → f i σ ≠ 0 := by
    intro _ _ σ hσ
    simp only [f]
    rw [show (σ : ℂ) - k = ((σ - k : ℝ) : ℂ) by push_cast; ring]
    exact riemannZeta₁_real_ne_zero (by linarith)
  have h2an : Differentiable ℂ fun u : ℂ => (2 : ℂ) ^ u := fun u =>
    differentiableAt_id.const_cpow (Or.inl two_ne_zero)
  have hh : AnalyticOnNhd ℂ h {s | θ < s.re} := by
    intro s hs
    have hs' : θ < s.re := hs
    refine analyticAt_const.mul ((LSeries_analyticOnNhd _ s ?_).sub ?_)
    · exact (abscissa_zetaTail_le k).trans_lt (by exact_mod_cast (show (k : ℝ) + 1 / 2 < s.re by linarith))
    · exact ((h2an.analyticAt _).dslope 0).comp (analyticAt_const.sub analyticAt_id)
  have hD : ∀ s : ℂ, θ + 1 < s.re →
      deriv Φ s = ∑ i ∈ (Finset.univ : Finset Unit), (η : ℂ) * logDeriv (f i) s + h s := by
    intro s hs
    have hsk : (k : ℝ) + 1 < s.re := by linarith
    set u : ℂ := (k : ℂ) + 1 - s
    have hu0 : u ≠ 0 := by intro h0; have := congrArg Complex.re h0; simp [u] at this; linarith
    have hab : abscissaOfAbsConv (powCoeff k) < s.re :=
      (abscissa_powCoeff_le k).trans_lt (by exact_mod_cast hsk)
    have hΦ : HasDerivAt Φ ((η : ℂ) * (-LSeries (logMul (powCoeff k)) s - (2 : ℂ) ^ u / u)) s :=
      ((LSeries_hasDerivAt hab).sub (hasDerivAt_liMellin k hsk)).const_mul _
    rw [hΦ.deriv, Finset.univ_unique, Finset.sum_singleton]
    have hlog : logDeriv (f default) s = 1 / (s - k - 1) -
        LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ k) s := by
      have hc : f default = riemannZeta₁ ∘ fun z => z - (k : ℂ) := rfl
      have hg : DifferentiableAt ℂ (fun z : ℂ => z - (k : ℂ)) s := by fun_prop
      rw [hc, logDeriv_comp (differentiable_riemannZeta₁ _) hg,
        deriv_sub_const, deriv_id'', mul_one,
        logDeriv_riemannZeta₁ (by simp; linarith), LSeries_sub_natCast]
    have htail : LSeries (zetaTail k) s = LSeries (fun n => (Λ n : ℂ) * (n : ℂ) ^ k) s -
        LSeries (logMul (powCoeff k)) s := by
      have h1 : LSeriesSummable (zetaTail k) s := LSeriesSummable_of_abscissaOfAbsConv_lt_re
        ((abscissa_zetaTail_le k).trans_lt (by exact_mod_cast (show (k : ℝ) + 1 / 2 < s.re by linarith)))
      have h2 : LSeriesSummable (logMul (powCoeff k)) s := LSeriesSummable_logMul_of_lt_re hab
      have := LSeries_add h1 h2
      rw [zetaTail, sub_add_cancel] at this
      rw [this, add_sub_cancel_right]; rfl
    have hds : dslope (fun u : ℂ => (2 : ℂ) ^ u) 0 u = ((2 : ℂ) ^ u - 1) / u := by
      rw [dslope_of_ne _ hu0, slope_def_field, Complex.cpow_zero, sub_zero]
    simp only [h]
    rw [hlog, htail, hds]
    have hsk1 : s - (k : ℂ) - 1 = -u := by simp only [u]; ring
    rw [hsk1]
    field_simp
    ring
  have hfin : analyticOrderAt (f ()) ρ ≠ ⊤ := by
    refine (hfan ()).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := ((θ + 1 : ℝ) : ℂ)) trivial trivial ?_
    rw [analyticOrderAt_eq_zero.2 (Or.inr (hreal () (Finset.mem_univ _) _ (by linarith)))]
    exact ENat.zero_ne_top
  have hmain := landau_zero_engine (Finset.univ : Finset Unit) (fun _ => (η : ℂ)) f h θ (θ + 1)
    hθ0 (by linarith) (momentGap C θ η k) hg0
    (fun t ht => by simp only [momentGap, if_neg (not_lt.2 ht.2.le)])
    (locallyIntegrableOn_momentGap C θ η habs k hθ0) (-(max θ (k + 1)))
    (momentGap_isBigO C θ η habs k hθ0) C Φ
    (fun σ hσ => (momentGap_mellin C θ η k (s := σ) (by simp; linarith) (by simp; linarith)).1)
    (fun s hs => (momentGap_mellin C θ η k (by linarith) (by linarith)).2)
    (fun i _ => (hfan i).mono (subset_univ _)) hreal hh hD hρ
    (fun _ => analyticOrderNatAt (f ()) ρ) (fun _ _ => (Nat.cast_analyticOrderNatAt hfin).symm)
  rw [Finset.univ_unique, Finset.sum_singleton] at hmain
  have hm0 : analyticOrderNatAt (f ()) ρ = 0 := by
    have := (mul_eq_zero.1 hmain).resolve_left hη0
    exact_mod_cast this
  have hord : analyticOrderAt (f ()) ρ = 0 := by
    rw [← Nat.cast_analyticOrderNatAt hfin, hm0]; rfl
  have hne : riemannZeta₁ (ρ - k) ≠ 0 := by
    rcases analyticOrderAt_eq_zero.1 hord with h' | h'
    · exact absurd (hfan () ρ trivial) h'
    · exact h'
  by_cases h1 : ρ - k = 1
  · rw [h1]; exact riemannZeta_one_ne_zero
  · rw [riemannZeta_eq_inv_sub_mul h1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.2 h1)) hne

/-- **The functional equation step**: no zero of `ζ` on `Re s > 1/2` gives the Riemann hypothesis
in Mathlib's form (zeros off the negative even integers lie on `Re s = 1/2`). -/
theorem riemannHypothesis_of_zeroFree (h : ∀ w : ℂ, 1 / 2 < w.re → riemannZeta w ≠ 0) :
    RiemannHypothesis := by
  intro s hs hnt _
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · set s' : ℂ := 1 - s
    have hs're : 1 / 2 < s'.re := by simp only [s', Complex.sub_re, Complex.one_re]; linarith
    have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hs; norm_num at hs
    have hn : ∀ n : ℕ, s' ≠ -n := by
      intro n hn'
      have := congrArg Complex.re hn'
      simp only [Complex.neg_re, Complex.natCast_re] at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs'1 : s' ≠ 1 := by
      intro h1; apply hs0; simp only [s'] at h1; linear_combination -h1
    have hfe := riemannZeta_one_sub hn hs'1
    rw [show 1 - s' = s by simp only [s']; ring, hs] at hfe
    have hΓ : Complex.Gamma s' ≠ 0 := Complex.Gamma_ne_zero hn
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    have hpow : (2 * (Real.pi : ℂ)) ^ (-s') ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hpi]; exact Complex.exp_ne_zero _
    have hz := h s' hs're
    have hcos : Complex.cos (Real.pi * s' / 2) = 0 := by
      rcases mul_eq_zero.1 hfe.symm with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · rcases mul_eq_zero.1 h2 with h3 | h3
          · rcases mul_eq_zero.1 h3 with h4 | h4
            · norm_num at h4
            · exact absurd h4 hpow
          · exact absurd h3 hΓ
        · exact h2
      · exact absurd h1 hz
    obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.1 hcos
    have hpi' : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs'm : s' = 2 * m + 1 := by
      have h2 : (Real.pi : ℂ) * (s' - (2 * m + 1)) = 0 := by linear_combination 2 * hm
      have := (mul_eq_zero.1 h2).resolve_left hpi'
      linear_combination this
    have hsm : s = -2 * m := by
      have : s = 1 - s' := by simp only [s']; ring
      rw [this, hs'm]; ring
    have hm0 : 0 ≤ m := by
      have := congrArg Complex.re hs'm
      simp at this
      have : (-1 : ℝ) < m := by linarith
      exact_mod_cast (show (-1 : ℤ) < m by exact_mod_cast this)
    rcases (show m = 0 ∨ 1 ≤ m by omega) with h0 | h1
    · apply hs0; rw [hsm, h0]; simp
    · apply hnt
      refine ⟨(m - 1).toNat, ?_⟩
      rw [hsm]
      have : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have : (((m - 1).toNat : ℕ) : ℂ) = (m : ℂ) - 1 := by exact_mod_cast this
      rw [this]; ring
  · exact h s hgt hs

/-- **Proposition 3₀, (2) ⇒ (1)** (ARCS paper §4.4): if for every `ε > 0` there is `C_ε` with
`E_k(N) ≤ C_ε N^{k+1/2+ε}` for all `N ≥ 2`, then the Riemann hypothesis holds. Here
`E_k(N) = Σ_{p≤N} p^k − Li_k(N)` and `Li_k(N) = li(N^{k+1}) − li(2^{k+1})`; the constant does not
affect the bounds. -/
theorem prop30_two_imp_RH (k : ℕ)
    (h2 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      momentError k N ≤ C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_zeroFree fun w hw => ?_
  set ε := (w.re - 1 / 2) / 2
  obtain ⟨C, hC⟩ := h2 ε (by simp only [ε]; linarith)
  have hθ0 : 0 ≤ (k : ℝ) + 1 / 2 + ε := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; simp only [ε]; linarith
  have := prop30_zeroFree_of_gap k (Or.inl rfl) (by simp only [ε]; linarith)
    (momentGap_nonneg_upper k hθ0 hC) (ρ := w + k)
    (by simp only [ε, Complex.add_re, Complex.natCast_re]; linarith)
  rwa [add_sub_cancel_right] at this

/-- **Proposition 3₀, (3) ⇒ (1)**: the same with the lower bound `E_k(N) ≥ −C_ε N^{k+1/2+ε}`. -/
theorem prop30_three_imp_RH (k : ℕ)
    (h3 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      -(C * (N : ℝ) ^ ((k : ℝ) + 1 / 2 + ε)) ≤ momentError k N) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_zeroFree fun w hw => ?_
  set ε := (w.re - 1 / 2) / 2
  obtain ⟨C, hC⟩ := h3 ε (by simp only [ε]; linarith)
  have := prop30_zeroFree_of_gap k (Or.inr rfl) (by simp only [ε]; linarith)
    (momentGap_nonneg_lower k (by simp only [ε]; linarith) hC) (ρ := w + k)
    (by simp only [ε, Complex.add_re, Complex.natCast_re]; linarith)
  rwa [add_sub_cancel_right] at this

end LeanBase.Classical
