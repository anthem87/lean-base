module

public import LeanBase.Classical.ArcProp3
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false

/-!
# The logarithmic integral and its Mellin transform (ARCS paper §4.4, Proposition 3₀)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/LogIntegral.lean), same author and licence.

* `liK k x = ∫_2^x t^k dt / log t` (`0` for `x ≤ 2`). It differs from `li(x^{k+1})` by the constant
  `li(2^{k+1})`, which does not affect bounds `O(x^{k+1/2+ε})`.
* `liMellin k s = ∫_2^∞ t^{k−s} dt / log t`, written as `mellin φ (k + 1 − s)` with
  `φ = 1_{t>2}/log t`; `hasDerivAt_liMellin`: its derivative is `2^{k+1−s}/(k + 1 − s)`
  (the ARCS paper's `∫_2^∞ t^{k−s} dt / log t = −log(s − k − 1) + (entire)`, in derivative form).
* `liK_mellin`: `∫_2^∞ Li_k(x) x^{−s−1} dx = liMellin k s / s` on `Re s > k + 1` (integration by
  parts).
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set MeasureTheory Asymptotics

/-- The integrand `t^k / log t` on `t > 2`, extended by `0`. -/
noncomputable def liIntegrand (k : ℕ) (t : ℝ) : ℝ := if 2 < t then t ^ k / Real.log t else 0

/-- `Li_k(x) = ∫_2^x t^k dt / log t` for `x ≥ 2`, `0` for `x ≤ 2`. It differs from
`li(x^{k+1}) = ∫^x t^k dt / log t` by a constant. -/
noncomputable def liK (k : ℕ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, liIntegrand k t

theorem liIntegrand_nonneg (k : ℕ) (t : ℝ) : 0 ≤ liIntegrand k t := by
  simp only [liIntegrand]
  split_ifs with h
  · have : 0 < Real.log t := Real.log_pos (by linarith)
    have : 0 ≤ t ^ k := pow_nonneg (by linarith) k
    positivity
  · exact le_rfl

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem liIntegrand_le (k : ℕ) {t x : ℝ} (ht : t ≤ x) : liIntegrand k t ≤ |x| ^ k / Real.log 2 := by
  simp only [liIntegrand]
  split_ifs with h
  · have hl : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) h.le
    have h2 := log_two_pos'
    have hpow : t ^ k ≤ |x| ^ k := pow_le_pow_left₀ (by linarith) (ht.trans (le_abs_self x)) k
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    calc t ^ k / Real.log t ≤ |x| ^ k / Real.log t := div_le_div_of_nonneg_right hpow hlt.le
      _ ≤ |x| ^ k / Real.log 2 := div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) _) h2 hl
  · have := log_two_pos'; positivity

theorem measurable_liIntegrand (k : ℕ) : Measurable (liIntegrand k) :=
  Measurable.ite measurableSet_Ioi ((measurable_id.pow_const k).div Real.measurable_log)
    measurable_const

theorem intervalIntegrable_liIntegrand (k : ℕ) (a b : ℝ) :
    IntervalIntegrable (liIntegrand k) volume a b := by
  refine (intervalIntegrable_iff).2 ?_
  refine Measure.integrableOn_of_bounded (M := (|a| + |b|) ^ k / Real.log 2)
    (by simp [Real.volume_uIoc]) (measurable_liIntegrand k).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht => ?_
  rw [Real.norm_of_nonneg (liIntegrand_nonneg k t)]
  have htb : t ≤ |a| + |b| := by
    have := (Set.uIoc_subset_uIcc ht).2
    have h1 : max a b ≤ |a| + |b| :=
      max_le (by linarith [le_abs_self a, abs_nonneg b]) (by linarith [le_abs_self b, abs_nonneg a])
    exact this.trans h1
  refine (liIntegrand_le k htb).trans ?_
  rw [abs_of_nonneg (by positivity)]

theorem continuous_liK (k : ℕ) : Continuous (liK k) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_liIntegrand k) 0

theorem liK_of_le_two (k : ℕ) {x : ℝ} (hx : x ≤ 2) : liK k x = 0 := by
  rw [liK, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
  · simp
  · have : t ≤ 2 := by
      rcases Set.mem_uIcc.1 ht with h | h
      · linarith [h.2]
      · linarith [h.2]
    simp [liIntegrand, not_lt.2 this]

theorem hasDerivAt_liK (k : ℕ) {x : ℝ} (hx : 2 < x) : HasDerivAt (liK k) (liIntegrand k x) x := by
  refine intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_liIntegrand k 0 x)
    (measurable_liIntegrand k).stronglyMeasurable.stronglyMeasurableAtFilter ?_
  have hev : liIntegrand k =ᶠ[𝓝 x] fun t => t ^ k / Real.log t := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp [liIntegrand, show 2 < t from ht]
  refine (ContinuousAt.congr ?_ hev.symm)
  exact (continuousAt_id.pow k).div (Real.continuousAt_log (by linarith))
    (Real.log_pos (by linarith)).ne'

theorem liK_mono (k : ℕ) : Monotone (liK k) := by
  intro x y hxy
  rw [liK, liK, ← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_liIntegrand k 0 x) (intervalIntegrable_liIntegrand k x y)]
  have : 0 ≤ ∫ t in x..y, liIntegrand k t :=
    intervalIntegral.integral_nonneg hxy fun t _ => liIntegrand_nonneg k t
  linarith

theorem liK_nonneg (k : ℕ) (x : ℝ) : 0 ≤ liK k x := by
  rcases le_or_gt x 2 with h | h
  · rw [liK_of_le_two k h]
  · rw [← liK_of_le_two k le_rfl]; exact liK_mono k h.le

theorem liK_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : liK k x ≤ x ^ (k + 1) / Real.log 2 := by
  have h := intervalIntegral.integral_mono_on hx (intervalIntegrable_liIntegrand k 0 x)
    (intervalIntegrable_const (c := |x| ^ k / Real.log 2)) fun t ht => liIntegrand_le k ht.2
  rw [intervalIntegral.integral_const, smul_eq_mul, abs_of_nonneg hx] at h
  rw [liK]
  calc _ ≤ (x - 0) * (x ^ k / Real.log 2) := h
    _ = x ^ (k + 1) / Real.log 2 := by ring

/-- `φ(t) = 1/log t` on `t > 2`, extended by `0`; `J(s) = mellin φ (k + 1 − s)`. -/
noncomputable def invLogTail (t : ℝ) : ℂ := ((if 2 < t then (Real.log t)⁻¹ else 0 : ℝ) : ℂ)

/-- `J(s) = ∫_2^∞ t^{k−s} dt / log t`. -/
noncomputable def liMellin (k : ℕ) (s : ℂ) : ℂ := mellin invLogTail ((k : ℂ) + 1 - s)

theorem norm_invLogTail_le (t : ℝ) : ‖invLogTail t‖ ≤ (Real.log 2)⁻¹ := by
  simp only [invLogTail, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos (inv_pos.2 (Real.log_pos (by linarith)))]
    exact inv_anti₀ log_two_pos' (Real.log_le_log (by norm_num) h.le)
  · simp [log_two_pos'.le]

theorem locallyIntegrableOn_invLogTail : LocallyIntegrableOn invLogTail (Ioi 0) := by
  have hm : Measurable invLogTail :=
    Complex.measurable_ofReal.comp (Measurable.ite measurableSet_Ioi Real.measurable_log.inv
      measurable_const)
  refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K _ hK =>
    Measure.integrableOn_of_bounded hK.measure_lt_top.ne hm.aestronglyMeasurable
      (Eventually.of_forall fun t => norm_invLogTail_le t)

theorem invLogTail_isBigO : invLogTail =O[atTop] (· ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (Real.log 2)⁻¹ (Eventually.of_forall fun t => ?_)
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_invLogTail_le t

/-- `J′(s) = 2^{k+1−s}/(k + 1 − s)` on `Re s > k + 1`. -/
theorem hasDerivAt_liMellin (k : ℕ) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    HasDerivAt (liMellin k) ((2 : ℂ) ^ ((k : ℂ) + 1 - s) / ((k : ℂ) + 1 - s)) s := by
  set u : ℂ := (k : ℂ) + 1 - s
  have hu : u.re < 0 := by simp [u]; linarith
  have hd := (mellin_hasDerivAt_of_isBigO_rpow locallyIntegrableOn_invLogTail invLogTail_isBigO
    (s := u) hu (isBigO_bot_of_vanish (fun t ht => by
      simp [invLogTail, not_lt.2 (show t ≤ 2 by linarith [ht.2])]) (u.re - 1))
    (by linarith)).2
  have hval : mellin (fun t => (Real.log t : ℝ) • invLogTail t) u = -(2 : ℂ) ^ u / u := by
    have heq : EqOn (fun t : ℝ => (t : ℂ) ^ (u - 1) • ((Real.log t : ℝ) • invLogTail t))
        ((Ioi (2 : ℝ)).indicator fun t : ℝ => (t : ℂ) ^ (u - 1)) (Ioi 0) := by
      intro t _
      simp only [invLogTail, Set.indicator, mem_Ioi]
      split_ifs with h
      · have hl' : (Real.log t : ℂ) ≠ 0 := by
          exact_mod_cast (Real.log_pos (by linarith)).ne'
        rw [Complex.real_smul, smul_eq_mul]; push_cast
        rw [mul_inv_cancel₀ hl', mul_one]
      · simp
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi heq, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, show max (0 : ℝ) 2 = 2 by norm_num,
      integral_Ioi_cpow_of_lt (by simp; linarith) (by norm_num : (0 : ℝ) < 2)]
    simp only [sub_add_cancel]; push_cast; ring
  have h2 : HasDerivAt (fun x : ℂ => (k : ℂ) + 1 - x) (-1) s := by
    simpa using (hasDerivAt_id' s).const_sub ((k : ℂ) + 1)
  have hcomp : HasDerivAt (fun s => mellin invLogTail ((k : ℂ) + 1 - s))
      (mellin (fun t => Real.log t • invLogTail t) u * -1) s :=
    HasDerivAt.comp (h₂ := mellin invLogTail) s (show HasDerivAt (mellin invLogTail)
      (mellin (fun t => Real.log t • invLogTail t) u) ((k : ℂ) + 1 - s) from hd) h2
  rw [hval] at hcomp
  show HasDerivAt (fun s => mellin invLogTail ((k : ℂ) + 1 - s)) _ s
  convert hcomp using 1
  ring

/-- **The Mellin transform of `Li_k`** (integration by parts): for `Re s > k + 1`,
`∫_2^∞ Li_k(x) x^{−s−1} dx = J(s)/s`. -/
theorem liK_mellin (k : ℕ) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    IntegrableOn (fun x : ℝ => (liK k x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 2) ∧
      ∫ x in Ioi (2 : ℝ), (liK k x : ℂ) * (x : ℂ) ^ (-s - 1) = liMellin k s / s := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
  have hσ : 0 < s.re := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set u : ℝ → ℂ := fun x => (liK k x : ℂ)
  set u' : ℝ → ℂ := fun x => (liIntegrand k x : ℂ)
  set v : ℝ → ℂ := fun x => (x : ℂ) ^ (-s - 1 + 1) / (-s - 1 + 1)
  set v' : ℝ → ℂ := fun x => (x : ℂ) ^ (-s - 1)
  have hu : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt u (u' x) x := fun x hx =>
    (hasDerivAt_liK k hx).ofReal_comp
  have hv : ∀ x ∈ Ioi (2 : ℝ), HasDerivAt v (v' x) x := fun x hx =>
    hasDerivAt_ofReal_cpow_const' (r := -s - 1) (by simp only [mem_Ioi] at hx; linarith)
      (fun h => hs0 (by linear_combination -h))
  have hlik : ∀ x : ℝ, 0 ≤ x → ‖u x‖ ≤ x ^ (k + 1) / Real.log 2 := fun x hx => by
    simp only [u, Complex.norm_real, Real.norm_of_nonneg (liK_nonneg k x)]
    exact liK_le k hx
  have hint : IntegrableOn (fun x : ℝ => x ^ ((k : ℝ) - s.re)) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hmeas_cpow : ∀ a : ℂ, AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ a)
      (volume.restrict (Ioi 2)) := fun a =>
    ContinuousOn.aestronglyMeasurable (fun x hx => (continuousAt_ofReal_cpow_const _ _
      (Or.inr (by simp only [mem_Ioi] at hx; linarith))).continuousWithinAt) measurableSet_Ioi
  have hpow : ∀ x : ℝ, 0 < x → (x : ℝ) ^ (k + 1) * x ^ (-s.re - 1) = x ^ ((k : ℝ) - s.re) := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]; congr 1; push_cast; ring
  have huv' : IntegrableOn (u * v') (Ioi 2) := by
    refine (hint.const_mul (Real.log 2)⁻¹).mono' ?_ ?_
    · exact ((Complex.continuous_ofReal.comp (continuous_liK k)).aestronglyMeasurable).mul
        (hmeas_cpow _)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : 0 < x := by simp only [mem_Ioi] at hx; linarith
      simp only [Pi.mul_apply, v', norm_mul, norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      calc ‖u x‖ * x ^ (-s.re - 1) ≤ x ^ (k + 1) / Real.log 2 * x ^ (-s.re - 1) := by
            gcongr; exact hlik x hx0.le
        _ = (Real.log 2)⁻¹ * x ^ ((k : ℝ) - s.re) := by rw [← hpow x hx0]; ring
  have hu'v : IntegrableOn (u' * v) (Ioi 2) := by
    refine (hint.const_mul ((Real.log 2)⁻¹ * ‖s‖⁻¹)).mono' ?_ ?_
    · refine ((Complex.measurable_ofReal.comp (measurable_liIntegrand k)).aestronglyMeasurable).mul
        (ContinuousOn.aestronglyMeasurable (fun x hx => ((continuousAt_ofReal_cpow_const _ _
          (Or.inr (by simp only [mem_Ioi] at hx; linarith))).div_const _).continuousWithinAt)
          measurableSet_Ioi)
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : 0 < x := by simp only [mem_Ioi] at hx; linarith
      simp only [Pi.mul_apply, u', v, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.norm_real, Real.norm_of_nonneg (liIntegrand_nonneg k x)]
      simp only [show -s - 1 + 1 = -s by ring, Complex.neg_re, norm_neg]
      have h1 := liIntegrand_le k (le_refl x)
      rw [abs_of_pos hx0] at h1
      have hxk : x ^ k * x ^ (-s.re) = x ^ ((k : ℝ) - s.re) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1
      have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
      calc liIntegrand k x * (x ^ (-s.re) / ‖s‖) ≤ x ^ k / Real.log 2 * (x ^ (-s.re) / ‖s‖) := by
            gcongr
        _ = (Real.log 2)⁻¹ * ‖s‖⁻¹ * x ^ ((k : ℝ) - s.re) := by rw [← hxk]; field_simp
  have h_zero : Tendsto (u * v) (𝓝[>] 2) (𝓝 0) := by
    have hc : ContinuousAt (u * v) 2 := by
      refine (Complex.continuous_ofReal.comp (continuous_liK k)).continuousAt.mul ?_
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (by norm_num))).div_const _
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 2))
    simpa [u, liK_of_le_two k le_rfl] using this
  have h_infty : Tendsto (u * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun x : ℝ => (Real.log 2)⁻¹ * ‖s‖⁻¹ * x ^ ((k : ℝ) + 1 - s.re)) atTop
        (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (show 0 < s.re - (k + 1) by linarith)).const_mul
        ((Real.log 2)⁻¹ * ‖s‖⁻¹)
      simp only [mul_zero] at this
      refine this.congr' (Eventually.of_forall fun x => ?_)
      congr 2; ring
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with x hx0
    simp only [Pi.mul_apply, v, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [show -s - 1 + 1 = -s by ring, Complex.neg_re, norm_neg]
    have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
    have hxk : x ^ (k + 1) * x ^ (-s.re) = x ^ ((k : ℝ) + 1 - s.re) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast; ring
    calc ‖u x‖ * (x ^ (-s.re) / ‖s‖) ≤ x ^ (k + 1) / Real.log 2 * (x ^ (-s.re) / ‖s‖) := by
          gcongr; exact hlik x hx0.le
      _ = (Real.log 2)⁻¹ * ‖s‖⁻¹ * x ^ ((k : ℝ) + 1 - s.re) := by rw [← hxk]; field_simp
  refine ⟨huv', ?_⟩
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  rw [hibp]
  -- `∫ u′ v = −J(s)/s`
  have hJ : ∫ x in Ioi (2 : ℝ), u' x * v x = -(liMellin k s / s) := by
    have heq : EqOn (fun t : ℝ => (t : ℂ) ^ ((k : ℂ) + 1 - s - 1) • invLogTail t)
        ((Ioi (2 : ℝ)).indicator fun x => -(s * (u' x * v x))) (Ioi 0) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [invLogTail, Set.indicator, mem_Ioi, u', v, liIntegrand]
      split_ifs with h
      · have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
        have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
        have e : (t : ℂ) ^ ((k : ℂ) + 1 - s - 1) = (t : ℂ) ^ (k : ℂ) * (t : ℂ) ^ (-s) := by
          rw [← Complex.cpow_add _ _ ht']; ring_nf
        rw [e, show -s - 1 + 1 = -s by ring, Complex.cpow_natCast, smul_eq_mul]
        push_cast
        field_simp
      · simp
    have hm : liMellin k s = ∫ x in Ioi (2 : ℝ), -(s * (u' x * v x)) := by
      rw [liMellin, mellin, setIntegral_congr_fun measurableSet_Ioi heq,
        setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, show max (0 : ℝ) 2 = 2 by norm_num]
    rw [hm, integral_neg, integral_const_mul]
    field_simp
  rw [hJ]
  ring

end LeanBase.Classical
