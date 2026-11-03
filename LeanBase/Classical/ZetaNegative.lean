module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Analysis.Calculus.DSlope
set_option autoImplicit false

/-!
# `ζ(σ) < 0` on `(0, 1)` via the Dirichlet eta function (ARCS paper §4.4, proof of Proposition 3₀)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/ZetaNegative.lean), same author and licence.

* `etaPair s = Σ_k [(2k+1)^{−s} − (2k+2)^{−s}]`: `η` with its terms paired. By the mean value
  theorem each pair is `≤ |s| (2k+1)^{−Re s − 1}`, so the series converges absolutely and locally
  uniformly on `Re s > 0`, and `etaPair` is holomorphic there (`differentiableOn_etaPair`).
* `etaPair_eq_of_one_lt`: `η(s) = (1 − 2^{1−s}) ζ(s)` on `Re s > 1` (split `ζ` into odd and even
  terms).
* `etaZeta s = −dslope (2^{1−·}) 1 s · ζ₁(s)` is entire (Mathlib's `riemannZeta₁`) and equals
  `(1 − 2^{1−s}) ζ(s)` for `s ≠ 1`; the identity theorem gives `etaPair = etaZeta` on `Re s > 0`.
* `riemannZeta_neg_of_mem_Ioo`: for `0 < σ < 1`, `η(σ) > 0` term by term and `1 − 2^{1−σ} < 0`,
  so `ζ(σ)` is a negative real number.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set

/-- The paired terms of `η(s) = Σ (−1)^{n−1} n^{−s}`: `(2k+1)^{−s} − (2k+2)^{−s}`. -/
noncomputable def etaTerm (s : ℂ) (k : ℕ) : ℂ :=
  ((2 * k + 1 : ℝ) : ℂ) ^ (-s) - ((2 * k + 2 : ℝ) : ℂ) ^ (-s)

/-- `η(s)` with the terms paired; the paired series converges absolutely on `Re s > 0`. -/
noncomputable def etaPair (s : ℂ) : ℂ := ∑' k, etaTerm s k

/-- `|(a)^{−s} − (a+1)^{−s}| ≤ |s| a^{−Re s − 1}` for `a ≥ 1`, `Re s ≥ −1` (mean value). -/
theorem norm_etaTerm_le (s : ℂ) (hs : -1 ≤ s.re) (k : ℕ) :
    ‖etaTerm s k‖ ≤ ‖s‖ * (2 * k + 1 : ℝ) ^ (-s.re - 1) := by
  set a : ℝ := 2 * k + 1
  have ha : 1 ≤ a := by simp only [a]; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  set f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hderiv : ∀ x ∈ Icc a (a + 1), HasDerivWithinAt f (-s * (x : ℂ) ^ (-s - 1)) (Icc a (a + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp only [f, neg_zero, Complex.cpow_zero, zero_mul]
      exact (hasDerivAt_const x (1 : ℂ)).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.2 hs0)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a (a + 1), ‖-s * (x : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hx0]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith))
      (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1) ⟨by linarith, le_rfl⟩
  rw [show a + 1 - a = 1 by ring, mul_one] at h
  rw [etaTerm, ← norm_neg, neg_sub]
  have e : ((2 * k + 2 : ℝ) : ℂ) = ((a + 1 : ℝ) : ℂ) := by simp only [a]; push_cast; ring
  rw [e]
  exact h

theorem summable_odd_rpow {δ : ℝ} (hδ : 0 < δ) :
    Summable fun k : ℕ => (2 * k + 1 : ℝ) ^ (-δ - 1) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -δ - 1 < -1 by linarith))
  refine h.of_nonneg_of_le (fun k => Real.rpow_nonneg (by positivity) _) fun k => ?_
  push_cast
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
    (by linarith)

theorem differentiableAt_etaTerm (k : ℕ) (s : ℂ) : DifferentiableAt ℂ (fun s => etaTerm s k) s := by
  have h1 : ((2 * k + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * k + 1).ne'
  have h2 : ((2 * k + 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * k + 2).ne'
  exact (differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
    (differentiableAt_id.neg.const_cpow (Or.inl h2))

/-- `η` (paired) is holomorphic on `Re s > 0`. -/
theorem differentiableOn_etaPair : DifferentiableOn ℂ etaPair {s | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2
  set R := ‖s₀‖ + 1
  set U : Set ℂ := {s | δ < s.re} ∩ Metric.ball 0 R
  have hU : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hmem : s₀ ∈ U := ⟨by simp only [δ, mem_setOf_eq]; linarith, by simp [R]⟩
  have hd : DifferentiableOn ℂ etaPair U := by
    refine differentiableOn_tsum_of_summable_norm ((summable_odd_rpow (half_pos hs₀')).mul_left R)
      (fun k => fun s _ => (differentiableAt_etaTerm k s).differentiableWithinAt) hU
      fun k w hw => ?_
    have hwre : δ < w.re := hw.1
    have hδ0 : 0 < δ := half_pos hs₀'
    have hδ : δ = s₀.re / 2 := rfl
    have hwn : ‖w‖ < R := by simpa using hw.2
    refine (norm_etaTerm_le w (by linarith) k).trans ?_
    have hk : (1 : ℝ) ≤ 2 * k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
    exact mul_le_mul hwn.le (Real.rpow_le_rpow_of_exponent_le hk (by linarith))
      (Real.rpow_nonneg (by positivity) _) (by simp only [R]; positivity)
  exact (hd s₀ hmem).differentiableAt (hU.mem_nhds hmem) |>.differentiableWithinAt

/-- `(1 − 2^{1−s}) ζ(s)`, completed at `s = 1`: an entire function. -/
noncomputable def etaZeta (s : ℂ) : ℂ :=
  -dslope (fun s : ℂ => (2 : ℂ) ^ (1 - s)) 1 s * riemannZeta₁ s

theorem differentiable_etaZeta : Differentiable ℂ etaZeta := by
  intro s
  have hg : Differentiable ℂ (fun s : ℂ => (2 : ℂ) ^ (1 - s)) := fun z =>
    (differentiableAt_const _).sub differentiableAt_id |>.const_cpow (Or.inl two_ne_zero)
  have ha : AnalyticAt ℂ (dslope (fun s : ℂ => (2 : ℂ) ^ (1 - s)) 1) s :=
    (hg.analyticAt s).dslope 1
  exact (ha.differentiableAt.neg).mul (differentiable_riemannZeta₁ s)

theorem etaZeta_eq {s : ℂ} (hs : s ≠ 1) : etaZeta s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [etaZeta, dslope_of_ne _ hs, slope_def_field, riemannZeta_eq_inv_sub_mul hs]
  simp only [sub_self, Complex.cpow_zero]
  field_simp
  ring

/-- **`η(s) = (1 − 2^{1−s}) ζ(s)` on `Re s > 1`.** -/
theorem etaPair_eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    etaPair s = (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s
  have hsum : Summable f := by
    have := Complex.summable_one_div_nat_cpow.2 hs
    exact (summable_nat_add_iff 1).2 this |>.congr fun n => by simp [f]
  have hodd : ∀ k : ℕ, f (2 * k) = ((2 * k + 1 : ℝ) : ℂ) ^ (-s) := fun k => by
    simp only [f, one_div, ← Complex.cpow_neg]; push_cast; ring_nf
  have heven : ∀ k : ℕ, f (2 * k + 1) = (2 : ℂ) ^ (-s) * f k := fun k => by
    simp only [f, one_div, ← Complex.cpow_neg]
    have e : ((2 * k + 1 : ℕ) : ℂ) + 1 = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast; ring
  have he : Summable fun k => f (2 * k) := hsum.comp_injective (fun a b h => by omega)
  have ho : Summable fun k => f (2 * k + 1) := hsum.comp_injective (fun a b h => by omega)
  have hz : riemannZeta s = ∑' n, f n := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hsplit := tsum_even_add_odd he ho
  have hB : ∑' k, f (2 * k + 1) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    simp_rw [heven]; rw [tsum_mul_left, hz]
  have hterm : ∀ k, etaTerm s k = f (2 * k) - f (2 * k + 1) := fun k => by
    rw [etaTerm, hodd, heven]
    simp only [f, one_div, ← Complex.cpow_neg]
    have e : ((2 * k + 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast; ring
  rw [etaPair, tsum_congr hterm, he.tsum_sub ho]
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  rw [h2]
  have hA : ∑' k, f (2 * k) = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by
    rw [← hB, hz, ← hsplit]; ring
  rw [hA, hB]; ring

/-- **`η(s) = (1 − 2^{1−s}) ζ(s)` on `Re s > 0`** (analytic continuation). -/
theorem etaPair_eq_etaZeta {s : ℂ} (hs : 0 < s.re) : etaPair s = etaZeta s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 := differentiableOn_etaPair.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ etaZeta {s : ℂ | 0 < s.re} := fun z _ =>
    differentiable_etaZeta.analyticAt z
  have hev : etaPair =ᶠ[𝓝 (2 : ℂ)] etaZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by norm_num)] with z hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    rw [etaPair_eq_of_one_lt hz, etaZeta_eq hz1]
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {s : ℂ | 0 < s.re} by norm_num) hev hs

/-- `η(σ) > 0` for real `σ > 0` (the paired terms are positive). -/
theorem etaPair_real_pos {σ : ℝ} (hσ : 0 < σ) :
    ∃ x : ℝ, 0 < x ∧ etaPair σ = x := by
  set t : ℕ → ℝ := fun k => (2 * k + 1 : ℝ) ^ (-σ) - (2 * k + 2 : ℝ) ^ (-σ)
  have hterm : ∀ k, etaTerm σ k = (t k : ℂ) := fun k => by
    simp only [etaTerm, t]
    push_cast
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  have ht0 : ∀ k, 0 < t k := fun k => by
    simp only [t, sub_pos]
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by linarith) (by linarith)
  have hsumC : Summable fun k => etaTerm σ k :=
    Summable.of_norm_bounded ((summable_odd_rpow hσ).mul_left ‖(σ : ℂ)‖) fun k =>
      by simpa using norm_etaTerm_le σ (by simp; linarith) k
  have hsumR : Summable t := by
    have : Summable fun k => (t k : ℂ) := hsumC.congr hterm
    exact Complex.summable_ofReal.1 this
  refine ⟨∑' k, t k, hsumR.tsum_pos (fun k => (ht0 k).le) 0 (ht0 0), ?_⟩
  rw [etaPair, tsum_congr hterm, Complex.ofReal_tsum]

/-- **`ζ(σ) < 0` for `0 < σ < 1`** (ARCS paper §4.4, "ζ(σ) < 0 on (0, 1)"), via
`(1 − 2^{1−σ}) ζ(σ) = η(σ) > 0` and `1 − 2^{1−σ} < 0`. -/
theorem riemannZeta_neg_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, x < 0 ∧ riemannZeta σ = x := by
  obtain ⟨e, he, hη⟩ := etaPair_real_pos h0
  have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne
  have hid := (etaPair_eq_etaZeta (s := σ) (by simpa using h0)).trans (etaZeta_eq hσ1)
  have hc : (2 : ℂ) ^ (1 - (σ : ℂ)) = (((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by norm_num)]; push_cast; ring_nf
  have hgt : 1 < (2 : ℝ) ^ (1 - σ) := Real.one_lt_rpow (by norm_num) (by linarith)
  set d : ℝ := 1 - (2 : ℝ) ^ (1 - σ)
  have hd : d < 0 := by simp only [d]; linarith
  refine ⟨e / d, div_neg_of_pos_of_neg he hd, ?_⟩
  rw [hc, hη] at hid
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne
  have : (1 - (((2 : ℝ) ^ (1 - σ) : ℝ) : ℂ)) = (d : ℂ) := by simp [d]
  rw [this] at hid
  push_cast
  field_simp
  linear_combination -hid

theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta σ ≠ 0 := by
  obtain ⟨x, hx, h⟩ := riemannZeta_neg_of_mem_Ioo h0 h1
  rw [h]; exact_mod_cast hx.ne

end LeanBase.Classical
