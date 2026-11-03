module

public import LeanBase.Classical.Landau
public import Mathlib.Analysis.MellinTransform
set_option autoImplicit false

/-!
# Landau's theorem for Mellin transforms of non-negative functions (ARCS paper §4, [Landau; Ingham, Ch. V])

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/LandauMellin.lean), same author and licence.

`landau_mellin`: for `g ≥ 0` vanishing on `(0, 1)`, locally integrable and of polynomial growth,
the abscissa of convergence of its Mellin transform is a real singularity. The growth hypothesis
`g = O(t^{−a})` holds in every use in the ARCS paper (`G = C x^θ ∓ H(x)` with `H(x) = O(x)`); it gives the
derivatives of the transform through `mellin_hasDerivAt_of_isBigO_rpow`.

Proof: `(mellin g)^{(n)}(c) = ∫ t^{c−1} log^n t g(t) dt ≥ 0`; the Taylor series at a real point `c`
of the half-plane, evaluated at a real point `z` beyond the abscissa, is a series of non-negative
integrals, which monotone convergence turns into `∫ t^{z−1} g(t) dt < ∞`: a contradiction.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set MeasureTheory Asymptotics

/-- `log^n · f = O(t^{−a'})` at `∞` for every `a' < a` when `f = O(t^{−a})`. -/
theorem isBigO_logPow {f : ℝ → ℂ} {a : ℝ} (hf : f =O[atTop] (· ^ (-a))) :
    ∀ n : ℕ, ∀ a' < a, (fun t : ℝ => (Real.log t : ℂ) ^ n * f t) =O[atTop] (· ^ (-a')) := by
  intro n
  induction n with
  | zero =>
    intro a' ha'
    simp only [pow_zero, one_mul]
    refine hf.trans (Eventually.isBigO ?_)
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) _)]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  | succ n ih =>
    intro a' ha'
    have h := isBigO_rpow_top_log_smul (E := ℂ) (show a' < (a' + a) / 2 by linarith)
      (ih ((a' + a) / 2) (by linarith))
    refine h.congr' (Eventually.of_forall fun t => ?_) (Eventually.of_forall fun t => rfl)
    simp only [Complex.real_smul, pow_succ]
    ring

/-- A function vanishing on `(0, 1)` is `O(t^{−b})` at `0⁺` for every `b`. -/
theorem isBigO_bot_of_vanish {f : ℝ → ℂ} (hf : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0) (b : ℝ) :
    f =O[𝓝[>] 0] (· ^ (-b)) := by
  have : f =ᶠ[𝓝[>] 0] fun _ => (0 : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hf t ht
  exact (isBigO_zero _ _).congr' this.symm EventuallyEq.rfl

theorem locallyIntegrable_logPow {f : ℝ → ℂ} (hloc : LocallyIntegrableOn f (Ioi 0)) (n : ℕ) :
    LocallyIntegrableOn (fun t : ℝ => (Real.log t : ℂ) ^ n * f t) (Ioi 0) := by
  have hc : ContinuousOn (fun t : ℝ => (Real.log t : ℂ) ^ n) (Ioi 0) := by
    apply ContinuousOn.pow
    exact Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ne_of_gt ht)
  exact hloc.continuousOn_mul hc isOpen_Ioi.isLocallyClosed

/-- The iterated derivatives of a Mellin transform: `(mellin f)^{(n)}(u) = mellin (log^n · f)(u)`
on `Re u < a`, for `f` vanishing on `(0, 1)` and `O(t^{−a})` at `∞`. -/
theorem iteratedDeriv_mellin {f : ℝ → ℂ} (hloc : LocallyIntegrableOn f (Ioi 0))
    (hf1 : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0) {a : ℝ} (hfa : f =O[atTop] (· ^ (-a))) :
    ∀ n : ℕ, ∀ u : ℂ, u.re < a →
      iteratedDeriv n (mellin f) u = mellin (fun t : ℝ => (Real.log t : ℂ) ^ n * f t) u := by
  intro n
  induction n with
  | zero => intro u _; simp
  | succ n ih =>
    intro u hu
    have hopen : IsOpen {s : ℂ | s.re < a} := isOpen_lt Complex.continuous_re continuous_const
    have hev : iteratedDeriv n (mellin f) =ᶠ[𝓝 u]
        mellin (fun t : ℝ => (Real.log t : ℂ) ^ n * f t) := by
      filter_upwards [hopen.mem_nhds hu] with s hs
      exact ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq]
    obtain ⟨a', hua', ha'⟩ := exists_between hu
    have hd := (mellin_hasDerivAt_of_isBigO_rpow (locallyIntegrable_logPow hloc n)
      (isBigO_logPow hfa n a' ha') hua'
      (isBigO_bot_of_vanish (fun t ht => by simp [hf1 t ht]) (u.re - 1))
      (by linarith)).2.deriv
    rw [hd]
    congr 1
    funext t
    simp only [Complex.real_smul, pow_succ]
    ring

/-- Geometry: with `D = u₀ − c > 0` and `δ = min(D/2, ε²/(4D))`, the ball of radius `D + δ` around
the real point `c` lies in `{Re s < u₀} ∪ B(u₀, ε)`. -/
theorem ball_subset_left (c u₀ ε : ℝ) (hc : c < u₀) (hε : 0 < ε) :
    Metric.ball (c : ℂ) ((u₀ - c) + min ((u₀ - c) / 2) (ε ^ 2 / (4 * (u₀ - c)))) ⊆
      {s : ℂ | s.re < u₀} ∪ Metric.ball (u₀ : ℂ) ε := by
  set D := u₀ - c
  have hD : 0 < D := by simp only [D]; linarith
  set δ := min (D / 2) (ε ^ 2 / (4 * D))
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ D / 2 := min_le_left _ _
  have hδ2 : δ * (4 * D) ≤ ε ^ 2 := by
    have := min_le_right (D / 2) (ε ^ 2 / (4 * D))
    rw [le_div_iff₀ (by positivity)] at this; exact this
  intro z hz
  by_cases h : z.re < u₀
  · left; exact h
  · right
    push Not at h
    rw [Metric.mem_ball, Complex.dist_eq_re_im] at hz ⊢
    rw [Real.sqrt_lt' (by positivity)] at hz ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hz ⊢
    have hv : 0 ≤ z.re - u₀ := by linarith
    have e : z.re - c = D + (z.re - u₀) := by simp only [D]; ring
    rw [e] at hz
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re - u₀), mul_nonneg hD.le hv]

/-- **Landau's theorem on Mellin transforms of non-negative functions** ([Landau; Ingham, Ch. V],
used in ARCS paper §4, Propositions 3 and 3₀ and Theorem S). Let `g ≥ 0` vanish on `(0, 1)`, be locally
integrable on `(0, ∞)`, and be `O(t^{−a})` at `∞` for some `a`. In Mathlib's convention
`mellin g u = ∫_0^∞ t^{u−1} g(t) dt`; the ARCS paper's transform is `∫_1^∞ G(x) x^{−s−1} dx = mellin G (−s)`.
If `mellin g` converges at no real point `u > u₀` (so `u₀` is the abscissa of convergence), then no
function holomorphic on `{Re u < u₀} ∪ B(u₀, ε)` agrees with `mellin g` on `Re u < u₀`: the abscissa
is a real singularity. -/
theorem landau_mellin (g : ℝ → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0)
    (hloc : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) (a : ℝ)
    (hga : (fun t => (g t : ℂ)) =O[atTop] (· ^ (-a))) (u₀ : ℝ)
    (hnot : ∀ u : ℝ, u₀ < u → ¬ MellinConvergent (fun t => (g t : ℂ)) u) :
    ¬ ∃ (F : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      DifferentiableOn ℂ F ({s : ℂ | s.re < u₀} ∪ Metric.ball (u₀ : ℂ) ε) ∧
      ∀ s : ℂ, s.re < u₀ → F s = mellin (fun t => (g t : ℂ)) s := by
  rintro ⟨F, ε, hε, hF, hFeq⟩
  set f : ℝ → ℂ := fun t => (g t : ℂ)
  have hf1 : ∀ t ∈ Ioo (0 : ℝ) 1, f t = 0 := fun t ht => by simp [f, hg1 t ht]
  set c : ℝ := min a u₀ - 1
  have hca : c < a := by simp only [c]; linarith [min_le_left a u₀]
  have hcu : c < u₀ := by simp only [c]; linarith [min_le_right a u₀]
  set D := u₀ - c
  have hD : 0 < D := by simp only [D]; linarith
  set δ := min (D / 2) (ε ^ 2 / (4 * D))
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  set r : ℝ := D + δ / 2
  set z : ℝ := c + r
  have hzu : u₀ < z := by simp only [z, r, D]; linarith
  have hball : DifferentiableOn ℂ F (Metric.ball (c : ℂ) (D + δ)) :=
    hF.mono (ball_subset_left c u₀ ε hcu hε)
  have hz : ((z : ℝ) : ℂ) ∈ Metric.ball (c : ℂ) (D + δ) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [z, add_sub_cancel_left, r]
    rw [abs_of_pos (by positivity)]
    linarith
  -- the coefficients `I n = ∫ t^{c−1} log^n t g(t)`
  let I : ℕ → ℝ := fun n => ∫ t in Ioi (0 : ℝ), t ^ (c - 1) * Real.log t ^ n * g t
  have hmel : ∀ n, mellin (fun t : ℝ => (Real.log t : ℂ) ^ n * f t) (c : ℂ) = ((I n : ℝ) : ℂ) := by
    intro n
    simp only [mellin, I]
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [f, smul_eq_mul]
    rw [show ((c : ℂ) - 1) = (((c - 1 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (le_of_lt ht)]
    push_cast
    ring
  -- Taylor expansion of `F` at `c`, evaluated at `z = c + r`
  have hopen : IsOpen {s : ℂ | s.re < u₀} := isOpen_lt Complex.continuous_re continuous_const
  have hev : F =ᶠ[𝓝 (c : ℂ)] mellin f := by
    filter_upwards [hopen.mem_nhds (show ((c : ℝ) : ℂ).re < u₀ by simpa using hcu)] with s hs
    exact hFeq s hs
  have hder : ∀ n, iteratedDeriv n F c = ((I n : ℝ) : ℂ) := by
    intro n
    rw [(hev.iteratedDeriv n).eq_of_nhds, iteratedDeriv_mellin hloc hf1 hga n c (by simpa using hca),
      hmel]
  set T : ℕ → ℝ := fun n => (n.factorial : ℝ)⁻¹ * r ^ n * I n
  have htay := Complex.hasSum_taylorSeries_on_ball hball hz
  have hcoef : ∀ n, (n.factorial : ℂ)⁻¹ • (((z : ℝ) : ℂ) - c) ^ n • iteratedDeriv n F c =
      ((T n : ℝ) : ℂ) := by
    intro n
    rw [hder, show (((z : ℝ) : ℂ) - c) = ((r : ℝ) : ℂ) by simp only [z]; push_cast; ring]
    simp only [smul_eq_mul, T]
    push_cast
    ring
  simp only [hcoef] at htay
  have hT : Summable T := Complex.summable_ofReal.1 htay.summable
  -- integrability of the coefficients' integrands
  have hint : ∀ n, IntegrableOn (fun t : ℝ => t ^ (c - 1) * Real.log t ^ n * g t) (Ioi 0) := by
    intro n
    obtain ⟨a', hca', ha'⟩ := exists_between hca
    have hmc := mellinConvergent_of_isBigO_rpow (locallyIntegrable_logPow hloc n)
      (isBigO_logPow hga n a' ha') (show ((c : ℝ) : ℂ).re < a' by simpa using hca')
      (isBigO_bot_of_vanish (fun t ht => by simp [hf1 t ht]) (c - 1)) (by simp)
    have := hmc.re
    refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [f, smul_eq_mul]
    rw [show ((c : ℂ) - 1) = (((c - 1 : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (le_of_lt ht)]
    norm_cast
    rw [RCLike.re_to_complex, Complex.ofReal_re]
    ring
  have hnn : ∀ n, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (c - 1) * Real.log t ^ n * g t := by
    intro n t ht
    by_cases ht1 : t < 1
    · rw [hg1 t ⟨ht, ht1⟩, mul_zero]
    · push Not at ht1
      have := Real.log_nonneg ht1
      have := hg0 t
      have := Real.rpow_nonneg (le_of_lt ht) (c - 1)
      positivity
  -- pointwise: the series of the integrands sums to `t^{z−1} g(t)`
  set term : ℕ → ℝ → ℝ := fun n t => (n.factorial : ℝ)⁻¹ * r ^ n * (t ^ (c - 1) * Real.log t ^ n * g t)
  have hr0 : 0 ≤ r := by positivity
  have hterm_nn : ∀ n, ∀ t ∈ Ioi (0 : ℝ), 0 ≤ term n t := fun n t ht => by
    have := hnn n t ht; simp only [term]; positivity
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n => term n t) (t ^ (z - 1) * g t) := by
    intro t ht
    have e : ∀ n, term n t = (t ^ (c - 1) * g t) * ((r * Real.log t) ^ n / n.factorial) := by
      intro n; simp only [term]; rw [mul_pow]; field_simp
    simp_rw [e]
    have hexp := (NormedSpace.expSeries_div_hasSum_exp (r * Real.log t)).mul_left (t ^ (c - 1) * g t)
    have hval : Real.exp (r * Real.log t) = t ^ r := by rw [Real.rpow_def_of_pos ht, mul_comm]
    rw [← Real.exp_eq_exp_ℝ, hval] at hexp
    convert hexp using 1
    rw [show z - 1 = (c - 1) + r by simp only [z]; ring, Real.rpow_add ht]
    ring
  -- Tonelli
  have hlint : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (z - 1) * g t) =
      ENNReal.ofReal (∑' n, T n) := by
    have h1 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (z - 1) * g t) =
        ∫⁻ t in Ioi (0 : ℝ), ∑' n, ENNReal.ofReal (term n t) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [← (hpoint t ht).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => hterm_nn n t ht)
        (hpoint t ht).summable]
    have hint' : ∀ n, IntegrableOn (term n) (Ioi 0) := fun n => (hint n).const_mul _
    rw [h1, lintegral_tsum (fun n => (hint' n).aemeasurable.ennreal_ofReal),
      ENNReal.ofReal_tsum_of_nonneg (fun n => ?_) hT]
    · congr 1
      funext n
      rw [← ofReal_integral_eq_lintegral_ofReal (hint' n)
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (hterm_nn n)))]
      congr 1
      simp only [term, T, I]
      rw [integral_const_mul]
    · simp only [T]
      have : 0 ≤ I n := setIntegral_nonneg measurableSet_Ioi (hnn n)
      positivity
  -- hence `t^{z−1} g(t)` is integrable, i.e. the Mellin integral converges at `z > u₀`
  have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (z - 1) * g t) (volume.restrict (Ioi 0)) := by
    have h0 := (hint 0).aestronglyMeasurable
    have hcont : ContinuousOn (fun t : ℝ => t ^ (z - c)) (Ioi 0) :=
      fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).continuousWithinAt
    have := (hcont.aestronglyMeasurable measurableSet_Ioi).mul h0
    refine this.congr ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
    simp only [Pi.mul_apply, pow_zero, mul_one]
    rw [← mul_assoc, ← Real.rpow_add ht]
    congr 2; ring
  have hintz : IntegrableOn (fun t : ℝ => t ^ (z - 1) * g t) (Ioi 0) := by
    refine (lintegral_ofReal_ne_top_iff_integrable hmeas
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))).1 ?_
    · have := hnn 0 t ht
      have := Real.rpow_nonneg (le_of_lt ht) (z - 1)
      have := hg0 t
      positivity
    · rw [hlint]; exact ENNReal.ofReal_ne_top
  apply hnot z hzu
  unfold MellinConvergent
  refine (hintz.ofReal (𝕜 := ℂ)).congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [f, smul_eq_mul]
  rw [show ((z : ℂ) - 1) = (((z - 1 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (le_of_lt ht)]
  push_cast
  ring_nf
  rfl

end LeanBase.Classical
