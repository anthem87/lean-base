module

public import LeanBase.Classical.LandauMellin
public import LeanBase.Classical.ZeroSingularity
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false

/-!
# Landau's theorem and the zero step together (ARCS paper §4, Propositions 3, 3₀ and Theorem S)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/LandauZeros.lean), same author and licence.

* `mellinConvergent_of_re_le`, `mellin_differentiableAt_of_convergent`: for `g` vanishing on
  `(0, 1)`, Mellin convergence at a real point propagates to the left, and the transform is
  holomorphic on the open half-plane of convergence (no pointwise growth bound needed).
* `landau_zero_engine`: if `g ≥ 0` has Mellin transform `C/(s − θ) − Φ(s)/s` on `Re s > σ₁` and
  `Φ′ = Σ_i A_i f_i′/f_i + h` there, with `f_i`, `h` analytic on `Re s > θ` and `f_i ≠ 0` on the real
  half-line `(θ, ∞)`, then `Σ_i A_i m_i(ρ) = 0` at every `ρ` with `Re ρ > θ`.

Proof of the engine: the abscissa `σ_c` of the transform is `≤ θ`, since otherwise a primitive of
`Σ A_i f_i′/f_i + h` on a zero-free disc at `σ_c` continues the transform across `σ_c`, against
`landau_mellin`. Then the identity theorem (with the denominators cleared) carries
`Φ′ = Σ A_i f_i′/f_i + h` to `Re s > θ`, and `not_analyticAt_of_logDeriv_combination` gives the
conclusion. The ARCS paper argues with `log L`; the logarithmic derivative avoids choosing branches.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex Filter Topology Set MeasureTheory Asymptotics

/-- For `g` vanishing on `(0, 1)`, Mellin convergence at a real `σ` gives convergence at every
`u` with `Re u ≤ σ`. -/
theorem mellinConvergent_of_re_le (g : ℝ → ℝ)
    (hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0)
    (hloc : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) {σ : ℝ}
    (hσ : MellinConvergent (fun t => (g t : ℂ)) σ) {u : ℂ} (hu : u.re ≤ σ) :
    MellinConvergent (fun t => (g t : ℂ)) u := by
  have hm := hloc.aestronglyMeasurable
  unfold MellinConvergent at hσ ⊢
  rw [mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hm] at hσ ⊢
  simp only [Complex.ofReal_re] at hσ
  refine hσ.mono' ?_ ?_
  · refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi).mul hm.norm
    exact fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    simp only [norm_mul, Real.norm_eq_abs, abs_norm]
    rw [abs_of_pos (Real.rpow_pos_of_pos ht _)]
    rcases lt_or_ge t 1 with h | h
    · simp [hg1 t ⟨ht, h⟩]
    · gcongr

/-- **A Mellin transform is holomorphic on its half-plane of (absolute) convergence.** For `g`
vanishing on `(0, 1)` and convergent at the real point `σ`, `mellin g`
is differentiable at every `s` with `Re s < σ`. (Mathlib's `mellin_differentiableAt_of_isBigO_rpow`
needs a pointwise `O(t^{−a})` bound; here only the integrability at `σ` is used.) -/
theorem mellin_differentiableAt_of_convergent (g : ℝ → ℝ)
    (hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0)
    (hloc : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) {σ : ℝ}
    (hσ : MellinConvergent (fun t => (g t : ℂ)) σ) {s : ℂ} (hs : s.re < σ) :
    DifferentiableAt ℂ (mellin fun t => (g t : ℂ)) s := by
  set f : ℝ → ℂ := fun t => (g t : ℂ)
  set F : ℂ → ℝ → ℂ := fun (z : ℂ) (t : ℝ) => (t : ℂ) ^ (z - 1) • f t
  set F' : ℂ → ℝ → ℂ := fun (z : ℂ) (t : ℝ) => ((t : ℂ) ^ (z - 1) * (Real.log t : ℂ)) • f t
  set v : ℝ := (σ - s.re) / 2
  have hv0 : 0 < v := by simp only [v]; linarith
  have hm := hloc.aestronglyMeasurable
  let bound : ℝ → ℝ := fun t : ℝ => v⁻¹ * (t ^ (σ - 1) * ‖f t‖)
  have h1 : ∀ᶠ z : ℂ in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict <| Ioi 0) := by
    refine Eventually.of_forall fun z => ?_
    have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) (Ioi 0) :=
      continuousOn_of_forall_continuousAt fun t ht =>
        continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
    exact (hc.aestronglyMeasurable measurableSet_Ioi).smul hm
  have h2 : IntegrableOn (F s) (Ioi (0 : ℝ)) :=
    mellinConvergent_of_re_le g hg1 hloc hσ hs.le
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict <| Ioi 0) := by
    apply LocallyIntegrableOn.aestronglyMeasurable
    refine hloc.continuousOn_smul isOpen_Ioi.isLocallyClosed
      ((continuousOn_of_forall_continuousAt fun t ht => ?_).mul ?_)
    · exact continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_gt ht)
    · refine continuous_ofReal.comp_continuousOn ?_
      exact Real.continuousOn_log.mono (subset_compl_singleton_iff.mpr self_notMem_Ioi)
  have h4 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ z : ℂ, z ∈ Metric.ball s v → ‖F' z t‖ ≤ bound t := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht z hz => ?_
    rcases lt_or_ge t 1 with h | h
    · simp [F', bound, f, hg1 t ⟨ht, h⟩]
    have hzre : z.re < s.re + v := by
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have := (Complex.re_le_norm (z - s)).trans_lt hz
      simp only [Complex.sub_re] at this; linarith
    simp only [F', bound, norm_smul, norm_mul]
    rw [norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg h)]
    simp only [Complex.sub_re, Complex.one_re]
    have hlog : Real.log t ≤ t ^ v / v := Real.log_le_rpow_div (by linarith) hv0
    have hpow : t ^ (z.re - 1) * t ^ v ≤ t ^ (σ - 1) := by
      rw [← Real.rpow_add (by linarith)]
      exact Real.rpow_le_rpow_of_exponent_le h (by simp only [v] at hzre ⊢; linarith)
    have hf0 : 0 ≤ ‖f t‖ := norm_nonneg _
    calc t ^ (z.re - 1) * Real.log t * ‖f t‖ ≤ t ^ (z.re - 1) * (t ^ v / v) * ‖f t‖ := by
          gcongr
      _ = v⁻¹ * (t ^ (z.re - 1) * t ^ v * ‖f t‖) := by ring
      _ ≤ v⁻¹ * (t ^ (σ - 1) * ‖f t‖) := by gcongr
  have h5 : IntegrableOn bound (Ioi 0) := by
    have := hσ
    unfold MellinConvergent at this
    rw [mellin_convergent_iff_norm subset_rfl measurableSet_Ioi hm] at this
    simp only [Complex.ofReal_re] at this
    exact this.const_mul _
  have h6 : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ∀ y : ℂ, y ∈ Metric.ball s v → HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht y _ => ?_
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1)) (t ^ (y - 1) * (Real.log t : ℂ)) y := by
      convert ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [ofReal_log (le_of_lt ht)]
      ring
    exact u1.smul_const (f t)
  have main :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv0) h1 h2 h3 h4 h5 h6
  exact main.2.differentiableAt


/-- `Σ_i A_i f_i′ Π_{j≠i} f_j + h Π_j f_j`: the combination `Σ_i A_i f_i′/f_i + h` with the
denominators cleared. -/
noncomputable def clearedComb {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : ι → ℂ)
    (f : ι → ℂ → ℂ) (h : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ i ∈ S, A i * (deriv (f i) s * ∏ j ∈ S.erase i, f j s) + h s * ∏ j ∈ S, f j s

theorem logDeriv_comb_mul_prod {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : ι → ℂ)
    (f : ι → ℂ → ℂ) (h : ℂ → ℂ) {s : ℂ} (hne : ∀ i ∈ S, f i s ≠ 0) :
    (∑ i ∈ S, A i * logDeriv (f i) s + h s) * ∏ j ∈ S, f j s = clearedComb S A f h s := by
  rw [clearedComb, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [logDeriv_apply, ← Finset.mul_prod_erase S (fun j => f j s) hi]
  field_simp [hne i hi]

theorem analyticOnNhd_clearedComb {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : ι → ℂ)
    (f : ι → ℂ → ℂ) (h : ℂ → ℂ) {U : Set ℂ} (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) U)
    (hh : AnalyticOnNhd ℂ h U) : AnalyticOnNhd ℂ (clearedComb S A f h) U := by
  have hp : ∀ T : Finset ι, T ⊆ S → AnalyticOnNhd ℂ (fun s => ∏ j ∈ T, f j s) U :=
    fun T hT => Finset.analyticOnNhd_fun_prod T fun j hj => hf j (hT hj)
  refine (Finset.analyticOnNhd_fun_sum S fun i hi => ?_).add (hh.mul (hp S subset_rfl))
  exact analyticOnNhd_const.mul (((hf i hi).deriv).mul (hp _ (Finset.erase_subset i S)))

/-- **Landau's theorem combined with the zero step** (the engine of the directions "bound ⇒ no
zeros" of Propositions 3, 3₀ and of Theorem S, ARCS paper §4).

Let `g ≥ 0` vanish on `(0, 1)` and have Mellin transform `∫ g(x) x^{−s−1} dx = C/(s − θ) − Φ(s)/s`
on `Re s > σ₁`, where `Φ′ = Σ_{i∈S} A_i f_i′/f_i + h` on `Re s > σ₁`, with `f_i` and `h` analytic on
`Re s > θ ≥ 0` and the `f_i` non-zero on the real half-line `(θ, ∞)`. Then at every `ρ` with
`Re ρ > θ` the orders `m_i` of the zeros of the `f_i` satisfy `Σ_i A_i m_i = 0`.

(In the ARCS paper `Φ = D`, `f_i = L(s, χ)`, and `g = C x^θ ∓ H(x)`; with one `f_i`, or under
condition (N), the conclusion says that the `f_i` have no zero with `Re ρ > θ`.) -/
theorem landau_zero_engine {ι : Type*} [DecidableEq ι] (S : Finset ι) (A : ι → ℂ)
    (f : ι → ℂ → ℂ) (h : ℂ → ℂ) (θ σ₁ : ℝ) (hθ0 : 0 ≤ θ) (hθσ : θ < σ₁)
    (g : ℝ → ℝ) (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t ∈ Ioo (0 : ℝ) 1, g t = 0)
    (hloc : LocallyIntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) (a : ℝ)
    (hga : (fun t => (g t : ℂ)) =O[atTop] (· ^ (-a))) (C : ℂ) (Φ : ℂ → ℂ)
    (hconv : ∀ σ : ℝ, σ₁ < σ → MellinConvergent (fun t => (g t : ℂ)) (-(σ : ℂ)))
    (hmel : ∀ s : ℂ, σ₁ < s.re → mellin (fun t => (g t : ℂ)) (-s) = C / (s - θ) - Φ s / s)
    (hf : ∀ i ∈ S, AnalyticOnNhd ℂ (f i) {s | θ < s.re})
    (hreal : ∀ i ∈ S, ∀ σ : ℝ, θ < σ → f i σ ≠ 0)
    (hh : AnalyticOnNhd ℂ h {s | θ < s.re})
    (hD : ∀ s : ℂ, σ₁ < s.re → deriv Φ s = ∑ i ∈ S, A i * logDeriv (f i) s + h s)
    {ρ : ℂ} (hρ : θ < ρ.re) (m : ι → ℕ) (hm : ∀ i ∈ S, analyticOrderAt (f i) ρ = m i) :
    ∑ i ∈ S, A i * m i = 0 := by
  set gc : ℝ → ℂ := fun t => (g t : ℂ)
  set M : ℂ → ℂ := fun s => mellin gc (-s)
  set Ψ : ℂ → ℂ := fun s => s * (C / (s - θ) - M s)
  set R : ℂ → ℂ := fun s => ∑ i ∈ S, A i * logDeriv (f i) s + h s
  set P : ℂ → ℂ := fun s => ∏ j ∈ S, f j s
  have hre_ne : ∀ s : ℂ, θ < s.re → s ≠ 0 ∧ s - θ ≠ 0 := by
    intro s hs
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [h0] at hs; simp at hs; linarith
    · have : s = θ := sub_eq_zero.1 h0
      rw [this] at hs; simp at hs
  -- `M = C/(s − θ) − Ψ/s`
  have hMΨ : ∀ s : ℂ, θ < s.re → M s = C / (s - θ) - Ψ s / s := by
    intro s hs
    have := (hre_ne s hs).1
    simp only [Ψ]; field_simp; ring
  -- convergence at a real point gives differentiability of `M` to its right
  have hMdiff : ∀ σ : ℝ, MellinConvergent gc (-(σ : ℂ)) → ∀ s : ℂ, σ < s.re →
      DifferentiableAt ℂ M s := by
    intro σ hσ s hs
    have hσ' : MellinConvergent gc ((-σ : ℝ) : ℂ) := by push_cast; exact hσ
    have := mellin_differentiableAt_of_convergent g hg1 hloc hσ' (s := -s)
      (by simp only [Complex.neg_re]; linarith)
    exact this.comp s differentiableAt_id.neg
  have hmono : ∀ σ σ' : ℝ, σ ≤ σ' → MellinConvergent gc (-(σ : ℂ)) →
      MellinConvergent gc (-(σ' : ℂ)) := by
    intro σ σ' hle hσ
    have hσ'' : MellinConvergent gc ((-σ : ℝ) : ℂ) := by push_cast; exact hσ
    refine mellinConvergent_of_re_le g hg1 hloc hσ'' ?_
    simp only [Complex.neg_re, Complex.ofReal_re]
    linarith
  -- the identity theorem, transported to `Re s > σ'`
  have hident : ∀ σ' : ℝ, θ ≤ σ' → σ' ≤ σ₁ + 1 → (∀ s : ℂ, σ' < s.re → DifferentiableAt ℂ M s) →
      ∀ s : ℂ, σ' < s.re → deriv Ψ s * P s = clearedComb S A f h s := by
    intro σ' hθσ' hσ'1 hMd
    set U : Set ℂ := {s | σ' < s.re}
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hUθ : U ⊆ {s | θ < s.re} := fun s hs => lt_of_le_of_lt hθσ' hs
    have hΨd : DifferentiableOn ℂ Ψ U := fun s hs => by
      have hs' := hre_ne s (hUθ hs)
      exact (differentiableAt_id.mul (((differentiableAt_const C).div
        (differentiableAt_id.sub_const _) hs'.2).sub (hMd s hs))).differentiableWithinAt
    have hL : AnalyticOnNhd ℂ (fun s => deriv Ψ s * P s) U :=
      ((hΨd.analyticOnNhd hUo).deriv).mul
        (Finset.analyticOnNhd_fun_prod S fun j hj => (hf j hj).mono hUθ)
    have hR : AnalyticOnNhd ℂ (clearedComb S A f h) U :=
      analyticOnNhd_clearedComb S A f h (fun i hi => (hf i hi).mono hUθ) (hh.mono hUθ)
    set z₀ : ℂ := ((σ₁ + 2 : ℝ) : ℂ)
    have hz₀ : σ₁ < z₀.re := by simp only [z₀, Complex.ofReal_re]; linarith
    have hz₀θ : θ < z₀.re := by linarith
    have hopen1 : {s : ℂ | σ₁ < s.re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀
    have hne : ∀ᶠ s in 𝓝 z₀, ∀ j ∈ S, f j s ≠ 0 := by
      rw [eventually_all_finset]
      intro j hj
      exact ((hf j hj z₀ hz₀θ).continuousAt).eventually_ne
        (hreal j hj (σ₁ + 2) (by linarith))
    have hΨΦ : ∀ᶠ s in 𝓝 z₀, Ψ =ᶠ[𝓝 s] Φ := by
      filter_upwards [hopen1] with s hs
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
      have hw' : σ₁ < w.re := hw
      have hw0 := (hre_ne w (by linarith)).1
      simp only [Ψ, M]
      rw [hmel w hw]
      field_simp
      ring
    have hev : (fun s => deriv Ψ s * P s) =ᶠ[𝓝 z₀] clearedComb S A f h := by
      filter_upwards [hopen1, hne, hΨΦ] with s hs hnes hΨΦs
      rw [hΨΦs.deriv_eq, hD s hs]
      exact logDeriv_comb_mul_prod S A f h hnes
    intro s hs
    exact hL.eqOn_of_preconnected_of_eventuallyEq hR (convex_halfSpace_re_gt σ').isPreconnected
      (show z₀ ∈ U by show σ' < z₀.re; simp only [z₀, Complex.ofReal_re]; linarith) hev hs
  -- Step 1: the abscissa of convergence is `≤ θ`
  set T : Set ℝ := {σ | θ ≤ σ ∧ MellinConvergent gc (-(σ : ℂ))}
  have hTne : σ₁ + 1 ∈ T := ⟨by linarith, hconv _ (by linarith)⟩
  have hTbdd : BddBelow T := ⟨θ, fun σ hσ => hσ.1⟩
  set σc := sInf T
  have hθσc : θ ≤ σc := le_csInf ⟨_, hTne⟩ fun σ hσ => hσ.1
  have hconvAbove : ∀ σ : ℝ, σc < σ → MellinConvergent gc (-(σ : ℂ)) := by
    intro σ hσ
    obtain ⟨σ', hσ'T, hσ'lt⟩ := exists_lt_of_csInf_lt ⟨_, hTne⟩ hσ
    exact hmono σ' σ hσ'lt.le hσ'T.2
  have hMdc : ∀ s : ℂ, σc < s.re → DifferentiableAt ℂ M s := by
    intro s hs
    obtain ⟨σ, h1, h2⟩ := exists_between hs
    exact hMdiff σ (hconvAbove σ h1) s h2
  have hσc : ¬ θ < σc := by
    intro hlt
    have hnot : ∀ u : ℝ, -σc < u → ¬ MellinConvergent gc u := by
      intro u hu hcv
      have hcv' : MellinConvergent gc (-((-u : ℝ) : ℂ)) := by push_cast; simpa using hcv
      by_cases hθu : θ ≤ -u
      · have := csInf_le hTbdd ⟨hθu, hcv'⟩
        linarith
      · have := csInf_le hTbdd ⟨le_rfl, hmono (-u) θ (by linarith) hcv'⟩
        linarith
    have hPc : P σc ≠ 0 := Finset.prod_ne_zero_iff.2 fun j hj => hreal j hj σc hlt
    have hPcont : ContinuousAt P σc :=
      (Finset.analyticOnNhd_fun_prod S fun j hj => hf j hj) _ (by simpa using hlt) |>.continuousAt
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hPcont.eventually_ne hPc)
    set ε := min ε₀ (σc - θ)
    have hε : 0 < ε := lt_min hε₀ (by linarith)
    set B := Metric.ball (σc : ℂ) ε
    have hBre : ∀ s ∈ B, θ < s.re := by
      intro s hs
      rw [Metric.mem_ball, Complex.dist_eq] at hs
      have h1 := (Complex.abs_re_le_norm (s - σc)).trans_lt hs
      simp only [Complex.sub_re, Complex.ofReal_re] at h1
      have := abs_lt.1 h1
      have : ε ≤ σc - θ := min_le_right _ _
      linarith
    have hBne : ∀ s ∈ B, ∀ j ∈ S, f j s ≠ 0 := by
      intro s hs
      exact Finset.prod_ne_zero_iff.1 (hball s (Metric.ball_subset_ball (min_le_left _ _) hs))
    have hRd : DifferentiableOn ℂ R B := by
      intro s hs
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (DifferentiableAt.fun_sum fun i hi => ?_).add
        (hh s (hBre s hs)).differentiableAt
      refine (differentiableAt_const _).mul ?_
      have hfa := hf i hi s (hBre s hs)
      simp only [logDeriv]
      exact hfa.deriv.differentiableAt.div hfa.differentiableAt (hBne s hs i hi)
    set s₀ : ℂ := ((σc + ε / 2 : ℝ) : ℂ)
    obtain ⟨Q, hQ0, hQ⟩ := (hRd.isExactOn_ball).with_val_at s₀ (Ψ s₀)
    set V : Set ℂ := B ∩ {s | σc < s.re}
    have hVo : IsOpen V := Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
    have hVc : IsPreconnected V := ((convex_ball _ _).inter (convex_halfSpace_re_gt _)).isPreconnected
    have hs₀V : s₀ ∈ V := by
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
        rw [show σc + ε / 2 - σc = ε / 2 by ring, abs_of_pos (by positivity)]
        linarith
      · simp only [s₀, mem_ofPred_eq, Complex.ofReal_re]; linarith
    have hidc := hident σc hθσc (csInf_le hTbdd hTne) hMdc
    have hΨV : ∀ s ∈ V, HasDerivAt Ψ (R s) s := by
      intro s hs
      have hs' := hre_ne s (lt_of_le_of_lt hθσc hs.2)
      have hd : DifferentiableAt ℂ Ψ s :=
        differentiableAt_id.mul (((differentiableAt_const C).div
          (differentiableAt_id.sub_const _) hs'.2).sub (hMdc s hs.2))
      have hPs : P s ≠ 0 := Finset.prod_ne_zero_iff.2 (hBne s hs.1)
      have e := hidc s hs.2
      rw [← logDeriv_comb_mul_prod S A f h (hBne s hs.1)] at e
      have : deriv Ψ s = R s := mul_right_cancel₀ hPs e
      rw [← this]
      exact hd.hasDerivAt
    have hΨQ : ∀ s ∈ V, Ψ s = Q s := by
      have hdiff : DifferentiableOn ℂ (fun s => Ψ s - Q s) V := fun s hs =>
        ((hΨV s hs).differentiableAt.sub (hQ s hs.1).differentiableAt).differentiableWithinAt
      have hzero : V.EqOn (deriv fun s => Ψ s - Q s) 0 := by
        intro s hs
        exact ((hΨV s hs).sub (hQ s hs.1)).deriv.trans (sub_self _)
      intro s hs
      have := hVo.is_const_of_deriv_eq_zero hVc hdiff hzero hs hs₀V
      rw [hQ0] at this
      simpa [sub_eq_zero] using this
    -- the continuation in the variable `u = −s`
    set K : ℂ → ℂ := fun u => C / (-u - θ) - Q (-u) / (-u)
    set F : ℂ → ℂ := fun u => if u.re < -σc then mellin gc u else K u
    have hnegB : ∀ u ∈ Metric.ball ((-σc : ℝ) : ℂ) ε, -u ∈ B := by
      intro u hu
      rw [Metric.mem_ball, Complex.dist_eq] at hu ⊢
      rw [show -u - (σc : ℂ) = -(u - ((-σc : ℝ) : ℂ)) by push_cast; ring, norm_neg]
      exact hu
    have hFK : ∀ u ∈ Metric.ball ((-σc : ℝ) : ℂ) ε, F u = K u := by
      intro u hu
      simp only [F]
      split_ifs with hlt'
      · have hV : -u ∈ V := ⟨hnegB u hu, by simp only [mem_ofPred_eq, Complex.neg_re]; linarith⟩
        have := hMΨ (-u) (lt_of_le_of_lt hθσc hV.2)
        simp only [M, neg_neg] at this
        rw [this, hΨQ (-u) hV]
      · rfl
    apply landau_mellin g hg0 hg1 hloc a hga (-σc) hnot
    refine ⟨F, ε, hε, ?_, fun s hs => by simp only [F, if_pos hs]; rfl⟩
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases hu with hu | hu
    · simp only [mem_ofPred_eq] at hu
      have hev : F =ᶠ[𝓝 u] mellin gc := by
        filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hu] with w hw
        have hw' : w.re < -σc := hw
        simp only [F, if_pos hw']
      refine hev.differentiableAt_iff.2 ?_
      have : DifferentiableAt ℂ M (-u) := hMdc (-u) (by simp only [Complex.neg_re]; linarith)
      have := this.comp u differentiableAt_id.neg
      simpa [M, Function.comp_def] using this
    · have hev : F =ᶠ[𝓝 u] K := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hu] with w hw
        exact hFK w hw
      refine hev.differentiableAt_iff.2 ?_
      have hB := hnegB u hu
      have hs' := hre_ne (-u) (hBre _ hB)
      have hQd : DifferentiableAt ℂ (fun u => Q (-u)) u :=
        (hQ (-u) hB).differentiableAt.comp u differentiableAt_id.neg
      exact ((differentiableAt_const C).div (differentiableAt_id.neg.sub_const _) hs'.2).sub
        (hQd.div differentiableAt_id.neg hs'.1)
  -- Step 2: the zero step at `ρ`
  have hσcθ : σc = θ := le_antisymm (not_lt.1 hσc) hθσc
  have hMθ : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ M s := fun s hs => hMdc s (hσcθ ▸ hs)
  have hidθ := hident θ le_rfl (by linarith) hMθ
  set U : Set ℂ := {s | θ < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hΨd : DifferentiableOn ℂ Ψ U := fun s hs => by
    have hs' := hre_ne s hs
    exact (differentiableAt_id.mul (((differentiableAt_const C).div
      (differentiableAt_id.sub_const _) hs'.2).sub (hMθ s hs))).differentiableWithinAt
  have hΨ'a : AnalyticAt ℂ (deriv Ψ) ρ := (hΨd.analyticOnNhd hUo).deriv ρ hρ
  have hPa : AnalyticOnNhd ℂ P U := Finset.analyticOnNhd_fun_prod S fun j hj => hf j hj
  have hPne : ∀ᶠ s in 𝓝[≠] ρ, P s ≠ 0 := by
    set z₀ : ℂ := ((σ₁ + 1 : ℝ) : ℂ)
    have hz₀ : z₀ ∈ U := by simp only [U, z₀, mem_ofPred_eq, Complex.ofReal_re]; linarith
    have h0 : analyticOrderAt P z₀ ≠ ⊤ := by
      rw [show analyticOrderAt P z₀ = 0 from analyticOrderAt_eq_zero.2
        (Or.inr (Finset.prod_ne_zero_iff.2 fun j hj => hreal j hj _ (by linarith)))]
      exact ENat.zero_ne_top
    have htop := hPa.analyticOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt θ).isPreconnected hz₀ hρ h0
    rcases (hPa ρ hρ).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.2 h) htop
    · exact h
  by_contra hsum
  refine not_analyticAt_of_logDeriv_combination S A f m (fun i hi => hf i hi ρ hρ) hm h
    (hh ρ hρ) hsum (deriv Ψ) hΨ'a ?_
  filter_upwards [hPne, nhdsWithin_le_nhds (hUo.mem_nhds hρ)] with s hPs hsU
  have hnes : ∀ j ∈ S, f j s ≠ 0 := Finset.prod_ne_zero_iff.1 hPs
  have e := hidθ s hsU
  rw [← logDeriv_comb_mul_prod S A f h hnes] at e
  exact mul_right_cancel₀ hPs e

end LeanBase.Classical
