module

public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false

/-!
# Landau's theorem for Dirichlet series with non-negative coefficients (ARCS paper §4, [Landau; Ingham, Ch. V])

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/Landau.lean), same author and licence.

`landau_dirichlet`: if `a_n ≥ 0` and the abscissa of convergence `σ₀` of `Σ a_n n^{−s}` is finite,
the function it defines on `Re s > σ₀` has no holomorphic continuation to a neighbourhood of
`s = σ₀`: the abscissa of convergence is a real singularity.

Proof: expand at `c = σ₀ + 1`; the Taylor coefficients are `(−1)^k Σ_n a_n (log n)^k n^{−c} / k!`.
Evaluated at the real point `c − r` with `1 < r`, every term is non-negative, so the double series
can be summed in the other order (Tonelli), and it gives `Σ_n a_n n^{−(c−r)} < ∞`, below the
abscissa.
-/

@[expose] public section

namespace LeanBase.Classical

open Complex LSeries Filter Topology

/-- `logMul^[k] f n = (log n)^k f n`. -/
theorem logMul_iterate (f : ℕ → ℂ) (k n : ℕ) : (logMul^[k] f) n = (Complex.log n) ^ k * f n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [logMul]
    ring

/-- For real `x` and `n ≥ 1`, `term (a·) x n = a_n n^{−x}` (real). -/
theorem term_ofReal (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    term (fun n => (a n : ℂ)) x n = ((if n = 0 then 0 else a n * (n : ℝ) ^ (-x) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [term_of_ne_zero hn.ne', ite_eq_right_of_eq_false _ _ (eq_false hn.ne')]
    have : ((n : ℂ) ^ (x : ℂ)) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
    rw [this, Real.rpow_neg (Nat.cast_nonneg n)]
    push_cast
    rw [div_eq_mul_inv]

/-- The geometric fact used in the proof: the ball of radius `1 + δ` around `σ₀ + 1`, with
`δ = min(1/2, ε²/4)`, lies in `{Re s > σ₀} ∪ B(σ₀, ε)`. -/
theorem ball_subset (σ₀ ε : ℝ) (hε : 0 < ε) :
    Metric.ball ((σ₀ + 1 : ℝ) : ℂ) (1 + min (1 / 2) (ε ^ 2 / 4)) ⊆
      {s : ℂ | σ₀ < s.re} ∪ Metric.ball (σ₀ : ℂ) ε := by
  set δ := min (1 / 2) (ε ^ 2 / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε ^ 2 / 4 := min_le_right _ _
  intro z hz
  by_cases h : σ₀ < z.re
  · left; exact h
  · right
    push Not at h
    rw [Metric.mem_ball, Complex.dist_eq_re_im] at hz ⊢
    rw [Real.sqrt_lt' (by positivity)] at hz ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_zero] at hz ⊢
    nlinarith [sq_nonneg z.im, sq_nonneg (σ₀ - z.re)]

/-- **Landau's theorem** for Dirichlet series with non-negative coefficients
([Landau; Ingham, Ch. V], used in ARCS paper §4): if `a_n ≥ 0` and the abscissa of (absolute)
convergence of `Σ a_n n^{−s}` is the real number `σ₀`, then no function holomorphic on
`{Re s > σ₀} ∪ B(σ₀, ε)` agrees with the series on `Re s > σ₀`: `s = σ₀` is a singularity. -/
theorem landau_dirichlet (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (σ₀ : ℝ)
    (hσ : abscissaOfAbsConv (fun n => (a n : ℂ)) = σ₀) :
    ¬ ∃ (F : ℂ → ℂ) (ε : ℝ), 0 < ε ∧
      DifferentiableOn ℂ F ({s : ℂ | σ₀ < s.re} ∪ Metric.ball (σ₀ : ℂ) ε) ∧
      ∀ s : ℂ, σ₀ < s.re → F s = LSeries (fun n => (a n : ℂ)) s := by
  rintro ⟨F, ε, hε, hF, hFeq⟩
  set f : ℕ → ℂ := fun n => (a n : ℂ)
  set δ := min (1 / 2) (ε ^ 2 / 4)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  set c : ℝ := σ₀ + 1
  set r : ℝ := 1 + δ / 2
  set x₀ : ℝ := c - r
  have hx₀ : x₀ < σ₀ := by simp only [x₀, c, r]; linarith
  have hball : DifferentiableOn ℂ F (Metric.ball (c : ℂ) (1 + δ)) := hF.mono (ball_subset σ₀ ε hε)
  have hz : ((x₀ : ℝ) : ℂ) ∈ Metric.ball (c : ℂ) (1 + δ) := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [x₀, r]
    rw [show c - (1 + δ / 2) - c = -(1 + δ / 2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith
  -- the coefficients
  have hab : ∀ k, abscissaOfAbsConv (logMul^[k] f) < ((c : ℂ)).re := by
    intro k
    rw [LSeries.abscissaOfAbsConv_logPowMul, hσ]
    simp only [Complex.ofReal_re, c]
    exact_mod_cast (by linarith : σ₀ < σ₀ + 1)
  let h : ℕ → ℕ → ℝ := fun k n => if n = 0 then 0 else a n * Real.log n ^ k * (n : ℝ) ^ (-c)
  have hterm : ∀ k n, term (logMul^[k] f) (c : ℂ) n = ((h k n : ℝ) : ℂ) := by
    intro k n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h]
    · rw [term_of_ne_zero hn.ne', logMul_iterate]
      simp only [h, ite_eq_right_of_eq_false _ _ (eq_false hn.ne'), f]
      have h1 : ((n : ℂ) ^ (c : ℂ)) = (((n : ℝ) ^ c : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
      have h2 : Complex.log n = ((Real.log n : ℝ) : ℂ) := (Complex.ofReal_natCast n ▸ (Complex.ofReal_log (Nat.cast_nonneg n)).symm)
      rw [h1, h2, Real.rpow_neg (Nat.cast_nonneg n)]
      push_cast
      ring
  have hsum_k : ∀ k, Summable (h k) := by
    intro k
    have := (LSeriesSummable_of_abscissaOfAbsConv_lt_re (hab k))
    unfold LSeriesSummable at this
    rw [show term (logMul^[k] f) (c : ℂ) = fun n => ((h k n : ℝ) : ℂ) from funext (hterm k)] at this
    exact Complex.summable_ofReal.1 this
  have hL : ∀ k, LSeries (logMul^[k] f) c = ((∑' n, h k n : ℝ) : ℂ) := by
    intro k
    rw [LSeries]; simp_rw [hterm]; exact (Complex.ofReal_tsum _).symm
  -- Taylor expansion at `c`, evaluated at `x₀ = c − r`
  have htay := Complex.hasSum_taylorSeries_on_ball hball hz
  have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : F =ᶠ[𝓝 (c : ℂ)] LSeries f := by
    filter_upwards [hopen.mem_nhds (show σ₀ < ((c : ℝ) : ℂ).re by simp [c])] with s hs
    exact hFeq s hs
  set T : ℕ → ℝ := fun k => (k.factorial : ℝ)⁻¹ * r ^ k * ∑' n, h k n
  have hcoef : ∀ k, (k.factorial : ℂ)⁻¹ • (((x₀ : ℝ) : ℂ) - c) ^ k • iteratedDeriv k F c = ((T k : ℝ) : ℂ) := by
    intro k
    rw [(hev.iteratedDeriv k).eq_of_nhds, LSeries_iteratedDeriv k (hab 0 |>.trans_eq' (by simp)), hL]
    have hxc : (((x₀ : ℝ) : ℂ) - c) = -((r : ℝ) : ℂ) := by simp only [x₀]; push_cast; ring
    rw [hxc]
    simp only [smul_eq_mul, T]
    push_cast
    rw [neg_pow]
    ring_nf
    rw [show ((-1 : ℂ)) ^ (k * 2) = 1 by rw [pow_mul']; norm_num, mul_one]
  simp only [hcoef] at htay
  have hT : Summable T := Complex.summable_ofReal.1 htay.summable
  -- Tonelli
  let g : ℕ × ℕ → ℝ := fun p => (p.1.factorial : ℝ)⁻¹ * r ^ p.1 * h p.1 p.2
  have hr0 : 0 ≤ r := by positivity
  have hh0 : ∀ k n, 0 ≤ h k n := by
    intro k n
    simp only [h]
    split_ifs with hn
    · exact le_rfl
    · have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
      have := ha n
      positivity
  have hg0 : 0 ≤ g := fun p => by
    simp only [g, Pi.zero_apply]; have := hh0 p.1 p.2; positivity
  have hgsum : Summable g := by
    refine (summable_prod_of_nonneg hg0).2 ⟨fun k => by simp only [g]; exact (hsum_k k).mul_left _, ?_⟩
    simp only [g, tsum_mul_left]
    exact hT
  have hgswap : Summable (fun p : ℕ × ℕ => g (p.2, p.1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.2 hgsum
  have hcol := ((summable_prod_of_nonneg (fun p => hg0 (p.2, p.1))).1 hgswap).2
  -- the column sums are `a_n n^{−x₀}`
  have hcolval : ∀ n, ∑' k, g (k, n) = if n = 0 then 0 else a n * (n : ℝ) ^ (-x₀) := by
    intro n
    simp only [g, h]
    split_ifs with hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ∀ k, (k.factorial : ℝ)⁻¹ * r ^ k * (a n * Real.log n ^ k * (n : ℝ) ^ (-c)) =
          (a n * (n : ℝ) ^ (-c)) * ((r * Real.log n) ^ k / k.factorial) := by
        intro k; rw [mul_pow]; field_simp
      simp_rw [e]
      rw [tsum_mul_left, ← congrFun NormedSpace.exp_eq_tsum_div, ← Real.exp_eq_exp_ℝ,
        show r * Real.log n = Real.log n * r by ring, ← Real.rpow_def_of_pos hnpos, mul_assoc,
        ← Real.rpow_add hnpos]
      congr 2
      simp only [x₀]; ring
  simp only [hcolval] at hcol
  have hsumm : LSeriesSummable f (x₀ : ℂ) := by
    unfold LSeriesSummable
    rw [show term f (x₀ : ℂ) = fun n => ((if n = 0 then 0 else a n * (n : ℝ) ^ (-x₀) : ℝ) : ℂ) from
      funext (term_ofReal a x₀)]
    exact Complex.summable_ofReal.2 hcol
  have hle := hsumm.abscissaOfAbsConv_le
  rw [hσ] at hle
  simp only [Complex.ofReal_re] at hle
  exact absurd (EReal.coe_le_coe_iff.1 hle) (not_le.2 hx₀)

end LeanBase.Classical
