module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
set_option autoImplicit false

/-!
# A zero of multiplicity `m` is a pole of the logarithmic derivative (ARCS paper §4)

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Classical/ZeroSingularity.lean), same author and licence.

* `tendsto_sub_mul_logDeriv`: if `f` is analytic at `ρ` with a zero of order `m`, then
  `(s − ρ) f′(s)/f(s) → m` as `s → ρ`, `s ≠ ρ`.
* `not_analyticAt_of_logDeriv_combination`: a combination `Σ A_i f_i′/f_i + h`, with `h` analytic
  at `ρ` and `Σ A_i m_i ≠ 0`, agrees with no function analytic at `ρ` on a punctured neighbourhood.
  This is the step of Proposition 3 and Theorem S: "a zero of `L(s, χ)` gives `D` a singularity
  with coefficient `Σ_χ A_χ m_χ(ρ)`", read through the derivative `D′ = Σ_χ A_χ L′/L + h′`.
-/

@[expose] public section

namespace LeanBase.Classical

open Filter Topology

theorem tendsto_sub_mul_logDeriv {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f ρ)
    (hm : analyticOrderAt f ρ = m) :
    Tendsto (fun s => (s - ρ) * logDeriv f s) (𝓝[≠] ρ) (𝓝 (m : ℂ)) := by
  obtain ⟨g, hg, hg0, heq⟩ := (hf.analyticOrderAt_eq_natCast).1 hm
  -- near `ρ`, `f = (s − ρ)^m g` on a neighbourhood of every point
  have hev : ∀ᶠ s in 𝓝 ρ, f =ᶠ[𝓝 s] fun z => (z - ρ) ^ m * g z := by
    have := heq.eventually_nhds
    filter_upwards [this] with s hs
    filter_upwards [hs] with z hz
    simpa [smul_eq_mul] using hz
  have hgan : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  -- the formula `(s − ρ) f′/f = m + (s − ρ) g′/g` on a punctured neighbourhood
  have hformula : ∀ᶠ s in 𝓝[≠] ρ, (s - ρ) * logDeriv f s = m + (s - ρ) * (deriv g s / g s) := by
    have h1 := nhdsWithin_le_nhds (s := {ρ}ᶜ) (hev.and (hgan.and hgne))
    filter_upwards [h1, self_mem_nhdsWithin] with s ⟨hfs, hgs, hgns⟩ hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 hs
    rw [logDeriv_apply, hfs.deriv_eq, hfs.eq_of_nhds]
    have hd : deriv (fun z => (z - ρ) ^ m * g z) s =
        (m : ℂ) * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
      have h2 : HasDerivAt (fun z => (z - ρ) ^ m) ((m : ℂ) * (s - ρ) ^ (m - 1)) s := by
        simpa using ((hasDerivAt_id s).sub_const ρ).fun_pow m
      exact (h2.mul hgs.differentiableAt.hasDerivAt).deriv
    rw [hd]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have : (s - ρ) ^ m = (s - ρ) * (s - ρ) ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [this]
      field_simp
  -- the limit
  have hlim : Tendsto (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) (𝓝[≠] ρ) (𝓝 (m : ℂ)) := by
    have hc : ContinuousAt (fun s => (m : ℂ) + (s - ρ) * (deriv g s / g s)) ρ := by
      apply ContinuousAt.add continuousAt_const
      apply ContinuousAt.mul (continuousAt_id.sub continuousAt_const)
      exact (hg.deriv.continuousAt).div hg.continuousAt hg0
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
    simpa using this
  exact hlim.congr' (hformula.mono fun s hs => hs.symm)

/-- **The zero step of Proposition 3 and Theorem S** (ARCS paper §4): if `Ψ` is analytic at `ρ`, it
cannot agree on a punctured neighbourhood of `ρ` with `Σ_i A_i f_i′/f_i + h`, where every `f_i` is
analytic at `ρ` with a zero of order `m_i` (possibly `0`), `h` is analytic at `ρ`, and
`Σ_i A_i m_i ≠ 0`. -/
theorem not_analyticAt_of_logDeriv_combination {ι : Type*} (S : Finset ι) (A : ι → ℂ)
    (f : ι → ℂ → ℂ) (m : ι → ℕ) {ρ : ℂ} (hf : ∀ i ∈ S, AnalyticAt ℂ (f i) ρ)
    (hm : ∀ i ∈ S, analyticOrderAt (f i) ρ = m i) (h : ℂ → ℂ) (hh : AnalyticAt ℂ h ρ)
    (hsum : ∑ i ∈ S, A i * m i ≠ 0) (Ψ : ℂ → ℂ) (hΨ : AnalyticAt ℂ Ψ ρ) :
    ¬ ∀ᶠ s in 𝓝[≠] ρ, Ψ s = ∑ i ∈ S, A i * logDeriv (f i) s + h s := by
  intro hEq
  -- `(s − ρ) Ψ(s) → 0`
  have h0 : Tendsto (fun s => (s - ρ) * Ψ s) (𝓝[≠] ρ) (𝓝 0) := by
    have hc : ContinuousAt (fun s => (s - ρ) * Ψ s) ρ :=
      (continuousAt_id.sub continuousAt_const).mul hΨ.continuousAt
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
    simpa using this
  -- `(s − ρ)(Σ A_i f_i′/f_i + h) → Σ A_i m_i`
  have h1 : Tendsto (fun s => (s - ρ) * (∑ i ∈ S, A i * logDeriv (f i) s + h s)) (𝓝[≠] ρ)
      (𝓝 (∑ i ∈ S, A i * m i)) := by
    have hsumlim : Tendsto (fun s => ∑ i ∈ S, A i * ((s - ρ) * logDeriv (f i) s)) (𝓝[≠] ρ)
        (𝓝 (∑ i ∈ S, A i * m i)) :=
      tendsto_finsetSum _ fun i hi => (tendsto_sub_mul_logDeriv (hf i hi) (hm i hi)).const_mul _
    have hhlim : Tendsto (fun s => (s - ρ) * h s) (𝓝[≠] ρ) (𝓝 0) := by
      have hc : ContinuousAt (fun s => (s - ρ) * h s) ρ :=
        (continuousAt_id.sub continuousAt_const).mul hh.continuousAt
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
      simpa using this
    have := hsumlim.add hhlim
    rw [add_zero] at this
    refine this.congr' (Eventually.of_forall fun s => ?_)
    simp only [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : Tendsto (fun s => (s - ρ) * Ψ s) (𝓝[≠] ρ) (𝓝 (∑ i ∈ S, A i * m i)) :=
    h1.congr' (hEq.mono fun s hs => by simp only [hs])
  exact hsum (tendsto_nhds_unique h2 h0)

end LeanBase.Classical
