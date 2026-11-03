module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false

/-!
# Prime sums: `p m`, `S(x) = 1 + Σ_{q ≤ x} q`, Bertrand and the grid step

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Remark22.lean), same author and licence.

`p m` is the `(m+1)`-st prime (`p 0 = 2`) and `S(x) = 1 + Σ_{q ≤ x} q` is the sum of `1, 2, 3, 5, …` up to `x`.

* `r_lt_one`: `p_{m+1} < 2p_m ≤ 1 + S_{p_m}`, so `r_m = p_{m+1}/(1 + S_{p_m}) < 1` (Bertrand's
  postulate, Mathlib, and `p_m ≤ 2 + Σ_{q < p_m} q` by induction: `p_le_sum`).
* `grid_step`: `Δ_m = log S_{p_{m+1}} − log S_{p_m} = log(1 + p_{m+1}/S_{p_m})
  = log(1 + r_m(1 + 1/S_{p_m})) ≤ log(2 + 1/S_{p_m})`, exactly.
* `r_asymp`: `m·r_m → 2` and `m·Δ_m → 2`, with the consequences of the prime number theorem
  `p_{m+1}/p_m → 1`, `S_{p_m} ∼ m p_m/2` as cited hypothesis (`PNTcons`; Mathlib has no PNT).
-/

open Finset Real Filter Topology

@[expose] public section

namespace LeanBase.PrimeSums

/-- `p m` is the `(m+1)`-st prime (`p 0 = 2`). -/
noncomputable def p (m : ℕ) : ℕ := Nat.nth Nat.Prime m

/-- `S(x) = 1 + Σ_{q prime, q ≤ x} q`, the sum of the elements `≤ x` of `{1, 2, 3, 5, …}`. -/
def S (x : ℕ) : ℕ := 1 + ∑ q ∈ (range (x + 1)).filter Nat.Prime, q

theorem p_prime (m : ℕ) : (p m).Prime := Nat.prime_nth_prime m

theorem p_lt_succ (m : ℕ) : p m < p (m + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr (lt_add_one m)

theorem p_ge_two (m : ℕ) : 2 ≤ p m := (p_prime m).two_le

/-- The primes below `p (m+1)` are those up to `p m`. -/
theorem primes_lt_succ (m : ℕ) :
    (range (p (m + 1))).filter Nat.Prime = (range (p m + 1)).filter Nat.Prime := by
  ext q
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_nth_of_lt_nth_succ h1 h2), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨lt_of_le_of_lt (Nat.le_of_lt_succ h1) (p_lt_succ m), h2⟩

/-- **Bertrand**: `p_{m+1} < 2p_m`. -/
theorem p_succ_lt (m : ℕ) : p (m + 1) < 2 * p m := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (p m) (by have := p_ge_two m; omega)
  have hne : q ≠ 2 * p m := by
    rintro rfl
    exact Nat.not_prime_mul (by norm_num) (by have := p_ge_two m; omega) hq
  have hle : p (m + 1) ≤ q := by
    by_contra h; push Not at h
    have := Nat.le_nth_of_lt_nth_succ h hq
    unfold p at h1; omega
  omega

/-- `p_m ≤ 2 + Σ_{q < p_m} q`, by induction with Bertrand's postulate. -/
theorem p_le_sum (m : ℕ) : p m ≤ 2 + ∑ q ∈ (range (p m)).filter Nat.Prime, q := by
  induction m with
  | zero =>
    have : p 0 = 2 := Nat.nth_prime_zero_eq_two
    rw [this]; omega
  | succ m ih =>
    rw [primes_lt_succ, range_add_one, filter_insert, if_pos (p_prime m), sum_insert (by simp)]
    have := p_succ_lt m
    omega

/-- **Completeness**: `r_m = p_{m+1}/(1 + S_{p_m}) < 1`, since
`p_{m+1} < 2p_m ≤ 1 + S_{p_m}`. -/
theorem r_lt_one (m : ℕ) : p (m + 1) < 2 * p m ∧ 2 * p m ≤ 1 + S (p m) := by
  refine ⟨p_succ_lt m, ?_⟩
  unfold S
  rw [range_add_one, filter_insert, if_pos (p_prime m), sum_insert (by simp)]
  have := p_le_sum m
  omega

/-- `S_{p_{m+1}} = S_{p_m} + p_{m+1}`. -/
theorem S_succ (m : ℕ) : S (p (m + 1)) = S (p m) + p (m + 1) := by
  unfold S
  rw [range_add_one, filter_insert, if_pos (p_prime (m + 1)), sum_insert (by simp), primes_lt_succ]
  ring

/-- `r_m = p_{m+1}/(1 + S_{p_m})`. -/
noncomputable def r (m : ℕ) : ℝ := p (m + 1) / (1 + S (p m))

theorem S_pos (x : ℕ) : (0 : ℝ) < S x := by unfold S; positivity

/-- **The grid step** (exact):
`Δ_m = log S_{p_{m+1}} − log S_{p_m} = log(1 + p_{m+1}/S_{p_m}) = log(1 + r_m(1 + 1/S_{p_m}))`,
and completeness `r_m ≤ 1` reads `Δ_m ≤ log(2 + 1/S_{p_m})`. -/
theorem grid_step (m : ℕ) :
    log (S (p (m + 1))) - log (S (p m)) = log (1 + p (m + 1) / (S (p m) : ℝ)) ∧
      log (1 + p (m + 1) / (S (p m) : ℝ)) = log (1 + r m * (1 + 1 / (S (p m) : ℝ))) ∧
      log (S (p (m + 1))) - log (S (p m)) ≤ log (2 + 1 / (S (p m) : ℝ)) := by
  have hS := S_pos (p m)
  have hS1 := S_pos (p (m + 1))
  have e1 : log (S (p (m + 1))) - log (S (p m)) = log (1 + p (m + 1) / (S (p m) : ℝ)) := by
    rw [← log_div hS1.ne' hS.ne', S_succ]; push_cast; congr 1; field_simp
  have e2 : (1 : ℝ) + p (m + 1) / (S (p m) : ℝ) = 1 + r m * (1 + 1 / (S (p m) : ℝ)) := by
    unfold r; field_simp; ring
  refine ⟨e1, by rw [e2], ?_⟩
  rw [e1]
  apply log_le_log (by positivity)
  have h := (r_lt_one m).1
  have h2 := (r_lt_one m).2
  have : (p (m + 1) : ℝ) ≤ 1 + S (p m) := by exact_mod_cast (h.trans_le h2).le
  have : (p (m + 1) : ℝ) / S (p m) ≤ (1 + S (p m)) / S (p m) := div_le_div_of_nonneg_right this hS.le
  have e : (1 + (S (p m) : ℝ)) / S (p m) = 1 + 1 / S (p m) := by field_simp; ring
  linarith

/-- **Consequences of the prime number theorem** (cited: e.g. Hardy–Wright, Thm 8 and §22.19, with
partial summation): `p_{m+1}/p_m → 1` and `S_{p_m}/(m p_m) → 1/2`. Mathlib has no prime number
theorem; this is an explicit hypothesis, never an axiom. -/
def PNTcons : Prop :=
  Tendsto (fun m : ℕ => (p (m + 1) : ℝ) / p m) atTop (𝓝 1) ∧
    Tendsto (fun m : ℕ => (S (p m) : ℝ) / (m * p m)) atTop (𝓝 (1 / 2))

/-- **Asymptotics**, with the consequences of the PNT as hypothesis:
`m·r_m → 2` and `m·Δ_m → 2`. -/
theorem r_asymp (h : PNTcons) :
    Tendsto (fun m : ℕ => m * r m) atTop (𝓝 2) ∧
      Tendsto (fun m : ℕ => m * (log (S (p (m + 1))) - log (S (p m)))) atTop (𝓝 2) := by
  obtain ⟨h1, h2⟩ := h
  -- `m r_m = (p_{m+1}/p_m) · (m p_m/S) · (S/(1 + S))`
  have hSinf : Tendsto (fun m : ℕ => (S (p m) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun m : ℕ => (m : ℝ))
    · intro m
      have hp : m ≤ p m := by
        induction m with
        | zero => exact Nat.zero_le _
        | succ m ih => have := p_lt_succ m; omega
      have : (p m : ℝ) ≤ S (p m) := by
        have := (r_lt_one m).2
        have h2 : p m ≤ S (p m) := by omega
        exact_mod_cast h2
      have : (m : ℝ) ≤ p m := by exact_mod_cast hp
      linarith
    · exact tendsto_natCast_atTop_atTop
  have hq : Tendsto (fun m : ℕ => (S (p m) : ℝ) / (1 + S (p m))) atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 / (1 + 1 / (S (p m) : ℝ))) atTop (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).add (hSinf.inv_tendsto_atTop.const_mul 1))
      simp only [mul_zero, add_zero] at this
      have h' := this.inv₀ (by norm_num)
      simpa [one_div] using h'
    refine this.congr fun m => ?_
    have := S_pos (p m); field_simp; ring
  have h2' : Tendsto (fun m : ℕ => (m * p m : ℝ) / S (p m)) atTop (𝓝 2) := by
    have := h2.inv₀ (by norm_num)
    norm_num at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    simp only [Pi.inv_apply]
  have hr : Tendsto (fun m : ℕ => m * r m) atTop (𝓝 2) := by
    have := (h1.mul h2').mul hq
    simp only [one_mul, mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with m hm
    unfold r
    have hp0 : (0 : ℝ) < p m := by have := p_ge_two m; positivity
    have := S_pos (p m)
    field_simp
  refine ⟨hr, ?_⟩
  -- `m Δ_m = m·x_m·(log(1 + x_m)/x_m)` with `x_m = r_m(1 + 1/S) → 0`
  have hx : Tendsto (fun m : ℕ => r m * (1 + 1 / (S (p m) : ℝ))) atTop (𝓝 0) := by
    have hr0 : Tendsto (fun m : ℕ => r m) atTop (𝓝 0) := by
      have := hr.div_atTop tendsto_natCast_atTop_atTop
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with m hm
      field_simp
    have := hr0.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hSinf.inv_tendsto_atTop.const_mul 1))
    simpa using this
  have hmx : Tendsto (fun m : ℕ => m * (r m * (1 + 1 / (S (p m) : ℝ)))) atTop (𝓝 2) := by
    have := hr.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (hSinf.inv_tendsto_atTop.const_mul 1))
    simp only [mul_zero, add_zero, mul_one] at this
    refine this.congr fun m => ?_
    simp only [one_div, one_mul, Pi.inv_apply]; ring
  have hlog : Tendsto (fun x : ℝ => log (1 + x) / x) (𝓝[≠] 0) (𝓝 1) := by
    have hd := Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)
    have hs := hd.tendsto_slope_zero
    simp only [log_one, sub_zero, inv_one, smul_eq_mul] at hs
    refine hs.congr fun x => ?_
    ring
  -- combine
  have hcomb : Tendsto (fun m : ℕ => m * (r m * (1 + 1 / (S (p m) : ℝ))) *
      (log (1 + r m * (1 + 1 / (S (p m) : ℝ))) / (r m * (1 + 1 / (S (p m) : ℝ))))) atTop (𝓝 2) := by
    have hx' : Tendsto (fun m : ℕ => r m * (1 + 1 / (S (p m) : ℝ))) atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hx
      filter_upwards with m
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have : 0 < r m := by unfold r; have := p_ge_two (m + 1); have := S_pos (p m); positivity
      have : 0 < 1 + 1 / (S (p m) : ℝ) := by have := S_pos (p m); positivity
      positivity
    have := hmx.mul (hlog.comp hx')
    simpa using this
  refine hcomb.congr fun m => ?_
  obtain ⟨e1, e2, -⟩ := grid_step m
  have hr0 : 0 < r m := by unfold r; have := p_ge_two (m + 1); have := S_pos (p m); positivity
  have : 0 < 1 + 1 / (S (p m) : ℝ) := by have := S_pos (p m); positivity
  rw [e1, e2]
  field_simp

end LeanBase.PrimeSums
