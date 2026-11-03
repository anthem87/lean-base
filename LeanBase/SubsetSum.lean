module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
set_option autoImplicit false

/-!
# Subset sums and Brown's gap-filling criterion

Extracted from arcs-algo (github.com/anthem87/arcs-algo, commit 372ba68, file ArcsAlgo/Checker.lean, first part, and ArcsAlgo/Brown.lean), same author and licence.

* `IsSubsetSum W T`: some set of distinct indices into `W` has weights summing to `T`.
* `brown`: for sorted weights, every `0 ≤ T ≤ Σ W` is a subset sum iff `w_{k+1} ≤ 1 + S_k`.
-/

@[expose] public section

namespace LeanBase

open Finset

/-- `T` is a subset sum of `W`: some set of distinct indices into `W` has weights summing to `T`.
-/
def IsSubsetSum (W : List ℕ) (T : ℕ) : Prop :=
  ∃ s : Finset (Fin W.length), ∑ i ∈ s, W.get i = T

/-! ### Structural lemmas on `IsSubsetSum` -/

/-- Over the empty list the only subset sum is `0` (base case of the subset-sum predicate). -/
theorem isSubsetSum_nil {T : ℕ} : IsSubsetSum [] T ↔ T = 0 := by
  constructor
  · rintro ⟨s, rfl⟩
    exact Finset.sum_eq_zero fun i _ => Fin.elim0 i
  · rintro rfl
    exact ⟨∅, by simp⟩

/-- Splitting a subset of the indices of `a :: W` into the part with index `0` and the rest
(auxiliary for the subset-sum predicate). -/
private theorem sum_cons_split (a : ℕ) (W : List ℕ) (s : Finset (Fin (W.length + 1))) :
    ∑ i ∈ s, (a :: W).get i =
      (if (0 : Fin (W.length + 1)) ∈ s then a else 0) +
        ∑ i ∈ s.preimage Fin.succ (Fin.succ_injective _).injOn, W.get i := by
  have h1 : ∀ {m : ℕ} (t : Finset (Fin m)) (f : Fin m → ℕ),
      ∑ i ∈ t, f i = ∑ i, if i ∈ t then f i else 0 := fun t f => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h1 (s.preimage _ _), Fin.sum_univ_succ]
  simp [Finset.mem_preimage]

/-- The recursion of the subset-sum predicate on the first weight: a subset of
`a :: W` either omits `a` or takes it. -/
theorem isSubsetSum_cons {a : ℕ} {W : List ℕ} {T : ℕ} :
    IsSubsetSum (a :: W) T ↔ IsSubsetSum W T ∨ ∃ T', IsSubsetSum W T' ∧ T = a + T' := by
  constructor
  · rintro ⟨s, hs⟩
    have := (sum_cons_split a W s).symm.trans hs
    split_ifs at this
    · exact Or.inr ⟨_, ⟨_, rfl⟩, this.symm⟩
    · exact Or.inl ⟨_, (zero_add _).symm.trans this⟩
  · rintro (⟨s, rfl⟩ | ⟨_, ⟨s, rfl⟩, rfl⟩)
    · refine ⟨s.map (Fin.succEmb _), ?_⟩
      rw [Finset.sum_map]
      simp
    · refine ⟨insert 0 (s.map (Fin.succEmb _)), ?_⟩
      rw [Finset.sum_insert (by simp [Fin.succ_ne_zero]), Finset.sum_map]
      simp

/-- The subset-sum predicate, phrased with sublists: `T` is a subset sum of
`W` iff some sublist of `W` sums to `T`. -/
theorem isSubsetSum_iff_sublist {W : List ℕ} {T : ℕ} :
    IsSubsetSum W T ↔ ∃ L : List ℕ, L.Sublist W ∧ L.sum = T := by
  induction W generalizing T with
  | nil => simp [isSubsetSum_nil, eq_comm]
  | cons a W ih =>
    rw [isSubsetSum_cons]
    simp only [ih, List.sublist_cons_iff]
    constructor
    · rintro (⟨L, hL, rfl⟩ | ⟨_, ⟨L, hL, rfl⟩, rfl⟩)
      · exact ⟨L, Or.inl hL, rfl⟩
      · exact ⟨a :: L, Or.inr ⟨L, rfl, hL⟩, by simp⟩
    · rintro ⟨L, hL | ⟨r, rfl, hr⟩, rfl⟩
      · exact Or.inl ⟨L, hL, rfl⟩
      · exact Or.inr ⟨_, ⟨r, hr, rfl⟩, by simp⟩

/-- Every subset sum is at most the total weight (`T ≤ Σ W`). -/
theorem le_sum_of_isSubsetSum {W : List ℕ} {T : ℕ} (h : IsSubsetSum W T) : T ≤ W.sum := by
  obtain ⟨L, hL, rfl⟩ := isSubsetSum_iff_sublist.1 h
  exact hL.sum_le_sum (fun _ _ => Nat.zero_le _)

/-! ### Brown's criterion (gap filling) -/


/-- The direction `←` of Brown's criterion, for the prefix of length `k`: if
`w_{j+1} ≤ 1 + S_j` for every `j < k`, every `T ≤ S_k` is a sum of a sublist of `W.take k`.
No sortedness is needed. -/
theorem brown_prefix (W : List ℕ)
    (h : ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum) :
    ∀ k ≤ W.length, ∀ T ≤ (W.take k).sum, ∃ L : List ℕ, L.Sublist (W.take k) ∧ L.sum = T := by
  intro k
  induction k with
  | zero => intro _ T hT; exact ⟨[], List.nil_sublist _, by simp at hT; simp [hT]⟩
  | succ k ih =>
    intro hk T hT
    have hk' : k < W.length := hk
    have htake : W.take (k + 1) = W.take k ++ [W[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some]
    have hw := h k hk'
    simp only [List.get_eq_getElem] at hw
    rw [htake] at hT ⊢
    rw [List.sum_append, List.sum_singleton] at hT
    by_cases hT' : T ≤ (W.take k).sum
    · obtain ⟨L, hL, rfl⟩ := ih (by omega) T hT'
      exact ⟨L, hL.trans (List.sublist_append_left _ _), rfl⟩
    · obtain ⟨L, hL, hs⟩ := ih (by omega) (T - W[k]) (by omega)
      exact ⟨L ++ [W[k]], hL.append_right _, by rw [List.sum_append, hs]; simp; omega⟩

/-- The direction `←` of Brown's criterion (gap filling): if `w_{k+1} ≤ 1 + S_k` for every
`k < n`, every `T ≤ Sₙ` is a subset sum. This holds for any list of weights, sorted or not. -/
theorem brown_mpr (W : List ℕ)
    (h : ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum) :
    ∀ T ≤ W.sum, IsSubsetSum W T := by
  intro T hT
  obtain ⟨L, hL, hs⟩ := brown_prefix W h W.length le_rfl T (by rwa [List.take_length])
  exact isSubsetSum_iff_sublist.2 ⟨L, by rwa [List.take_length] at hL, hs⟩

/-- The direction `→` of Brown's criterion: if `W` is sorted increasingly and every
`T ≤ Sₙ` is a subset sum, then `w_{k+1} ≤ 1 + S_k` for every `k < n`. Sortedness is needed
(`W = [2, 1]` is a counterexample without it); positivity is not. -/
theorem brown_mp (W : List ℕ) (hW : W.Pairwise (· ≤ ·))
    (h : ∀ T ≤ W.sum, IsSubsetSum W T) :
    ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum := by
  intro k hk
  simp only [List.get_eq_getElem]
  by_contra hlt
  replace hlt := Nat.lt_of_not_le hlt
  -- The target `S_k + 1` lies in `[0, Sₙ]` but is not a subset sum.
  have hdrop := List.drop_eq_getElem_cons hk
  have hsum : (W.take k).sum + 1 ≤ W.sum := by
    rw [← List.sum_take_add_sum_drop W k, hdrop, List.sum_cons]
    omega
  obtain ⟨L, hL, hs⟩ := isSubsetSum_iff_sublist.1 (h _ hsum)
  rw [← List.take_append_drop k W, List.sublist_append_iff] at hL
  obtain ⟨L₁, L₂, rfl, hL₁, hL₂⟩ := hL
  have h₁ : L₁.sum ≤ (W.take k).sum := hL₁.sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [List.sum_append] at hs
  cases L₂ with
  | nil => simp at hs; omega
  | cons x L₂ =>
    -- `x` is a weight of index `≥ k`, hence `x ≥ w_{k+1} > S_k + 1`.
    have hx : x ∈ W.drop k := hL₂.subset List.mem_cons_self
    have hsorted : (W.drop k).Pairwise (· ≤ ·) := hW.sublist (List.drop_sublist _ _)
    rw [hdrop] at hx hsorted
    have hkx : W[k] ≤ x := by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact le_rfl
      · exact List.pairwise_cons.1 hsorted |>.1 x hx
    have : x ≤ (x :: L₂).sum := List.le_sum_of_mem List.mem_cons_self
    omega

/-- Brown's criterion (gap filling, Brown): for weights `w₁ ≤ … ≤ wₙ`, every
`0 ≤ T ≤ Sₙ` is a subset sum iff `w_{k+1} ≤ 1 + S_k` for every `0 ≤ k < n`.
Sortedness is used only in the direction `→` (see `brown_mp`, `brown_mpr`); the positivity
hypothesis is not used in either direction. -/
theorem brown (W : List ℕ) (hW : W.Pairwise (· ≤ ·)) (_hpos : ∀ w ∈ W, 0 < w) :
    (∀ T ≤ W.sum, IsSubsetSum W T) ↔
      ∀ k (hk : k < W.length), W.get ⟨k, hk⟩ ≤ 1 + (W.take k).sum :=
  ⟨brown_mp W hW, brown_mpr W⟩

end LeanBase
