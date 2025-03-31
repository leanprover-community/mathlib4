/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Span as a Sum

In this file, we show that any element in the two-sided ideal span of a set `s` in `R` is a
finite sum of the form `∑ i, rᵢ * sᵢ * tᵢ` where `rᵢ, tᵢ ∈ R, sᵢ ∈ s` .

## Main Results

* `TwoSidedIdeal.mem_span_iff_exists_fin`: `x ∈ span s` iff there exists a linear combination
  `∑ i, rᵢ * sᵢ * rᵢ' = x` where only finite terms are non-zero.
* `TwoSidedIdeal.mem_span_ideal_iff_exists_fin`: elements in the two-sided ideal closure of an
  (left) ideal `I` is in the form of `∑ i, xᵢ * rᵢ`(`rᵢ ∈ R` and `xᵢ ∈ I`) where only
  finite terms are non-zero.

-/
variable {R : Type*} [Ring R]

namespace TwoSidedIdeal

lemma mem_span_iff_exists_fin (s : Set R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xL : ι → R) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, xL i * (y i : R) * xR i := by
  constructor
  · intro hx
    induction hx using span_induction with
    | mem x h => exact ⟨PUnit, inferInstance, fun _ ↦ 1, fun _ ↦ 1, fun _ ↦ ⟨x, h⟩, by simp⟩
    | zero => exact ⟨Empty, inferInstance, fun _ ↦ 1, fun _ ↦ 1, Empty.elim, by simp⟩
    | add x y hx hy hx1 hy1 =>
      obtain ⟨ι1, _, xL1, xR1, y1, eq1⟩ := hx1
      obtain ⟨ι2, _, xL2, xR2, y2, eq2⟩ := hy1
      exact ⟨(ι1 ⊕ ι2), inferInstance, Sum.elim xL1 xL2, Sum.elim xR1 xR2,
        Sum.elim y1 y2, by simp [eq1, eq2]⟩
    | neg x hx hx1 =>
      obtain ⟨ι, _, xL, xR, y, eq⟩ := hx1
      exact ⟨ι, inferInstance, fun i ↦ - (xL i), xR, y, by simp [eq]⟩
    | left_absorb a y hx hx1 =>
      obtain ⟨ι, _, xL, xR, y, eq⟩ := hx1
      exact ⟨ι, inferInstance, fun i ↦ a * xL i, xR, y, by
        simp [eq, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]⟩
    | right_absorb b y hx hx1 =>
      obtain ⟨ι, _, xL, xR, y, eq⟩ := hx1
      exact ⟨ι, inferInstance, xL, fun i ↦ xR i * b, y, by
        simp [eq, Finset.mul_sum, Finset.sum_mul, ← mul_assoc]⟩
  · rintro ⟨_, _, _, _, _, rfl⟩
    exact finsetSum_mem _ _ _ <| fun _ _ ↦ mul_mem_right _ _ _ <| mul_mem_left _ _ _ <|
      subset_span <| Subtype.coe_prop _

lemma mem_span_ideal_iff_exists_fin (s : Ideal R) (x : R) :
    x ∈ span s ↔
    ∃ (ι : Type) (_ : Fintype ι) (xR : ι → R) (y : ι → s),
    x = ∑ i : ι, (y i : R) * xR i := by
  rw [mem_span_iff_exists_fin]
  exact ⟨fun ⟨n, fin, xL, xR, y, _⟩ ↦ ⟨n, fin, xR, fun i ↦ ⟨xL i * y i, s.mul_mem_left _ (y i).2⟩,
    by simp_all⟩, fun ⟨n, fin, xR, y, hy⟩ ↦ ⟨n, fin, 1, xR, y, by simp_all⟩⟩

lemma mem_span_range_iff_exists_multisetSum (ι : Type*) (v : ι → R) (x : R) :
    x ∈ span (Set.range v) ↔ ∃ l : Multiset (R × ι × R),
    (l.map fun | (l, i, r) => l * v i * r).sum = x := by
  constructor
  · rw [mem_span_iff_exists_fin]
    rintro ⟨κ, _, xL, xR, y, rfl⟩
    choose e he using fun k ↦ (y k).2
    exact ⟨Multiset.map (fun i ↦ (xL i, e i, xR i)) (Finset.univ.val : Multiset κ), by simp [he]⟩
  · rintro ⟨l, rfl⟩
    refine multiset_sum_mem _ ?_
    simp only [Multiset.mem_map, Prod.exists, forall_exists_index, and_imp]
    rintro xL xR i r hi rfl
    exact mul_mem_right _ _ _ <| mul_mem_left _ _ _ <| subset_span <| Set.mem_range_self _

end TwoSidedIdeal
