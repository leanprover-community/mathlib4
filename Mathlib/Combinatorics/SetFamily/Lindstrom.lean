/-
Copyright (c) 2025 Strahinja Gvozdić, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Strahinja Gvozdić, Bhavik Mehta
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Qify

/-!
# Lindström

This file proves the classical theorem of Lindström about subfamilies with equal unions, as well as
its stronger version about subfamilies with equal unions and intersections.

## Main declarations

* `Finset.exists_disjoint_finset_biUnion_eq_biUnion`: Lindström's theorem. Suppose we are given a
  finite base set of size `n` and nonempty subsets `f₁,...,fₘ` of the base set. If `n + 1 ≤ m`, then
  there exist disjoint nonempty sets of indices `I, J ⊆ {1,...,m}` such that
  `⋃ i ∈ I, fᵢ = ⋃ j ∈ J, fⱼ`.
* `Finset.exists_disjoint_finset_biUnion_eq_biUnion_inf_eq_inf`: Stronger version of Lindström's
  theorem. Given `n` and `f₁,...,fₘ` as before, if `n + 2 ≤ m`, then there exist disjoint nonempty
  sets of indices `I, J ⊆ {1,...,m}` such that `⋃ i ∈ I, fᵢ = ⋃ j ∈ J, fⱼ` and
  `⋂ i ∈ I, fᵢ = ⋂ j ∈ J, fⱼ`.
-/
open Finset Fintype

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

private theorem Finset.exists_neg_of_sum_zero_of_exists_nonzero
    {ι M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M] {s : Finset ι}
    (f : ι → M) (h₁ : ∑ i ∈ s, f i = 0) (h₂ : ∃ i ∈ s, f i ≠ 0) :
    ∃ i ∈ s, f i < 0 := by
  obtain ⟨i, hi, hfi⟩ := h₂
  by_contra! h
  have : ¬ ∃ x ∈ s, 0 < f x := by simp [← sum_pos_iff_of_nonneg h, h₁]
  exact this ⟨i, hi, lt_of_le_of_ne' (h i hi) hfi⟩

omit [Fintype α] [Fintype β] in
private lemma biUnion_eq_empty (s : Finset α) (f : α → Finset β) :
    s.biUnion f = ∅ ↔ ∀ a ∈ s, f a = ∅ := by
  grind

/-- **Lindström's theorem** Suppose we are given a finite base set of size `n` and nonempty subsets
  `f₁,...,fₘ` of the base set. If `n + 1 ≤ m`, then there exist disjoint nonempty sets of indices
  `I, J ⊆ {1,...,m}` such that `⋃ i ∈ I, fᵢ = ⋃ j ∈ J, fⱼ`. -/
theorem Finset.exists_disjoint_finset_biUnion_eq_biUnion (f : α → Finset β)
    (h : Fintype.card β + 1 ≤ Fintype.card α) (hf : ∀ i, (f i).Nonempty) :
    ∃ I J : Finset α, Disjoint I J ∧ I.Nonempty ∧ J.Nonempty ∧ I.biUnion f = J.biUnion f := by
  -- We define the family of characteristic vectors of the given sets. Since the number of
  -- characteristic vectors is larger than the dimension of the space, they need to be linearly
  -- dependent, i.e. there are scalars `cᵢ` not all zero such that `∑ i ∈ I, cᵢvᵢ = 0`.
  let v (i : α) (x : β) : ℚ := if x ∈ f i then 1 else 0
  have hv : ¬ LinearIndependent ℚ v := by
    intro h
    have : Fintype.card α ≤ Fintype.card β := by simpa using h.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, hci⟩ : ∃ c : α → ℚ, ∑ i, c i • v i = 0 ∧ ∃ i, c i ≠ 0 := by
    simpa [Fintype.linearIndependent_iff] using hv
  -- We take for `I` the set of indices whose corresponding scalars are positive. Similarly,
  -- indices in `J` correspond to negative scalars. These will clearly be disjoint.
  let I : Finset α := { i | 0 < c i }
  let J : Finset α := { i | c i < 0 }
  -- First we show that `⋃ i ∈ I, fᵢ = ⋃ j ∈ J, fⱼ` by showing the two inclusions separately. To
  -- show the inclusions, note that the existence of a strictly positive term in the sum `∑ i, cᵢvᵢ`
  -- implies the existence of the strictly negative one and vice-versa.
  have : ∀ a ∈ I, ∀ x ∈ f a, ∃ b ∈ J, x ∈ f b := by
    intro a ha x hx
    have hzero : ∑ i, c i * v i x = 0 := by simpa using congr($hc x)
    have hpos : 0 < c a * v a x := by simpa [v, hx, I] using ha
    obtain ⟨b, -, hb⟩ := exists_neg_of_sum_zero_of_exists_nonzero _ hzero (by grind)
    simp [mul_ite, v] at hb
    exact ⟨b, by grind⟩
  have : ∀ b ∈ J, ∀ x ∈ f b, ∃ a ∈ I, x ∈ f a := by
    intro b hb x hx
    have hzero : ∑ i, c i * v i x = 0 := by simpa using congr($hc x)
    have hpos : c b * v b x < 0 := by simpa [v, hx, J] using hb
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_zero_of_exists_nonzero _ hzero (by grind)
    simp [mul_ite, v] at ha
    exact ⟨a, by grind⟩
  have : I.biUnion f = J.biUnion f := by grind
  -- Then we show that at least one of `I` and `J` is nonempty, which follows from the fact that
  -- at least one of `cᵢ`'s is nonzero. Using the equality of the unions, this implies that both
  -- `I` and `J` are nonempty. This concludes.
  have : I.Nonempty ∨ J.Nonempty := by grind [filter_nonempty_iff]
  have : I.Nonempty := by grind [biUnion_empty, biUnion_eq_empty, not_nonempty_iff_eq_empty]
  have : J.Nonempty := by grind [biUnion_empty, biUnion_eq_empty, not_nonempty_iff_eq_empty]
  exact ⟨I, J, by grind [disjoint_left]⟩

/-- Strengthening of the Lindström's theorem. Suppose we are given a finite base set of size `n`
  and nonempty subsets `f₁,...,fₘ` of the base set. If `n + 2 ≤ m`, then there exist disjoint
  nonempty sets of indices `I, J ⊆ {1,...,m}` such that `⋃ i ∈ I, fᵢ = ⋃ j ∈ J, fⱼ` and
  `⋂ i ∈ I, fᵢ = ⋂ j ∈ J, fⱼ`. -/
theorem Finset.exists_disjoint_finset_biUnion_eq_biUnion_inf_eq_inf (f : α → Finset β)
    (h : Fintype.card β + 2 ≤ Fintype.card α) (hf : ∀ i, (f i).Nonempty) :
    ∃ I J : Finset α, Disjoint I J ∧ I.Nonempty ∧ J.Nonempty ∧ I.biUnion f = J.biUnion f
    ∧ I.inf f = J.inf f := by
  -- Idea of the proof is similar as for the Lindström's theorem. Here we introduce a new element
  -- contained in all `fᵢ`'s to the base set, and define characteristic vectors as before.
  let β' := Option β
  let v (i : α) (x : β') : ℚ := match x with
  | some x => if x ∈ f i then 1 else 0
  | none   => 1
  have v_le_one j x : v j x ≤ 1 := by aesop
  -- Since we increased the dimension of the space of characteristic vectors by just one, it is
  -- still smaller than the number of vectors, so they need to be linearly dependent. Now everything
  -- except the equality of intersections is proven as for the Lindström's theorem.
  have hv : ¬ LinearIndependent ℚ v := by
    intro h
    have : Fintype.card α ≤ Fintype.card β + 1 := by
      simpa [← card_option] using h.fintype_card_le_finrank
    omega
  obtain ⟨c, hc, hci⟩ : ∃ c : α → ℚ, ∑ i, c i • v i = 0 ∧ ∃ i, c i ≠ 0 := by
    simpa [Fintype.linearIndependent_iff] using hv
  let I : Finset α := { i | 0 < c i }
  let J : Finset α := { i | c i < 0 }
  let Z : Finset α := { i | c i = 0 }
  have : I.Nonempty ∨ J.Nonempty := by grind [filter_nonempty_iff]
  have : ∀ a ∈ I, ∀ x ∈ f a, ∃ b ∈ J, x ∈ f b := by
    intro a ha x hx
    have hzero : ∑ i, c i * v i x = 0 := by simpa using congr($hc x)
    have hpos : 0 < c a * v a x := by simpa [v, hx, I] using ha
    obtain ⟨b, -, hb⟩ := exists_neg_of_sum_zero_of_exists_nonzero _ hzero (by grind)
    simp only [mul_ite, v] at hb
    exact ⟨b, by grind⟩
  have : ∀ b ∈ J, ∀ x ∈ f b, ∃ a ∈ I, x ∈ f a := by
    intro b hb x hx
    have hzero : ∑ i, c i * v i x = 0 := by simpa using congr($hc x)
    have hpos : c b * v b x < 0 := by simpa [v, hx, J] using hb
    obtain ⟨a, -, ha⟩ := exists_pos_of_sum_zero_of_exists_nonzero _ hzero (by grind)
    simp only [mul_ite, v] at ha
    exact ⟨a, by grind⟩
  have : I.biUnion f = J.biUnion f := by grind
  have : I.Nonempty := by grind [biUnion_empty, biUnion_eq_empty, not_nonempty_iff_eq_empty]
  have : J.Nonempty := by grind [biUnion_empty, biUnion_eq_empty, not_nonempty_iff_eq_empty]
  -- From the definition of `cᵢ` it follows that the vector `∑ i ∈ I, cᵢvᵢ` is the same as the
  -- vector `-∑ j ∈ J, cⱼvⱼ`
  have hij : ∑ i ∈ I, c i • v i = -∑ j ∈ J, c j • v j := by
    calc
          ∑ i ∈ I, c i • v i
      _ = ∑ i ∈ I, c i • v i + ∑ z ∈ Z, c z • v z + ∑ j ∈ J, c j • v j - ∑ j ∈ J, c j • v j := by
        simpa [left_eq_add] using Finset.sum_eq_zero (fun _ hi => by simp [mem_filter.mp hi])
      _ = ∑ i with 0 ≤ c i, c i • v i + ∑ j with c j < 0, c j • v j - ∑ j ∈ J, c j • v j := by
        simp [show I = {i ∈ ({i | 0 ≤ c i} : Finset α) | ¬c i = 0} by grind,
          show Z = {i ∈ ({i | 0 ≤ c i} : Finset α) | c i = 0} by grind,
          ← sum_filter_not_add_sum_filter {i | 0 ≤ c i} (fun i => c i = 0), J]
      _ = -∑ j ∈ J, c j • v j := by
        simpa [← sum_filter_add_sum_filter_not univ (fun i => 0 ≤ c i), β', v] using hc
  -- Now we are ready to prove that the intersections are equal. What we do is essentially prove
  -- that for `t = ∑ i ∈ I, cᵢ`, `x ∈ ⋂ i ∈ I, fᵢ` if and only if `(∑ i ∈ I, cᵢvᵢ)ₓ = t` (and
  -- similarly `x ∈ ⋂ j ∈ J, fⱼ` if and only if `(-∑ j ∈ J, cⱼvⱼ)ₓ = t`). This is because `vᵢ ≤ 1`,
  -- so the value of `t` (or `-t`) at the given coordinate can only be attained if and only if all
  -- `vᵢ`'s are `1` at this coordinate. It then follows using the previous fact that the
  -- intersections are equal, which concludes the proof.
  have : I.inf f = J.inf f := by
    simp [Finset.ext_iff, mem_inf]
    intro x
    constructor
    · intro hx
      by_contra!
      obtain ⟨j₀, hj₀, h⟩ := this
      suffices -∑ j ∈ J, c j * v j x < _ by exact lt_irrefl _ this
      calc
            -∑ j ∈ J, c j * v j x
        _ < -∑ j ∈ J, c j := by
          simpa using sum_lt_sum (fun j hj => by
            nth_rewrite 1 [← mul_one (c j)]
            exact (mul_le_mul_left_of_neg (mem_filter.mp hj).2).mpr (v_le_one j x)
          ) ⟨j₀, hj₀, by
            nth_rewrite 1 [← mul_one (c j₀)]
            exact (mul_lt_mul_left_of_neg (mem_filter.mp hj₀).2).mpr (by simp_all [β', v])
          ⟩
        _ = ∑ i ∈ I, c i := by
          simpa [β', v] using Eq.symm congr($hij Option.none)
        _ = ∑ i ∈ I, c i * v i x := Finset.sum_congr (rfl) (by simp_all [β', v])
        _ = -∑ j ∈ J, c j * v j x := by simpa [β', v] using congr($hij x)
    · intro hx
      by_contra!
      obtain ⟨i₀, hi₀, h⟩ := this
      suffices ∑ i ∈ I, c i * v i x < _ by exact lt_irrefl _ this
      calc
            ∑ i ∈ I, c i * v i x
        _ < ∑ i ∈ I, c i := sum_lt_sum (fun i hi => by
            nth_rewrite 2 [← mul_one (c i)]
            exact (mul_le_mul_iff_right₀ (mem_filter.mp hi).2).mpr <| v_le_one i x
          ) ⟨i₀, hi₀, by
            nth_rewrite 2 [← mul_one (c i₀)]
            exact (mul_lt_mul_iff_right₀ (mem_filter.mp hi₀).2).mpr (by simp_all [β', v])
          ⟩
        _ = -∑ j ∈ J, c j := by simpa [β', v] using congr($hij Option.none)
        _ = -∑ j ∈ J, c j * v j x := by
          simpa using Finset.sum_congr (rfl) (by simp_all [β', v])
        _ = ∑ i ∈ I, c i * v i x := by simpa [β', v] using Eq.symm congr($hij x)
  exact ⟨I, J, by grind [disjoint_left]⟩
