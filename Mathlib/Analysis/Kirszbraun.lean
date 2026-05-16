/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.WeakDual

/-
# Kirszbraun’s theorem

In this file, we prove Kirszbraun’s theorem, which says that a function `f : H₁ → H₂` between two
Hilbert spaces that is `γ`-Lipschitz on a subset `A ⊆ H₁` admits a `γ`-Lipschitz extension to the
whole space.

## References

* https://en.wikipedia.org/wiki/Kirszbraun_theorem
* https://www1.essex.ac.uk/maths/people/fremlin/n11706.pdf

-/

@[expose] public section

open scoped RealInnerProductSpace
open NNReal Set Metric

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂] {f : H₁ → H₂} {A B : Set H₁}
  {γ : ℝ≥0}

namespace LipschitzOnWith

/-- If `A` is a finite subset of `H₁` and `f : H₁ → H₂` is Lipschitz with `1` on `A` such that
for all `a ∈ A`, `‖a‖ < ‖f a‖`, then `0` does not belong to the convex hull of `f '' A`. -/
lemma zero_not_in_convexHull (hA : A.Finite) (hfx : ∀ a ∈ A, ‖a‖ < ‖f a‖)
    (hfL : LipschitzOnWith 1 f A) :
    0 ∉ convexHull ℝ (f '' A) := by
  have hp {a b} (ha : a ∈ A) (hb : b ∈ A) : ⟪a, b⟫ < ⟪f a, f b⟫ := calc
    _ = (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖ - ‖a - b‖ * ‖a - b‖) / 2 :=
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two _ _
    _ < (‖f a‖ * ‖f a‖ + ‖f b‖ * ‖f b‖ - ‖f a - f b‖ * ‖f a - f b‖) / 2 := by sorry
    _ = ⟪f a, f b⟫ :=
      (real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two _ _).symm
  intro h
  -- Suppose `0` is in the convex hull. Write `0` as a convex combination of elements from `A`.
  -- `c` is the coefficients.
  obtain ⟨c, hc⟩ := (hA.image f).convexHull_eq (R := ℝ) ▸ h
  have : ∀ y ∈ (hA.image f).toFinset, ∃ x ∈ A, f x = y := by sorry
  choose i hi using this
  have : 0 < ‖(0 : H₂)‖ ^ 2 := calc
    _ ≤ ‖∑ y : (hA.image f).toFinset, c y • i y.1 y.2‖ ^ 2 := sq_nonneg _
    _ = ⟪∑ y : (hA.image f).toFinset, c y • i y.1 y.2,
      ∑ z : (hA.image f).toFinset, c z • i z.1 z.2⟫ := (real_inner_self_eq_norm_sq _).symm
    _ = ∑ y : (hA.image f).toFinset, (∑ z : (hA.image f).toFinset,
      ⟪c y • i y.1 y.2, c z • i z.1 z.2⟫) := by sorry
    _ < ∑ y : (hA.image f).toFinset, (∑ z : (hA.image f).toFinset,
      c y * c z * ⟪i y.1 y.2, i z.1 z.2⟫) := by sorry
    _ = ∑ y ∈ (hA.image f).toFinset, (∑ z ∈ (hA.image f).toFinset, c y * c z * ⟪y, z⟫) := by sorry
    _ = ⟪∑ y ∈ (hA.image f).toFinset, c y • y, ∑ z ∈ (hA.image f).toFinset, c z • z⟫ := by sorry
    _ = ⟪(0 : H₂), 0⟫ := by
      suffices 0 = ∑ y ∈ (hA.image f).toFinset, c y • y from by grind
      -- Expand the definition of centerMass in `hc`.
      sorry
    _ = _  := real_inner_self_eq_norm_sq 0
  simp_all

/-- If `A` is a finite subset of `H₁` and `f : H₁ → H₂` is Lipschitz with `γ` on `A`, then for all
`x : H₁`, there exists `y : H₂` such that `‖y - f a‖ ≤ γ‖x - a‖` for all `a ∈ A`. -/
lemma extend_singleton (hA : A.Finite) (hfL : LipschitzOnWith γ f A) (x : H₁) :
    ∃ y, ∀ a ∈ A, ‖y - f a‖ ≤ γ * ‖x - a‖ := by
  sorry

/-- If `A, B` are finite subsets of `H₁` and `f : H₁ → H₂` is Lipschitz with `γ` on `A`, then
there exists `g : H₁ → H₂` that extends `f` and is Lipschitz with `γ` on `A ∪ B`. -/
lemma extend_finite_set (hA : A.Finite) (hB : B.Finite) (hfA : LipschitzOnWith γ f A) :
    ∃ g, LipschitzOnWith γ g (A ∪ B) ∧ EqOn f g A := by
  refine hB.induction_to ∅ (empty_subset B)
    (C := fun S => ∃ g, LipschitzOnWith γ g (A ∪ S) ∧ EqOn f g A) ?_ (fun S hBS hS => ?_)
  · simpa using ⟨f, hfA, eqOn_refl f A⟩
  choose b hb using nonempty_of_ssubset hBS
  obtain ⟨g, hg⟩ := hS
  by_cases hbs : b ∈ A ∪ S
  · exact ⟨b, hb, g, by simpa [union_insert, insert_eq_self.2 hbs] using hg.1, hg.2⟩
  obtain ⟨y, hy⟩ := hfA.extend_singleton hA b
  refine ⟨b, hb, ?_, fun x hx z hz => ?_, fun a ha => ?_⟩
  · classical
    let g : H₁ → H₂ := fun x =>
      if x ∈ A ∪ S then g x
      else if x = b then y else 0
    use g
  · have {x} (hx : x ∈ A ∪ S) : edist (g x) y ≤ γ * edist x b := by sorry
    by_cases hxa : x ∈ A ∪ S
    · by_cases hza : z ∈ A ∪ S
      · simp [hxa, hza, hg.1 hxa hza]
      · have hzb : z = b := by grind
        simp [hxa, ↓reduceIte, hza, ← hzb, hzb ▸ this hxa]
    · have hxb : x = b := by grind
      simp [hxa, ← hxb]
      by_cases hza : z ∈ A ∪ S
      · simp [hza, edist_comm y, edist_comm x, hxb ▸ this hza]
      · have hzb : z = b := by grind
        simp [hza, ← hzb]
  · simp_all [hg.2 ha]

/-- **Kirszbraun’s theorem**: A function `f : H₁ → H₂` that is `γ`-Lipschitz on a subset `A` admits
a `γ`-Lipschitz extension to the whole space. -/
theorem extend_univ (hfA : LipschitzOnWith γ f A) :
    ∃ g, LipschitzWith γ g ∧ EqOn f g A := by
  -- The case that `A = ∅` is trivial
  rcases eq_empty_or_nonempty A with (rfl | hA)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken (zero_le _), eqOn_empty _ _⟩
  choose a ha using hA
  let X := pi univ fun x => toWeakSpace ℝ H₂ '' (closedBall 0 (‖f a‖ + γ * ‖x - a‖))
  have hC : IsCompact X := by
    refine isCompact_univ_pi fun i => ?_
    -- Show weak compactness of closed balls.
    sorry
  let F : {I : Set H₁ | I.Finite} → Set (H₁ → WeakSpace ℝ H₂) := fun I =>
    {g | g ∈ X ∧ LipschitzOnWith γ ((toWeakSpace ℝ H₂).invFun ∘ g) I ∧ EqOn f g (A ∩ I)}
  have : (⋂ I, F I).Nonempty := by
    have : ⋂ I, F I ⊆ X := iInter_subset_of_subset ⟨{a}, by simp⟩ (by grind)
    refine (inter_eq_self_of_subset_right this) ▸ hC.inter_iInter_nonempty F (fun I => ?_) ?_
    · -- Show that each `F I` is closed.
      sorry
    · intro J
      rcases Finset.eq_empty_or_nonempty J with (rfl | hJ)
      · simp only [coe_setOf, Finset.notMem_empty, iInter_of_empty, iInter_univ, inter_univ]
        -- Show that `X` is nonempty
        sorry
      · choose j hj using hJ
        have : (X ∩ ⋂ i ∈ J, F i) = ⋂ i ∈ J, F i :=
          inter_eq_self_of_subset_right (iInter_subset_of_subset j (by simp_all; grind))
        refine this.symm ▸ ?_
        -- Show the finite intersection property.
        sorry
  choose g hg using this
  refine ⟨g, fun x y => ?_, fun x hx => ?_⟩
  · exact (mem_iInter.1 hg ⟨{a, x, y}, by simp⟩).2.1 (by simp) (by simp)
  · exact (mem_iInter.1 hg ⟨{a, x}, by simp⟩).2.2 ⟨hx, by simp⟩

end LipschitzOnWith
