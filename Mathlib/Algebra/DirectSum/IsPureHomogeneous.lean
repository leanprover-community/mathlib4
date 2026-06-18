/-
Copyright (c) 2026 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Purely homogeneous relations

* `DirectSum.Rel.IsPureHomogeneous`: a relation `r` is `PureHomogeneous` iff `r a b` implies that
  `a` and `b` are homogeneous of the same degree.

-/

@[expose] public section

open DirectSum

variable {ι M σ : Type*} {r : M → M → Prop}
    (ℳ : ι → σ) [SetLike σ M]

/-- A relation `r` is `PureHomogeneous` with respect to a family `ℳ : ι → σ` (where `SetLike σ M`)
iff `r a b` implies that `a` and `b` are homogeneous of the same degree. -/
def Rel.IsPureHomogeneous (r : M → M → Prop) : Prop :=
  ∀ {a b : M} (_ : r a b), ∃ i, a ∈ ℳ i ∧ b ∈ ℳ i

theorem Rel.isPureHomogeneous_iff :
    Rel.IsPureHomogeneous ℳ r ↔ ∀ {a b : M} (_ : r a b), ∃ i, a ∈ ℳ i ∧ b ∈ ℳ i := Iff.rfl

variable [DecidableEq ι]

section AddCommMonoid

variable {ℳ} [AddCommMonoid M] [AddSubmonoidClass σ M] [DirectSum.Decomposition ℳ]

lemma Rel.IsPureHomogeneous.isHomogeneous (hr0 : r 0 0) (hr : Rel.IsPureHomogeneous ℳ r) :
    Rel.IsHomogeneous ℳ r := by
  intro a b h i
  obtain ⟨j, ha, hb⟩ := hr h
  obtain rfl | hji := eq_or_ne j i
  · simp [decompose_of_mem_same, ha, hb, h]
  · simp [decompose_of_mem_ne _ ha hji, decompose_of_mem_ne _ hb hji, hr0]

theorem Rel.IsPureHomogeneous.addConGenIsHomogeneous (hr : Rel.IsPureHomogeneous ℳ r) :
    Rel.IsHomogeneous ℳ (AddConGen.Rel r) := by
  intro a b h i
  induction h with
  | refl x => exact AddConGen.Rel.refl _
  | of a b h =>
    obtain ⟨j, ha, hb⟩ := hr h
    obtain rfl | hji := eq_or_ne j i
    · simp [decompose_of_mem_same, ha, hb, h, AddConGen.Rel.of]
    · simp [decompose_of_mem_ne _ ha hji, decompose_of_mem_ne _ hb hji, AddConGen.Rel.refl]
  | symm _ ih => exact AddConGen.Rel.symm ih
  | trans h h' ih ih' => exact AddConGen.Rel.trans ih ih'
  | add h h' ih ih' =>
    simp only [decompose_add, add_apply, AddMemClass.coe_add]
    exact AddConGen.Rel.add ih ih'

end AddCommMonoid

section Semiring

variable [AddMonoid ι] [Semiring M] [AddSubmonoidClass σ M] [GradedRing ℳ]

theorem Rel.IsPureHomogeneous.ringConGenIsHomogeneous (hr : Rel.IsPureHomogeneous ℳ r) :
    Rel.IsHomogeneous ℳ (RingConGen.Rel r) := by
  intro a b h i
  induction h generalizing i with
  | refl x => exact RingConGen.Rel.refl _
  | of a b h =>
    obtain ⟨j, ha, hb⟩ := hr h
    obtain rfl | hji := eq_or_ne j i
    · simp [decompose_of_mem_same, ha, hb, h, RingConGen.Rel.of]
    · simp [decompose_of_mem_ne _ ha hji, decompose_of_mem_ne _ hb hji, RingConGen.Rel.refl]
  | symm _ ih => exact RingConGen.Rel.symm (ih i)
  | trans h h' ih ih' => exact RingConGen.Rel.trans (ih i) (ih' i)
  | add h h' ih ih' => simp [RingConGen.Rel.add (ih i) (ih' i)]
  | @mul w x y z h h' ih ih' =>
    classical
    simp only [decompose_mul, DirectSum.coe_mul_apply]
    rw [Finset.sum_subset Finset.subset_union_right]
    · nth_rewrite 2 [Finset.sum_subset Finset.subset_union_left]
      · apply RingConGen.Rel.sum
        intro u _
        exact RingConGen.Rel.mul (ih u.1) (ih' u.2)
      · intro u hu hu'
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          DFinsupp.mem_support_toFun, ne_eq, not_and, and_imp] at hu hu'
        rcases hu with (⟨⟨hux, huz⟩, hui⟩ | ⟨⟨huw, huy⟩, hui⟩)
        · exact (hu' hux huz hui).elim
        · simp only [hui, not_true_eq_false, imp_false, Decidable.not_not] at hu'
          by_cases h : decompose ℳ x u.1 = 0
          · simp [h]
          · simp [hu' h]
    · intro u hu hu'
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product,
        DFinsupp.mem_support_toFun, ne_eq, not_and, and_imp] at hu hu'
      rcases hu with (⟨⟨hux, huz⟩, hui⟩ | ⟨⟨huw, huy⟩, hui⟩)
      · simp only [hui, not_true_eq_false, imp_false, Decidable.not_not] at hu'
        by_cases h : decompose ℳ w u.1 = 0
        · simp [h]
        · simp [hu' h]
      · exact (hu' huw huy hui).elim

end Semiring

end
