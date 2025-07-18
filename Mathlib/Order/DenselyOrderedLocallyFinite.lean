/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Finset.Defs

/-!
# Linear locally finite orders are densely ordered iff they are trivial

## Main results
* `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`:
  A linear locally finite order is densely ordered if and only if it is a subsingleton.

-/

variable {X : Type*} [LinearOrder X] [LocallyFiniteOrder X]

lemma LocallyFiniteOrder.denselyOrdered_iff_subsingleton :
    DenselyOrdered X ↔ Subsingleton X := by
  refine ⟨fun H ↦ ?_, fun h ↦ h.instDenselyOrdered⟩
  constructor
  intro a b
  wlog hab : a < b generalizing a b
  · push_neg at hab
    refine hab.eq_or_lt.elim (fun h ↦ h.symm) fun hab' ↦ ?_
    exact (this _ _ hab').symm
  choose f hf hf' using H.dense a
  let g : {x // a < x} → {x // a < x} := fun x ↦ ⟨f x x.prop, hf _ _⟩
  have hg x : (g x : X) < x := hf' _ _
  have hga k : a < g^[k + 1] ⟨b, hab⟩ := by
    rw [Function.iterate_succ', Function.comp_apply]
    exact hf _ _
  have hgb k : g^[k + 1] ⟨b, hab⟩ < b := by
    induction k
    · simpa using hg _
    · rw [Function.iterate_succ', Function.comp_apply]
      exact (hg _).trans ‹_›
  have hg' k : (g^[k + 1] ⟨b, hab⟩ : X) ∈ finsetIoo a b := by
    simp only [finset_mem_Ioo a b, hga, hgb, and_self]
  have hgm : StrictAnti (fun k ↦ g^[k + 1] ⟨b, hab⟩) := by
    intro k l hkl
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hkl
    clear hkl
    simp only [Function.iterate_succ', Function.comp_apply]
    refine (hg _).trans_le ?_
    induction n with
    | zero => simp
    | succ n IH =>
      rw [← add_assoc, Function.iterate_succ', Function.comp_apply]
      exact (hg _).le.trans IH
  have hr : (Finset.range ((finsetIoo a b).card + 1)).map
      ⟨_, (Subtype.val_injective.comp hgm.injective).comp Nat.succ_injective⟩ ⊆ finsetIoo a b := by
    intro x
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Function.comp_apply,
      forall_exists_index, and_imp]
    rintro _ _ rfl
    exact hg' _
  simpa using Finset.card_le_card hr

lemma denselyOrdered_set_iff_subsingleton {s : Set X} :
    DenselyOrdered s ↔ s.Subsingleton := by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]

lemma denselyOrdered_withBot_set_iff_subsingleton {s : Set (WithBot X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  refine ⟨fun H ↦ ?_, fun h ↦ h.denselyOrdered⟩
  by_cases hs : DenselyOrdered (WithBot.some ⁻¹' s)
  · contrapose! hs
    rw [denselyOrdered_set_iff_subsingleton, Set.not_subsingleton_iff]
    rw [Set.not_subsingleton_iff, ← Set.nontrivial_coe_sort] at hs
    obtain ⟨x, y, hxy⟩ := hs
    wlog H : x < y generalizing x y
    · exact this y x hxy.symm (lt_of_le_of_ne (not_lt.mp H) hxy.symm)
    obtain ⟨z, hz, hz'⟩ := exists_between H
    have hz0 : (⊥ : WithBot X) < z := by simp [(Subtype.coe_lt_coe.mpr hz).trans_le']
    refine ⟨WithBot.unbot z hz0.ne', by simp, WithBot.unbot y (hz0.trans hz').ne', by simp, ?_⟩
    rw [ne_eq, ← WithBot.coe_eq_coe]
    simpa [Subtype.ext_iff] using hz'.ne
  · contrapose! hs
    constructor
    simp only [Subtype.exists, Set.mem_preimage, Subtype.forall, Subtype.mk_lt_mk, exists_and_right,
      exists_prop]
    intro x hx y hy hxy
    have : (⟨_, hx⟩ : s) < ⟨_, hy⟩ := by simp [hxy]
    obtain ⟨z, hz, hz'⟩ := exists_between this
    simp only [← Subtype.coe_lt_coe] at hz hz'
    refine ⟨WithBot.unbot z (hz.trans_le' (by simp)).ne', ⟨?_, ?_⟩, ?_⟩
    · simp
    · rw [← WithBot.coe_lt_coe]
      simp [hz.trans_le]
    · rw [← WithBot.coe_lt_coe]
      simp [hz'.trans_le']

lemma denselyOrdered_withTop_set_iff_subsingleton {s : Set (WithTop X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  have he : StrictAnti (WithTop.toDual.image s) :=
    WithTop.toDual.image_strictAnti _ (fun ⦃a b⦄ a ↦ a)
  rw [denselyOrdered_iff_of_strictAnti _ he, denselyOrdered_withBot_set_iff_subsingleton,
    WithTop.toDual.injective.subsingleton_image_iff]
