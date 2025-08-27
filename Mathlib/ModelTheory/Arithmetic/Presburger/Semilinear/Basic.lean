/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Nat
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Semilinear sets are closed under intersection and set difference

This file proves that the semilinear sets in any commutative cancellative monoids are closed under
intersection and set difference. They are also closed under complement if the monoid is finitely
generated. These are generalizations of the same results in `ℕ ^ k` to, for example, `ℤ ^ k`.

Note: these results can be further generalized to non-cancellative monoids; see
[eilenberg1969](eilenberg1969).

## Main Results

- `Set.Semilinear.inter`, `Set.Semilinear.diff`, `Set.Semilinear.compl`: semilinear sets in a
  commutative cancellative monoid are closed under intersection and set difference
  (unconditionally), and closed under complement when the monoid is finitely generated.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v w

namespace Set

variable {α : Type u} [AddCommMonoid α] {β : Type v} [AddCommMonoid β] {s s₁ s₂ : Set α}

open Pointwise AddSubmonoid

theorem Linear.exists_addSubmonoid_fg (hs : s.Linear) :
    ∃ (P : AddSubmonoid α) (s' : Set P), P.FG ∧ s'.Linear ∧ s = Subtype.val '' s' := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  refine ⟨_, _, ⟨insert a t, rfl⟩,
    ⟨⟨a, mem_closure_of_mem (Finset.mem_insert_self a t)⟩,
      t.attach.image fun ⟨b, hb⟩ => ⟨b, mem_closure_of_mem (Finset.mem_insert_of_mem hb)⟩, rfl⟩, ?_⟩
  rw [← coe_subtype, image_vadd_distrib, subtype_apply, ← coe_map, AddMonoidHom.map_mclosure]
  congr!
  ext b
  simp only [Finset.mem_coe, subtype_apply, Finset.coe_image, Finset.coe_attach, image_univ,
    mem_image, mem_range, Subtype.exists, Subtype.mk.injEq, exists_prop, exists_eq_right,
    exists_eq_right_right]
  rw [iff_and_self]
  exact fun hb => mem_closure_of_mem (Finset.mem_insert_of_mem hb)

theorem Semilinear.exists_addSubmonoid_fg (hs : s.Semilinear) :
    ∃ (P : AddSubmonoid α) (s' : Set P), P.FG ∧ s'.Semilinear ∧ s = Subtype.val '' s' := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  choose! P S' hP hS' hP' using fun t ht => (hS t ht).exists_addSubmonoid_fg
  refine ⟨S.sup P, ⋃ (t : S), AddSubmonoid.inclusion (Finset.le_sup t.2) '' S' t.1,
    FG.finset_sup _ _ hP, iUnion fun t => (hS' t.1 t.2).semilinear.image _, ?_⟩
  simp_rw [sUnion_eq_iUnion, image_iUnion, image_image, AddSubmonoid.coe_inclusion,
    ← fun t : S => hP' t.1 t.2]
  rfl

theorem Semilinear.exists_addSubmonoid_fg₂ (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) :
    ∃ (P : AddSubmonoid α) (s₁' s₂' : Set P), P.FG ∧ s₁'.Semilinear ∧ s₁ = Subtype.val '' s₁'
      ∧ s₂'.Semilinear ∧ s₂ = Subtype.val '' s₂' := by
  rcases hs₁.exists_addSubmonoid_fg with ⟨P₁, s₁', hP₁, hs₁', rfl⟩
  rcases hs₂.exists_addSubmonoid_fg with ⟨P₂, s₂', hP₂, hs₂', rfl⟩
  refine ⟨P₁ ⊔ P₂, (AddSubmonoid.inclusion le_sup_left) '' s₁',
    (AddSubmonoid.inclusion le_sup_right) '' s₂', hP₁.sup hP₂, hs₁'.image _, ?_, hs₂'.image _, ?_⟩
    <;> simp_rw [image_image, AddSubmonoid.coe_inclusion]

variable {F : Type*} [FunLike F α β] [AddMonoidHomClass F α β]

theorem Semilinear.preimage [AddMonoid.FG α] [IsCancelAdd β] {s : Set β} (hs : s.Semilinear)
    (f : F) : (f ⁻¹' s).Semilinear := by
  rcases fg_iff_exists_fin_addMonoidHom.1 (AddMonoid.FG.fg_top (M := α)) with ⟨n, g, hg⟩
  rw [AddMonoidHom.mrange_eq_top] at hg
  rw [← image_preimage_eq (f ⁻¹' s) hg]
  apply image
  rw [← preimage_comp, ← AddMonoidHom.coe_coe, ← AddMonoidHom.coe_comp]
  exact hs.preimage_nat _

variable [IsCancelAdd α]

/-- Semilinear sets in a commutative cancellative monoid are closed under intersection. -/
theorem Semilinear.inter (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ ∩ s₂).Semilinear := by
  rcases hs₁.exists_addSubmonoid_fg₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_inter Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' ∩ s₂') hf, preimage_inter]
  apply image
  apply inter_nat <;> apply preimage_nat <;> assumption

/-- Semilinear sets in a commutative cancellative monoid are closed under set difference. -/
theorem Semilinear.diff (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ \ s₂).Semilinear := by
  rcases hs₁.exists_addSubmonoid_fg₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_diff Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' \ s₂') hf, preimage_diff]
  apply image
  apply diff_nat <;> apply preimage_nat <;> assumption

/-- Semilinear sets in a finitely generated commutative cancellative monoid are closed under
complement. -/
theorem Semilinear.compl [AddMonoid.FG α] (hs : s.Semilinear) : sᶜ.Semilinear := by
  rw [compl_eq_univ_diff]
  exact univ.diff hs

example {ι : Type*} [Finite ι] {s : Set (ι → ℤ)} (hs : s.Semilinear) : sᶜ.Semilinear := hs.compl

end Set
