/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Nat
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Semilinear sets are closed under intersection and set difference

This file proves that the semilinear sets in a cancellative monoid are closed under intersection and
set difference. They are also closed under complement if the monoid is finitely generated. These are
generalizations of the same results in `ℕ ^ k` to, for example, `ℤ ^ k`.

Note: these results can be further generalized to non-cancellative monoids; see
[eilenberg1969](eilenberg1969).

## Main Results

- `IsSemilinearSet.inter`, `IsSemilinearSet.diff`: semilinear sets (in a cancellative monoid) are
  closed under intersection and set difference.
- `IsSemilinearSet.compl`: semilinear sets in a finitely generated cancellative monoid are closed
  under complement.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

variable {M N ι : Type*} [AddCommMonoid M] [AddCommMonoid N] {s s₁ s₂ : Set M}

open Set Pointwise AddSubmonoid

theorem IsLinearSet.exists_fg_eq_subtypeVal (hs : IsLinearSet s) :
    ∃ (P : AddSubmonoid M) (s' : Set P), P.FG ∧ IsLinearSet s' ∧ s = Subtype.val '' s' := by
  rcases hs with ⟨a, t, ht, rfl⟩
  refine ⟨_, _, (fg_iff _).2 ⟨insert a t, rfl, ht.insert a⟩,
    ⟨⟨_, mem_closure_of_mem (mem_insert a t)⟩, _, ht.preimage Subtype.val_injective.injOn, rfl⟩, ?_⟩
  rw [← coe_subtype, image_vadd_distrib, subtype_apply, ← coe_map, AddMonoidHom.map_mclosure]
  congr
  ext x
  simpa using mem_closure_of_mem ∘ mem_insert_of_mem a

theorem IsSemilinearSet.exists_fg_eq_subtypeVal (hs : IsSemilinearSet s) :
    ∃ (P : AddSubmonoid M) (s' : Set P), P.FG ∧ IsSemilinearSet s' ∧ s = Subtype.val '' s' := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  choose! P t hP ht ht' using fun s hs => (hS' s hs).exists_fg_eq_subtypeVal
  haveI : Finite S := hS
  refine ⟨⨆ s : S, P s, ⋃ (s : S), AddSubmonoid.inclusion (le_iSup _ s) '' t s.1,
    .iSup _ fun s => hP s s.2, .iUnion fun s => .image (ht s s.2).isSemilinearSet _, ?_⟩
  simp_rw [sUnion_eq_iUnion, image_iUnion, image_image, AddSubmonoid.coe_inclusion,
    fun s : S => ht' s s.2]

theorem IsSemilinearSet.exists_fg_eq_subtypeVal₂ (hs₁ : IsSemilinearSet s₁)
    (hs₂ : IsSemilinearSet s₂) :
    ∃ (P : AddSubmonoid M) (s₁' s₂' : Set P), P.FG ∧ IsSemilinearSet s₁' ∧ s₁ = Subtype.val '' s₁'
      ∧ IsSemilinearSet s₂' ∧ s₂ = Subtype.val '' s₂' := by
  rcases hs₁.exists_fg_eq_subtypeVal with ⟨P₁, s₁', hP₁, hs₁', rfl⟩
  rcases hs₂.exists_fg_eq_subtypeVal with ⟨P₂, s₂', hP₂, hs₂', rfl⟩
  refine ⟨P₁ ⊔ P₂, (AddSubmonoid.inclusion le_sup_left) '' s₁',
    (AddSubmonoid.inclusion le_sup_right) '' s₂', hP₁.sup hP₂, hs₁'.image _, ?_, hs₂'.image _, ?_⟩
    <;> simp_rw [image_image, AddSubmonoid.coe_inclusion]

theorem IsSemilinearSet.preimage [AddMonoid.FG M] [IsCancelAdd N] {F : Type*} [FunLike F M N]
    [AddMonoidHomClass F M N] {s : Set N} (hs : IsSemilinearSet s) (f : F) :
    IsSemilinearSet (f ⁻¹' s) := by
  rcases fg_iff_exists_fin_addMonoidHom.1 (AddMonoid.FG.fg_top (M := M)) with ⟨n, g, hg⟩
  rw [AddMonoidHom.mrange_eq_top] at hg
  rw [← image_preimage_eq (f ⁻¹' s) hg]
  apply image
  rw [← preimage_comp, ← AddMonoidHom.coe_coe, ← AddMonoidHom.coe_comp]
  exact Nat.isSemilinearSet_preimage hs _

variable [IsCancelAdd M]

/-- Semilinear sets are closed under intersection. -/
theorem IsSemilinearSet.inter (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∩ s₂) := by
  rcases hs₁.exists_fg_eq_subtypeVal₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_inter Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' ∩ s₂') hf, preimage_inter]
  apply image
  apply Nat.isSemilinearSet_inter <;> apply Nat.isSemilinearSet_preimage <;> assumption

/-- Semilinear sets are closed under set difference. -/
theorem IsSemilinearSet.diff (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ \ s₂) := by
  rcases hs₁.exists_fg_eq_subtypeVal₂ hs₂ with ⟨P, s₁', s₂', hP, hs₁', rfl, hs₂', rfl⟩
  rw [← image_diff Subtype.val_injective]
  apply image (f := P.subtype)
  rw [← AddMonoid.fg_iff_addSubmonoid_fg, AddMonoid.fg_def, fg_iff_exists_fin_addMonoidHom] at hP
  rcases hP with ⟨n, f, hf⟩
  rw [AddMonoidHom.mrange_eq_top] at hf
  rw [← image_preimage_eq (s₁' \ s₂') hf, preimage_diff]
  apply image
  apply Nat.isSemilinearSet_diff <;> apply Nat.isSemilinearSet_preimage <;> assumption

variable [AddMonoid.FG M]

theorem IsSemilinearSet.sInter {S : Set (Set M)} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsSemilinearSet s) : IsSemilinearSet (⋂₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using hS'.1.inter (ih hS'.2)

theorem IsSemilinearSet.iInter [Finite ι] {s : ι → Set M} (hs : ∀ i, IsSemilinearSet (s i)) :
    IsSemilinearSet (⋂ i, s i) := by
  rw [← sInter_range]
  apply sInter (finite_range s)
  simpa

theorem IsSemilinearSet.biInter {s : Set ι} {t : ι → Set M} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) := by
  rw [← sInter_image]
  apply sInter (hs.image t)
  simpa

theorem IsSemilinearSet.biInter_finset {s : Finset ι} {t : ι → Set M}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) :=
  biInter s.finite_toSet ht

/-- Semilinear sets in a finitely generated monoid are closed under complement. -/
theorem IsSemilinearSet.compl (hs : IsSemilinearSet s) : IsSemilinearSet sᶜ := by
  rw [compl_eq_univ_diff]
  exact diff .univ hs

example {ι : Type*} [Finite ι] {s : Set (ι → ℤ)} (hs : IsSemilinearSet s) : IsSemilinearSet sᶜ :=
  hs.compl
