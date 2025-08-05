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

variable {α : Type u} [AddCommMonoid α] {β : Type v} [AddCommMonoid β] {ι : Type w}
  {s s₁ s₂ : Set α}

open Pointwise Submodule

theorem Linear.exists_submodule_fg (hs : s.Linear) :
    ∃ (M : Submodule ℕ α) (s' : Set M), M.FG ∧ s'.Linear ∧ s = M.subtype '' s' := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  refine ⟨_, _, ⟨insert a t, rfl⟩,
    ⟨⟨a, mem_span_of_mem (Finset.mem_insert_self a t)⟩,
      t.attach.image fun ⟨b, hb⟩ => ⟨b, mem_span_of_mem (Finset.mem_insert_of_mem hb)⟩, rfl⟩, ?_⟩
  rw [image_vadd_distrib, subtype_apply, ← map_coe, ← span_image]
  congr!
  ext b
  simp only [Finset.mem_coe, subtype_apply, Finset.coe_image, Finset.coe_attach, image_univ,
    mem_image, mem_range, Subtype.exists, Subtype.mk.injEq, exists_prop, exists_eq_right,
    exists_eq_right_right]
  rw [iff_and_self]
  exact fun hb => mem_span_of_mem (Finset.mem_insert_of_mem hb)

theorem Semilinear.exists_submodule_fg (hs : s.Semilinear) :
    ∃ (M : Submodule ℕ α) (s' : Set M), M.FG ∧ s'.Semilinear ∧ s = Subtype.val '' s' := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  choose! M S' hM hS' hM' using fun t ht => (hS t ht).exists_submodule_fg
  refine ⟨S.sup M, ⋃ (t : S), Submodule.inclusion (Finset.le_sup t.2) '' S' t.1,
    fg_finset_sup _ _ hM, iUnion fun t => (hS' t.1 t.2).semilinear.image _, ?_⟩
  simp_rw [sUnion_eq_iUnion, image_iUnion, image_image, Submodule.coe_inclusion,
    ← coe_subtype, ← fun t : S => hM' t.1 t.2]
  rfl

theorem Semilinear.exists_submodule_fg₂ (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) :
    ∃ (M : Submodule ℕ α) (s₁' s₂' : Set M), M.FG ∧ s₁'.Semilinear ∧ s₁ = Subtype.val '' s₁'
      ∧ s₂'.Semilinear ∧ s₂ = Subtype.val '' s₂' := by
  rcases hs₁.exists_submodule_fg with ⟨M₁, s₁', hM₁, hs₁', rfl⟩
  rcases hs₂.exists_submodule_fg with ⟨M₂, s₂', hM₂, hs₂', rfl⟩
  refine ⟨M₁ ⊔ M₂, (Submodule.inclusion le_sup_left) '' s₁',
    (Submodule.inclusion le_sup_right) '' s₂', hM₁.sup hM₂, hs₁'.image _, ?_, hs₂'.image _, ?_⟩
    <;> simp_rw [image_image, Submodule.coe_inclusion]

theorem Linear.exists_image_eq_of_surjective {s : Set β} {f : α →ₗ[ℕ] β} (hs : s.Linear)
    (hf : Function.Surjective f) : ∃ s', s'.Linear ∧ s = f '' s' := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  rcases hf.hasRightInverse with ⟨g, hg⟩
  refine ⟨_, ⟨g a, t.image g, rfl⟩, ?_⟩
  rw [image_vadd_distrib, hg a, ← map_coe, map_span, ← Finset.coe_image, Finset.image_image,
    hg.comp_eq_id, Finset.image_id]

theorem Semilinear.exists_image_eq_of_surjective {s : Set β} {f : α →ₗ[ℕ] β} (hs : s.Semilinear)
    (hf : Function.Surjective f) : ∃ s', s'.Semilinear ∧ s = f '' s' := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  choose! g hg using fun t ht => (hS t ht).exists_image_eq_of_surjective hf
  refine ⟨⋃₀ S.image g, sUnion fun s hs => ?_, ?_⟩
  · simp only [Finset.mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (hg t ht).1.semilinear
  · simp_rw [image_sUnion, Finset.coe_image, sUnion_eq_biUnion, biUnion_image, Finset.mem_coe]
    conv => enter [2, 1, t, 1, ht]; rw [← (hg t ht).2]

variable [IsCancelAdd α]

theorem Semilinear.preimage_nat_of_surjective [Fintype ι] {f : (ι → ℕ) →ₗ[ℕ] α} (hs : s.Semilinear)
    (hf : Function.Surjective f) : (f ⁻¹' s).Semilinear := by
  rcases hs.exists_image_eq_of_surjective hf with ⟨s₁, hs₁, rfl⟩
  apply proj'
  rw [setOf_and]
  apply inter_nat
  · exact hs₁.preimage_nat (LinearMap.funLeft ℕ ℕ Sum.inr)
  · refine (Linear.of_subtractive_addSubmonoid_nat {
        carrier := setOf _
        add_mem' h₁ h₂ := ?_
        zero_mem' := ?_
      } fun _ h₁ _ h₂ => ?_).semilinear <;> simp_all [Pi.add_comp]

/-- Semilinear sets in a commutative cancellative monoid are closed under intersection. -/
theorem Semilinear.inter (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ ∩ s₂).Semilinear := by
  rcases hs₁.exists_submodule_fg₂ hs₂ with ⟨M, s₁', s₂', hM, hs₁', rfl, hs₂', rfl⟩
  rw [← image_inter Subtype.val_injective]
  refine image ?_ M.subtype
  rw [← Module.Finite.iff_fg] at hM
  rcases hM.exists_fin' with ⟨n, f, hf⟩
  rw [← image_preimage_eq (s₁' ∩ s₂') hf, preimage_inter]
  apply image
  apply inter_nat <;> apply preimage_nat_of_surjective <;> assumption

/-- Semilinear sets in a commutative cancellative monoid are closed under set difference. -/
theorem Semilinear.diff (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ \ s₂).Semilinear := by
  rcases hs₁.exists_submodule_fg₂ hs₂ with ⟨M, s₁', s₂', hM, hs₁', rfl, hs₂', rfl⟩
  rw [← image_diff Subtype.val_injective]
  refine image ?_ M.subtype
  rw [← Module.Finite.iff_fg] at hM
  rcases hM.exists_fin' with ⟨n, f, hf⟩
  rw [← image_preimage_eq (s₁' \ s₂') hf, preimage_diff]
  apply image
  apply diff_nat <;> apply preimage_nat_of_surjective <;> assumption

/-- Semilinear sets in a finitely generated commutative cancellative monoid are closed under
  complement. -/
theorem Semilinear.compl [Module.Finite ℕ α] (hs : s.Semilinear) : sᶜ.Semilinear := by
  rw [compl_eq_univ_diff]
  exact univ.diff hs

example [Fintype ι] {s : Set (ι → ℤ)} (hs : s.Semilinear) : sᶜ.Semilinear := hs.compl

end Set
