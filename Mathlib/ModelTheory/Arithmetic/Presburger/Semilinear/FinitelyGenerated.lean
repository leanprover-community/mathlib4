/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Nat
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Semilinear sets in finitely generated commutative monoids

This file proves that the semilinear sets in finitely generated commutative cancellative monoids
are closed under intersection and complement. These are generalizations of the same results in
`ℕ ^ k` to, for example, `ℤ ^ k`.

Note: these results can be further generalized to non-cancellative monoids; see
[eilenberg1969](eilenberg1969).

## Main Results

- `Set.Semilinear.inter`, `Set.Semilinear.compl`: semilinear sets in a finitely generated
  commutative cancellative monoid are closed under intersection and complement.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v w

namespace Set

variable {α : Type u} [AddCommMonoid α] {β : Type v} [AddCommMonoid β] {ι : Type w}

open Pointwise Submodule

theorem Linear.exists_image_eq {s : Set β} {f : α →ₗ[ℕ] β} (hs : s.Linear)
    (hf : Function.Surjective f) : ∃ s', s'.Linear ∧ s = f '' s' := by
  classical
  rcases hs with ⟨a, t, rfl⟩
  rcases hf.hasRightInverse with ⟨g, hg⟩
  refine ⟨_, ⟨g a, t.image g, rfl⟩, ?_⟩
  rw [image_vadd_distrib, hg a, ← map_coe, map_span, ← Finset.coe_image, Finset.image_image,
    hg.comp_eq_id, Finset.image_id]

theorem Semilinear.exists_image_eq {s : Set β} {f : α →ₗ[ℕ] β} (hs : s.Semilinear)
    (hf : Function.Surjective f) : ∃ s', s'.Semilinear ∧ s = f '' s' := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  choose! g hg using fun t ht => (hS t ht).exists_image_eq hf
  refine ⟨⋃₀ S.image g, sUnion_finset fun s hs => ?_, ?_⟩
  · simp only [Finset.mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    exact (hg t ht).1.semilinear
  · simp_rw [image_sUnion, Finset.coe_image, sUnion_eq_biUnion, biUnion_image, Finset.mem_coe]
    conv => enter [2, 1, t, 1, ht]; rw [← (hg t ht).2]

variable [IsCancelAdd α]

theorem Semilinear.preimage_nat' [Fintype ι] {s : Set α} {f : (ι → ℕ) →ₗ[ℕ] α} (hs : s.Semilinear)
    (hf : Function.Surjective f) : (f ⁻¹' s).Semilinear := by
  rcases hs.exists_image_eq hf with ⟨s₁, hs₁, rfl⟩
  apply proj'
  rw [setOf_and]
  apply inter_nat
  · exact hs₁.preimage_nat (LinearMap.funLeft ℕ ℕ Sum.inr)
  · simp_rw [eq_comm]
    refine (Linear.of_subtractive_addSubmonoid_nat {
        carrier := setOf _
        add_mem' h₁ h₂ := ?_
        zero_mem' := ?_
      } fun _ h₁ _ h₂ => ?_).semilinear
    · simp only [mem_setOf] at *
      simp [Pi.add_comp, h₁, h₂]
    · simp
    · simp only [AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, mem_setOf_eq] at *
      simpa [Pi.add_comp, h₁] using h₂

variable [Module.Finite ℕ α] {s s₁ s₂ : Set α}

/-- Semilinear sets in a finitely generated commutative cancellative monoid are closed under
  intersection. -/
theorem Semilinear.inter (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) : (s₁ ∩ s₂).Semilinear := by
  rcases Module.Finite.exists_fin' ℕ α with ⟨n, f, hf⟩
  rw [← image_preimage_eq (s₁ ∩ s₂) hf, preimage_inter]
  apply image
  apply inter_nat <;> apply preimage_nat' <;> assumption

/-- Semilinear sets in a finitely generated commutative cancellative monoid are closed under
  complement. -/
theorem Semilinear.compl (hs : s.Semilinear) : sᶜ.Semilinear := by
  rcases Module.Finite.exists_fin' ℕ α with ⟨n, f, hf⟩
  rw [← image_preimage_eq sᶜ hf, preimage_compl]
  apply image
  apply compl_nat
  apply preimage_nat' <;> assumption

example [Fintype ι] {s : Set (ι → ℕ)} (hs : s.Semilinear) : sᶜ.Semilinear := hs.compl
example [Fintype ι] {s : Set (ι → ℤ)} (hs : s.Semilinear) : sᶜ.Semilinear := hs.compl

end Set
