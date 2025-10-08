/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao
-/

import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure

/-!

# Main definitions and results

In a field extension `K/k`

* `FiniteGaloisIntermediateField` : The type of intermediate fields of `K/k`
  that are finite and Galois over `k`

* `adjoin` : The finite Galois intermediate field obtained from the normal closure of adjoining a
  finite `s : Set K` to `k`.

# TODO

* `FiniteGaloisIntermediateField` should be a `ConditionallyCompleteLattice` but isn't proved yet.

-/

open IntermediateField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- The type of intermediate fields of `K/k` that are finite and Galois over `k` -/
structure FiniteGaloisIntermediateField extends IntermediateField k K where
  [finiteDimensional : FiniteDimensional k toIntermediateField]
  [isGalois : IsGalois k toIntermediateField]

namespace FiniteGaloisIntermediateField

instance : Coe (FiniteGaloisIntermediateField k K) (IntermediateField k K) where
  coe := toIntermediateField

instance : CoeSort (FiniteGaloisIntermediateField k K) (Type _) where
  coe L := L.toIntermediateField

instance (L : FiniteGaloisIntermediateField k K) : FiniteDimensional k L :=
  L.finiteDimensional

instance (L : FiniteGaloisIntermediateField k K) : IsGalois k L := L.isGalois

variable {k K}

lemma val_injective : Function.Injective (toIntermediateField (k := k) (K := K)) := by
  rintro ⟨⟩ ⟨⟩ eq
  simpa only [mk.injEq] using eq

/-- Turns the collection of finite Galois IntermediateFields of `K/k` into a lattice. -/
instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊔ L₂) where

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₁] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₁) inf_le_left).toRingHom.injective

instance (L₁ L₂ : IntermediateField k K) [FiniteDimensional k L₂] :
    FiniteDimensional k ↑(L₁ ⊓ L₂) :=
  .of_injective (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).toLinearMap
    (IntermediateField.inclusion (E := L₁ ⊓ L₂) (F := L₂) inf_le_right).injective

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₁] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_left)

instance (L₁ L₂ : IntermediateField k K) [Algebra.IsSeparable k L₂] :
    Algebra.IsSeparable k ↑(L₁ ⊓ L₂) :=
  .of_algHom _ _ (IntermediateField.inclusion inf_le_right)

instance (L₁ L₂ : IntermediateField k K) [IsGalois k L₁] [IsGalois k L₂] :
    IsGalois k ↑(L₁ ⊓ L₂) where

instance : Max (FiniteGaloisIntermediateField k K) where
  max L₁ L₂ := .mk <| L₁ ⊔ L₂

instance : Min (FiniteGaloisIntermediateField k K) where
  min L₁ L₂ := .mk <| L₁ ⊓ L₂

instance : Lattice (FiniteGaloisIntermediateField k K) :=
  val_injective.lattice _ (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : OrderBot (FiniteGaloisIntermediateField k K) where
  bot := .mk ⊥
  bot_le _ := bot_le (α := IntermediateField _ _)

@[simp]
lemma le_iff (L₁ L₂ : FiniteGaloisIntermediateField k K) :
    L₁ ≤ L₂ ↔ L₁.toIntermediateField ≤ L₂.toIntermediateField :=
  Iff.rfl

variable (k) in
/-- The minimal (finite) Galois intermediate field containing a finite set `s : Set K` in a
Galois extension `K/k` defined as the the normal closure of the field obtained by adjoining
the set `s : Set K` to `k`. -/
noncomputable def adjoin [IsGalois k K] (s : Set K) [Finite s] :
    FiniteGaloisIntermediateField k K := {
  normalClosure k (IntermediateField.adjoin k (s : Set K)) K with
  finiteDimensional :=
    letI : FiniteDimensional k (IntermediateField.adjoin k (s : Set K)) :=
      IntermediateField.finiteDimensional_adjoin <| fun z _ =>
        IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic z)
    normalClosure.is_finiteDimensional k (IntermediateField.adjoin k (s : Set K)) K
  isGalois := IsGalois.normalClosure k (IntermediateField.adjoin k (s : Set K)) K }

@[simp]
lemma adjoin_val [IsGalois k K] (s : Set K) [Finite s] :
    (FiniteGaloisIntermediateField.adjoin k s) =
    normalClosure k (IntermediateField.adjoin k s) K :=
  rfl

variable (k) in
lemma subset_adjoin [IsGalois k K] (s : Set K) [Finite s] :
    s ⊆ (adjoin k s).toIntermediateField :=
  (IntermediateField.subset_adjoin k s).trans (IntermediateField.le_normalClosure _)

theorem adjoin_simple_le_iff [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} :
    adjoin k {x} ≤ L ↔ x ∈ L.toIntermediateField := by
  simp only [le_iff, adjoin_val, IntermediateField.normalClosure_le_iff_of_normal,
    IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]

@[simp]
theorem adjoin_map [IsGalois k K] (f : K →ₐ[k] K) (s : Set K) [Finite s] :
    adjoin k (f '' s) = adjoin k s := by
  apply val_injective; dsimp [adjoin_val]
  rw [← IntermediateField.adjoin_map, IntermediateField.normalClosure_map_eq]

@[simp]
theorem adjoin_simple_map_algHom [IsGalois k K] (f : K →ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} := by
  simpa only [Set.image_singleton] using adjoin_map f { x }

@[simp]
theorem adjoin_simple_map_algEquiv [IsGalois k K] (f : K ≃ₐ[k] K) (x : K) :
    adjoin k {f x} = adjoin k {x} :=
  adjoin_simple_map_algHom (f : K →ₐ[k] K) x

nonrec lemma mem_fixingSubgroup_iff (α : K ≃ₐ[k] K) (L : FiniteGaloisIntermediateField k K) :
    α ∈ L.fixingSubgroup ↔ α.restrictNormalHom L = 1 := by
  simp [IntermediateField.fixingSubgroup, mem_fixingSubgroup_iff, AlgEquiv.ext_iff, Subtype.ext_iff,
    AlgEquiv.restrictNormalHom_apply]

end FiniteGaloisIntermediateField
