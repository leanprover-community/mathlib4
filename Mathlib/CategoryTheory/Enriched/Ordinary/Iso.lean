/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
import Mathlib.CategoryTheory.Enriched.Iso

/-!
# Isomorphisms in enriched ordinary categories

We provide the infrastructure to convert between isos in a category `C` enriched over a monoidal
category `V` and `V`-enriched isos in `C`.
-/

universe v' v u u'

namespace CategoryTheory

open MonoidalCategory

section

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]

/-- Obtain an `V`-enriched isomorphism from an isomorphism in a `V`-enriched ordinary category. -/
@[simps]
def EnrichedIso.ofIso {X Y : C} (I : X ≅ Y) : X ≅[V] Y where
  hom := eHomEquiv V I.hom
  inv := eHomEquiv V I.inv
  hom_inv := by simp [← eHomEquiv_comp]
  inv_hom := by simp [← eHomEquiv_comp]

@[simp]
lemma EnrichedIso.ofIso_refl {X : C} : EnrichedIso.ofIso V (.refl X) = .refl X := by
  ext <;> simp [← eHomEquiv_id]

@[simp]
lemma EnrichedIso.ofIso_symm {X Y : C} (I : X ≅ Y) :
    (EnrichedIso.ofIso V I).symm = .ofIso _ I.symm := by
  ext <;> simp

@[simp]
lemma EnrichedIso.ofIso_trans {X Y Z : C} (I : X ≅ Y) (J : Y ≅ Z) :
    (EnrichedIso.ofIso V I).trans (.ofIso V J) = .ofIso _ (I.trans J) := by
  ext <;> simp [← eHomEquiv_comp]

/-- Obtain an iso in a `V`-enriched ordinary category from a `V`-enriched isomorphism. -/
@[simps]
def EnrichedIso.iso {X Y : C} (I : X ≅[V] Y) : X ≅ Y where
  hom := (eHomEquiv V).symm I.hom
  inv := (eHomEquiv V).symm I.inv
  hom_inv_id := by rw [← eHomEquiv_symm_comp V I.hom I.inv, I.hom_inv, eHomEquiv_symm_id]
  inv_hom_id := by rw [← eHomEquiv_symm_comp V I.inv I.hom, I.inv_hom, eHomEquiv_symm_id]

/-- The type of `V`-enriched isomorphisms is equivalent to the type of isomorphisms in a
`V`-enriched ordinary category. -/
@[simps]
def EnrichedIso.equivIso (X Y : C) : (X ≅[V] Y) ≃ (X ≅ Y) where
  toFun := iso V
  invFun := ofIso V
  left_inv I := by ext <;> simp
  right_inv I := by ext; simp

@[simp]
lemma EnrichedIso.iso_refl {X : C} : EnrichedIso.iso V (.refl X) = .refl X := by
  ext; simp

@[simp]
lemma EnrichedIso.iso_symm {X Y : C} (I : X ≅[V] Y) :
    EnrichedIso.iso V I.symm = (EnrichedIso.iso V I).symm := by
  ext; simp

@[simp]
lemma EnrichedIso.iso_trans {X Y Z : C} (I : X ≅[V] Y) (J : Y ≅[V] Z) :
    EnrichedIso.iso V (I.trans J) = (EnrichedIso.iso V I).trans (EnrichedIso.iso V J) := by
  ext; simp [eHomEquiv_symm_comp]

end

/-- The type equivalence between isos in `ForgetEnrichment V C` and `V`-enriched isos in `C`. -/
def ForgetEnrichment.enrichedIsoEquivIso {V : Type u'} [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [EnrichedCategory V C] (X Y : ForgetEnrichment V C) :
    ((ForgetEnrichment.to V X) ≅[V] (ForgetEnrichment.to V Y)) ≃ (X ≅ Y) :=
  EnrichedIso.equivIso V X Y

end CategoryTheory
