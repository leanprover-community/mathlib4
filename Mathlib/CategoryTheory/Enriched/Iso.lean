/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Enriched.Basic

universe w v u₁

/-!
# Isomorphisms in ordinary categories

We define the notion of `V`-enriched isomorphisms in `V`-enriched categories and relate them
to the isomorphisms in the category `ForgetEnrichment V C`.
-/


namespace CategoryTheory

open MonoidalCategory

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

variable {C : Type u₁} [EnrichedCategory V C]

/-- Isomorphisms in a `V`-enriched category `C`consist of a morphism
`𝟙_ V ⟶ X ⟶[V] Y`, an inverse `𝟙_ V ⟶ Y ⟶[V] X`, and proofs that these compose to the identity
morphism. -/
@[ext]
structure EnrichedIso (X Y : C) where
  /-- The forward direction of an isomorphism. -/
  hom : 𝟙_ V ⟶ X ⟶[V] Y
  /-- The backward direction of an isomorphism. -/
  inv : 𝟙_ V ⟶ Y ⟶[V] X
  hom_inv : (λ_ _).inv ≫ (hom ⊗ₘ inv) ≫ eComp V X Y X = eId V X := by aesop_cat
  inv_hom : (λ_ _).inv ≫ (inv ⊗ₘ hom) ≫ eComp V Y X Y = eId V Y := by aesop_cat

@[inherit_doc EnrichedIso]
notation X " ≅[" V "] " Y:10 => EnrichedIso V X Y

namespace EnrichedIso

variable {V}

/-- The identity isomorphism in a `V`-enriched category. -/
@[refl, simps]
def refl (X : C) : X ≅[V] X where
  hom := eId V X
  inv := eId V X
  hom_inv := by simp [tensorHom_def']
  inv_hom := by simp [tensorHom_def']

/-- The inverse isomorphism of an isomorphism in a `V`-enriched category. -/
@[symm, simps]
def symm {X Y : C} (I : X ≅[V] Y) : Y ≅[V] X where
  hom := I.inv
  inv := I.hom
  hom_inv := I.inv_hom
  inv_hom := I.hom_inv

open EnrichedCategory

lemma trans_hom_inv {X Y Z : C} (I : X ≅[V] Y) (J : Y ≅[V] Z) :
    (λ_ (𝟙_ V)).inv ≫ ((λ_ (𝟙_ V)).inv ≫ (I.hom ⊗ₘ J.hom) ≫ eComp V X Y Z ⊗ₘ (λ_ (𝟙_ V)).inv ≫
      (J.inv ⊗ₘ I.inv) ≫ eComp V Z Y X) ≫ eComp V X Z X = eId V X := by
  rw [tensor_comp, tensor_comp, tensorHom_def (eComp V X Y Z), Category.assoc, Category.assoc,
    Category.assoc, ← e_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, ← e_assoc', associator_inv_naturality_assoc,
    tensorHom_def' (g := I.inv), Category.assoc, ← comp_whiskerRight_assoc,
    associator_naturality_assoc, tensorHom_def (f := I.hom), Category.assoc,
    ← whiskerLeft_comp_assoc, (Iso.inv_comp_eq _).mp J.hom_inv, ← I.hom_inv,
    tensorHom_def' I.hom]
  simp only [whiskerLeft_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerRight_tensor, whiskerRight_id, triangle_assoc, e_comp_id]
  monoidal

/-- The composition of to isomorphisms in a `V`-enriched category. -/
@[trans, simps]
def trans {X Y Z : C} (I : X ≅[V] Y) (J : Y ≅[V] Z) : X ≅[V] Z where
  hom := (λ_ _).inv ≫ (I.hom ⊗ₘ J.hom) ≫ eComp V X Y Z
  inv := (λ_ _).inv ≫ (J.inv ⊗ₘ I.inv) ≫ eComp V Z Y X
  hom_inv := trans_hom_inv I J
  inv_hom := trans_hom_inv J.symm I.symm

end EnrichedIso

/-- The isomorphism in `ForgetEnrichment W C` induced by a `W`-enriched iso in `C`. -/
@[simps]
def ForgetEnrichment.isoOf {X Y : C} (I : X ≅[V] Y) :
    ForgetEnrichment.of V X ≅ ForgetEnrichment.of V Y where
  hom := homOf V I.hom
  inv := homOf V I.inv
  hom_inv_id := by simp [← homOf_comp, I.hom_inv]
  inv_hom_id := by simp [← homOf_comp, I.inv_hom]

@[simp]
lemma ForgetEnrichment.isoOf_refl (X : C) : isoOf V (.refl X) = Iso.refl (of V X) := by
  ext; simp

@[simp]
lemma ForgetEnrichment.isoOf_symm {X Y : C} (I : X ≅[V] Y) :
    isoOf V (.symm I) = (isoOf V I).symm := by
  rfl

@[simp]
lemma ForgetEnrichment.isoOf_trans {X Y Z : C} (I : X ≅[V] Y) (J : Y ≅[V] Z) :
    isoOf V (I.trans J) = (isoOf V I).trans (isoOf V J) := by
  ext; simp [← Category.assoc, homOf_comp]

/-- The `V`-enriched isomorphism in `C` associated to an iso `X ≅ Y` in `ForgetEnrichment V C`. -/
@[simps]
def ForgetEnrichment.isoTo {X Y : ForgetEnrichment V C} (I : X ≅ Y) :
    EnrichedIso V (ForgetEnrichment.to V X) (ForgetEnrichment.to V Y) where
  hom := homTo V I.hom
  inv := homTo V I.inv
  hom_inv := by rw [← Category.assoc, ← homTo_comp, I.hom_inv_id, homTo_id]
  inv_hom := by rw [← Category.assoc, ← homTo_comp, I.inv_hom_id, homTo_id]

@[simp]
lemma ForgetEnrichment.isoTo_rfl {X : ForgetEnrichment V C} :
    isoTo V (.refl X) = .refl (ForgetEnrichment.to V X) := by
  ext <;> simp

@[simp]
lemma ForgetEnrichment.isoTo_symm {X Y : ForgetEnrichment V C} (I : X ≅ Y) :
    isoTo V I.symm = .symm (isoTo V I) := by
  ext <;> simp

@[simp]
lemma ForgetEnrichment.isoTo_trans {X Y Z : ForgetEnrichment V C} (I : X ≅ Y) (J : Y ≅ Z) :
    isoTo V (I.trans J) = .trans (isoTo V I) (isoTo V J) := by
  ext <;> simp

/-- The type equivalence between isos in `ForgetEnrichment V C` and `V`-enriched isos in `C`. -/
def ForgetEnrichment.equivIsoEnrichedIso (X Y : ForgetEnrichment V C) :
    (X ≅ Y) ≃ (ForgetEnrichment.to V X) ≅[V] (ForgetEnrichment.to V Y) where
  toFun := ForgetEnrichment.isoTo V
  invFun := ForgetEnrichment.isoOf V

end CategoryTheory
