/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The mapping cocone

Given a morphism `φ : K ⟶ L` of cochain complexes, the mapping cone
allows to obtain a triangle `K ⟶ L ⟶ mappingCone φ ⟶ ...`. In this
file, we define the mapping cocone, which fits in a rotated triangle:
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex Pretriangulated

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The mapping cocone of a morphism `φ : K ⟶ L` of cochain complexes: it is
`(mappingCone φ)⟦(-1 : ℤ)⟧`. -/
noncomputable def mappingCocone [HasHomotopyCofiber φ] :
    CochainComplex C ℤ := (mappingCone φ)⟦(-1 : ℤ)⟧

namespace mappingCocone

section

variable [HasHomotopyCofiber φ]

/-- The first projection `mappingCocone φ ⟶ K`. -/
noncomputable def fst : mappingCocone φ ⟶ K :=
  -((mappingCone.fst φ).leftShift (-1) 0 (add_neg_cancel 1)).homOf

/-- The second projection in `Cochain (mappingCocone φ) L (-1)`. -/
noncomputable def snd : Cochain (mappingCocone φ) L (-1) :=
  (mappingCone.snd φ).leftShift (-1) (-1) (zero_add _)

/-- The left inclusion in `Cochain K (mappingCocone φ) 0`. -/
noncomputable def inl : Cochain K (mappingCocone φ) 0 :=
  (mappingCone.inl φ).rightShift (-1) 0 (zero_add _)

/-- The right inclusion in `Cocycle L (mappingCocone φ) 1`. -/
noncomputable def inr : Cocycle L (mappingCocone φ) 1 :=
  (Cocycle.ofHom (mappingCone.inr φ)).rightShift (-1) 1 (by lia)

@[reassoc (attr := simp)]
lemma inl_v_fst_f (p : ℤ) :
    (inl φ).v p p (add_zero p) ≫ (fst φ).f p = 𝟙 _ := by
  simp [inl, fst, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]

@[reassoc (attr := simp)]
lemma inl_v_snd_v (p q : ℤ) (hpq : p + -1 = q) :
    (inl φ).v p p (add_zero p) ≫ (snd φ).v p q hpq = 0 := by
  obtain rfl : q = p + -1 := by lia
  simp [inl, snd, Cochain.rightShift_v (n := -1) _ _ _ _ p _ _ (p + -1) (by lia),
    Cochain.leftShift_v _ _ _ _ _ _ hpq]

@[reassoc (attr := simp)]
lemma inr_v_fst_f (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (fst φ).f q = 0 := by
  simp [inr, fst, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ hpq]

lemma inr_v_snd_v (p q : ℤ) (hpq : p + 1 = q) :
    (inr φ).1.v p q hpq ≫ (snd φ).v q p (by lia) = 𝟙 _ := by
  simp [inr, snd, Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero p),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

lemma id_X (p q : ℤ) (hpq : p + -1 = q) :
    (fst φ).f p ≫ (inl φ).v p p (add_zero p) +
      (snd φ).v p q hpq ≫ (inr φ).1.v q p (by lia) = 𝟙 _ := by
  obtain rfl : q = p + -1 := by lia
  simp [fst, inl, snd, inr, mappingCocone,
    Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ hpq,
    Cochain.leftShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (p + -1)),
    Int.negOnePow_even 2 ⟨1, rfl⟩,
    mappingCone.id_X φ (p + -1) p (by lia)]

end

section

variable [HasBinaryBiproducts C]

/-- Given a morphism `φ : K ⟶ L` of cochain complexes, this is the triangle
`mappingCocone φ ⟶ K ⟶ L ⟶ ...`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def triangle : Triangle (CochainComplex C ℤ ) :=
  Triangle.mk (fst φ) φ
    ((mappingCone.triangle φ).mor₂ ≫ (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).inv.app _)

/-- Rotating the triangle `mappingCocone.triangle φ` gives a triangle that is
isomorphic to `mappingCone.triangle φ`. -/
noncomputable def rotateTriangleIso :
    (triangle φ).rotate ≅ mappingCone.triangle φ := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by lia)).app _)
    (by simp) (by simp [triangle]) ?_
  dsimp
  ext n
  simp [fst, mappingCone.triangle, Cochain.leftShift_v _ _ _ _ _ _ _ _ rfl,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]

end

end mappingCocone

end CochainComplex
