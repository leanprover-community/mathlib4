/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Equivalence

/-! 2-commutative squares of functors

Similarly as `CommSq.lean` defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type _} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  [Category C₅] [Category C₆]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- `CatCommSq T L R B` expresses that there is a 2-commutative square of functors, where
the functors `T`, `L`, `R` and `B` are respectively the left, top, right and bottom functors
of the square. -/
@[ext]
class CatCommSq where
  /-- the isomorphism corresponding to a 2-commutative diagram -/
  iso' : T ⋙ R ≅ L ⋙ B

namespace CatCommSq

/-- Assuming `[CatCommSq T L R B]`, `iso T L R B` is the isomorphism `T ⋙ R ≅ L ⋙ B`
given by the 2-commutative square. -/
def iso [h : CatCommSq T L R B] : T ⋙ R ≅ L ⋙ B := h.iso'

variable {L T R B}

/-- Horizontal composition of 2-commutative squares -/
@[simps! iso'_hom_app iso'_inv_app]
def hComp (T₁ : C₁ ⥤ C₂) (T₂ : C₂ ⥤ C₃) (V₁ : C₁ ⥤ C₄) (V₂ : C₂ ⥤ C₅) (V₃ : C₃ ⥤ C₆)
    (B₁ : C₄ ⥤ C₅) (B₂ : C₅ ⥤ C₆) [CatCommSq T₁ V₁ V₂ B₁] [CatCommSq T₂ V₂ V₃ B₂] :
    CatCommSq (T₁ ⋙ T₂) V₁ V₃ (B₁ ⋙ B₂) where
  iso' := Functor.associator _ _ _ ≪≫ isoWhiskerLeft T₁ (iso T₂ V₂ V₃ B₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso T₁ V₁ V₂ B₁) B₂ ≪≫
    Functor.associator _ _ _

/-- Vertical composition of 2-commutative squares -/
@[simps! iso'_hom_app iso'_inv_app]
def vComp (L₁ : C₁ ⥤ C₂) (L₂ : C₂ ⥤ C₃) (H₁ : C₁ ⥤ C₄) (H₂ : C₂ ⥤ C₅) (H₃ : C₃ ⥤ C₆)
    (R₁ : C₄ ⥤ C₅) (R₂ : C₅ ⥤ C₆) [CatCommSq H₁ L₁ R₁ H₂] [CatCommSq H₂ L₂ R₂ H₃] :
    CatCommSq H₁ (L₁ ⋙ L₂) (R₁ ⋙ R₂) H₃ where
  iso' := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (iso H₁ L₁ R₁ H₂) R₂ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft L₁ (iso H₂ L₂ R₂ H₃) ≪≫
      (Functor.associator _ _ _).symm

section

variable (T : C₁ ≌ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ≌ C₄)

/-- Horizontal inverse of a 2-commutative square -/
@[simps! iso'_hom_app iso'_inv_app]
def hInv (_ : CatCommSq T.functor L R B.functor) : CatCommSq T.inverse R L B.inverse where
  iso' := isoWhiskerLeft _ (L.rightUnitor.symm ≪≫ isoWhiskerLeft L B.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (iso T.functor L R B.functor).symm B.inverse ≪≫
      Functor.associator _ _ _  ) ≪≫ (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight T.counitIso _ ≪≫ Functor.leftUnitor _

/-- Horizontal inverse of a 2-commutative square -/
@[simps! iso'_hom_app iso'_inv_app]
def hInv'(h : CatCommSq T.inverse R L B.inverse) : CatCommSq T.functor L R B.functor :=
  hInv T.symm R L B.symm h

/-- In a square of categories, when the top and bottom functors are part
of equivalence of categorires, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv _ _ _ _
  invFun := hInv' _ _ _ _
  left_inv h := by
    ext X
    have eq := h.iso'.hom.naturality (T.unitIso.hom.app X)
    dsimp at eq
    simp only [Functor.comp_obj, hInv'_iso'_hom_app, iso, hInv_iso'_inv_app, Functor.map_comp,
      Equivalence.fun_inv_map, Functor.id_obj, Category.assoc,
      Equivalence.counitInv_functor_comp, Category.comp_id, Iso.inv_hom_id_app_assoc]
    rw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X))), ← eq,
      assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, Functor.map_id, comp_id, Equivalence.counitInv_app_functor]
  right_inv h := by
    ext X
    have eq := h.iso'.hom.naturality (T.counitIso.hom.app X)
    dsimp at eq
    simp only [Functor.comp_obj, hInv_iso'_hom_app, iso, hInv'_iso'_inv_app, Functor.map_comp,
      Equivalence.inv_fun_map, Functor.id_obj, assoc, Equivalence.unit_inverse_comp, comp_id,
      Iso.hom_inv_id_app_assoc, ← eq, ← L.map_comp_assoc, Functor.map_id, id_comp]

end

end CatCommSq

end CategoryTheory
