/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Equivalence

/-!
# 2-commutative squares of functors

Similarly as `CommSq.lean` defines the notion of commutative squares,
this file introduces the notion of 2-commutative squares of functors.

If `T : C₁ ⥤ C₂`, `L : C₁ ⥤ C₃`, `R : C₂ ⥤ C₄`, `B : C₃ ⥤ C₄` are functors,
then `[CatCommSq T L R B]` contains the datum of an isomorphism `T ⋙ R ≅ L ⋙ B`.

Future work: using this notion in the development of the localization of categories
(e.g. localization of adjunctions).

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
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

lemma hInv_hInv (h : CatCommSq T.functor L R B.functor) :
  hInv T.symm R L B.symm (hInv T L R B h) = h := by
    ext X
    -- ⊢ NatTrans.app iso'.hom X = NatTrans.app iso'.hom X
    erw [← cancel_mono (B.functor.map (L.map (T.unitIso.hom.app X))),
      ← h.iso'.hom.naturality (T.unitIso.hom.app X), hInv_iso'_hom_app, hInv_iso'_inv_app]
    dsimp
    -- ⊢ (NatTrans.app B.counitIso.inv (R.obj (T.functor.obj X)) ≫ B.functor.map (B.i …
    simp only [Functor.comp_obj, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      Equivalence.counitInv_app_functor, Functor.map_id]
    simp only [Functor.map_comp, Equivalence.fun_inv_map, assoc,
      Equivalence.counitInv_functor_comp, comp_id, Iso.inv_hom_id_app_assoc]
    rfl
    -- 🎉 no goals

/-- In a square of categories, when the top and bottom functors are part
of equivalence of categorires, it is equivalent to show 2-commutativity for
the functors of these equivalences or for their inverses. -/
def hInvEquiv : CatCommSq T.functor L R B.functor ≃ CatCommSq T.inverse R L B.inverse where
  toFun := hInv T L R B
  invFun := hInv T.symm R L B.symm
  left_inv := hInv_hInv T L R B
  right_inv := hInv_hInv T.symm R L B.symm

end

instance hInv' [h : CatCommSq T L R B] [IsEquivalence T] [IsEquivalence B] :
    CatCommSq T.inv R L B.inv :=
  hInv T.asEquivalence L R B.asEquivalence h

end CatCommSq

end CategoryTheory
