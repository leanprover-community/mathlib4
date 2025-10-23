/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.LeftResolutions.Basic

/-!
# Transport left resolutions along equivalences

-/

namespace CategoryTheory.Abelian

open Category

variable {A C : Type*} [Category C] [Category A]
  {A' C' : Type*} [Category C'] [Category A']

namespace LeftResolutions

open Functor

/-- Transport `LeftResolutions` via equivalences of categories. -/
def transport {ι : C ⥤ A} (Λ : LeftResolutions ι) {ι' : C' ⥤ A'}
    (eA : A' ≌ A) (eC : C' ≌ C) (e : ι' ⋙ eA.functor ≅ eC.functor ⋙ ι) :
    LeftResolutions ι' where
  F := eA.functor ⋙ Λ.F ⋙ eC.inverse
  π := (rightUnitor _).inv ≫ whiskerLeft _ eA.unitIso.hom ≫
      (associator _ _ _).hom ≫ whiskerLeft _ (associator _ _ _).inv ≫
      whiskerLeft _ (whiskerRight e.hom _) ≫ (associator _ _ _).inv ≫
      whiskerRight (associator _ _ _).inv _ ≫
      whiskerRight (whiskerRight (associator _ _ _).hom _) _ ≫
      whiskerRight (whiskerRight (whiskerLeft _ ((associator _ _ _).hom ≫
      whiskerLeft Λ.F eC.counitIso.hom ≫ Λ.F.rightUnitor.hom)) _) _ ≫
        (whiskerRight ((associator _ _ _).hom ≫ whiskerLeft _ Λ.π ≫
          (rightUnitor _).hom) _) ≫ eA.unitIso.inv
  hπ X := by
    dsimp
    simp only [Functor.map_id, comp_id, id_comp]
    infer_instance

/-- If we have an isomorphism `e : G ⋙ ι' ≅ ι`, then any `Λ : LeftResolutions ι`
induces `Λ.ofCompIso e : LeftResolutions ι'`. -/
def ofCompIso {ι : C ⥤ A} (Λ : LeftResolutions ι) {ι' : C' ⥤ A} {G : C ⥤ C'}
    (e : G ⋙ ι' ≅ ι) :
    LeftResolutions ι' where
  F := Λ.F ⋙ G
  π := (associator _ _ _).hom ≫ whiskerLeft _ e.hom ≫ Λ.π
  hπ X := by dsimp; infer_instance

end LeftResolutions

end CategoryTheory.Abelian
