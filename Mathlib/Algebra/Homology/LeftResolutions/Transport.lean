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

variable {A C : Type*} [Category C] [Category A] {ι : C ⥤ A}
  {A' C' : Type*} [Category C'] [Category A'] {ι' : C' ⥤ A'}

namespace LeftResolutions

def transport (Λ : LeftResolutions ι)
    (eA : A' ≌ A) (eC : C' ≌ C) (e : ι' ⋙ eA.functor ≅ eC.functor ⋙ ι) :
    LeftResolutions ι' where
  F := eA.functor ⋙ Λ.F ⋙ eC.inverse
  π := (Functor.rightUnitor _).inv ≫ whiskerLeft _ eA.unitIso.hom ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft _ (Functor.associator _ _ _).inv ≫
      whiskerLeft _ (whiskerRight e.hom _) ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight (Functor.associator _ _ _).inv _ ≫
      whiskerRight (whiskerRight (Functor.associator _ _ _).hom _) _ ≫
      whiskerRight (whiskerRight (whiskerLeft _ ((Functor.associator _ _ _).hom ≫
      whiskerLeft Λ.F eC.counitIso.hom ≫ Λ.F.rightUnitor.hom)) _) _ ≫
        (whiskerRight ((Functor.associator _ _ _).hom ≫ whiskerLeft _ Λ.π ≫
          (Functor.rightUnitor _).hom) _) ≫ eA.unitIso.inv
  hπ := by
    dsimp
    simp only [Functor.map_id, comp_id, id_comp]
    infer_instance

end LeftResolutions

end CategoryTheory.Abelian
