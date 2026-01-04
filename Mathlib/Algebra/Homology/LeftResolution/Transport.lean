/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Basic

/-!
# Transport left resolutions along equivalences

If `ι : C ⥤ A` is equipped with `Λ : LeftResolution ι` and
`ι' : C' ⥤ A'` is a functor which corresponds to `ι` via
equivalences of categories `A' ≌ A` and `C' ≌ C`, we
define `Λ.transport .. : LeftResolution ι'`.

-/

@[expose] public section

namespace CategoryTheory.Abelian

open Category

variable {A C : Type*} [Category* C] [Category* A]
  {A' C' : Type*} [Category* C'] [Category* A']

namespace LeftResolution

open Functor

/-- Transport `LeftResolution` via equivalences of categories. -/
def transport {ι : C ⥤ A} (Λ : LeftResolution ι) {ι' : C' ⥤ A'}
    (eA : A' ≌ A) (eC : C' ≌ C) (e : ι' ⋙ eA.functor ≅ eC.functor ⋙ ι) :
    LeftResolution ι' where
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
  epi_π_app _ := by dsimp; infer_instance

/-- If we have an isomorphism `e : G ⋙ ι' ≅ ι`, then any `Λ : LeftResolution ι`
induces `Λ.ofCompIso e : LeftResolution ι'`. -/
def ofCompIso {ι : C ⥤ A} (Λ : LeftResolution ι) {ι' : C' ⥤ A} {G : C ⥤ C'}
    (e : G ⋙ ι' ≅ ι) :
    LeftResolution ι' where
  F := Λ.F ⋙ G
  π := (associator _ _ _).hom ≫ whiskerLeft _ e.hom ≫ Λ.π
  epi_π_app _ := by dsimp; infer_instance

end LeftResolution

end CategoryTheory.Abelian
