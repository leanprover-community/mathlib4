/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover

/-!
# Morphisms between automorphisms in Galois categories

-/

-- to be moved to `CategoryTheory/Galois`

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- If `f ≫ g = fg`, this is the morphism between the group of automorphisms
of `Over.mk f` to the group of automorphism of `Over.mk fg`. -/
@[implicit_reducible]
def Aut.overMap {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk f) →* Aut (Over.mk fg) where
  toFun σ := Over.isoMk ((Over.forget ..).mapIso σ)
    (by simp [← fac, Functor.mapIso, dsimp% σ.hom.w_assoc])
  map_one' := rfl
  map_mul' _ _ := rfl

open PreGaloisCategory

namespace GaloisCategory

variable [GaloisCategory C]

section

variable {Y' Y X : C}
  [PreGaloisCategory.IsConnected X] (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
  [IsGaloisCover fg] [IsGaloisCover g]

noncomputable def autMapOfIsGaloisCover (h : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk fg) →* Aut (Over.mk g) :=
  autMapHom (Over.homMk f)

@[reassoc (attr := simp)]
lemma comp_autMapOfIsGaloisCover_hom_left
    (γ : Aut (Over.mk fg)) (h : f ≫ g = fg := by cat_disch) :
    f ≫ ((autMapOfIsGaloisCover f g fg h) γ).hom.left =
      γ.hom.left ≫ f :=
  (Over.forget _).congr_map
    (comp_autMap (Over.homMk f : Over.mk fg ⟶ Over.mk g) γ)

lemma autMapOfIsGaloisCover_eq
    (γ : Aut (Over.mk fg)) (φ : Aut (Over.mk g)) (h : f ≫ g = fg := by cat_disch)
    (hφ : f ≫ φ.hom.left = γ.hom.left ≫ f := by cat_disch) :
    (autMapOfIsGaloisCover f g fg) γ = φ :=
  autMap_unique _ _ _ (by cat_disch)

@[reassoc (attr := simp)]
lemma comp_autMapOfIsGaloisCover_inv_left
    (γ : Aut (Over.mk fg)) (h : f ≫ g = fg := by cat_disch) :
    f ≫ ((autMapOfIsGaloisCover f g fg h) γ).inv.left =
      γ.inv.left ≫ f := by
  simpa using! comp_autMapOfIsGaloisCover_hom_left f g fg γ⁻¹

end

end GaloisCategory

end CategoryTheory
