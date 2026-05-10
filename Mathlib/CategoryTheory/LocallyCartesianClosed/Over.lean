/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# Cartesian monoidal structure on slices induced by chosen pullbacks

## Main declarations

- `cartesianMonoidalCategoryOver` provides a cartesian monoidal structure on the slice categories
  `Over X` for all objects `X : C`, induced by chosen pullbacks in the base category `C`.
  This is the computable analogue of the noncomputable instance
  `CategoryTheory.Over.cartesianMonoidalCategory`.

- For a cartesian monoidal category `C`, and for any object `X` of `C`,
  `toOver X` is a functor from `C` to `Over X` which maps an object `A : C` to the projection
  `A ⊗ X ⟶ X` in `Over X`. This is the computable analogue of the functor `Over.star`.

## Main results

- `cartesianMonoidalCategoryOver` proves that the slices of a category with chosen pullbacks are
  cartesian monoidal.

- `toOverPullbackIsoToOver` shows that in a category with chosen pullbacks, for any morphism
  `f : Y ⟶ X`, the functors `toOver X ⋙ pullback f` and `toOver Y` are naturally isomorphic.

- `toOverIteratedSliceForwardIsoPullback` shows that in a category with chosen pullbacks the functor
  `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
  `toOver (Over.mk f) : Over X ⥤ Over (Over.mk f)` post-composed with the iterated slice equivalence
  `Over (Over.mk f) ⥤ Over Y`. Note that the functor `toOver (Over.mk f)` exists by the result
  `cartesianMonoidalCategoryOver`.

### TODO

- Show that the functors `pullback f` are monoidal with respect to
  the cartesian monoidal structures on slices.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

namespace ChosenPullbacksAlong

open CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

section

open Limits

variable {X : C} (Y Z : Over X)

/-- The binary fan provided by `fst'` and `snd'`. -/
abbrev binaryFan [ChosenPullbacksAlong Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

/-- The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`. -/
def binaryFanIsBinaryProduct [ChosenPullbacksAlong Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

end

/-- A computable instance of `CartesianMonoidalCategory` for `Over X` when `C` has
chosen pullbacks. Contrast this with the noncomputable instance provided by
`CategoryTheory.Over.cartesianMonoidalCategory`.
-/
@[instance_reducible]
def cartesianMonoidalCategoryOver [ChosenPullbacks C] (X : C) :
    CartesianMonoidalCategory (Over X) :=
  ofChosenFiniteProducts (C := Over X)
    ⟨Limits.asEmptyCone (Over.mk (𝟙 X)), Limits.IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z ↦ ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

namespace Over

open MonoidalCategory

variable [ChosenPullbacks C] {X : C}

attribute [local instance] cartesianMonoidalCategoryOver

@[ext]
lemma tensorObj_ext {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y ⊗ Z).left)
    (e₁ : f₁ ≫ fst Y.hom Z.hom = f₂ ≫ fst Y.hom Z.hom)
    (e₂ : f₁ ≫ snd Y.hom Z.hom = f₂ ≫ snd Y.hom Z.hom) : f₁ = f₂ :=
  hom_ext Y.hom Z.hom e₁ e₂

@[simp]
lemma tensorObj_left (Y Z : Over X) : (Y ⊗ Z).left = pullbackObj Y.hom Z.hom := rfl

@[simp]
lemma tensorObj_hom (Y Z : Over X) : (Y ⊗ Z).hom = snd Y.hom Z.hom ≫ Z.hom := rfl

@[simp]
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

lemma fst_eq_fst' (Y Z : Over X) :
    CartesianMonoidalCategory.fst Y Z = fst' Y.hom Z.hom :=
  rfl

lemma snd_eq_snd' (Y Z : Over X) :
    CartesianMonoidalCategory.snd Y Z = snd' Y.hom Z.hom :=
  rfl

@[simp]
lemma lift_left {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z) :
    (CartesianMonoidalCategory.lift f g).left = lift f.left g.left := rfl

@[simp]
lemma toUnit_left {Z : Over X} : (toUnit Z).left = Z.hom := rfl

@[reassoc (attr := simp)]
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ fst R.hom (snd S.hom T.hom ≫ T.hom) =
      fst (R ⊗ S).hom T.hom ≫ fst R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_fst R S T)

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ fst S.hom T.hom =
      fst (R ⊗ S).hom T.hom ≫ snd R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_fst R S T)

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ snd S.hom T.hom =
      snd (R ⊗ S).hom T.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_snd R S T)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ fst R.hom S.hom =
      fst R.hom (S ⊗ T).hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_fst R S T)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ snd R.hom S.hom =
      snd R.hom (S ⊗ T).hom ≫ fst S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_snd R S T)

@[reassoc (attr := simp)]
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ snd (snd R.hom S.hom ≫ S.hom) T.hom =
      snd R.hom (S ⊗ T).hom ≫ snd S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_snd R S T)

@[simp]
lemma leftUnitor_hom_left (Z : Over X) :
    (λ_ Z).hom.left = snd _ Z.hom := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_fst (Z : Over X) :
    (λ_ Z).inv.left ≫ fst (𝟙 X) Z.hom = Z.hom :=
  congr_arg CommaMorphism.left (leftUnitor_inv_fst Z)

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ snd (𝟙 X) Y.hom = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (leftUnitor_inv_snd Y)

@[simp]
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ fst Y.hom (𝟙 X) = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (rightUnitor_inv_fst Y)

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ snd Y.hom (𝟙 X) = Y.hom :=
  congr_arg CommaMorphism.left (rightUnitor_inv_snd Y)

lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullbackMap R.hom T.hom R.hom S.hom (𝟙 _) f.left (𝟙 _) :=
  rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ fst R.hom T.hom = fst R.hom S.hom :=
  congr_arg CommaMorphism.left (whiskerLeft_fst R f)

@[reassoc (attr := simp)]
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ snd R.hom T.hom = snd R.hom S.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerLeft_snd R f)

lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullbackMap T.hom R.hom S.hom R.hom f.left (𝟙 _) (𝟙 _) :=
  rfl

@[reassoc (attr := simp)]
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ fst T.hom R.hom = fst S.hom R.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerRight_fst f R)

@[reassoc (attr := simp)]
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ snd T.hom R.hom = snd S.hom R.hom :=
  congr_arg CommaMorphism.left (whiskerRight_snd f R)

lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left = pullbackMap S.hom U.hom R.hom T.hom f.left g.left (𝟙 _) :=
  rfl

@[reassoc (attr := simp)]
lemma tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ fst S.hom U.hom = fst R.hom T.hom ≫ f.left :=
  congr_arg CommaMorphism.left (tensorHom_fst f g)

@[reassoc (attr := simp)]
lemma tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ snd S.hom U.hom = snd R.hom T.hom ≫ g.left :=
  congr_arg CommaMorphism.left (tensorHom_snd f g)

end Over

end ChosenPullbacksAlong

section ToOver

open ChosenPullbacksAlong CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

/-- The functor which maps an object `A` in `C` to the projection `A ⊗ X ⟶ X` in `Over X`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom map_left]
def toOver (X : C) : C ⥤ Over X where
  obj A := Over.mk <| CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

@[simp]
lemma toOver_map {X : C} {A A' : C} (f : A ⟶ A') :
    (toOver X).map f = Over.homMk (f ▷ X) := by
  simp [toOver]

variable (C)

/-- The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit X`. -/
@[simps! obj_left obj_hom map_left]
def toOverUnit : C ⥤ Over (𝟙_ C) where
  obj X := Over.mk <| toUnit X
  map f := Over.homMk f

/-- The slice category over the terminal unit object is equivalent to the original category. -/
@[simps]
def equivToOverUnit : Over (𝟙_ C) ≌ C where
  functor := Over.forget _
  inverse := toOverUnit _
  unitIso := NatIso.ofComponents fun X => Over.isoMk (Iso.refl _)
  counitIso := NatIso.ofComponents fun X => Iso.refl _

variable {C}

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryToUnit

/-- The isomorphism of functors `toOverUnit C ⋙ ChosenPullbacksAlong.pullback (toUnit X)` and
`toOver X`. -/
@[simps!]
def toOverUnitPullback (X : C) :
    toOverUnit C ⋙ pullback (toUnit X) ≅ toOver X :=
  NatIso.ofComponents fun X => Iso.refl _

/-- The functor `toOver X` is the right adjoint to the functor `Over.forget X`. -/
@[simps! unit_app counit_app]
def forgetAdjToOver (X : C) : Over.forget X ⊣ toOver X where
  unit.app Z := Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X

theorem forgetAdjToOver.homEquiv_symm {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A) :
     ((forgetAdjToOver X).homEquiv Z A).symm f = f.left ≫ (fst _ _) := by
   rw [Adjunction.homEquiv_counit, forgetAdjToOver_counit_app]
   simp

/-- The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`. -/
@[simps!]
def toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C :=
  (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

/-- A natural isomorphism between the functors `toOver Y` and `toOver X ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
@[simps!]
def toOverPullbackIsoToOver {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f] :
    toOver X ⋙ pullback f ≅ toOver Y :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

attribute [local instance] cartesianMonoidalCategoryOver

omit [CartesianMonoidalCategory C] in
/-- The functor `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
`toOver : Over X ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivalence `Over (Over.mk f) ⥤ Over Y`. -/
@[simps!]
def toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X) :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

end ToOver

end CategoryTheory
