/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Chosen pullbacks

## Main declarations

- `ChosenPullback` : For a morphism `f : Y ⟶ X` in `C`, the type class `ChosenPullback f`
provides the data of a pullback functor `Over X ⥤ Over Y` as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullback` has good closure properties, e.g., isos have chosen pullbacks, and
  composition of morphisms with chosen pullbacks have chosen pullbacks.

-  `Over.ChosenPullback.isPullback` proves that for morphisms `f` and `g` with the same codomain,
  the object `Over.ChosenPullback.pullbackObj f g` together with morphisms
  `Over.ChosenPullback.fst f g` and `Over.ChosenPullback.snd f g` form a pullback square
  over `f` and `g`.

- We prove that in cartesian monoidal categories, morphisms to the terminal object and the product
  projections have chosen pullbacks.

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

namespace Over

/-- A choice of pullback functor `Over X ⥤ Over Y` along a morphism `f : Y ⟶ X` in `C`
as a right adjoint to the functor `Over.map f`. -/
class ChosenPullback {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

namespace ChosenPullback

/-- `ChosenPullback (Over.mk f).hom` from  `ChosenPullback f`. -/
def overMkHom {Y X : C} (f : Y ⟶ X) [ChosenPullback f] : ChosenPullback (Over.mk f).hom :=
  inferInstanceAs (ChosenPullback f)

/-- Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPullback`. -/
@[simps]
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] :
    ChosenPullback f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- The identity morphism has a chosen pullback. -/
@[simps]
def id (X : C) : ChosenPullback (𝟙 X) where
  pullback := 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

/-- Every isomorphism has a chosen pullback. -/
@[simps]
def iso {Y X : C} (f : Y ≅ X) : ChosenPullback f.hom where
  pullback.obj Z := Over.mk (Z.hom ≫ f.inv)
  pullback.map {Y Z} g := Over.homMk (g.left)
  mapPullbackAdj.unit.app T := Over.homMk (𝟙 T.left)
  mapPullbackAdj.counit.app U := Over.homMk (𝟙 _)

/-- The composition of morphisms with chosen pullbacks has a chosen pullback. -/
@[simps]
def comp {Z Y X : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    [ChosenPullback f] [ChosenPullback g] : ChosenPullback (g ≫ f) where
  pullback := pullback f ⋙ pullback g
  mapPullbackAdj := ((mapPullbackAdj g).comp (mapPullbackAdj f)).ofNatIsoLeft
    (Over.mapComp g f).symm

/-- In cartesian monoidal categories, any morphism to the terminal object has a chosen pullback. -/
@[simps]
def cartesianMonoidalCategoryToTerminal [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullback f where
  pullback.obj Y := Over.mk (fst X Y.left)
  pullback.map {Y Z} g := Over.homMk (X ◁ g.left)
  mapPullbackAdj := Adjunction.mkOfHomEquiv
    { homEquiv U Z :=
      { toFun z := Over.homMk (lift U.hom z.left)
        invFun u := Over.homMk (u.left ≫ snd X Z.left)
        left_inv k := by simp
        right_inv k := by
          ext
          dsimp
          ext
          · simpa using k.w.symm
          · aesop } }

/-- In cartesian monoidal categories, the first product projections `fst` have chosen pullbacks. -/
@[simps]
def cartesianMonoidalCategoryFst [CartesianMonoidalCategory C] {X Y : C} :
    ChosenPullback (fst X Y : X ⊗ Y ⟶ X) where
  pullback.obj Z := Over.mk (Z.hom ▷ Y)
  pullback.map g := Over.homMk (g.left ▷ Y)
  mapPullbackAdj.unit.app T := Over.homMk (lift (𝟙 _) (T.hom ≫ snd _ _))
  mapPullbackAdj.counit.app U := Over.homMk (fst _ _)

/-- In cartesian monoidal categories, the second product projections `snd` have chosen pullbacks. -/
@[simps]
def cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] {X Y : C} :
    ChosenPullback (snd X Y : X ⊗ Y ⟶ Y) where
  pullback.obj Z := Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

section PullbackFromChosenPullbacks

variable {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullback g]

/-- The underlying object of the chosen pullback along `g` of `f`. -/
abbrev pullbackObj := ((pullback g).obj (Over.mk f)).left

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk f`. -/
abbrev fst' := (mapPullbackAdj g).counit.app (Over.mk f)

/-- The first projection from the chosen pullback along `g` of `f` to the domain of `f`. -/
abbrev fst : pullbackObj f g ⟶ Y := fst' f g |>.left

theorem fst'_left : (fst' f g).left = fst f g := rfl

/-- The second projection from the chosen pullback along `g` of `f` to the domain of `g`. -/
abbrev snd : pullbackObj f g ⟶ Z := (pullback g).obj (Over.mk f) |>.hom

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk g`. -/
abbrev snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g) :=
  Over.homMk (snd f g)

theorem snd'_left : (snd' f g).left = snd f g := by
  rfl

variable {f g}

@[reassoc]
theorem condition : fst f g ≫ f = snd f g ≫ g :=
  Over.w (fst' f g)

variable (f g) in

@[ext]
theorem hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
    (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) :
    φ₁ = φ₂ := by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using h₂.symm)
  have : (adj.homEquiv U _).symm φ₁' = (adj.homEquiv U _).symm φ₂' := by
    simp [adj.homEquiv_symm_apply]
    apply (forget X).map_injective
    simpa using h₁
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    exact this
  apply congr_arg CommaMorphism.left this

section Lift

variable {W : C} (a : W ⟶ Y) (b : W ⟶ Z) (h : a ≫ f = b ≫ g)

/-- Given morphisms `a : W ⟶ Y` and `b : W ⟶ Z` satisfying `a ≫ f = b ≫ g`,
constructs the unique morphism `W ⟶ pullbackObj f g`. -/
def lift : W ⟶ pullbackObj f g :=
  (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

@[reassoc (attr := simp)]
theorem lift_fst : lift a b h ≫ fst f g = a := by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  let l' := adj.homEquiv (Over.mk b) (Over.mk f) (Over.homMk a)
  have : (Over.map g).map l' ≫ fst' f g = a' := by
    simp [← Adjunction.homEquiv_counit]
    aesop
  apply congr_arg CommaMorphism.left this

@[reassoc (attr := simp)]
theorem lift_snd : lift a b h ≫ snd f g = b := by
  simp [lift]

theorem isPullback {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullback g] :
    IsPullback (fst f g) (snd f g) f g where
  w := condition
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst s.snd s.condition)
      (by simp) (by simp) (by aesop)⟩

end Lift

end PullbackFromChosenPullbacks

end ChosenPullback

end Over

end CategoryTheory
