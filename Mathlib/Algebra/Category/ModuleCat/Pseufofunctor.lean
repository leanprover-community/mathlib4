/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat

/-!
# The pseudofunctor(s) which send a ring to its category of modules

In this file, we construct the pseudofunctor
`ModuleCat.restrictScalarsPseudofunctor : Pseudofunctor (LocallyDiscrete RingCatᵒᵖ) Cat`
which sends a ring `R` to its category of modules: the functoriality is given
by the restriction of scalars functors.

TODO: Define
`ModuleCat.extendScalarsPseudofunctor : Pseudofunctor (LocallyDiscrete CommRingCat) Cat`.

-/

universe v u

namespace CategoryTheory

section

class IsDiscrete (C : Type*) [Category C] where
  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y

attribute [instance] IsDiscrete.subsingleton

lemma obj_ext_of_isDiscrete {C : Type*} [Category C] [IsDiscrete C]
    {X Y : C} (f : X ⟶ Y) : X = Y := IsDiscrete.eq_of_hom f

instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
  eq_of_hom := by rintro ⟨_⟩ ⟨_⟩ ⟨⟨rfl⟩⟩; rfl

end

namespace Bicategory

abbrev IsLocallyDiscrete (B : Type*) [Bicategory B] := ∀ (b c : B), IsDiscrete (b ⟶ c)

instance (C : Type*) [Category C] :
    IsLocallyDiscrete (LocallyDiscrete C) := fun _ _ ↦ Discrete.isDiscrete _

end Bicategory

open Bicategory

@[simps]
def pseudofunctorOfIsLocallyDiscrete
    {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C] [Strict B]
    (obj : B → C)
    (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ (b : B), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by aesop_cat)
    (map₂_left_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp) :=
        by aesop_cat)
    (map₂_right_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) :=
        by aesop_cat) :
    Pseudofunctor B C where
  obj := obj
  map := map
  map₂ φ := eqToHom (by
    obtain rfl := obj_ext_of_isDiscrete φ
    dsimp)
  mapId := mapId
  mapComp := mapComp
  map₂_whisker_left _ _ _ η := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp
  map₂_whisker_right η _ := by
    obtain rfl := obj_ext_of_isDiscrete η
    simp

namespace LocallyDiscrete

@[simps!]
def mkPseudofunctor {B C : Type*} [Category B] [Bicategory C]
    (obj : B → C)
    (map : ∀ {b b' : B}, (b ⟶ b') → (obj b ⟶ obj b'))
    (mapId : ∀ (b : B), map (𝟙 b) ≅ 𝟙 _)
    (mapComp : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), map (f ≫ g) ≅ map f ≫ map g)
    (map₂_associator : ∀ {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃),
      (mapComp (f ≫ g) h).hom ≫
        (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫
          map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv = eqToHom (by simp) := by aesop_cat)
    (map₂_left_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp (𝟙 b₀) f).hom ≫ (mapId b₀).hom ▷ map f ≫ (λ_ (map f)).hom = eqToHom (by simp) :=
        by aesop_cat)
    (map₂_right_unitor : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁),
      (mapComp f (𝟙 b₁)).hom ≫ map f ◁ (mapId b₁).hom ≫ (ρ_ (map f)).hom = eqToHom (by simp) :=
        by aesop_cat) :
    Pseudofunctor (LocallyDiscrete B) C :=
  pseudofunctorOfIsLocallyDiscrete (fun b ↦ obj b.as) (fun f ↦ map f.as)
    (fun _ ↦ mapId _) (fun _ _ ↦ mapComp _ _) (fun _ _ _ ↦ map₂_associator _ _ _)
    (fun _ ↦ map₂_left_unitor _) (fun _ ↦ map₂_right_unitor _)

end LocallyDiscrete

end CategoryTheory

open CategoryTheory

namespace ModuleCat

@[simps! obj map mapId mapComp]
noncomputable def restrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete RingCat.{u}ᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{v} R.unop))
    (fun f ↦ restrictScalars f.unop)
    (fun R ↦ restrictScalarsId R.unop)
    (fun f g ↦ restrictScalarsComp g.unop f.unop)

noncomputable def extendsScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (ModuleCat.{u} R))
    (fun f ↦ extendScalars f)
    (fun R ↦ sorry) sorry sorry sorry sorry

end ModuleCat
