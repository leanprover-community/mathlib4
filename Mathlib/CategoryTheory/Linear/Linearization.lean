/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Linearization of a category

Let `C` be a category and `R` be a commutative ring.
We construct a `R`-linear category `Linearization C R` and
a functor `toLinearization C R : C ⥤ Linearization C R`.
The morphisms in `Linearization C R` are the free `R`-modules
on the types of morphisms in `C`.

-/

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- Given a category `C` and a commutative ring `R`, this is the `R`-linearization
of the category `C`: it has basically the same objects as `C`, but types of morphisms
are the free `R`-modules on the types of morphisms in `C`. -/
structure Linearization (R : Type w) [CommRing R] where
  /-- the underlying object in the original category -/
  obj : C

variable {C} {R : Type w} [CommRing R] {X Y Z T : Linearization C R}

namespace Linearization

variable (X Y) in
/-- The types of morphisms in `Linearization C R`: this is the free `R`-module
on a type of morphisms in `C`. -/
def Hom := (X.obj ⟶ Y.obj) →₀ R

noncomputable instance : AddCommGroup (Hom X Y) :=
  inferInstanceAs (AddCommGroup ((X.obj ⟶ Y.obj) →₀ R))

noncomputable instance : Module R (Hom X Y) :=
  inferInstanceAs (Module R ((X.obj ⟶ Y.obj) →₀ R))

namespace Hom

/-- Constructor for morphisms in `Linearization C R`.
(Use `Linearization.single` instead.) -/
noncomputable def single (f : X.obj ⟶ Y.obj) :
    Hom X Y :=
  Finsupp.single f 1

variable (X) in
/-- The identity morphism in `Linearization C R`. -/
noncomputable abbrev id : Hom X X := single (𝟙 X.obj)

/-- The composition of morphisms in `Linearization C R`. -/
noncomputable def comp : Hom X Y →ₗ[R] Hom Y Z →ₗ[R] Hom X Z :=
  Finsupp.linearCombination R
    (fun f ↦ Finsupp.linearCombination R (fun g ↦ Hom.single (f ≫ g)))

@[ext]
lemma linearMap_ext {T : Type*} [AddCommGroup T] [Module R T] {f g : Hom X Y →ₗ[R] T}
    (h : ∀ (m : X.obj ⟶ Y.obj), f (.single m) = g (.single m)) :
    f = g := by
  dsimp [Hom]
  aesop

@[simp]
lemma single_comp_single (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    (single f).comp (single g) = single (f ≫ g) := by
  simp [Hom, comp, single]

@[simp]
lemma id_comp (f : Hom X Y) : (id X).comp f = f := by
  suffices comp (Z := Y) (id X) = .id from DFunLike.congr_fun this f
  aesop

@[simp]
lemma comp_id (f : Hom X Y) : f.comp (id Y) = f := by
  suffices (comp (X := X)).flip (id Y) = .id from DFunLike.congr_fun this f
  aesop

@[simp]
lemma assoc (f : Hom X Y) (g : Hom Y Z) (h : Hom Z T) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  suffices (comp (X := X) (Y := Y) (Z := Z)).compr₂ (comp (Z := T)) =
      ((LinearMap.llcomp _ _ _ _).flip.comp comp).flip.comp comp from
    DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this f) g) h
  aesop

end Hom

noncomputable instance : Category (Linearization C R) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

/-- Constructor for morphisms in `Linearization C R`. -/
noncomputable def single (f : X.obj ⟶ Y.obj) : X ⟶ Y := Hom.single f

@[reassoc (attr := simp)]
lemma single_comp_single (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    single f ≫ single g = single (f ≫ g) :=
  Hom.single_comp_single _ _

noncomputable instance : AddCommGroup (X ⟶ Y) :=
  inferInstanceAs (AddCommGroup (Hom X Y))

noncomputable instance : Module R (X ⟶ Y) :=
  inferInstanceAs (Module R (Hom X Y))

noncomputable instance : Preadditive (Linearization C R) where
  comp_add _ _ _ f g₁ g₂ := by exact (Hom.comp f).map_add g₁ g₂
  add_comp _ _ _ f₁ f₂ g := by exact DFunLike.congr_fun (Hom.comp.map_add f₁ f₂) g

noncomputable instance : Linear R (Linearization C R) where
  comp_smul _ _ _ f r g := by exact (Hom.comp f).map_smul r g
  smul_comp X Y Z r f g := by exact DFunLike.congr_fun (Hom.comp.map_smul r f) g

end Linearization

variable (C R) in
/-- The functor from a category to its linearization. -/
noncomputable def toLinearization : C ⥤ Linearization C R where
  obj X := .mk X
  map f := Linearization.single f

end CategoryTheory
