/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

# Implementation details

`Functor.Linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/


namespace CategoryTheory

variable (R : Type*) [Semiring R] {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
class Functor.Linear : Prop where
  /-- the functor induces a linear map on morphisms -/
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by aesop_cat

lemma Functor.linear_iff (F : C ⥤ D) :
    Functor.Linear R F ↔ ∀ (X : C) (r : R), F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  constructor
  · intro h X r
    rw [h.map_smul, F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this, F.map_comp, h, Linear.smul_comp, Category.id_comp]

section Linear

namespace Functor

section

variable {R} [Linear R F]

@[simp]
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  Functor.Linear.map_smul _ _

@[simp]
theorem map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  apply map_smul

instance : Linear R (𝟭 C) where

instance {E : Type*} [Category E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)
    [Linear R G] : Linear R (F ⋙ G) where

variable (R) [F.Additive]

/-- `F.mapLinearMap` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }

theorem coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) →ₗ[R] _) = F.map := rfl

end

variable {F} in
lemma linear_of_iso {G : C ⥤ D} (e : F ≅ G) [F.Linear R] : G.Linear R := by
  exact
    { map_smul := fun f r => by
        simp only [← NatIso.naturality_1 e (r • f), F.map_smul, Linear.smul_comp,
          NatTrans.naturality, Linear.comp_smul, Iso.inv_hom_id_app_assoc] }

section InducedCategory

instance inducedFunctorLinear (F : C → D) : Functor.Linear R (inducedFunctor F) where

end InducedCategory

instance fullSubcategoryInclusionLinear {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear R C] (Z : ObjectProperty C) : Z.ι.Linear R where

section

variable {R} [Additive F]

instance natLinear : F.Linear ℕ where
  map_smul := F.mapAddHom.map_nsmul

instance intLinear : F.Linear ℤ where
  map_smul f r := F.mapAddHom.map_zsmul f r

variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]

instance ratLinear : F.Linear ℚ where
  map_smul f r := F.mapAddHom.toRatLinearMap.map_smul r f

end

end Functor

namespace Equivalence

instance inverseLinear (e : C ≌ D) [e.functor.Linear R] : e.inverse.Linear R where
  map_smul r f := by
    apply e.functor.map_injective
    simp

end Equivalence

end Linear

end CategoryTheory
