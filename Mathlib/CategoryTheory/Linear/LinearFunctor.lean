/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

#align_import category_theory.linear.linear_functor from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

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

variable (R : Type*) [Semiring R]

/-- An additive functor `F` is `R`-linear provided `F.map` is an `R`-module morphism. -/
class Functor.Linear {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive] : Prop where
  /-- the functor induces a linear map on morphisms -/
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by aesop_cat
#align category_theory.functor.linear CategoryTheory.Functor.Linear

section Linear

namespace Functor

section

variable {R}
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] (F : C ⥤ D) [Additive F] [Linear R F]

@[simp]
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  Functor.Linear.map_smul _ _
#align category_theory.functor.map_smul CategoryTheory.Functor.map_smul

@[simp]
theorem map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  apply map_smul

instance : Linear R (𝟭 C) where

instance {E : Type*} [Category E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)
    [Additive G] [Linear R G] : Linear R (F ⋙ G) where

variable (R)

/-- `F.mapLinearMap` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
def mapLinearMap {X Y : C} : (X ⟶ Y) →ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }
#align category_theory.functor.map_linear_map CategoryTheory.Functor.mapLinearMap

theorem coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) →ₗ[R] _) = F.map := rfl
#align category_theory.functor.coe_map_linear_map CategoryTheory.Functor.coe_mapLinearMap

end

section InducedCategory

variable {C : Type*} {D : Type*} [Category D] [Preadditive D] [CategoryTheory.Linear R D]
  (F : C → D)

instance inducedFunctorLinear : Functor.Linear R (inducedFunctor F) where
#align category_theory.functor.induced_functor_linear CategoryTheory.Functor.inducedFunctorLinear

end InducedCategory

instance fullSubcategoryInclusionLinear {C : Type*} [Category C] [Preadditive C]
    [CategoryTheory.Linear R C] (Z : C → Prop) : (fullSubcategoryInclusion Z).Linear R where
#align category_theory.functor.full_subcategory_inclusion_linear CategoryTheory.Functor.fullSubcategoryInclusionLinear

section

variable {R} {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] (F : C ⥤ D)
  [Additive F]

instance natLinear : F.Linear ℕ where
  map_smul := F.mapAddHom.map_nsmul
#align category_theory.functor.nat_linear CategoryTheory.Functor.natLinear

instance intLinear : F.Linear ℤ where
  map_smul f r := F.mapAddHom.map_zsmul f r
#align category_theory.functor.int_linear CategoryTheory.Functor.intLinear

variable [CategoryTheory.Linear ℚ C] [CategoryTheory.Linear ℚ D]

instance ratLinear : F.Linear ℚ where
  map_smul f r := F.mapAddHom.toRatLinearMap.map_smul r f
#align category_theory.functor.rat_linear CategoryTheory.Functor.ratLinear

end

end Functor

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Linear R C] [Preadditive D]
  [Linear R D]

instance inverseLinear (e : C ≌ D) [e.functor.Additive] [e.functor.Linear R] :
  e.inverse.Linear R where
    map_smul r f := by
      apply e.functor.map_injective
      simp
#align category_theory.equivalence.inverse_linear CategoryTheory.Equivalence.inverseLinear

end Equivalence

end Linear

end CategoryTheory
