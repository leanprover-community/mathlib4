/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Linear Functors

For a functor between two `R`-linear categories, `Functor.Linear` records
that the induced maps on hom types preserve the `R`-action.
If the functor is also additive, then these maps are `R`-linear.

## Implementation details

`Functor.Linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` preserves scalar multiplication.
For an additive functor, this is enough to package `F.map` as an `R`-linear map.

-/

@[expose] public section


namespace CategoryTheory

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

/-- A functor `F` is `R`-linear if `F.map` preserves scalar multiplication on morphisms. -/
class Functor.Linear : Prop where
  /-- the functor preserves scalar multiplication on morphisms -/
  map_smul : ∀ {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by cat_disch

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

section

variable {E : Type*} [Category* E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)

instance [Linear R G] : Linear R (F ⋙ G) where

set_option backward.isDefEq.respectTransparency false in
lemma linear_of_full_essSurj_comp [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)] :
    Functor.Linear R G := by
  refine ⟨fun {X Y} f r ↦ ?_⟩
  obtain ⟨X', Y', eX, eY, f', rfl⟩ :
      ∃ (X' Y' : C) (eX : F.obj X' ≅ X) (eY : F.obj Y' ≅ Y)
        (f' : X' ⟶ Y'), f = eX.inv ≫ F.map f' ≫ eY.hom := by
    obtain ⟨f', hf'⟩ :=
      F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
    exact ⟨_, _, F.objObjPreimageIso X, F.objObjPreimageIso Y, f', by cat_disch⟩
  simpa only [comp_map, map_smul, Linear.smul_comp, Linear.comp_smul, ← G.map_comp]
    using G.map eX.inv ≫= ((F ⋙ G).map_smul r f') =≫ G.map eY.hom

lemma linear_comp_iff_of_full_of_essSurj [F.Full] [F.EssSurj] :
    Functor.Linear R (F ⋙ G) ↔ Functor.Linear R G :=
  ⟨fun _ ↦ linear_of_full_essSurj_comp F G, fun _ ↦ inferInstance⟩

end

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

instance fullSubcategoryInclusionLinear {C : Type*} [Category* C] [Preadditive C]
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
