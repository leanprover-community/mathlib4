/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# `TensorAlgebra` as a functor `ModuleCat R ⥤ AlgCat R`

In this file we define the functor `AlgCat.tensorAlgebra : ModuleCat R ⥤ AlgCat R`
sending an `R`-module `M` to the tensor algebra `TensorAlgebra R M`. We
show that this functor is a left-adjoint to the forgetful functor `AlgCat R ⥤ ModuleCat R`.
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace AlgCat

/-- The functor sending an `R`-module `M` to its tensor algebra over `R`. -/
@[simps]
def tensorAlgebra (R : Type u) [CommRing R] : ModuleCat.{w} R ⥤ AlgCat.{max u w} R where
  obj M := AlgCat.of R (TensorAlgebra R M)
  map f := AlgCat.ofHom (TensorAlgebra.lift _ (TensorAlgebra.ι _ ∘ₗ f.hom))

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Taking the tensor algebra forms a left adjoint of the forgetful functor from `AlgCat R` to
`ModuleCat R`. -/
@[simps]
def tensorAlgebraAdj : tensorAlgebra.{u} R ⊣ forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) where
  unit.app M := ModuleCat.ofHom (TensorAlgebra.ι _)
  counit.app A := AlgCat.ofHom (TensorAlgebra.lift R .id)
  counit.naturality _ _ _ := by
    ext : 1
    apply TensorAlgebra.hom_ext
    ext
    simp
  left_triangle_components _ := by
    ext : 1
    dsimp
    ext
    simp

set_option backward.isDefEq.respectTransparency false in
instance (R : Type v) [CommRing R] [Small.{u} R] :
    (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)).IsRightAdjoint := by
  let e : AlgCat.{u} R ≌ AlgCat.{u} (Shrink.{u} R) :=
    restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv R)
  have : e.inverse ⋙ forget₂ (AlgCat R) (ModuleCat R) = forget₂ _ _ ⋙
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv R)).inverse :=
    rfl
  rw [← Functor.isRightAdjoint_comp_iff_right e.inverse, this]
  have := (tensorAlgebraAdj (Shrink.{u} R)).isRightAdjoint
  infer_instance

instance : (forget₂ RingCat.{u} AddCommGrpCat.{u}).IsRightAdjoint := by
  rw [← Functor.isRightAdjoint_comp_iff_right (forget₂ (AlgCat.{u} ℤ) RingCat.{u})]
  have heq : forget₂ (AlgCat.{u} ℤ) _ ⋙ forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} =
      forget₂ (AlgCat.{u} ℤ) RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} :=
    rfl
  rw [← heq]
  infer_instance

end AlgCat
