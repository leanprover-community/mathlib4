/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The algebra morphism from locally constant functions to continuous functions.

-/

@[expose] public section


namespace LocallyConstant

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive (attr := simps) /-- The inclusion of locally-constant functions into continuous
functions as an additive monoid hom. -/]
def toContinuousMapMonoidHom [Monoid Y] [ContinuousMul Y] : LocallyConstant X Y →* C(X, Y) where
  toFun := (↑)
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps]
def toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y] [Module R Y]
    [ContinuousAdd Y] [ContinuousConstSMul R Y] : LocallyConstant X Y →ₗ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapAddMonoidHom
  map_smul' x y := by
    ext
    simp

@[simp] lemma toAddMonoidHom_toContinuousMapLinearMap (R : Type*) [Semiring R] [AddCommMonoid Y]
    [Module R Y] [ContinuousAdd Y] [ContinuousConstSMul R Y] :
    (toContinuousMapLinearMap R (X := X) (Y := Y)).toAddMonoidHom = toContinuousMapAddMonoidHom :=
  rfl

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps]
def toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [IsTopologicalSemiring Y] : LocallyConstant X Y →ₐ[R] C(X, Y) where
  toFun := (↑)
  __ := toContinuousMapMonoidHom
  __ := toContinuousMapAddMonoidHom
  commutes' r := by
    ext x
    simp [Algebra.smul_def]

@[simp] lemma toLinearMap_toContinuousMapAlgHom (R : Type*) [CommSemiring R] [Semiring Y]
    [Algebra R Y] [IsTopologicalSemiring Y] :
    (toContinuousMapAlgHom R (X := X) (Y := Y)).toLinearMap = toContinuousMapLinearMap R := rfl

theorem separatesPoints_range_toContinuousMapAlgHom (R : Type*) [CommSemiring R]
    [TotallySeparatedSpace X] [Semiring Y] [Algebra R Y] [IsTopologicalSemiring Y] [Nontrivial Y] :
    (toContinuousMapAlgHom R : _ →ₐ[R] C(X, Y)).range.SeparatesPoints := fun _ _ hxy ↦
  have ⟨_, hU, _, _⟩ := exists_isClopen_of_totally_separated hxy
  ⟨charFn Y hU, by simp_all [charFn]⟩

end LocallyConstant
