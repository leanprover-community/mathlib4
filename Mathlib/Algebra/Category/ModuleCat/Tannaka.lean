/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Tannaka duality for rings

A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.

-/

universe u

open CategoryTheory

attribute [local simp] add_smul mul_smul in
attribute [local ext] End.ext in
/-- An ingredient of Tannaka duality for rings:
A ring `R` is equivalent to
the endomorphisms of the additive forgetful functor `Module R ⥤ AddCommGroup`.
-/
def ringEquivEndForget₂ (R : Type u) [Ring R] :
    R ≃+* End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) where
  toFun r :=
    ObjectProperty.homMk
      { app M := @AddCommGrpCat.ofHom M.carrier M.carrier _ _
          (DistribMulAction.toAddMonoidHom M r) }
  invFun φ := φ.hom.app (ModuleCat.of R R) (1 : R)
  left_inv _ := by simp
  right_inv φ := by
    ext M (x : M)
    have w := CategoryTheory.congr_fun
      (φ.hom.naturality (ModuleCat.ofHom (LinearMap.toSpanSingleton R M x))) (1 : R)
    exact w.symm.trans (congr_arg (φ.hom.app M) (one_smul R x))
  map_add' := by cat_disch
  map_mul' := by cat_disch
