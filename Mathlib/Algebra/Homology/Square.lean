/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

This file is the bundled counterpart of `Algebra.Homology.CommSq`.
The same results are obtained here for squares `sq : Square C` where
`C` is an additive category.

-/
namespace CategoryTheory

open Category Limits

namespace Square

variable {C : Type*} [Category C] [Preadditive C]
  (sq : Square C) [HasBinaryBiproduct sq.X₂ sq.X₃]

/-- The cokernel cofork attached to a commutative square in a preadditive category. -/
noncomputable abbrev cokernelCofork :
    CokernelCofork (biprod.lift sq.f₁₂ (-sq.f₁₃)) :=
  CokernelCofork.ofπ (biprod.desc sq.f₂₄ sq.f₃₄) (by simp [sq.fac])

/-- A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel. -/
noncomputable def isPushoutEquivIsColimitCokernelCofork :
    sq.IsPushout ≃ IsColimit sq.cokernelCofork :=
  Equiv.trans
    { toFun := fun h ↦ h.isColimit
      invFun := fun h ↦ IsPushout.mk _ h
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    sq.commSq.isColimitEquivIsColimitCokernelCofork

variable {sq} in
/-- The colimit cokernel cofork attached to a pushout square. -/
noncomputable def IsPushout.isColimitCokernelCofork (h : sq.IsPushout) :
    IsColimit sq.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

/-- The kernel fork attached to a commutative square in a preadditive category. -/
noncomputable abbrev kernelFork :
    KernelFork (biprod.desc sq.f₂₄ (-sq.f₃₄)) :=
  KernelFork.ofι (biprod.lift sq.f₁₂ sq.f₁₃) (by simp [sq.fac])

/-- A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel. -/
noncomputable def isPullbackEquivIsLimitKernelFork :
    sq.IsPullback ≃ IsLimit sq.kernelFork :=
  Equiv.trans
    { toFun := fun h ↦ h.isLimit
      invFun := fun h ↦ IsPullback.mk _ h
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    sq.commSq.isLimitEquivIsLimitKernelFork

variable {sq} in
/-- The limit kernel fork attached to a pullback square. -/
noncomputable def IsPullback.isLimitKernelFork (h : sq.IsPullback) :
    IsLimit sq.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

end Square

end CategoryTheory
