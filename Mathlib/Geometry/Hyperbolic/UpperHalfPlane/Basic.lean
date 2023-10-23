/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Upper Half Plane
-/

noncomputable section

open scoped UpperHalfPlane ComplexConjugate NNReal Topology MatrixGroups

open Set Metric Filter Real Matrix SpecialLinearGroup

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R

namespace UpperHalfPlane

namespace PSL2R

instance PSLsmul : SMul PSL(2, ℝ) ℍ where
  smul g := Quotient.liftOn' g (· • ·) fun A B hAB => by
    rw [@QuotientGroup.leftRel_apply, SpecialLinearGroup.coset_center_iff_2] at hAB
    · cases hAB with
      | inl hAB =>
        rw [hAB]
      | inr hAB =>
        rw [hAB]
        ext1 z
        simp only
        show (A : GL(2, ℝ)⁺) • z = (-A : GL(2, ℝ)⁺) • z
        simp
    · trivial

instance PSLaction : MulAction PSL(2, ℝ) ℍ :=
  Function.Surjective.mulActionLeft
      (QuotientGroup.mk' <| Subgroup.center SL(2, ℝ))
      (QuotientGroup.mk'_surjective <| Subgroup.center SL(2, ℝ)) fun _ _ => rfl

instance PSLisometric : IsometricSMul PSL(2, ℝ) ℍ where
  isometry_smul g := Quotient.inductionOn' g fun A => by
    refine Eq.subst ?_ <| isometry_smul ℍ A
    aesop

end PSL2R
