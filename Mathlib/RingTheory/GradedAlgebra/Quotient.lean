/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.Module.GradedModule.QuotientGrading
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Quotient of a Graded Ring by a Homogeneous Ideal

-/

open SetLike DirectSum

variable {ι σ A : Type*}

variable [CommRing A]
variable [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ)
variable [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
variable (I : HomogeneousIdeal 𝒜)

namespace HomogeneousIdeal

def quotientGrading (i : ι) := HomogeneousSubmodule.quotientGrading I i

instance : Decomposition I.quotientGrading := HomogeneousSubmodule.quotientDecomposition I

instance : GradedMonoid I.quotientGrading where
  one_mem := ⟨Quotient.mk'' ⟨1, GradedOne.one_mem⟩, rfl⟩
  mul_mem i j x y hx hy := by
    induction x using Quotient.inductionOn' with | h x' => ?_
    induction y using Quotient.inductionOn' with | h y' => ?_
    rcases hx with ⟨x, hx'⟩
    rcases hy with ⟨y, hy'⟩
    rw [← hx', ← hy']
    clear x' y' hx' hy'
    induction x using Quotient.inductionOn' with | h x => ?_
    induction y using Quotient.inductionOn' with | h y => ?_
    exact ⟨Quotient.mk'' ⟨x.1 * y.1, GradedMul.mul_mem x.2 y.2⟩, rfl⟩

instance : GradedRing I.quotientGrading where

end HomogeneousIdeal
