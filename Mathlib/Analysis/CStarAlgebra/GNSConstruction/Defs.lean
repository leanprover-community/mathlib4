/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.PositiveLinearFunctional
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Definitions of structures for the GNS (Gelfand-Naimark-Segal) construction

In this file we do the "construction" part of the GNS construction. We define a Hilbert space
as the completion of a quotient of A after we mod out by an appropriately constructed subspace.
The inner product is induced by a fixed positive linear functional `f`.

Most of the structures, theorems, and definitions in this file should not be referenced directly,
but they are described below for the sake of clarity and completeness.

## Main results

- `f.GNS` : a type synonym of `A` that "forgets" the norm of `A` and bundles in a fixed
  linear functional `f` so that we can construct an inner product and inner product-induced norm.
- `f.GNS_HilbertSpace` : the Hilbert space that we construct as the completion of `f.GNS_Quotient`.

## References

Most of this work follows from private course notes prepared by Professor Konrad Aguilar at Pomona
College.

For another, similar approach, see "A Primer on Spectral Theory" by Bernard Aupetit, the other main
refence used here.
-/

@[expose] public section
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. This erases the norm
on `A`, while remainaing structurally equivalent via the `LinearEquivalence`, `toGNS`.
-/
def GNS (_f : A →ₚ[ℂ] ℂ) := A
instance : AddCommGroup (f.GNS) := inferInstanceAs (AddCommGroup A)
instance : Module ℂ (f.GNS) := inferInstanceAs (Module ℂ A)
instance : Ring (f.GNS) := inferInstanceAs (Ring A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toGNS : A ≃ₗ[ℂ] (f.GNS) := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofGNS : (f.GNS) ≃ₗ[ℂ] A := (f.toGNS).symm

instance preInnerProdSpace : PreInnerProductSpace.Core ℂ f.GNS where
  inner a b := f (star (f.ofGNS a) * (f.ofGNS b))
  conj_inner_symm a b := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg a := (RCLike.re_nonneg_of_nonneg (x := f (star (f.ofGNS a) * (f.ofGNS a)))
      (LE.le.isSelfAdjoint (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (f.ofGNS a))))).mpr
        (PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (f.ofGNS a)))
  add_left a b c := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp

noncomputable instance : SeminormedAddCommGroup f.GNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preInnerProdSpace)
noncomputable instance : NormedSpace ℂ f.GNS :=
  InnerProductSpace.Core.toNormedSpace (c := f.preInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.GNS :=
  InnerProductSpace.ofCore f.preInnerProdSpace

abbrev GNS_Quotient := SeparationQuotient f.GNS

noncomputable instance GNS_Quot_InnerProdSpace : InnerProductSpace ℂ f.GNS_Quotient := by
  infer_instance

/--
`f.GNS_Quotient` is an inner product space.
-/
noncomputable instance GNS_Quot_InnerProdSpaceCore : InnerProductSpace.Core ℂ (f.GNS_Quotient)
 := InnerProductSpace.toCore

/--
The Hilbert space constructed from `f` is `GNS_HilbertSpace`. It is the closure under the inner
product-induced norm of `f.GNS_Quotient`.
-/
abbrev GNS_HilbertSpace := UniformSpace.Completion (f.GNS_Quotient)

instance : HilbertSpace ℂ (f.GNS_HilbertSpace) where

@[simp]
theorem GNS_Quotient_inner_apply (a : (f.GNS)) (b : (f.GNS)) :
  f.GNS_Quot_InnerProdSpaceCore.inner (SeparationQuotient.mk a) (SeparationQuotient.mk b)
    = f (star a * b) := by rfl

end PositiveLinearMap
