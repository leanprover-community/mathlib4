/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
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
open Complex
open scoped ComplexOrder

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] (f : A →ₚ[ℂ] ℂ)

namespace PositiveLinearMap

set_option linter.unusedVariables false in
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. This erases the norm
on `A`, while remainaing structurally equivalent via the `LinearEquivalence`, `toGNS`.
-/
@[nolint unusedArguments]
def GNS (f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup f.GNS := inferInstanceAs (AddCommGroup A)
instance : Module ℂ f.GNS := inferInstanceAs (Module ℂ A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toGNS : A ≃ₗ[ℂ] f.GNS := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofGNS : f.GNS ≃ₗ[ℂ] A := (f.toGNS).symm

@[simp]
lemma toGNS_ofGNS (a : f.GNS) : f.toGNS (f.ofGNS a) = a := rfl

@[simp]
lemma ofGNS_toGNS (a : A) : f.ofGNS (f.toGNS a) = a := rfl

@[simp]
lemma symm_ofGNS : (f.ofGNS).symm = f.toGNS := rfl

@[simp]
lemma symm_toGNS : (f.toGNS).symm = f.ofGNS := rfl

variable [StarOrderedRing A]

def preInnerProdSpace : PreInnerProductSpace.Core ℂ f.GNS where
  inner a b := f (star (f.ofGNS a) * f.ofGNS b)
  conj_inner_symm := by simp [← Complex.star_def, ← map_star f]
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (f.map_nonneg (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by rw [map_add, star_add, add_mul, map_add]
  smul_left := by simp [smul_mul_assoc]

noncomputable instance : SeminormedAddCommGroup f.GNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := f.preInnerProdSpace)
noncomputable instance : InnerProductSpace ℂ f.GNS :=
  InnerProductSpace.ofCore f.preInnerProdSpace

lemma GNS_inner_def (a b : f.GNS) :
    inner ℂ a b = f (star (f.ofGNS a) * f.ofGNS b) := rfl

lemma GNS_norm_def (a : f.GNS) :
    ‖a‖ = (f (star (f.ofGNS a) * f.ofGNS a)).re.sqrt := rfl

lemma GNS_norm_sq (a : f.GNS) :
    ‖a‖ ^ 2 = (f (star (f.ofGNS a) * f.ofGNS a)) := by
  have : 0 ≤ f (star (f.ofGNS a) * f.ofGNS a) := map_nonneg f <| star_mul_self_nonneg _
  rw [GNS_norm_def, ← ofReal_pow, Real.sq_sqrt]
  · rw [conj_eq_iff_re.mp this.star_eq]
  · rwa [re_nonneg_iff_nonneg this.isSelfAdjoint]

/--
The Hilbert space constructed from a positive linear functional on a C⋆-algebra.
-/
abbrev GNS_HilbertSpace := UniformSpace.Completion f.GNS

end PositiveLinearMap
