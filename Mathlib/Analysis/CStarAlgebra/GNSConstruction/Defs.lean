/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.PositiveLinearFunctional
public import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Definitions of structures for the GNS construction

In this file we do the "construction" part of the GNS construction. We define a Hilbert space
as the completion of a quotient of A after we mod out by an appropriately constructed subspace.
The inner product is induced by a fixed positive linear functional `f`.

Most of the structures, theorems, and definitions in this file should not be referenced directly,
but they are described below for the sake of clarity and completeness.

## Main results

- `f.GNS` : a type synonym of `A` that "forgets" the norm of `A` and bundles in a fixed
  linear functional `f` so that we can construct an inner product and inner product-induced norm.
- `f.GNS_Submodule`: the subspace of `A` defined as all elements `a : A` for which
  `f (star a * a) = 0`.
- `f.GNS_Quotient` : the quotient space of `(f.GNS) ⧸ (f.GNS_Submodule)`. We complete this space
  with respect to its inner product-induced norm to produce `f.GNS_HilbertSpace`.
- `f.GNS_Quotient_inner` : the inner product on `f.GNS_Quotient`.
- `f.GNS_HilbertSpace` : the Hilbert space that we construct as the completion of `f.GNS_Quotient`.

## References

Most of this work follows from private course notes prepared by Professor Konrad Aguilar at Pomona
College.

For another, similar approach, see "A Primer on Spectral Theory" by Bernard Aupetit, the other main
refence used here.
-/

@[expose] public section
open scoped ComplexOrder
--open PositiveLinearFunctional

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable (f : A →ₚ[ℂ] ℂ)
namespace PositiveLinearMap
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. -/
def GNS (_f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup (f.GNS) := inferInstanceAs (AddCommGroup A)
instance : Module ℂ (f.GNS) := inferInstanceAs (Module ℂ A)
instance : NonUnitalRing (f.GNS) := inferInstanceAs (NonUnitalRing A)
instance : PartialOrder (f.GNS) := inferInstanceAs (PartialOrder A)
instance : Ring (f.GNS) := inferInstanceAs (Ring A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toGNS : A ≃ₗ[ℂ] (f.GNS) := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofGNS : (f.GNS) ≃ₗ[ℂ] A := (f.toGNS).symm

variable [StarOrderedRing A]
instance : StarOrderedRing (f.GNS) := inferInstanceAs (StarOrderedRing A)

instance GNS_Submodule (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (f.GNS) where
  carrier := {a : (f.GNS) | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    simp [left_distrib, right_distrib, ha, hb, maps_zero_prod_to_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq] at hx
    simp [hx]

noncomputable def GNS_inner :
  (f.GNS) →ₗ⋆[ℂ] (f.GNS) →ₗ[ℂ] ℂ :=  (LinearMap.mul ℂ (f.GNS)).comp
    (starLinearEquiv ℂ (A := (f.GNS)) : (f.GNS) →ₗ⋆[ℂ] (f.GNS))|>.compr₂ₛₗ (f.toLinearMap)

omit [StarOrderedRing A] in
@[simp]
theorem GNS_inner_apply (x y : (f.GNS)) :
  f.GNS_inner x y = f (star x * y) := rfl

/--
If `GNS_Quotient` is the quotient space that we will complete to produce a Hilbert space.
-/
def GNS_Quotient := (f.GNS) ⧸ (f.GNS_Submodule)

instance : AddCommGroup (f.GNS_Quotient) := by unfold GNS_Quotient; infer_instance
instance : Module ℂ (f.GNS_Quotient) := by unfold GNS_Quotient; infer_instance

/--
This theorem allows us to extend `GNS_inner` from `f.GNS →ₗ⋆[ℂ] f.GNS →ₗ[ℂ] ℂ` to
`A →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ`
-/
theorem GNS_inner_well_defined (a : (f.GNS)) :
    f.GNS_Submodule ≤ LinearMap.ker ((f.GNS_inner a)) := by
  intro b bh
  have hab := f.induced_inner_norm_sq_self_le a b
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

/--
This defines and extension of `GNS_inner` from `f.GNS →ₗ⋆[ℂ] f.GNS →ₗ[ℂ] ℂ`
to `A →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ`.
-/
noncomputable def GNS_Quotient_inner_right :
  A →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ where
  toFun p := Submodule.liftQ (f.GNS_Submodule) (f.GNS_inner p) (f.GNS_inner_well_defined p)
  map_add' _ _ := by simp only [GNS_Quotient, map_add]; ext; simp
  map_smul' _ _ := by simp only [GNS_Quotient, LinearMap.map_smulₛₗ]; ext; simp

/--
This allows us to lift `f.GNS_Quotient_inner_right` from `A →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ` to
`f.GNS_Quotient →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ`.
-/
theorem GNS_Quotient_inner_right_well_defined :
    f.GNS_Submodule ≤ LinearMap.ker (f.GNS_Quotient_inner_right) := by
  intro a ah
  change Submodule.liftQ (f.GNS_Submodule) (f.GNS_inner a) (f.GNS_inner_well_defined a) = 0
  ext b
  have hab := f.induced_inner_norm_sq_self_le a b
  rw [ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

/--
We deinfe `GNS_Quotient_inner` as the lifting of `f.GNS_Quotient_inner_right` from
`A →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ` to `f.GNS_Quotient →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ`.
-/
noncomputable def GNS_Quotient_inner : f.GNS_Quotient →ₗ⋆[ℂ] f.GNS_Quotient →ₗ[ℂ] ℂ :=
  Submodule.liftQ (f.GNS_Submodule) (f.GNS_Quotient_inner_right)
    (f.GNS_Quotient_inner_right_well_defined)

/--
When elments of `f.GNS_Quotient` are constructed from elements of `A`, `GNS_Quotient_inner`
simplifies to `GNS_inner`.
-/
@[simp]
theorem GNS_Quotient_inner_def (a b : (f.GNS)) :
  ((f.GNS_Quotient_inner) (Submodule.Quotient.mk a)) (Submodule.Quotient.mk b) =
    f.GNS_inner a b := by rfl

/--
`f.GNS_Quotient` is an inner product space with `f.GNS_Quotient_inner` as its inner product.
-/
noncomputable instance GNS_Quotient_InnerProductSpace :
    InnerProductSpace.Core ℂ (f.GNS_Quotient) where
  inner a b := f.GNS_Quotient_inner a b
  conj_inner_symm a b := by
    induction a using Submodule.Quotient.induction_on with | _ a
    induction b using Submodule.Quotient.induction_on with | _ b
    simp only [GNS_inner_apply, f.GNS_Quotient_inner_def a b]
    change star (f (star b * a)) = f (star a * b)
    rw [← map_star]
    simp
  re_inner_nonneg a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    have zeroleq : 0 ≤ f (star a * a) := f.map_nonneg (star_mul_self_nonneg a)
    have := f.re_of_self_star_self (star a)
    rw [star_star] at this
    rw [← this] at zeroleq
    simp [Complex.zero_le_real.mp zeroleq]
  add_left a b c := by simp
  smul_left a b c := by simp
  definite a := by
    induction a using Submodule.Quotient.induction_on
    exact (Submodule.Quotient.mk_eq_zero (f.GNS_Submodule)).mpr

noncomputable instance : NormedAddCommGroup (f.GNS_Quotient) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := f.GNS_Quotient_InnerProductSpace)
noncomputable instance : InnerProductSpace ℂ (f.GNS_Quotient) :=
  InnerProductSpace.ofCore (f.GNS_Quotient_InnerProductSpace).toCore
noncomputable instance : NormedSpace ℂ (f.GNS_Quotient) := by infer_instance

/--
The Hilbert space constructed from `f` is `GNS_HilbertSpace`. It is the closure under the inner
product-induced norm of `f.GNS_Quotient`.
-/
def GNS_HilbertSpace := UniformSpace.Completion (f.GNS_Quotient)

noncomputable instance : UniformSpace (f.GNS_HilbertSpace) := by
  unfold GNS_HilbertSpace; infer_instance
instance : CompleteSpace (f.GNS_HilbertSpace) := by
  unfold GNS_HilbertSpace; infer_instance
noncomputable instance : NormedAddCommGroup (f.GNS_HilbertSpace) := by
  unfold GNS_HilbertSpace; infer_instance
noncomputable instance : InnerProductSpace ℂ (f.GNS_HilbertSpace) := by
  unfold GNS_HilbertSpace; infer_instance
instance : HilbertSpace ℂ (f.GNS_HilbertSpace) where

@[simp]
theorem GNS_Quotient_inner_apply (a : (f.GNS)) (b : (f.GNS)) :
  f.GNS_Quotient_InnerProductSpace.inner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    = f (star a * b) := by rfl

end PositiveLinearMap
