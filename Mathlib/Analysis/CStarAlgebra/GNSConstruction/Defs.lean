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

- `GNS f` or `f.GNS`: a type synonym of `A` that "forgets" the norm of `A` and bundles in a fixed
  linear functional `f` so that we can construct an inner product and inner product-induced norm.
- `N`: the subspace of `A` defined as all elements `a : A` for which `f (star a * a) = 0`.
- `sq` : a semi-inner product that we will use to define a proper inner product on `A / N f`.
- `A_mod_N` : the quotient space that we will complete to produce a Hilbert space.
- `H` : the Hilbert space that we construct, parameterized by positive linear functional, `f`.

## References

Most of this work follows from private course notes prepared by Professor Konrad Aguilar at Pomona
College.

For another, similar approach, see "A Primer on Spectral Theory" by Bernard Aupetit, the other main
refence used here.
-/

@[expose] public section
open scoped ComplexOrder
open PositiveLinearFunctional

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]
variable (f : A →ₚ[ℂ] ℂ)
namespace PositiveLinearMap
/-- The GNS space on a non-unital C⋆-algebra with a positive linear functional. -/
def GNS (_f : A →ₚ[ℂ] ℂ) := A

instance : AddCommGroup (GNS f) := inferInstanceAs (AddCommGroup A)
instance : Module ℂ (GNS f) := inferInstanceAs (Module ℂ A)
instance : NonUnitalRing (GNS f) := inferInstanceAs (NonUnitalRing A)
instance : PartialOrder (GNS f) := inferInstanceAs (PartialOrder A)
instance : Ring (GNS f) := inferInstanceAs (Ring A)

/-- The map from the C⋆-algebra to the GNS space, as a linear equivalence. -/
def toGNS : A ≃ₗ[ℂ] (GNS f) := LinearEquiv.refl ℂ _

/-- The map from the GNS space to the C⋆-algebra, as a linear equivalence. -/
def ofGNS : (GNS f) ≃ₗ[ℂ] A := (toGNS f).symm

@[simp] lemma toGNS_apply (a : A) : toGNS f a = (a : (GNS f)) := rfl
@[simp] lemma ofGNS_apply (a : (GNS f)) : ofGNS f a = (a : A) := rfl

variable [StarOrderedRing A]
instance : StarOrderedRing (GNS f) := inferInstanceAs (StarOrderedRing A)

/-- Only an implementation for the instances below. -/
noncomputable def preInnerProductSpace :
    PreInnerProductSpace.Core ℂ (GNS f) where
  inner x y := f (star (ofGNS f x) * ofGNS f y)
  conj_inner_symm x y := star_star (ofGNS f y) ▸
    star_mul (star _) (ofGNS f x) ▸ map_star f _ |>.symm
  re_inner_nonneg _ := RCLike.nonneg_iff.mp (map_nonneg f (star_mul_self_nonneg _)) |>.1
  add_left _ _ _ := by simp [add_mul]
  smul_left _ _ _ := by simp

noncomputable instance : SeminormedAddCommGroup (GNS f) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInnerProductSpace f)
noncomputable instance : InnerProductSpace ℂ (GNS f) := InnerProductSpace.ofCore _
noncomputable instance : NormedSpace ℂ (GNS f) :=
  InnerProductSpace.Core.toNormedSpace (c := preInnerProductSpace f)

lemma GNS_inner_def (a b : (GNS f)) :
    inner ℂ a b = f (star (ofGNS f a) * ofGNS f b) := rfl

lemma GNS_norm_def (a : (GNS f)) :
    ‖a‖ = (f (star (ofGNS f a) * ofGNS f a)).re.sqrt := rfl

instance N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (GNS f) where
  carrier := {a : (GNS f) | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    simp [left_distrib, right_distrib, ha, hb, f_maps_zero_prod_to_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq] at hx
    simp [hx]

noncomputable def sq : -- Code from Eric Wieser
  (GNS f) →ₗ⋆[ℂ] (GNS f) →ₗ[ℂ] ℂ :=  (LinearMap.mul ℂ (GNS f)).comp
    (starLinearEquiv ℂ (A := (GNS f)) : (GNS f) →ₗ⋆[ℂ] (GNS f))|>.compr₂ₛₗ (toLinearMap f)

omit [StarOrderedRing A] in
@[simp]
theorem sq_apply (x y : (GNS f)) : -- Code from Eric Wieser
  sq f x y = f (star x * y) := rfl

/--
If `A_mod_N` is the quotient space that we will complete to produce a Hilbert space.
-/
def A_mod_N := (GNS f) ⧸ (N f)

instance : AddCommGroup (A_mod_N f) := by unfold A_mod_N; infer_instance
instance : Module ℂ (A_mod_N f) := by unfold A_mod_N; infer_instance

/--
This theorem allows us to extend `sq` from `A → A → ℂ` to `A → N f → ℂ`
-/
theorem sq_well_defined (a : (GNS f)) : N f ≤ LinearMap.ker ((sq f a)) := by
  intro b bh
  have hab := f_inner_norm_sq_self_le f a b
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

/--
This defines and extension of `sq` from `A → A → ℂ` to `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ`.
-/
noncomputable def half_sq :
  A →ₗ⋆[ℂ] (GNS f) ⧸ N f →ₗ[ℂ] ℂ where
  toFun p := Submodule.liftQ (N f) (sq f p) (sq_well_defined f p)
  map_add' a b := by simp only [map_add]; ext x; simp
  map_smul' a b := by ext x; simp

/--
This allows us to lift `half_sq` from `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ` to
`A / N f →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ`.
-/
theorem half_sq_well_defined : N f ≤ LinearMap.ker (half_sq f) := by
  intro a ah
  change Submodule.liftQ (N f) (sq f a) (sq_well_defined f a) = 0
  ext b
  have hab := f_inner_norm_sq_self_le f a b
  rw [ah, zero_mul] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

/--
We deinfe `inner_f` as the lifting of `half_sq` from `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ` to
`A / N f →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ`.
-/
noncomputable def inner_f := Submodule.liftQ (N f) (half_sq f) (half_sq_well_defined f)

/--
When elments of `A / N f` are constructed from elements of `A`, `inner_f` simplifies to `sq`.
-/
@[simp]
theorem inner_f_def (a b : (GNS f)) :
  ((inner_f f) (Submodule.Quotient.mk a)) (Submodule.Quotient.mk b) = sq f a b := by rfl

/--
`A / N f` is an inner product space with `inner_f` as its inner product.
-/
noncomputable instance A_mod_N_innerProd_space : InnerProductSpace.Core ℂ (A_mod_N f) where
  inner a b := inner_f f a b
  conj_inner_symm a b := by
    induction a using Submodule.Quotient.induction_on with | _ a
    induction b using Submodule.Quotient.induction_on with | _ b
    simp only [sq_apply, inner_f_def f a b]
    change star (f (star b * a)) = f (star a * b)
    rw [← map_star]
    simp
  re_inner_nonneg a := by
    induction a using Submodule.Quotient.induction_on with | _ a
    have zeroleq : 0 ≤ f (star a * a) := PositiveLinearMap.map_nonneg f (star_mul_self_nonneg a)
    have := re_of_self_star_self f (star a)
    rw [star_star] at this
    rw [← this] at zeroleq
    simp [Complex.zero_le_real.mp zeroleq]
  add_left a b c := by simp
  smul_left a b c := by simp
  definite a := by
    induction a using Submodule.Quotient.induction_on
    exact (Submodule.Quotient.mk_eq_zero (N f)).mpr

noncomputable instance : NormedAddCommGroup (A_mod_N f) :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := A_mod_N_innerProd_space f)
noncomputable instance : InnerProductSpace ℂ (A_mod_N f) :=
  InnerProductSpace.ofCore (A_mod_N_innerProd_space f).toCore
noncomputable instance : NormedSpace ℂ (A_mod_N f) := by infer_instance

/--
The Hilbert space constructed from `f` is `H`. It is the closure under the inner product-induced
norm of `A / N f`.
-/
def H := UniformSpace.Completion (A_mod_N f)

noncomputable instance : UniformSpace (H f) := by unfold H; infer_instance
instance : CompleteSpace (H f) := by unfold H; infer_instance
noncomputable instance : NormedAddCommGroup (H f) := by unfold H; infer_instance
noncomputable instance : InnerProductSpace ℂ (H f) := by unfold H; infer_instance
instance : HilbertSpace ℂ (H f) where

@[simp]
theorem inner_f_apply_on_quot_mk (a : (GNS f)) (b : (GNS f)) :
  (A_mod_N_innerProd_space f).inner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    = f (star a * b) := by rfl

end PositiveLinearMap
