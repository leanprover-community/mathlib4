/-
Copyright (c) 2025 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/

module
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.CStarAlgebra.GNSConstruction.PositiveLinearFunctional

/-!
# Definitions of structures for the GNS construction

In this file we do the "construction" part of the GNS construction. We define a Hilbert space
as the completion of a quotient of A after we mod out by an appropriately constructed subspace.
The inner product is induced by a fixed positive linear functional `f`.

Most of the structures, theorems, and definitions in this file should not be referenced directly,
but they are described below for the sake of clarity and completeness.

## Main results

- `WithFunctional`: a type synonym of `A` that "forgets" the norm of `A` and bundles in a fixed
  linear functional `f` so that we can construct an inner product and inner product-induced norm.
  `WithFunctional A f` is isomorphic to `A` and so they are sometimes used interchangeably where
  Lean can correctly distinguish which one to use.
- `N`: the subspace of `A` defined as all elements for which `f (star a * a) = 0`.
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (f : A →ₚ[ℂ] ℂ)

def WithFunctional (_A : Type*) [CStarAlgebra _A] [PartialOrder _A] (_f : _A →ₚ[ℂ] ℂ) := _A

namespace GNS

/-- The canonical inclusion of `A` into `WithFunctional A f`. -/
def toFunctional : A → WithFunctional A f := id

/-- The canonical inclusion of `WithFunctional A f` into `A`. -/
def ofFunctional : WithFunctional A f → A := id

instance [AddCommGroup A] : AddCommGroup (WithFunctional A f) := ‹AddCommGroup A›
instance [Semiring A] : Semiring (WithFunctional A f) := ‹Semiring A›
instance [NonUnitalNonAssocSemiring A] :
  NonUnitalNonAssocSemiring (WithFunctional A f) := ‹NonUnitalNonAssocSemiring A›
instance [Semiring ℂ] [AddCommGroup A] [Module ℂ A] :
  Module ℂ (WithFunctional A f) := ‹Module ℂ (WithFunctional A f)›
instance : NonUnitalSeminormedRing (WithFunctional A f) := by unfold WithFunctional; infer_instance
instance : CStarAlgebra (WithFunctional A f) := by unfold WithFunctional; infer_instance

instance OfFunctionalLinear : LinearMap (RingHom.id ℂ) (WithFunctional A f) A where
  toFun := ofFunctional f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `WithFunctional.toFunctional` and `WithFunctional.toFunctional` as an equivalence. -/
--@[simps]
protected def equiv : WithFunctional A f ≃ A where
  toFun := ofFunctional f
  invFun := toFunctional f
  left_inv _ := rfl
  right_inv _ := rfl

instance N (f : A →ₚ[ℂ] ℂ) : Submodule ℂ (WithFunctional A f) where
  carrier := {a : (WithFunctional A f) | f (star a * a) = 0}
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    simp [left_distrib, right_distrib, ha, hb, f_maps_zero_prod_to_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    rw [Set.mem_setOf_eq] at hx
    simp [hx]

noncomputable def sq : -- Code from Eric Wieser
  (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f) →ₗ[ℂ] ℂ :=
  (LinearMap.mul ℂ (WithFunctional A f)).comp
  (starLinearEquiv ℂ (A := (WithFunctional A f)) :
    (WithFunctional A f) →ₗ⋆[ℂ] (WithFunctional A f))
    |>.compr₂ₛₗ (f.comp (OfFunctionalLinear f))

omit [StarOrderedRing A] in
@[simp]
theorem sq_apply (x y : (WithFunctional A f)) : -- Code from Eric Wieser
  sq f x y = f (star x * y) := rfl

/--
If `A_mod_N` is the quotient space that we will complete to produce a Hilbert space.
-/
def A_mod_N := (WithFunctional A f) ⧸ (N f)

instance : AddCommGroup (A_mod_N f) := by unfold A_mod_N; infer_instance
instance : Module ℂ (A_mod_N f) := by unfold A_mod_N; infer_instance

/--
This theorem allows us to extend `sq` from `A → A → ℂ` to `A → N f → ℂ`
-/
theorem sq_well_defined (a : WithFunctional A f) : N f ≤ LinearMap.ker ((sq f a)) := by
  intro b bh
  have hab := f_inner_norm_sq_self_le f a b
  rw [bh, mul_zero] at hab
  norm_cast at hab
  rwa [sq_nonpos_iff, norm_eq_zero] at hab

/--
This defines and extension of `sq` from `A → A → ℂ` to `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ`.
-/
noncomputable instance half_sq :
  A →ₗ⋆[ℂ] WithFunctional A f ⧸ N f →ₗ[ℂ] ℂ where
  toFun p := Submodule.liftQ (N f) (sq f p) (sq_well_defined f p)
  map_add' a b := by simp only [map_add]; ext x; simp
  map_smul' a b := by ext x; simp

/--
This allows us to extend `half_sq` from `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ` to
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
We deinfe `inner_f` as the extension of `half_sq` from `A →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ` to
`A / N f →ₗ⋆[ℂ] A ⧸ N f →ₗ[ℂ] ℂ`.
-/
noncomputable def inner_f := Submodule.liftQ (N f) (half_sq f) (half_sq_well_defined f)

/--
When elments of `A / N f` are constructed from elements of `A`, `inner_f` simplifies to `sq`.
-/
@[simp]
theorem inner_f_def (a b : WithFunctional A f) :
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
    have zeroleq : 0 ≤ f (star a * a) :=
      PositiveLinearMap.map_nonneg f (star_mul_self_nonneg (ofFunctional f a))
    have := f_of_a_star_a_is_real f (star a)
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


def aToMyQuot (a : A) : A_mod_N f := Submodule.Quotient.mk a
def myQuotToH (a : A_mod_N f) : H f := UniformSpace.Completion.coe' a
def aToH (a : A) : H f := myQuotToH f (aToMyQuot f a)

@[simp]
theorem inner_f_apply_on_quot_mk (a : WithFunctional A f) (b : WithFunctional A f) :
  (A_mod_N_innerProd_space f).inner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
    = f (star a * b) := by rfl

end GNS
