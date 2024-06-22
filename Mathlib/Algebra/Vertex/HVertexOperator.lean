/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of `meromorphic left-moving 2D field`.  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.
## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
## Main results
* Ext
## To do:
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product
  (needs PR#10781).
* `HahnSeries Γ R`-module structure on `HVertexOperator Γ R V W` (needs PR#10846).  This means we
  can consider products of the form `(X-Y)^n A(X)B(Y)` for all integers `n`, where `(X-Y)^n` is
  expanded as `X^n(1-Y/X)^n` in `R((X))((Y))`.
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`.-/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace VertexAlg

@[ext]
theorem HetVertexOperator.ext (A B : HVertexOperator Γ R V W) (h : ∀(v : V), A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficient of a heterogeneous vertex operator, viewed as a formal power series with
coefficients in linear maps. -/
@[simps]
def coeff (A : HVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun := fun (x : V) => (A x).coeff n
  map_add' := by
      intro x y
      simp only [map_add, HahnSeries.add_coeff', Pi.add_apply, forall_const]
      exact rfl
  map_smul' := by
      intro r x
      simp only [map_smul, HahnSeries.smul_coeff, RingHom.id_apply, forall_const]
      exact rfl

theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) : (A v).coeff.support.IsPWO :=
  (A v).isPWO_support'

@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def HetVertexOperator.of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (f · x)).IsPWO) : HVertexOperator Γ R V W where
  toFun := fun x =>
  { coeff := fun g => f g x
    isPWO_support' := hf x }
  map_add' := by
    intros
    simp only [map_add]
    exact rfl
  map_smul' := by
    intros
    simp only [map_smul, RingHom.id_apply]
    exact rfl
