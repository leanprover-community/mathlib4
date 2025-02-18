/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis.Ext

/-!
# Constructing a linear map given the value at the basis

## Main definitions

* `Basis.constr`: given `b : Basis ι R M` and `f : ι → M`, construct a linear map `g` so that
  `g (b i) = f i`.
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace Basis

variable (b : Basis ι R M)

section Constr

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

/-- Construct a linear map given the value at the basis, called `Basis.constr b S f` where `b` is
a basis, `f` is the value of the linear map over the elements of the basis, and `S` is an
extra semiring (typically `S = R` or `S = ℕ`).

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M' where
  toFun f := (Finsupp.linearCombination R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp

theorem constr_def (f : ι → M') :
    constr (M' := M') b S f = linearCombination R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl

theorem constr_apply (f : ι → M') (x : M) :
    constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (constr (M' := M') b S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]

theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) :
    constr (M' := M') b S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)

theorem constr_self (f : M →ₗ[R] M') : (constr (M' := M') b S fun i => f (b i)) = f :=
  b.constr_eq S fun _ => rfl

theorem constr_range {f : ι → M'} :
    LinearMap.range (constr (M' := M') b S f) = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_linearCombination, Set.image_id]

@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
    constr (M' := M') b S (f ∘ v) = f.comp (constr (M' := M') b S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

@[simp]
theorem constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι → M') (x : M) :
    (constr (M' := M') b S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

end Constr

end Basis

end Module
