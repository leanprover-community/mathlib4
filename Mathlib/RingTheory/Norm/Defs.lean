/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

* https://en.wikipedia.org/wiki/Field_norm

-/

@[expose] public section


universe u v w

variable {R S : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K : Type*} [Field K]
variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
@[stacks 0BIF "Norm"]
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) := rfl

@[simp]
theorem norm_self : Algebra.norm R = MonoidHom.id R := by
  ext
  simp [norm_apply]

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial

variable {R}

theorem norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R x = 1 := by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_toMatrix b, ← toMatrix_lmul_eq]; rfl

/-- If `x` is in the base ring `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  haveI := Classical.decEq ι
  rw [norm_apply, ← det_toMatrix b, lmul_algebraMap]
  simp

variable [Free R S]

/-- If `x` is in the base ring `R` and `S` is free over `R`, then the norm is `x ^ [S : R]`.

(If `S` is not finitely generated over `R`, then `norm = 1 = x ^ 0 = x ^ (finrank R S)`.)
-/
@[simp]
protected theorem norm_algebraMap (x : R) : norm R (algebraMap R S x) = x ^ finrank R S := by
  rw [norm_apply, lmul_algebraMap, det_lsmul]

variable (R) in
protected lemma norm_natCast (n : ℕ) : norm R (n : S) = n ^ Module.finrank R S := by
  rw [← map_natCast (algebraMap R S), Algebra.norm_algebraMap]

end Algebra
