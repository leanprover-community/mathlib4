/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Eric Wieser
-/
module

public import Mathlib.RingTheory.PowerBasis
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Init
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# The minimal polynomial divides the characteristic polynomial of a matrix.

This also includes some miscellaneous results about `minpoly` on matrices.
-/

public section


noncomputable section

open Matrix Module Polynomial

universe u v w

variable {R : Type u} [CommRing R]
variable {n : Type v} [DecidableEq n] [Fintype n]
variable {N : Type w} [AddCommGroup N] [Module R N]

namespace Matrix

variable (M : Matrix n n R)

@[simp]
theorem minpoly_toLin' : minpoly R (toLin' M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv' : Matrix n n R ≃ₐ[R] _) M

@[simp]
theorem minpoly_toLin (b : Basis n R N) (M : Matrix n n R) :
    minpoly R (toLin b b M) = minpoly R M :=
  minpoly.algEquiv_eq (toLinAlgEquiv b : Matrix n n R ≃ₐ[R] _) M

theorem isIntegral : IsIntegral R M :=
  ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly M)

end Matrix

namespace LinearMap

@[simp]
theorem minpoly_toMatrix' (f : (n → R) →ₗ[R] n → R) : minpoly R (toMatrix' f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv' : _ ≃ₐ[R] Matrix n n R) f

@[simp]
theorem minpoly_toMatrix (b : Basis n R N) (f : N →ₗ[R] N) :
    minpoly R (toMatrix b b f) = minpoly R f :=
  minpoly.algEquiv_eq (toMatrixAlgEquiv b : _ ≃ₐ[R] Matrix n n R) f

end LinearMap

section PowerBasis

open Algebra

/-- The characteristic polynomial of the map `fun x => a * x` is the minimal polynomial of `a`.

In combination with `det_eq_sign_charpoly_coeff` or `trace_eq_neg_charpoly_coeff`
and a bit of rewriting, this will allow us to conclude the
field norm resp. trace of `x` is the product resp. sum of `x`'s conjugates.
-/
theorem charpoly_leftMulMatrix {S : Type*} [Ring S] [Algebra R S] (h : PowerBasis R S) :
    (leftMulMatrix h.basis h.gen).charpoly = minpoly R h.gen := by
  cases subsingleton_or_nontrivial R; · subsingleton
  apply minpoly.unique' R h.gen (charpoly_monic _)
  · apply (injective_iff_map_eq_zero (G := S) (leftMulMatrix _)).mp
      (leftMulMatrix_injective h.basis)
    rw [← Polynomial.aeval_algHom_apply, aeval_self_charpoly]
  refine fun q hq => or_iff_not_imp_left.2 fun h0 => ?_
  rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin] at hq
  contrapose! hq; exact h.dim_le_degree_of_root h0 hq

end PowerBasis
