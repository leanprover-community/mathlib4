/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Hadamard
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Derivatives of Matrices
-/

variable {ι : Type*} {R : Type*} {A : Type*} {m n p q : Type*}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

namespace Matrix
open scoped Kronecker

section NormedAlgebra

variable [NontriviallyNormedField R] [NormedRing A] [NormedAlgebra R A]

theorem hasDerivAt_matrix {f : R → Matrix m n A} {r : R} {f' : Matrix m n A} :
    HasDerivAt f f' r ↔ ∀ i j, HasDerivAt (fun r => f r i j) (f' i j) r := by
  erw [hasDerivAt_pi]
  simp_rw [hasDerivAt_pi]

theorem HasDerivAt.matrix_mul {X : R → Matrix m n A} {Y : R → Matrix n p A} {X' : Matrix m n A}
    {Y' : Matrix n p A} {r : R} (hX : HasDerivAt X X' r) (hY : HasDerivAt Y Y' r) :
    HasDerivAt (fun a => X a * Y a) (X' * Y r + X r * Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  intro i j
  simp only [mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.sum fun k _hk => (hX _ _).mul (hY _ _)

theorem HasDerivAt.matrix_kronecker {X : R → Matrix m n A} {Y : R → Matrix p q A}
    {X' : Matrix m n A} {Y' : Matrix p q A} {r : R} (hX : HasDerivAt X X' r)
    (hY : HasDerivAt Y Y' r) : HasDerivAt (fun a => X a ⊗ₖ Y a) (X' ⊗ₖ Y r + X r ⊗ₖ Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  rintro ⟨i, i'⟩ ⟨j, j'⟩
  exact (hX _ _).mul (hY _ _)

theorem HasDerivAt.matrix_hadamard {X Y : R → Matrix m n A} {X' Y' : Matrix m n A} {r : R}
    (hX : HasDerivAt X X' r) (hY : HasDerivAt Y Y' r) :
    HasDerivAt (fun a => X a ⊙ Y a) (X' ⊙ Y r + X r ⊙ Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  rintro i j
  exact (hX _ _).mul (hY _ _)

theorem HasDerivAt.trace {X : R → Matrix m m A} {X' : Matrix m m A} {r : R}
    (hX : HasDerivAt X X' r) : HasDerivAt (fun a => (X a).trace) X'.trace r :=
  HasDerivAt.sum fun i _hi => (hasDerivAt_matrix.mp hX : _) i i

theorem HasDerivAt.transpose {X : R → Matrix m n A} {X' : Matrix m n A} {r : R}
    (hX : HasDerivAt X X' r) : HasDerivAt (fun a => (X a)ᵀ) X'ᵀ r :=
  hasDerivAt_matrix.mpr fun i j => (hasDerivAt_matrix.mp hX : _) j i

theorem HasDerivAt.conjTranspose [StarRing R] [TrivialStar R] [StarAddMonoid A] [StarModule R A]
    [ContinuousStar A] {X : R → Matrix m n A} {X' : Matrix m n A} {r : R} (hX : HasDerivAt X X' r) :
    HasDerivAt (fun a => (X a)ᴴ) X'ᴴ r :=
  hasDerivAt_matrix.mpr fun i j => ((hasDerivAt_matrix.mp hX : _) j i).star

theorem deriv_matrix (f : R → Matrix m n A) (r : R) (hX : DifferentiableAt R f r) :
    deriv f r = of fun i j => deriv (fun r => f r i j) r := by
  ext i j
  rw [of_apply, deriv_pi]
  · dsimp only
    rw [deriv_pi]
    intro i
    rw [differentiableAt_pi] at hX
    simp_rw [differentiableAt_pi] at hX
    apply hX
  · intro i
    rw [differentiableAt_pi] at hX
    apply hX

end NormedAlgebra

section LinftyOpNorm

variable [DecidableEq m]
variable [NontriviallyNormedField R] [NormedCommRing A] [NormedAlgebra R A] [CompleteSpace A]

theorem HasDerivAt.matrix_inv {X : R → Matrix m m A} {X' : Matrix m m A} {r : R}
    (hX : HasDerivAt X X' r) (hX' : IsUnit (X r)) :
    HasDerivAt (fun a => (X a)⁻¹) (-(X r)⁻¹ * X' * (X r)⁻¹) r := by
  let i1 : NormedRing (Matrix m m A) := Matrix.linftyOpNormedRing
  let i2 : NormedAlgebra R (Matrix m m A) := Matrix.linftyOpNormedAlgebra
  simp_rw [nonsing_inv_eq_ring_inverse]
  obtain ⟨u, hu⟩ := hX'
  have : HasFDerivAt _ (_ : _ →L[R] _) _ := hasFDerivAt_ring_inverse u
  simp_rw [← Ring.inverse_unit u, hu] at this
  rw [hasDerivAt_iff_hasFDerivAt] at hX ⊢
  convert HasFDerivAt.comp _ this hX
  ext r : 2 -- porting note: added one!
  -- porting note: added `()`-wrapped lemmas
  simp [Matrix.mul_smul, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply]

end LinftyOpNorm

end Matrix
