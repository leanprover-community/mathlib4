/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# The Lie algebra of a root system
-/

noncomputable section

open Set

namespace RootPairing.Base

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible]
  {b : P.Base}

def e₁₂ (i : b.support) : Matrix b.support ι R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if i' = i ∧ P.root j = - P.root i then 1 else 0

def e₂₁ (i : b.support) : Matrix ι b.support R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if i' = i then ↑|b.cartanMatrix i j| else 0

def e₂₂ (i : b.support) : Matrix ι ι R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if P.root i' = P.root i + P.root j then P.chainBotCoeff i j else 0

def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.fromBlocks 0 (e₁₂ i) (e₂₁ i) (e₂₂ i)

def f₁₂ (i : b.support) : Matrix b.support ι R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if i' = i ∧ P.root j = P.root i then 1 else 0

def f₂₁ (i : b.support) : Matrix ι b.support R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if P.root i' = - P.root i then ↑|b.cartanMatrix i j| else 0

def f₂₂ (i : b.support) : Matrix ι ι R :=
  Matrix.of fun i' j ↦ open scoped Classical in
    if P.root i' = P.root i - P.root j then P.chainTopCoeff i j else 0

def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.fromBlocks 0 (f₁₂ i) (f₂₁ i) (f₂₂ i)

def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.fromBlocks 0 0 0 <| open scoped Classical in Matrix.diagonal (P.pairingIn ℤ · i)

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsReduced] [P.IsIrreducible] in
lemma lie_h_h [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  ext (k | k) (l | l)
  · simp [Ring.lie_def, Matrix.mul_apply, h]
  · simp [Ring.lie_def, Matrix.mul_apply, h]
  · simp [Ring.lie_def, Matrix.mul_apply, h]
  · simp [Ring.lie_def, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm (P.pairingIn ℤ k i : R),
      h]
    aesop

omit [P.IsReduced] [P.IsIrreducible] in
/-- Lemma 3.3 (a) from [Geck](Geck2017).

TODO Add part (b) as well as Lemmas 3.4, 3.5. -/
lemma lie_h_e [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h j, e i⁆ = b.cartanMatrix i j • e i := by
  ext (k|k) (l|l)
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e]
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e, e₁₂]
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ _)]
    · rw [apply_ite (- · : R → R)]
      convert ite_congr rfl _ (fun _ ↦ neg_zero)
      simp +contextual
    · simp +contextual
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e, e₂₁]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    · convert ite_congr rfl _ (fun _ ↦ rfl)
      simp +contextual
    · classical
      simp +contextual [Matrix.diagonal_apply]
      aesop
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e, e₂₂]
    classical
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_compl_add_sum {k, l}]
    rw [Finset.sum_eq_zero, zero_add]
    · rcases eq_or_ne k l with (rfl | hkl)
      · simp [P.ne_zero]
      · simp [hkl]
        rw [ite_sub_ite]
        convert ite_congr rfl _ _
        · intro hkil
          suffices P.pairingIn ℤ k j = P.pairingIn ℤ i j + P.pairingIn ℤ l j by
            rw [this]
            norm_cast
            ring
          suffices P.pairing k j = P.pairing i j + P.pairing l j by
            apply Int.cast_injective (α := R)
            simpa [← P.algebraMap_pairingIn ℤ] using this
          simp only [← root_coroot_eq_pairing, hkil, map_add, LinearMap.add_apply]
        · simp
    · simp +contextual [Matrix.diagonal_apply]
      aesop

lemma lie_h_f [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h j, f i⁆ = -b.cartanMatrix i j • f i := by
  sorry

lemma lie_e_f_same [Fintype b.support] [Fintype ι] (i : b.support) :
    ⁅e i, f i⁆ = h i := by
  sorry

lemma lie_e_f_ne [Fintype b.support] [Fintype ι] (i j : b.support) (hij : i ≠ j) :
    ⁅e i, f j⁆ = 0 := by
  sorry

variable (b)
variable [Fintype b.support] [Fintype ι] [DecidableEq ι]

/-- The Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range e ∪ range f)

example [IsNoetherianRing R] : Module.Finite R b.lieAlgebra := inferInstance

end RootPairing.Base
