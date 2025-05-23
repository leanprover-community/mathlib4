/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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
  Matrix.of fun j ↦ open scoped Classical in
    Pi.single i ↑|b.cartanMatrix i j|

def e₂₁ (i : b.support) : Matrix ι b.support R :=
  Matrix.of fun j ↦ open scoped Classical in
    if P.root j = - P.root i then Pi.single i 1 else 0

def e₂₂ (i : b.support) : Matrix ι ι R :=
  Matrix.of fun j k ↦ open scoped Classical in
    if P.root j + P.root i = P.root k then P.chainBotCoeff i j else 0

def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  (Matrix.fromBlocks 0 (e₁₂ i) (e₂₁ i) (e₂₂ i)).transpose

def f₁₂ (i : b.support) : Matrix b.support ι R :=
  Matrix.of fun j ↦ open scoped Classical in
    Pi.single (P.reflection_perm i i) ↑|b.cartanMatrix i j|

def f₂₁ (i : b.support) : Matrix ι b.support R :=
  Matrix.of fun j k ↦ open scoped Classical in
    if P.root j - P.root i = P.root k then P.chainTopCoeff i j else 0

def f₂₂ (i : b.support) : Matrix ι ι R :=
  Matrix.of fun j ↦ open scoped Classical in
    if P.root j = P.root i then Pi.single i 1 else 0

def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.fromBlocks 0 (f₁₂ i) (f₂₁ i) (f₂₂ i)

def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  Matrix.fromBlocks 0 0 0 <| Matrix.of fun j _ ↦ P.pairingIn ℤ j i

/-- Lemma 3.3 (a) from [Geck](Geck2017).

TODO Add part (b) as well as Lemmas 3.4, 3.5. -/
lemma lie_h_e [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h j, e i⁆ = b.cartanMatrix i j • e i := by
  ext (k|k) (l|l)
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e]
  · simp [Ring.lie_def, cartanMatrix, cartanMatrixIn_def, Matrix.mul_apply, h, e, e₂₁]
    rw [Finset.sum_eq_single_of_mem (↑i) (Finset.mem_univ _)]
    · simp [mul_comm, Pi.single_apply]
      sorry
    · simp +contextual [Pi.single_apply]
      sorry
  · sorry
  · sorry

variable (b)
variable [Fintype b.support] [Fintype ι] [DecidableEq ι]

/-- The Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range e ∪ range f)

instance : LieRingModule b.lieAlgebra (b.support ⊕ ι → R) := sorry

instance : LieModule R b.lieAlgebra (b.support ⊕ ι → R) := sorry

instance : LieModule.IsFaithful R b.lieAlgebra (b.support ⊕ ι → R) := sorry

instance : Module.Finite R b.lieAlgebra := sorry

end RootPairing.Base
