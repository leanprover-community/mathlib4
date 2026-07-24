/-
Copyright (c) 2026 Ryan Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan Smith
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Suzuki Groups

We define the Suzuki groups `suzukiGroup n` (often denoted $Sz(q)$ where $q = 2^{2n+1}$)
for any natural number `n : ℕ`.

## Main definitions

* `suzukiGroup n`: The Suzuki group $Sz(2^{2n+1})$, defined as a subgroup of
  `GL (Fin 4) (GaloisField 2 (2 * n + 1))`.
* `Suzuki.unipotentMatrix n a b`: The matrix $S(a, b)$.
* `Suzuki.weylMatrix n`: The Weyl generator matrix $w$.
* `Suzuki.unipotent n a b`: The unipotent generator as an element of `GL (Fin 4) (Fq n)`.
* `Suzuki.weyl n`: The Weyl generator as an element of `GL (Fin 4) (Fq n)`.
* `Suzuki.generators n`: The set of generators for $Sz(2^{2n+1})$.
-/

@[expose] public section

noncomputable section

open Matrix

namespace Suzuki

variable (n : ℕ)

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The field $\mathbb{F}_q$ where $q = 2^{2n+1}$. -/
abbrev Fq (n : ℕ) : Type := GaloisField 2 (2 * n + 1)

/-- The field endomorphism $\sigma(x) = x^{2^{n+1}}$ on $\mathbb{F}_{2^{2n+1}}$. -/
def sigma (n : ℕ) (x : Fq n) : Fq n := x ^ (2 ^ (n + 1))

/-- The unipotent matrix generator $S(a, b)$ for $a, b \in \mathbb{F}_q$. -/
def unipotentMatrix (n : ℕ) (a b : Fq n) : Matrix (Fin 4) (Fin 4) (Fq n) :=
  ![![1, 0, 0, 0],
    ![a, 1, 0, 0],
    ![a * sigma n a + b, sigma n a, 1, 0],
    ![a ^ 2 * sigma n a + a * b + sigma n b, b, a, 1]]

/-- The Weyl group generator matrix $w$. -/
def weylMatrix (n : ℕ) : Matrix (Fin 4) (Fin 4) (Fq n) :=
  ![![0, 0, 0, 1],
    ![0, 0, 1, 0],
    ![0, 1, 0, 0],
    ![1, 0, 0, 0]]

/-- Proof that `unipotentMatrix n a b` has determinant 1. -/
lemma det_unipotentMatrix (a b : Fq n) : (unipotentMatrix n a b).det = 1 := by
  dsimp [unipotentMatrix]
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp [submatrix_apply, det_fin_three, Fin.succAbove]

/-- Proof that `weylMatrix n` has determinant 1. -/
lemma det_weylMatrix : (weylMatrix n).det = 1 := by
  dsimp [weylMatrix]
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp [submatrix_apply, det_fin_three, Fin.succAbove]
  ring

/-- The unipotent generator as an element of `GL (Fin 4) (Fq n)`. -/
def unipotent (a b : Fq n) : GL (Fin 4) (Fq n) :=
  ((isUnit_iff_isUnit_det (A := unipotentMatrix n a b)).mpr
    (by rw [det_unipotentMatrix]; exact isUnit_one)).unit

/-- The Weyl generator as an element of `GL (Fin 4) (Fq n)`. -/
def weyl : GL (Fin 4) (Fq n) :=
  ((isUnit_iff_isUnit_det (A := weylMatrix n)).mpr
    (by rw [det_weylMatrix]; exact isUnit_one)).unit

/-- The set of generators for the Suzuki group $Sz(2^{2n+1})$. -/
def generators : Set (GL (Fin 4) (Fq n)) :=
  {g | (∃ a b, g = unipotent n a b) ∨ g = weyl n}

end Suzuki

/-- The Suzuki group $Sz(2^{2n+1})$, defined as a subgroup of
`GL (Fin 4) (GaloisField 2 (2 * n + 1))`. -/
def suzukiGroup (n : ℕ) : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))) :=
  Subgroup.closure (Suzuki.generators n)
