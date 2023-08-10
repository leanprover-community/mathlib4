/-
Copyright (c) 2023 Mohanad ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import Mathlib.Data.IsROrC.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Spectrum

variable {𝕂: Type}[IsROrC 𝕂][DecidableEq 𝕂]
variable {M N: ℕ}

open Matrix BigOperators

namespace Matrix

open IsHermitian

lemma rank_eq_card_pos_eigs_conj_transpose_mul_self (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.rank = Fintype.card {i // (isHermitian_transpose_mul_self A).eigenvalues i ≠ 0} := by
  sorry
  -- rw[← rank_conjTranspose_mul_self, IsHermitian.rank_eq_card_non_zero_eigs]

lemma rank_eq_card_pos_eigs_self_mul_conj_transpose (A : Matrix (Fin M) (Fin N) 𝕂) :
    A.rank = Fintype.card {i // (isHermitian_mul_conjTranspose_self A).eigenvalues i ≠ 0} := by
  sorry
  -- rw[← rank_self_mul_conjTranspose, IsHermitian.rank_eq_card_non_zero_eigs]

end Matrix
