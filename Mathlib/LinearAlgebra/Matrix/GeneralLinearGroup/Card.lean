/-
Copyright (c) 2024 Thomas Lanard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Inna Capdeboscq, Johan Commelin, Thomas Lanard, Peiran Wu
-/
import Mathlib.Data.Matrix.Rank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Cardinal of the general linear group over finite rings

This file computes the cardinal of the general linear group over finite rings.

## Main statements

* `card_linearInependent` gives the cardinal of the set of linearly independent vectors over a
  finite dimensional vector space over a finite field.
* `Matrix.card_GL_field` gives the cardinal of the general linear group over a finite field.
-/

open LinearMap

section LinearIndependent

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]

local notation "q" => Fintype.card K
local notation "n" => FiniteDimensional.finrank K V

attribute [local instance] Fintype.ofFinite in
open Fintype in
/-- The cardinal of the set of linearly independent vectors over a finite dimensional vector space
over a finite field. -/
theorem card_linearIndependent {k : ℕ} (hk : k ≤ n) :
    Nat.card { s : Fin k → V // LinearIndependent K s } =
      ∏ i : Fin k, (q ^ n - q ^ i.val) := by
  rw [Nat.card_eq_fintype_card]
  induction k with
  | zero => simp only [LinearIndependent, Finsupp.total_fin_zero, ker_zero, card_ofSubsingleton,
      Finset.univ_eq_empty, Finset.prod_empty]
  | succ k ih =>
      have (s : { s : Fin k → V // LinearIndependent K s }) :
          card ((Submodule.span K (Set.range (s : Fin k → V)))ᶜ : Set (V)) =
          (q) ^ n - (q) ^ k := by
            rw [card_compl_set, card_eq_pow_finrank (K := K)
            (V := ((Submodule.span K (Set.range (s : Fin k → V))) : Set (V)))]
            simp only [SetLike.coe_sort_coe, finrank_span_eq_card s.2, card_fin]
            rw [card_eq_pow_finrank (K := K)]
      simp [card_congr (equiv_linearIndependent k), sum_congr _ _ this, ih (Nat.le_of_succ_le hk),
        mul_comm, Fin.prod_univ_succAbove _ k]

end LinearIndependent

namespace Matrix

section field

variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽]

local notation "q" => Fintype.card 𝔽

variable (n : ℕ)

/-- Equivalence between `GL n F` and `n` vectors of length `n` that are linearly independent. Given
by sending a matrix to its coloumns. -/
noncomputable def equiv_GL_linearindependent (hn : 0 < n) :
    GL (Fin n) 𝔽 ≃ { s : Fin n → Fin n → 𝔽 // LinearIndependent 𝔽 s } where
  toFun M := ⟨transpose M, by
    apply linearIndependent_iff_card_eq_finrank_span.2
    rw [Set.finrank, ← rank_eq_finrank_span_cols, rank_unit]⟩
  invFun M := GeneralLinearGroup.mk'' (transpose (M.1)) <| by
    have : Nonempty (Fin n) := Fin.pos_iff_nonempty.1 hn
    let b := basisOfLinearIndependentOfCardEqFinrank M.2 (by simp)
    have := (Pi.basisFun 𝔽 (Fin n)).invertibleToMatrix b
    rw [← Basis.coePiBasisFun.toMatrix_eq_transpose,
      ← coe_basisOfLinearIndependentOfCardEqFinrank M.2]
    exact isUnit_det_of_invertible _
  left_inv := fun x ↦ Units.ext (ext fun i j ↦ rfl)
  right_inv := by exact congrFun rfl

/-- The cardinal of the general linear group over a finite field. -/
theorem card_GL_field :
    Nat.card (GL (Fin n) 𝔽) = ∏ i : (Fin n), (q ^ n - q ^ ( i : ℕ )) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.card_eq_fintype_card]
  · rw [Nat.card_congr (equiv_GL_linearindependent n hn), card_linearIndependent,
    FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin]
    simp only [FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_fin, le_refl]

end field

end Matrix
