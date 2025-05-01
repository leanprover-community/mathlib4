/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/


variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {R : Type*} [Semiring R] [InvariantBasisNumber R]

theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M * N = 1)
    (h' : N * M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)

open Function in
/-- Nontrivial commutative semirings `R` satisfy the rank condition.

If `R` is moreover a ring, then it satisfies the strong rank condition, see
`commRing_strongRankCondition`. It is unclear whether this generalizes to semirings. -/
instance (priority := 100) rankCondition_of_nontrivial_of_commSemiring {R : Type*}
    [CommSemiring R] [Nontrivial R] : RankCondition R where
  le_of_fin_surjective {n m} f hf := by
    by_contra! lt
    let p : (Fin m → R) →ₗ[R] Fin n → R := .funLeft R R (Fin.castLE lt.le)
    have hp : Surjective p :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective lt.le)
    have ⟨g, eq⟩ := (p ∘ₗ f).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr <| hp.comp hf)
    let e := Matrix.toLinAlgEquiv' (R := R) (n := Fin n).symm
    apply_fun e at eq
    rw [← Module.End.mul_eq_comp, ← Module.End.one_eq_id, map_mul, map_one,
      Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _),
      ← map_mul, ← map_one e, e.injective.eq_iff] at eq
    have : Injective p := (p.coe_comp f ▸ LinearMap.injective_of_comp_eq_id _ _ eq).of_comp_right hf
    have ⟨⟨i, lt⟩, eq⟩ := injective_comp_right_iff_surjective.mp this ⟨n, lt⟩
    exact lt.ne congr($eq)
