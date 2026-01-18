/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/

@[expose] public section

section

open Function Matrix LinearMap

variable {R : Type*} [Semiring R]

instance (priority := low) [OrzechProperty R] : IsStablyFiniteRing R :=
  isStablyFiniteRing_iff_injective_of_surjective.mpr fun _ ↦
    OrzechProperty.injective_of_surjective_endomorphism

instance (priority := low) [IsStablyFiniteRing R] [Nontrivial R] : RankCondition R where
  le_of_fin_surjective {n m} f hf := by
    by_contra! lt
    let p : (Fin m → R) →ₗ[R] Fin n → R := funLeft R R (Fin.castLE lt.le)
    have hp : Surjective p := funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective lt.le)
    have : Injective p := .of_comp_right
      (Module.End.injective_of_surjective_fin (f := p ∘ₗ f) (hp.comp hf)) hf
    have ⟨⟨i, lt⟩, eq⟩ := injective_comp_right_iff_surjective.mp this ⟨n, lt⟩
    exact lt.ne congr($eq)

theorem rankCondition_iff_le_of_comp_eq_one : RankCondition R ↔ ∀ n m
    (f : (Fin n → R) →ₗ[R] Fin m → R) (g : (Fin m → R) →ₗ[R] Fin n → R), f ∘ₗ g = 1 → m ≤ n :=
  (rankCondition_iff R).trans ⟨fun h _ _ f _ eq ↦ h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf ↦ have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩

theorem rankCondition_iff_matrix : RankCondition R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), g * f = 1 → m ≤ n := by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
    |>.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]

theorem invariantBasisNumber_iff_matrix : InvariantBasisNumber R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), f * g = 1 → g * f = 1 → n = m :=
  (invariantBasisNumber_iff R).trans <| .intro (fun h n m f g hfg hgf ↦
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e ↦ h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

/-- The rank condition is left-right symmetric. Note that the strong rank condition
is not left-right symmetric, see Remark (1.32) in §1.1D of [lam_1999]. -/
protected theorem MulOpposite.rankCondition_iff : RankCondition Rᵐᵒᵖ ↔ RankCondition R := by
  simp_rw [rankCondition_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
  refine forall_swap.trans <| .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f ↦ .trans (forall_congr' fun g ↦ ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff]
  congrm (?_ = ?_ → _)
  · ext; simp [map, mul_apply]
  · simp

/-- Invariant basis number is left-right symmetric. -/
protected theorem MulOpposite.invariantBasisNumber_iff :
    InvariantBasisNumber Rᵐᵒᵖ ↔ InvariantBasisNumber R := by
  simp_rw [invariantBasisNumber_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
  refine forall_swap.trans <| .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f ↦ .trans (forall_congr' fun g ↦ ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff, ← (transposeAddEquiv (Fin m) ..).injective.eq_iff]
  congrm (?_ = ?_ → ?_ = ?_ → _)
  iterate 2 ext; simp [map, mul_apply]; simp

instance [RankCondition R] : RankCondition Rᵐᵒᵖ := MulOpposite.rankCondition_iff.mpr ‹_›

instance [InvariantBasisNumber R] : InvariantBasisNumber Rᵐᵒᵖ :=
  MulOpposite.invariantBasisNumber_iff.mpr ‹_›

end

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
    [CommSemiring R] [Nontrivial R] : RankCondition R := inferInstance
