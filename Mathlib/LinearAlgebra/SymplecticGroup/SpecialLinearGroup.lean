/-
Copyright (c) 2026 Shirin Shafaie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shirin Shafaie
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The symplectic group on 2 × 2 matrices and the special linear group

For `n = 1`, the symplectic group is isomorphic to the special linear group:
$\operatorname{Sp}_2(R) \cong \operatorname{SL}_2(R)$.

More precisely, for any commutative ring, a matrix indexed by `Fin 1 ⊕ Fin 1`
is symplectic if and only if its determinant is one. More generally, the same
characterisation holds for matrices indexed by `ι ⊕ ι`, where `ι` is a singleton type.

The parameter `Fin 1` indexes the single symplectic coordinate pair. The matrix
indices `Fin 1 ⊕ Fin 1` therefore have two elements. Reindexing by `finSumFinEquiv`
gives an equivalence with $\operatorname{SL}_2(R)$, whose matrices are indexed by `Fin 2`.

## Main results

* `Matrix.det_unique_sum_unique`: the determinant formula for matrices indexed by
  `ι ⊕ ι`, where `ι` is a singleton type.
* `Matrix.det_fin_one_sum_fin_one`: the determinant formula for `Fin 1 ⊕ Fin 1`.
* `SymplecticGroup.mem_unique_iff_det_eq_one`: a matrix indexed by `ι ⊕ ι`,
  where `ι` is a singleton type, is symplectic if and only if its determinant is one.
* `SymplecticGroup.mem_fin_one_iff_det_eq_one`: a 2 × 2 matrix is symplectic if and
  only if its determinant is one.
* `SymplecticGroup.finOneEquivSpecialLinear`: a group equivalence with the special linear
  group on the same indices.
* `SymplecticGroup.finOneEquivSL2`: a group equivalence with $\operatorname{SL}_2(R)$,
  indexed by `Fin 2`.
-/

@[expose] public section

namespace Matrix

/-- The two-by-two determinant formula for matrices indexed by `ι ⊕ ι`,
where `ι` is a singleton type. -/
theorem det_unique_sum_unique (ι R : Type*)
    [Unique ι] [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    M.det =
      M (Sum.inl default) (Sum.inl default) *
        M (Sum.inr default) (Sum.inr default) -
      M (Sum.inl default) (Sum.inr default) *
        M (Sum.inr default) (Sum.inl default) := by
  let e : (ι ⊕ ι) ≃ Fin 2 :=
    (Equiv.sumCongr
      (Equiv.ofUnique ι (Fin 1))
      (Equiv.ofUnique ι (Fin 1))).trans finSumFinEquiv
  calc
    M.det = (Matrix.reindex e e M).det :=
      (Matrix.det_reindex_self e M).symm
    _ = _ := by
      rw [Matrix.det_fin_two]
      rfl

/-- The usual two-by-two determinant formula, indexed by `Fin 1 ⊕ Fin 1`. -/
theorem det_fin_one_sum_fin_one
    {R : Type*} [CommRing R]
    (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    M.det =
      M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) -
      M (Sum.inl 0) (Sum.inr 0) * M (Sum.inr 0) (Sum.inl 0) :=
  det_unique_sum_unique (Fin 1) R M

end Matrix

namespace SymplecticGroup

/-- A matrix indexed by `ι ⊕ ι`, where `ι` is a singleton type, is symplectic
if and only if its determinant is one. -/
theorem mem_unique_iff_det_eq_one
    (ι R : Type*) [Unique ι] [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    M ∈ Matrix.symplecticGroup ι R ↔ M.det = 1 := by
  refine ⟨SymplecticGroup.det_eq_one, ?_⟩
  intro hdet
  rw [Matrix.det_unique_sum_unique ι R M] at hdet
  rw [← Matrix.fromBlocks_toBlocks M, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j
  all_goals
    have hi : i = default := Subsingleton.elim _ _
    have hj : j = default := Subsingleton.elim _ _
    subst i
    subst j
    simp [Matrix.mul_apply, Matrix.transpose_apply, mul_comm]
  · simpa [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_unique,
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.sub_apply, Matrix.one_apply, mul_comm] using hdet

/-- In dimension two, a matrix is symplectic if and only if its determinant is one. -/
theorem mem_fin_one_iff_det_eq_one
    {R : Type*} [CommRing R]
    (M : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) :
    M ∈ Matrix.symplecticGroup (Fin 1) R ↔ M.det = 1 :=
  mem_unique_iff_det_eq_one (Fin 1) R M

/-- The symplectic group on 2 × 2 matrices is equivalent to the special linear group
on `Fin 1 ⊕ Fin 1`. The underlying matrix is unchanged. -/
def finOneEquivSpecialLinear (R : Type*) [CommRing R] :
    ↥(Matrix.symplecticGroup (Fin 1) R) ≃*
      Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 1) R where
  __ := Equiv.subtypeEquivRight fun A => SymplecticGroup.mem_fin_one_iff_det_eq_one A
  map_mul' _ _ := Subtype.ext rfl

/-- The symplectic group on 2 × 2 matrices is equivalent to $\operatorname{SL}_2(R)$.
The source matrices are indexed by `Fin 1 ⊕ Fin 1`, and the target matrices by `Fin 2`. -/
def finOneEquivSL2 (R : Type*) [CommRing R] :
    ↥(Matrix.symplecticGroup (Fin 1) R) ≃*
      Matrix.SpecialLinearGroup (Fin 2) R :=
  (finOneEquivSpecialLinear R).trans
    (Matrix.SpecialLinearGroup.reindex R
      (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2))

@[simp]
theorem finOneEquivSL2_apply_coe
    (R : Type*) [CommRing R]
    (A : ↥(Matrix.symplecticGroup (Fin 1) R)) :
    ((finOneEquivSL2 R) A : Matrix (Fin 2) (Fin 2) R) =
      Matrix.reindex
        (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2)
        (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2)
        (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) := rfl

@[simp]
theorem finOneEquivSL2_symm_apply_coe
    (R : Type*) [CommRing R]
    (A : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((finOneEquivSL2 R).symm A :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) =
      Matrix.reindex
        (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm
        (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm
        (A : Matrix (Fin 2) (Fin 2) R) := rfl

end SymplecticGroup
