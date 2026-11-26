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
characterisation holds for matrices indexed by `ι ⊕ ι`, where `ι` has a maximum of one element.

The parameter `Fin 1` indexes the single symplectic coordinate pair. The matrix
indices `Fin 1 ⊕ Fin 1` therefore have two elements. Reindexing by `finSumFinEquiv`
gives an equivalence with $\operatorname{SL}_2(R)$, whose matrices are indexed by `Fin 2`.

## Main results

* `Matrix.det_subsingleton_sum_subsingleton`: the determinant formula for matrices indexed by
  `ι ⊕ m`, given an index in each of the two subsingleton types.
* `SymplecticGroup.mem_subsingleton_iff_det_eq_one`: a matrix indexed by `ι ⊕ ι`,
  where `ι` has a maximum of one element, is symplectic if and only if its determinant is one.
* `SymplecticGroup.subsingletonEquivSpecialLinear`: for a subsingleton `m`, the symplectic
  group is equivalent to the special linear group on `m ⊕ m`.
* `SymplecticGroup.finOneEquivSL2`: a group equivalence with $\operatorname{SL}_2(R)$,
  indexed by `Fin 2`.
-/

@[expose] public section

namespace SymplecticGroup

open Matrix

/-- A matrix indexed by `ι ⊕ ι`, where `ι` is a subsingleton type, is symplectic
if and only if its determinant is one. -/
theorem mem_subsingleton_iff_det_eq_one
    (ι R : Type*) [Subsingleton ι] [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    M ∈ symplecticGroup ι R ↔ M.det = 1 := by
  refine ⟨det_eq_one, fun hdet ↦ ?_⟩
  rw [← fromBlocks_toBlocks M, fromBlocks_mem_iff]
  simp_rw [← Matrix.ext_iff, ← forall_and, Subsingleton.forall₂_iff]
  intro i
  simpa [Matrix.mul_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂,
    Fintype.sum_subsingleton _ i, det_subsingleton_sum_subsingleton M i i, mul_comm] using hdet

/-- If `m` is a subsingleton, the symplectic group is equivalent to the special linear group
on `m ⊕ m`. The underlying matrix is unchanged. -/
def subsingletonEquivSpecialLinear (R m : Type*) [Fintype m] [Subsingleton m]
    [DecidableEq m] [CommRing R] :
    ↥(symplecticGroup m R) ≃*
      SpecialLinearGroup (m ⊕ m) R where
  __ := Equiv.subtypeEquivRight fun A ↦ mem_subsingleton_iff_det_eq_one m R A
  map_mul' _ _ := rfl

/-- The symplectic group on 2 × 2 matrices is equivalent to $\operatorname{SL}_2(R)$.
The source matrices are indexed by `Fin 1 ⊕ Fin 1`, and the target matrices by `Fin 2`. -/
def finOneEquivSL2 (R : Type*) [CommRing R] :
    ↥(symplecticGroup (Fin 1) R) ≃*
      SpecialLinearGroup (Fin 2) R :=
  (subsingletonEquivSpecialLinear R (Fin 1)).trans
    (SpecialLinearGroup.reindex R finSumFinEquiv)

@[simp]
theorem finOneEquivSL2_apply_coe
    (R : Type*) [CommRing R]
    (A : ↥(symplecticGroup (Fin 1) R)) :
    ((finOneEquivSL2 R) A : Matrix (Fin 2) (Fin 2) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) := rfl

@[simp]
theorem finOneEquivSL2_symm_apply_coe
    (R : Type*) [CommRing R]
    (A : SpecialLinearGroup (Fin 2) R) :
    ((finOneEquivSL2 R).symm A :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) R) =
      Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (A : Matrix (Fin 2) (Fin 2) R) := rfl

end SymplecticGroup
