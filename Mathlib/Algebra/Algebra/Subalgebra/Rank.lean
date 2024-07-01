/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# Some results on the ranks of subalgebras

This file contains some results on the ranks of subalgebras,
which are corollaries of `rank_mul_rank`.
Since their proof essentially depends on the fact that a non-trivial commutative ring
satisfies strong rank condition, we put them into a separate file.

-/

open FiniteDimensional

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (A B : Subalgebra R S) [Module.Free R A] [Module.Free R B]
  [Module.Free A (Algebra.adjoin A (B : Set S))]
  [Module.Free B (Algebra.adjoin B (A : Set S))]

theorem rank_sup_eq_rank_left_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R A * Module.rank A (Algebra.adjoin A (B : Set S)) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · haveI := Module.subsingleton R S; simp
  nontriviality S using rank_subsingleton'
  letI : Algebra A (Algebra.adjoin A (B : Set S)) := Subalgebra.algebra _
  letI : SMul A (Algebra.adjoin A (B : Set S)) := Algebra.toSMul
  haveI : IsScalarTower R A (Algebra.adjoin A (B : Set S)) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [rank_mul_rank R A (Algebra.adjoin A (B : Set S))]
  change _ = Module.rank R ((Algebra.adjoin A (B : Set S)).restrictScalars R)
  rw [Algebra.restrictScalars_adjoin]; rfl

theorem rank_sup_eq_rank_right_mul_rank_of_free :
    Module.rank R ↥(A ⊔ B) = Module.rank R B * Module.rank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, rank_sup_eq_rank_left_mul_rank_of_free]

theorem finrank_sup_eq_finrank_left_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R A * finrank A (Algebra.adjoin A (B : Set S)) := by
  simpa only [map_mul] using congr(Cardinal.toNat $(rank_sup_eq_rank_left_mul_rank_of_free A B))

theorem finrank_sup_eq_finrank_right_mul_finrank_of_free :
    finrank R ↥(A ⊔ B) = finrank R B * finrank B (Algebra.adjoin B (A : Set S)) := by
  rw [sup_comm, finrank_sup_eq_finrank_left_mul_finrank_of_free]

theorem finrank_left_dvd_finrank_sup_of_free :
    finrank R A ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_left_mul_finrank_of_free A B⟩

theorem finrank_right_dvd_finrank_sup_of_free :
    finrank R B ∣ finrank R ↥(A ⊔ B) := ⟨_, finrank_sup_eq_finrank_right_mul_finrank_of_free A B⟩

end Subalgebra
