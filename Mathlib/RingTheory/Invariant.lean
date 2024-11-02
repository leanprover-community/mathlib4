/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

## Main statements
* `Algebra.IsInvariant.isIntegral`: If `G` is finite, then `B/A` is an integral extensions.

TODO: Prove the existence of Frobenius elements in this general setting.

-/

namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- An action of a group `G` on an extension of rings `B/A` is invariant if every fixed  -/
class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

variable {A B G}

theorem isInvariant_def :
    IsInvariant A B G ↔ ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

end Algebra

section IsIntegral

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/-- Characteristic polynomial of a group action on a ring. -/
noncomputable def charpoly (b : B) : B[X] := ∏ g : G, (X - C (g • b))

theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl

theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

theorem charpoly_monic (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)

theorem charpoly_eval (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul, eval_sub, eval_C, eval_X, sub_self]

variable {G}

theorem charpoly_smul (b : B) (g : G) : g • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul, Finset.smul_prod_perm]

private theorem charpoly_coeff_smul (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, charpoly_smul]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

theorem exists_map_eq_charpoly [Fintype G] (b : B) :
    ∃ M : A[X], M.Monic ∧ M.map (algebraMap A B) = charpoly G b := by
  have hinv k : ∃ a : A, algebraMap A B a = (charpoly G b).coeff k :=
    isInvariant ((charpoly G b).coeff k) (charpoly_coeff_smul b k)
  let f : ℕ → A := fun k ↦ (hinv k).choose
  have hf : ∀ k, algebraMap A B (f k) = (charpoly G b).coeff k := fun k ↦ (hinv k).choose_spec
  use X ^ (charpoly G b).natDegree + ∑ k ∈ Finset.range (charpoly G b).natDegree, C (f k) * X ^ k
  constructor
  · apply Polynomial.monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    apply Polynomial.degree_sum_fin_lt
  · simp_rw [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hf]
    exact (charpoly_monic G b).as_sum.symm

include G in
theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨f, hf1, hf2⟩ := exists_map_eq_charpoly A B G b
  refine ⟨f, hf1, ?_⟩
  rw [← eval_map, hf2, charpoly_eval]

end Algebra.IsInvariant

end IsIntegral
