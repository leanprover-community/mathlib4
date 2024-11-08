/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Polynomial.GroupRingAction
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

/-!
# Invariant Extensions of Rings

Given an extension of rings `B/A` and an action of `G` on `B`, we introduce a predicate
`Algebra.IsInvariant A B G` which states that every fixed point of `B` lies in the image of `A`.

## Main statements
* `Algebra.IsInvariant.isIntegral`: If `G` is finite, then `B/A` is an integral extension.

TODO: Prove the existence of Frobenius elements in this general setting.

-/

namespace Algebra

variable (A B G : Type*) [CommSemiring A] [Semiring B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- An action of a group `G` on an extension of rings `B/A` is invariant if every fixed point of
`B` lies in the image of `A`. The converse statement that every point in the image of `A` is fixed
by `G` is `smul_algebraMap` (assuming `SMulCommClass A B G`). -/
@[mk_iff] class IsInvariant : Prop where
  isInvariant : ∀ b : B, (∀ g : G, g • b = b) → ∃ a : A, algebraMap A B a = b

end Algebra

section IsIntegral

variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

namespace MulSemiringAction

open Polynomial

variable {B} [Fintype G]

/-- Characteristic polynomial of a finite group action on a ring. -/
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

theorem charpoly_coeff_smul (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, charpoly_smul]

end MulSemiringAction

namespace Algebra.IsInvariant

open MulSemiringAction Polynomial

variable [IsInvariant A B G]

theorem charpoly_mem_lifts [Fintype G] (b : B) :
    charpoly G b ∈ Polynomial.lifts (algebraMap A B) :=
  (charpoly G b).lifts_iff_coeff_lifts.mpr fun n ↦ isInvariant _ (charpoly_coeff_smul b n)

theorem isIntegral [Finite G] : Algebra.IsIntegral A B := by
  cases nonempty_fintype G
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨p, hp1, -, hp2⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (charpoly_mem_lifts A B G b) (charpoly_monic G b)
  exact ⟨p, hp2, by rw [← eval_map, hp1, charpoly_eval]⟩

end Algebra.IsInvariant

end IsIntegral
