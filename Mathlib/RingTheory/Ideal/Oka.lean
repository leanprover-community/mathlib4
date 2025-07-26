/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
import Mathlib.RingTheory.Ideal.Colon

/-!
# Oka predicates

This file introduces the notion of oka predicates and standard results about them.

## Main results

- `Ideal.isPrime_of_maximal_not_isOka`: if an ideal is maximal for not satisfying an oka predicate
  then it is prime.
- `IsOka.forall_of_forall_prime`: if all prime ideals of a ring satisfy an oka predicate, then all
  its ideals also satisfy the predicate.
-/

open Ideal

variable {R : Type*} [CommSemiring R]

/-- A predicate `P : Ideal R → Prop` over the ideals of a ring `R` is said to be Oka if R satisfies
it (`P ⊤`) and whenever we have `I : Ideal R`, `P (I.colon (span {a})` and `P (I ⊔ span {a})` for
some `a : R` then `P I`. -/
def IsOka (P : Ideal R → Prop) : Prop :=
  P ⊤ ∧ (∀ {I : Ideal R} {a : R}, P (I ⊔ span {a}) → P (I.colon (span {a})) → P I)

variable {P : Ideal R → Prop}

/-- If an ideal is maximal for not satisfying an oka predicate then it is prime. -/
theorem Ideal.isPrime_of_maximal_not_isOka (hP : IsOka P) {I : Ideal R}
    (hI : Maximal (¬P ·) I) : I.IsPrime := by
  by_contra h
  have I_ne_top : I ≠ ⊤ := fun hI' ↦ hI.1 (hI' ▸ hP.1)
  obtain ⟨a, ha, b, hb, hab⟩ := (not_isPrime_iff.1 h).resolve_left I_ne_top
  have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
  have h₂ : P (I.colon (span {a})) :=
    of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne
      (fun _ hx ↦ mem_colon_singleton.2 <| I.mul_mem_right a hx)
      (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ hab))
  exact hI.1 (hP.2 h₁ h₂)

/-- If all prime ideals of a ring satisfy an oka predicate, then all its ideals also satisfy the
predicate. `hmax` is generaly obtained using Zorn's lemma. -/
theorem Ideal.forall_of_forall_prime_isOka (hP : IsOka P)
    (hmax : (∃ I, ¬P I) → ∃ I, Maximal (¬P ·) I) (hprime : ∀ I, I.IsPrime → P I) : ∀ I, P I := by
  by_contra!
  obtain ⟨I, hI⟩ := hmax this
  exact hI.1 <| hprime I (isPrime_of_maximal_not_isOka hP hI)
