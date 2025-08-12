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

## References

- [stacks-project]: The Stacks project, [tag 05K7](https://stacks.math.columbia.edu/tag/05K7)
- [lam_reyes_2009]: *Oka and Ako ideal families in commutative rings*, 2009
-/

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- A predicate `P : Ideal R → Prop` over the ideals of a ring `R` is said to be Oka if R satisfies
it (`P ⊤`) and whenever we have `I : Ideal R`, `P (I.colon (span {a})` and `P (I ⊔ span {a})` for
some `a : R` then `P I`. -/
@[stacks 05K9]
structure IsOka (P : Ideal R → Prop) : Prop where
  top : P ⊤
  oka {I : Ideal R} {a : R} : P (I ⊔ span {a}) → P (I.colon (span {a})) → P I

namespace IsOka

variable {P : Ideal R → Prop}

/-- If an ideal is maximal for not satisfying an oka predicate then it is prime. -/
@[stacks 05KE]
theorem isPrime_of_maximal_not_isOka (hP : IsOka P) {I : Ideal R}
    (hI : Maximal (¬P ·) I) : I.IsPrime := by
  by_contra h
  have I_ne_top : I ≠ ⊤ := fun hI' ↦ hI.prop (hI' ▸ hP.top)
  obtain ⟨a, ha, b, hb, hab⟩ := (not_isPrime_iff.1 h).resolve_left I_ne_top
  have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
  have h₂ : P (I.colon (span {a})) := of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne le_colon
    (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ hab))
  exact hI.prop (hP.oka h₁ h₂)

/-- If all prime ideals of a ring satisfy an oka predicate, then all its ideals also satisfy the
predicate. `hmax` is generaly obtained using Zorn's lemma. -/
theorem forall_of_forall_prime_isOka (hP : IsOka P)
    (hmax : (∃ I, ¬P I) → ∃ I, Maximal (¬P ·) I) (hprime : ∀ I, I.IsPrime → P I) : ∀ I, P I := by
  by_contra!
  obtain ⟨I, hI⟩ := hmax this
  exact hI.prop <| hprime I (hP.isPrime_of_maximal_not_isOka hI)

end IsOka

end Ideal
