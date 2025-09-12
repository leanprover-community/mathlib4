/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
import Mathlib.RingTheory.Ideal.Colon

/-!
# Oka predicates

This file introduces the notion of Oka predicates and standard results about them.

## Main results

- `Ideal.IsOka.isPrime_of_maximal_not`: if an ideal is maximal for not satisfying an Oka predicate,
  then it is prime.
- `Ideal.IsOka.forall_of_forall_prime`: if all prime ideals of a ring satisfy an Oka predicate,
  then all its ideals also satisfy the predicate.

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

variable {P : Ideal R → Prop} (hP : IsOka P)
include hP

/-- If an ideal is maximal for not satisfying an Oka predicate then it is prime. -/
@[stacks 05KE]
theorem isPrime_of_maximal_not {I : Ideal R} (hI : Maximal (¬P ·) I) : I.IsPrime where
  ne_top' hI' := hI.prop (hI' ▸ hP.top)
  mem_or_mem' := by
    by_contra!
    obtain ⟨a, b, hab, ha, hb⟩ := this
    have h₁ : P (I ⊔ span {a}) := of_not_not <| hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
    have h₂ : P (I.colon (span {a})) := of_not_not <| hI.not_prop_of_gt <| lt_of_le_of_ne le_colon
      (fun H ↦ hb <| H ▸ mem_colon_singleton.2 (mul_comm a b ▸ hab))
    exact hI.prop (hP.oka h₁ h₂)

/-- If a ring `R` verify:
1. All prime ideals of `R` satisfy an Oka predicate `P`.
2. One ideal not satisfying `P` implies that there is an ideal maximal for not satisfying `P`.

Then all the ideals of `R` satisfy `P`. -/
theorem forall_of_forall_prime (hmax : ∀ I, ¬P I → ∃ I, Maximal (¬P ·) I)
    (hprime : ∀ I, I.IsPrime → P I) (I : Ideal R) : P I := by
  by_contra! hI
  obtain ⟨I, hI⟩ := hmax I hI
  exact hI.prop <| hprime I (hP.isPrime_of_maximal_not hI)

/-- A variant of `forall_of_forall_prime` with a different spelling of the condition `hmax`. -/
theorem forall_of_forall_prime'
    (hchain : ∀ C ⊆ {I | ¬P I}, IsChain (· ≤ ·) C → ∀ _ ∈ C, P (sSup C) → ∃ I ∈ C, P I)
    (hprime : ∀ I, I.IsPrime → P I) : ∀ I, P I := by
  refine forall_of_forall_prime hP (fun I hI ↦ ?_) hprime
  obtain ⟨M, _, hM⟩ : ∃ M, I ≤ M ∧ Maximal (¬P ·) M := by
    refine zorn_le_nonempty₀ {I | ¬P I} (fun C hC₁ hC₂ J hJ ↦ ⟨sSup C, ?_, fun _ ↦ le_sSup⟩) I hI
    intro H
    obtain ⟨_, h₁, h₂⟩ := hchain C hC₁ hC₂ J hJ H
    exact hC₁ h₁ h₂
  exact ⟨M, hM⟩

end IsOka

end Ideal
