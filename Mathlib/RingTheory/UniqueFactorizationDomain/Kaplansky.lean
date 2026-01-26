/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Emilie Uthaiwat
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal

/-!

# Kaplansky criterion for factoriality

We prove Kaplansky criterion for factoriality: an integral domain is a UFD if and only if every
nonzero prime ideal contains a prime element.

## Main declarations

`iff_exists_prime_mem_of_isPrime`: an integral domain is a UFD if and only if every nonzero prime
ideal contains a prime element.

-/

variable {R : Type*}

namespace UniqueFactorizationMonoid

open Set Ideal Submonoid

/-- The set of ideals of a semiring `R` that are disjoint from a given subsemigroup `S`. -/
def kaplanskySet [Semiring R] (S : Subsemigroup R) := {I : Ideal R | Disjoint (I : Set R) S}

section semiring

variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}

theorem mem_kaplanskySet_iff : P ∈ kaplanskySet S ↔ (P : Set R) ∩ S = ∅ :=
  disjoint_iff_inter_eq_empty

/-- If `0 ∉ S`, then every chain in `kaplanskySet S` has an upper bound. -/
theorem exists_mem_kaplanskySet_le {C : Set (Ideal R)} (hS : 0 ∉ S) (hC : C ⊆ kaplanskySet S)
      (hC₂ : IsChain (· ≤ ·) C) : ∃ P ∈ kaplanskySet S, ∀ J ∈ C, J ≤ P := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨_, hI⟩
  · exact ⟨⊥, by simpa [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem]⟩
  · refine ⟨sSup C, ?_, fun _ hz ↦ le_sSup hz⟩
    rw [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem]
    intro x hx
    rcases (Submodule.mem_sSup_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
    have hx₂ : (J : Set R) ∩ S ≠ ∅ := nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
    exact hx₂ (mem_kaplanskySet_iff.mp (hC hJ₁))

/-- If `0 ∉ S`, then there is a maximal element in `kaplanskySet S`. -/
theorem exists_mem_kaplanskySet_eq_of_le (hS : 0 ∉ S) :
    ∃ P ∈ kaplanskySet S, ∀ I ∈ kaplanskySet S, P ≤ I → I = P := by
  obtain ⟨P, hP⟩ := zorn_le₀ (kaplanskySet S) (fun _ ↦ exists_mem_kaplanskySet_le hS)
  exact ⟨P, hP.1, fun _ hI H ↦ le_antisymm (hP.2 hI H) H⟩

end semiring

section IsDomain

variable [CommSemiring R] [IsDomain R]

theorem span_notMem_kaplanskySet {a : R} (ha : a ≠ 0)
      (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) :
    span {a} ∉ kaplanskySet (closure {r : R | Prime r}).toSubsemigroup := by
  have hzero : 0 ∉ closure {r : R | Prime r} := fun h ↦ by
    rcases exists_multiset_of_mem_closure h with ⟨l, hl, hprod⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_mem_kaplanskySet_eq_of_le hzero with ⟨T, hT, hT₂⟩
  have hT₃ : T ≠ ⊥ := fun h₂ ↦ ha (span_singleton_eq_bot.1 ((h₂ ▸ hT₂) _ h (zero_le _)))
  have Tpri := isPrime_of_maximally_disjoint T _ hT (fun J hJ H ↦ hJ.ne (hT₂ J H hJ.le).symm)
  rcases (H T) hT₃ Tpri with ⟨x, H₃, H₄⟩
  rw [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem] at hT
  exact hT x ⟨H₃, subset_closure H₄⟩

/-- The nontrivial implication of Kaplansky's criterion: an integral domain is a UFD if every
nonzero prime ideal contains a prime element. -/
theorem of_exists_prime_mem_of_isPrime
    (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) : UniqueFactorizationMonoid R := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ ?_
  have ha₂ := span_notMem_kaplanskySet ha H
  rw [mem_kaplanskySet_iff] at ha₂
  rcases nonempty_iff_ne_empty.2 ha₂ with ⟨x, hx, hx₂⟩
  obtain ⟨b, hb⟩ := mem_span_singleton'.1 hx
  rw [← hb, mul_comm] at hx₂
  have hsubset : closure {r : R | Prime r} ≤ closure {r : R | IsUnit r ∨ Prime r} :=
    closure_mono (by grind)
  have := divisor_closure_eq_closure _ _ (hsubset hx₂)
  clear ha ha₂ hx hb hx₂
  induction this using closure_induction with
  | mem z hz =>
      rcases hz with h | h
      · exact ⟨∅, by simpa using (associated_one_iff_isUnit.2 h).symm⟩
      · exact ⟨{z}, by simpa⟩
  | one => exact ⟨∅, by simp⟩
  | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
      obtain ⟨S₁, hS₁pri, hS₁⟩ := h₁
      obtain ⟨S₂, hS₂pri, hS₂⟩ := h₂
      refine ⟨S₁ + S₂, by grind, ?_⟩
      rw [Multiset.prod_add]
      exact hS₁.mul_mul hS₂

/-- Kaplansky's criterion: an integral domain is a UFD if and only if every nonzero prime ideal
contains a prime element. -/
public theorem iff_exists_prime_mem_of_isPrime :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x :=
  ⟨fun _ _ hI hI₂ ↦ hI₂.exists_mem_prime_of_ne_bot hI,
    fun H ↦ of_exists_prime_mem_of_isPrime H⟩

end IsDomain

end UniqueFactorizationMonoid
