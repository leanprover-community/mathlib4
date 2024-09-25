/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Order.Irreducible
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Noetherian

/-!
# Lasker ring

A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into finitely
many primary ideals.

## Implementation details

There is a generalization for submodules that needs to be implemented.

-/

section IsLasker

variable (R : Type*) [CommSemiring R]

/-- A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
finitely many primary ideals.-/
def IsLasker : Prop :=
  ∀ I : Ideal R, ∃ s : Finset (Ideal R), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

end IsLasker

namespace Ideal

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

lemma isPrimary_of_infIrred {I : Ideal R} (h : InfIrred I) : I.IsPrimary := by
  refine ⟨h.ne_top, fun {a b} hab ↦ ?_⟩
  let f : ℕ → Ideal R := fun n ↦ (I.colon (span {b ^ n}))
  have hf : Monotone f := by
    intro n m hnm
    simp_rw [f]
    exact (Submodule.colon_mono le_rfl (Ideal.span_singleton_le_span_singleton.mpr
      (pow_dvd_pow b hnm)))
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr ‹_› ⟨f, hf⟩
  rcases h with ⟨-, h⟩
  specialize @h (I.colon (span {b ^ n})) (I + (span {b ^ n})) ?_
  · refine le_antisymm ?_ (le_inf ?_ ?_)
    · intro r
      simp only [Submodule.add_eq_sup, sup_comm I, mem_inf, mem_colon_singleton,
        mem_span_singleton_sup, and_imp, forall_exists_index]
      rintro hrb t s hs rfl
      refine add_mem ?_ hs
      have := hn (n + n) (by simp)
      simp only [OrderHom.coe_mk, f] at this
      rw [add_mul, mul_assoc, ← pow_add] at hrb
      rwa [← mem_colon_singleton, this, mem_colon_singleton,
           ← Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ hs)]
    · intro
      simpa only [mem_colon_singleton] using mul_mem_right _ _
    · simp
  rcases h with (h|h)
  · replace h : I = I.colon (span {b}) := by
      rcases eq_or_ne n 0 with rfl|hn'
      · simpa [f] using hn 1 zero_le_one
      refine le_antisymm ?_ (h.le.trans' (Submodule.colon_mono le_rfl ?_))
      · intro
        simpa only [mem_colon_singleton] using mul_mem_right _ _
      · exact span_singleton_le_span_singleton.mpr (dvd_pow_self b hn')
    rw [← mem_colon_singleton, ← h] at hab
    exact Or.inl hab
  · rw [← h]
    refine Or.inr ⟨n, ?_⟩
    simpa using mem_sup_right (mem_span_singleton_self _)

lemma exists_isPrimary_decomposition (I : Ideal R) :
    ∃ s : Finset (Ideal R), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary :=
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦
    isPrimary_of_infIrred (h' ht)

variable (R)

lemma isLasker : IsLasker R := exists_isPrimary_decomposition

end Noetherian

end Ideal
