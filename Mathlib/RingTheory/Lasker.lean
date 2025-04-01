/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Order.Irreducible
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Lasker ring

## Main declarations

- `IsLasker`: A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
  finitely many primary ideals.
- `IsLasker.minimal`: Any `I : Ideal R` in a ring `R` satisfying `IsLasker R` can be
  decomposed into primary ideals, such that the decomposition is minimal:
  each primary ideal is necessary, and each primary ideal has an independent radical.
- `Ideal.isLasker`: Every Noetherian commutative ring is a Lasker ring.

## Implementation details

There is a generalization for submodules that needs to be implemented.
Also, one needs to prove that the radicals of minimal decompositions are independent of the
  precise decomposition.

-/

section IsLasker

variable (R : Type*) [CommSemiring R]

/-- A ring `R` satisfies `IsLasker R` when any `I : Ideal R` can be decomposed into
finitely many primary ideals. -/
def IsLasker : Prop :=
  ∀ I : Ideal R, ∃ s : Finset (Ideal R), s.inf id = I ∧ ∀ ⦃J⦄, J ∈ s → J.IsPrimary

variable {R}

namespace Ideal

lemma decomposition_erase_inf [DecidableEq (Ideal R)] {I : Ideal R}
    {s : Finset (Ideal R)} (hs : s.inf id = I) :
    ∃ t : Finset (Ideal R), t ⊆ s ∧ t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  induction s using Finset.strongInductionOn
  rename_i _ s IH
  by_cases H : ∀ J ∈ s, ¬ (s.erase J).inf id ≤ J
  · exact ⟨s, Finset.Subset.rfl, hs, H⟩
  push_neg at H
  obtain ⟨J, hJ, hJ'⟩ := H
  refine (IH (s.erase J) (Finset.erase_ssubset hJ) ?_).imp
    fun t ↦ And.imp_left (fun ht ↦ ht.trans (Finset.erase_subset _ _))
  rw [← Finset.insert_erase hJ] at hs
  simp [← hs, hJ']

open scoped Function -- required for scoped `on` notation

lemma isPrimary_decomposition_pairwise_ne_radical {I : Ideal R}
    {s : Finset (Ideal R)} (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Ideal R), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      (t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical) := by
  classical
  refine ⟨(s.image (fun J ↦ {I ∈ s | I.radical = J.radical})).image fun t ↦ t.inf id,
    ?_, ?_, ?_⟩
  · rw [← hs]
    refine le_antisymm ?_ ?_ <;> intro x hx
    · simp only [Finset.inf_image, CompTriple.comp_eq, Submodule.mem_finset_inf,
      Function.comp_apply, Finset.mem_filter, id_eq, and_imp] at hx ⊢
      intro J hJ
      exact hx J hJ J hJ rfl
    · simp only [Submodule.mem_finset_inf, id_eq, Finset.inf_image, CompTriple.comp_eq,
      Function.comp_apply, Finset.mem_filter, and_imp] at hx ⊢
      intro J _ K hK _
      exact hx K hK
  · simp only [Finset.mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    intro J hJ
    refine isPrimary_finset_inf (i := J) ?_ ?_ (by simp)
    · simp [hJ]
    · simp only [Finset.mem_filter, id_eq, and_imp]
      intro y hy
      simp [hs' hy]
  · intro I hI J hJ hIJ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, exists_exists_and_eq_and] at hI hJ
    obtain ⟨I', hI', hI⟩ := hI
    obtain ⟨J', hJ', hJ⟩ := hJ
    simp only [Function.onFun, ne_eq]
    contrapose! hIJ
    suffices I'.radical = J'.radical by
      rw [← hI, ← hJ, this]
    · rw [← hI, radical_finset_inf (i := I') (by simp [hI']) (by simp), id_eq] at hIJ
      rw [hIJ, ← hJ, radical_finset_inf (i := J') (by simp [hJ']) (by simp), id_eq]

lemma exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition [DecidableEq (Ideal R)]
    {I : Ideal R} {s : Finset (Ideal R)} (hs : s.inf id = I) (hs' : ∀ ⦃J⦄, J ∈ s → J.IsPrimary) :
    ∃ t : Finset (Ideal R), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨t, ht, ht', ht''⟩ := isPrimary_decomposition_pairwise_ne_radical hs hs'
  obtain ⟨u, hut, hu, hu'⟩ := decomposition_erase_inf ht
  exact ⟨u, hu, fun _ hi ↦ ht' (hut hi), ht''.mono hut, hu'⟩

lemma IsLasker.minimal [DecidableEq (Ideal R)] (h : IsLasker R) (I : Ideal R) :
    ∃ t : Finset (Ideal R), t.inf id = I ∧ (∀ ⦃J⦄, J ∈ t → J.IsPrimary) ∧
      ((t : Set (Ideal R)).Pairwise ((· ≠ ·) on radical)) ∧
      (∀ ⦃J⦄, J ∈ t → ¬ (t.erase J).inf id ≤ J) := by
  obtain ⟨s, hs, hs'⟩ := h I
  exact exists_minimal_isPrimary_decomposition_of_isPrimary_decomposition hs hs'

end Ideal

end IsLasker

namespace Ideal

section Noetherian

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

lemma _root_.InfIrred.isPrimary {I : Ideal R} (h : InfIrred I) : I.IsPrimary := by
  rw [Ideal.isPrimary_iff]
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
  · refine le_antisymm (fun r ↦ ?_) (le_inf (fun _ ↦ ?_) ?_)
    · simp only [Submodule.add_eq_sup, sup_comm I, mem_inf, mem_colon_singleton,
        mem_span_singleton_sup, and_imp, forall_exists_index]
      rintro hrb t s hs rfl
      refine add_mem ?_ hs
      have := hn (n + n) (by simp)
      simp only [OrderHom.coe_mk, f] at this
      rw [add_mul, mul_assoc, ← pow_add] at hrb
      rwa [← mem_colon_singleton, this, mem_colon_singleton,
           ← Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ hs)]
    · simpa only [mem_colon_singleton] using mul_mem_right _ _
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

variable (R) in
/-- The Lasker--Noether theorem: every ideal in a Noetherian ring admits a decomposition into
  primary ideals. -/
lemma isLasker : IsLasker R := fun I ↦
  (exists_infIrred_decomposition I).imp fun _ h ↦ h.imp_right fun h' _ ht ↦ (h' ht).isPrimary

end Noetherian

end Ideal
