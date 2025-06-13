/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.JacobsonSpace

/-!
# The prime spectrum of a jacobson ring

## Main results
- `PrimeSpectrum.exists_isClosed_singleton_of_isJacobson`:
  The spectrum of a jacobson ring is a jacobson space.
- `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobson`:
  If `R` is both noetherian and jacobson, then the following are equivalent for `x : Spec R`:
  1. `{x}` is open (i.e. `x` is an isolated point)
  2. `{x}` is clopen
  3. `{x}` is both closed and stable under generalization
    (i.e. `x` is both a minimal prime and a maximal ideal)
-/

open Ideal

variable {R : Type*} [CommRing R]

namespace PrimeSpectrum

lemma exists_isClosed_singleton_of_isJacobsonRing [IsJacobsonRing R]
    (s : (Set (PrimeSpectrum R))) (hs : IsOpen s) (hs' : s.Nonempty) :
    ∃ x ∈ s, IsClosed {x} := by
  simp_rw [isClosed_singleton_iff_isMaximal]
  obtain ⟨I, hI'⟩ := (isClosed_iff_zeroLocus_ideal _).mp hs.isClosed_compl
  simp_rw [← @Set.notMem_compl_iff _ s, hI', mem_zeroLocus]
  have := hs'.ne_empty
  contrapose! this
  simp_rw [not_imp_not] at this
  rw [← Set.compl_univ, eq_compl_comm, hI', eq_comm, ← zeroLocus_bot,
    zeroLocus_eq_iff, Ideal.radical_eq_jacobson, Ideal.radical_eq_jacobson]
  refine le_antisymm (le_sInf ?_) (Ideal.jacobson_mono bot_le)
  rintro x ⟨-, hx⟩
  exact sInf_le ⟨this ⟨x, hx.isPrime⟩ hx, hx⟩

instance [IsJacobsonRing R] : JacobsonSpace (PrimeSpectrum R) := by
  rw [jacobsonSpace_iff_locallyClosed]
  rintro S hS ⟨U, Z, hU, hZ, rfl⟩
  simp only [← isClosed_compl_iff, isClosed_iff_zeroLocus_ideal, @compl_eq_comm _ U] at hU hZ
  obtain ⟨⟨I, rfl⟩, ⟨J, rfl⟩⟩ := And.intro hU hZ
  simp only [Set.nonempty_iff_ne_empty, ne_eq, Set.inter_assoc,
    ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset,
    zeroLocus_subset_zeroLocus_iff, Ideal.radical_eq_jacobson, Ideal.jacobson, le_sInf_iff] at hS ⊢
  contrapose! hS
  rintro x ⟨hJx, hx⟩
  exact @hS ⟨x, hx.isPrime⟩ ⟨hJx, (isClosed_singleton_iff_isMaximal _).mpr hx⟩

lemma isJacobsonRing_iff_jacobsonSpace :
    IsJacobsonRing R ↔ JacobsonSpace (PrimeSpectrum R) := by
  refine ⟨fun _ ↦ inferInstance, fun H ↦ ⟨fun I hI ↦ le_antisymm ?_ Ideal.le_jacobson⟩⟩
  rw [← I.isRadical_jacobson.radical]
  conv_rhs => rw [← hI.radical]
  simp_rw [← vanishingIdeal_zeroLocus_eq_radical]
  apply vanishingIdeal_anti_mono
  rw [← H.1 (isClosed_zeroLocus I), (isClosed_zeroLocus _).closure_subset_iff]
  rintro x ⟨hx : I ≤ x.asIdeal, hx'⟩
  show jacobson I ≤ x.asIdeal
  exact sInf_le ⟨hx, (isClosed_singleton_iff_isMaximal _).mp hx'⟩

/--
If `R` is both noetherian and jacobson, then the following are equivalent for `x : Spec R`:
1. `{x}` is open (i.e. `x` is an isolated point)
2. `{x}` is clopen
3. `{x}` is both closed and stable under generalization
  (i.e. `x` is both a minimal prime and a maximal ideal)
-/
lemma isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
    [IsNoetherianRing R] [IsJacobsonRing R] (x : PrimeSpectrum R) :
    List.TFAE [IsOpen {x}, IsClopen {x}, IsClosed {x} ∧ StableUnderGeneralization {x}] := by
  tfae_have 1 → 2
  | h => by
    obtain ⟨y, rfl : y = x, h'⟩ := exists_isClosed_singleton_of_isJacobsonRing _ h
      ⟨x, Set.mem_singleton x⟩
    exact ⟨h', h⟩
  tfae_have 2 → 3
  | h => ⟨h.isClosed, h.isOpen.stableUnderGeneralization⟩
  tfae_have 3 → 1
  | ⟨h₁, h₂⟩ => by
    rw [isClosed_singleton_iff_isMaximal, ← isMax_iff] at h₁
    suffices {x} = (⋃ p ∈ { p : PrimeSpectrum R | IsMin p ∧ p ≠ x }, closure {p})ᶜ by
      rw [this, isOpen_compl_iff]
      refine Set.Finite.isClosed_biUnion ?_ (fun _ _ ↦ isClosed_closure)
      exact (finite_setOf_isMin R).subset fun x h ↦ h.1
    ext p
    simp only [Set.mem_singleton_iff, ne_eq, Set.mem_setOf_eq, Set.compl_iUnion, Set.mem_iInter,
      Set.mem_compl_iff, and_imp, ← specializes_iff_mem_closure, ← le_iff_specializes,
      not_imp_not]
    constructor
    · rintro rfl _ _
      rw [stableUnderGeneralization_singleton, ← isMin_iff] at h₂
      exact h₂.eq_of_le
    · intros hp
      apply h₁.eq_of_ge
      obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le (J := p.asIdeal) bot_le
      exact (hp ⟨q, hq.1.1⟩ (isMin_iff.mpr hq) hq').ge.trans hq'
  tfae_finish

end PrimeSpectrum
