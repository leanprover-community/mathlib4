/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Noetherian
import Mathlib.RingTheory.Jacobson

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

variable {R : Type*} [CommRing R] [IsJacobsonRing R]

namespace PrimeSpectrum

lemma exists_isClosed_singleton_of_isJacobsonRing
    (s : (Set (PrimeSpectrum R))) (hs : IsOpen s) (hs' : s.Nonempty) :
    ∃ x ∈ s, IsClosed {x} := by
  simp_rw [isClosed_singleton_iff_isMaximal]
  obtain ⟨I, hI'⟩ := (isClosed_iff_zeroLocus_ideal _).mp hs.isClosed_compl
  simp_rw [← @Set.not_mem_compl_iff _ s, hI', mem_zeroLocus]
  have := hs'.ne_empty
  contrapose! this
  simp_rw [not_imp_not] at this
  rw [← Set.compl_univ, eq_compl_comm, hI', eq_comm, ← zeroLocus_bot,
    zeroLocus_eq_iff, Ideal.radical_eq_jacobson, Ideal.radical_eq_jacobson]
  refine le_antisymm (le_sInf ?_) (Ideal.jacobson_mono bot_le)
  rintro x ⟨-, hx⟩
  exact sInf_le ⟨this ⟨x, hx.isPrime⟩ hx, hx⟩

/--
If `R` is both noetherian and jacobson, then the following are equivalent for `x : Spec R`:
1. `{x}` is open (i.e. `x` is an isolated point)
2. `{x}` is clopen
3. `{x}` is both closed and stable under generalization
  (i.e. `x` is both a minimal prime and a maximal ideal)
-/
lemma isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing
    [IsNoetherianRing R] (x : PrimeSpectrum R) :
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
