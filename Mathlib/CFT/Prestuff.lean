/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.Localization.AtPrime.Basic
/-! #Stuff -/

@[expose] public section

instance Subalgebra.faithfulSMul_right
    {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]
    (S : Subalgebra R A) : FaithfulSMul R S := .tower_bot R S A

lemma Localization.localRingHom_bijective_of_saturated_inf_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P : Ideal S} [P.IsPrime] {s : Subalgebra R S}
    (H : s.saturation (P.primeCompl ⊓ s.toSubmonoid) (by simp) = ⊤) (p : Ideal s)
    [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr ?_
    suffices ∀ y ∈ s, ∀ z ∉ P, z * y = 0 → ∃ t ∉ P, t ∈ s ∧ t * y = 0 by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff, Subtype.ext_iff] using this
    intro y hys z hzP e
    obtain ⟨t, ⟨htP, _⟩, ht⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, ‹P.IsPrime›.mul_notMem htP hzP, ht, by simp [mul_assoc, e]⟩
  · suffices ∀ y, ∀ z ∉ P, ∃ y' ∈ s, ∃ z' ∉ P, z' ∈ s ∧ ∃ t ∉ P, t * (z * y') = t * (z' * y) by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).exists,
        (IsLocalization.mk'_surjective P.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq, - map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, Function.Surjective] using this
    intro y z hzP
    obtain ⟨a, ⟨haP, has⟩, ha⟩ := H.ge (Set.mem_univ y)
    obtain ⟨b, ⟨hbP, hbs⟩, hb⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, mul_mem ha hbs, _, P.primeCompl.mul_mem (mul_mem hbP hzP) haP, mul_mem hb has, 1,
      P.primeCompl.one_mem, by ring⟩

lemma Localization.localRingHom_bijective_of_not_conductor_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {x : S} {P : Ideal S} [P.IsPrime] (hx : ¬ conductor R x ≤ P) {s : Subalgebra R S}
    (hs : s = Algebra.adjoin R {x}) (p : Ideal s) [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  obtain ⟨a, ha, haP⟩ := SetLike.not_le_iff_exists.mp hx
  replace ha (b : _) : a * b ∈ s := by simpa [hs] using ha b
  exact Localization.localRingHom_bijective_of_saturated_inf_eq_top
    (top_le_iff.mp fun y _ ↦ ⟨a, ⟨haP, by simpa using ha 1⟩, ha _⟩) _
