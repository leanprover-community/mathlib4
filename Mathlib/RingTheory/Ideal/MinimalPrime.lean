/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Order.Minimal

#align_import ring_theory.ideal.minimal_prime from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal

## Main results
- `Ideal.minimalPrimes`: `I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
- `minimalPrimes`: `minimalPrimes R` is the set of minimal primes of `R`.
- `Ideal.exists_minimalPrimes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `Ideal.radical_minimalPrimes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `Ideal.sInf_minimalPrimes`: The intersection of minimal primes over `I` is `I.radical`.
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.
- `Localization.AtPrime.prime_unique_of_minimal`: When localizing at a minimal prime ideal `I`,
  the resulting ring only has a single prime ideal.

-/


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (I J : Ideal R)

/-- `I.minimalPrimes` is the set of ideals that are minimal primes over `I`. -/
protected def Ideal.minimalPrimes : Set (Ideal R) :=
  minimals (· ≤ ·) { p | p.IsPrime ∧ I ≤ p }
#align ideal.minimal_primes Ideal.minimalPrimes

variable (R) in
/-- `minimalPrimes R` is the set of minimal primes of `R`.
This is defined as `Ideal.minimalPrimes ⊥`. -/
def minimalPrimes : Set (Ideal R) :=
  Ideal.minimalPrimes ⊥
#align minimal_primes minimalPrimes

lemma minimalPrimes_eq_minimals : minimalPrimes R = minimals (· ≤ ·) (setOf Ideal.IsPrime) :=
  congr_arg (minimals (· ≤ ·)) (by simp)

variable {I J}

theorem Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.minimalPrimes, p ≤ J := by
  suffices
    ∃ m ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ OrderDual.ofDual p },
      OrderDual.toDual J ≤ m ∧ ∀ z ∈ { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ p }, m ≤ z → z = m by
    obtain ⟨p, h₁, h₂, h₃⟩ := this
    simp_rw [← @eq_comm _ p] at h₃
    exact ⟨p, ⟨h₁, fun a b c => le_of_eq (h₃ a b c)⟩, h₂⟩
  apply zorn_nonempty_partialOrder₀
  swap
  · refine ⟨show J.IsPrime by infer_instance, e⟩
  rintro (c : Set (Ideal R)) hc hc' J' hJ'
  refine
    ⟨OrderDual.toDual (sInf c),
      ⟨Ideal.sInf_isPrime_of_isChain ⟨J', hJ'⟩ hc'.symm fun x hx => (hc hx).1, ?_⟩, ?_⟩
  · rw [OrderDual.ofDual_toDual, le_sInf_iff]
    exact fun _ hx => (hc hx).2
  · rintro z hz
    rw [OrderDual.le_toDual]
    exact sInf_le hz
#align ideal.exists_minimal_primes_le Ideal.exists_minimalPrimes_le

@[simp]
theorem Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes := by
  rw [Ideal.minimalPrimes, Ideal.minimalPrimes]
  ext p
  refine ⟨?_, ?_⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  · refine ⟨⟨a, a.radical_le_iff.1 ha⟩, ?_⟩
    simp only [Set.mem_setOf_eq, and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
  · refine ⟨⟨a, a.radical_le_iff.2 ha⟩, ?_⟩
    simp only [Set.mem_setOf_eq, and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.1 h3) h4
#align ideal.radical_minimal_primes Ideal.radical_minimalPrimes

@[simp]
theorem Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical := by
  rw [I.radical_eq_sInf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_sInf] at hx ⊢
    rintro J ⟨e, hJ⟩
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    exact hp' (hx hp)
  · apply sInf_le_sInf _
    intro I hI
    exact hI.1.symm
#align ideal.Inf_minimal_primes Ideal.sInf_minimalPrimes

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective {f : R →+* S}
    (hf : Function.Injective f) (p) (H : p ∈ minimalPrimes R) :
    ∃ p' : Ideal S, p'.IsPrime ∧ p'.comap f = p := by
  have := H.1.1
  have : Nontrivial (Localization (Submonoid.map f p.primeCompl)) := by
    refine ⟨⟨1, 0, ?_⟩⟩
    convert (IsLocalization.map_injective_of_injective p.primeCompl (Localization.AtPrime p)
        (Localization <| p.primeCompl.map f) hf).ne one_ne_zero
    · rw [map_one]
    · rw [map_zero]
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization (Submonoid.map f p.primeCompl))
  refine ⟨M.comap (algebraMap S <| Localization (Submonoid.map f p.primeCompl)), inferInstance, ?_⟩
  rw [Ideal.comap_comap, ← @IsLocalization.map_comp _ _ _ _ _ _ _ _ Localization.isLocalization
      _ _ _ _ p.primeCompl.le_comap_map _ Localization.isLocalization,
    ← Ideal.comap_comap]
  suffices _ ≤ p by exact this.antisymm (H.2 ⟨inferInstance, bot_le⟩ this)
  intro x hx
  by_contra h
  apply hM.ne_top
  apply M.eq_top_of_isUnit_mem hx
  apply IsUnit.map
  apply IsLocalization.map_units _ (show p.primeCompl from ⟨x, h⟩)
#align ideal.exists_comap_eq_of_mem_minimal_primes_of_injective Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {I J : Ideal R}

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p := by
  have := H.1.1
  let f' := (Ideal.Quotient.mk I).comp f
  have e : RingHom.ker f' = I.comap f := by
    ext1
    exact Submodule.Quotient.mk_eq_zero _
  have : RingHom.ker (Ideal.Quotient.mk <| RingHom.ker f') ≤ p := by
    rw [Ideal.mk_ker, e]
    exact H.1.2
  suffices _ by
    have ⟨p', hp₁, hp₂⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
      (RingHom.kerLift_injective f') (p.map <| Ideal.Quotient.mk <| RingHom.ker f') this
    refine ⟨p'.comap <| Ideal.Quotient.mk I, Ideal.IsPrime.comap _, ?_, ?_⟩
    · exact Ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)
    · convert congr_arg (Ideal.comap <| Ideal.Quotient.mk <| RingHom.ker f') hp₂
      rwa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk <| RingHom.ker f')
        Ideal.Quotient.mk_surjective, eq_comm, sup_eq_left]
  refine ⟨⟨?_, bot_le⟩, ?_⟩
  · apply Ideal.map_isPrime_of_surjective _ this
    exact Ideal.Quotient.mk_surjective
  · rintro q ⟨hq, -⟩ hq'
    rw [← Ideal.map_comap_of_surjective
        (Ideal.Quotient.mk (RingHom.ker ((Ideal.Quotient.mk I).comp f)))
        Ideal.Quotient.mk_surjective q]
    apply Ideal.map_mono
    apply H.2
    · refine ⟨inferInstance, (Ideal.mk_ker.trans e).symm.trans_le (Ideal.comap_mono bot_le)⟩
    · refine (Ideal.comap_mono hq').trans ?_
      rw [Ideal.comap_map_of_surjective]
      exacts [sup_le rfl.le this, Ideal.Quotient.mk_surjective]
#align ideal.exists_comap_eq_of_mem_minimal_primes Ideal.exists_comap_eq_of_mem_minimalPrimes

theorem Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' ∈ I.minimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.1.1
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.1.2⟩ this).antisymm this
#align ideal.exists_minimal_primes_comap_eq Ideal.exists_minimalPrimes_comap_eq

theorem Ideal.minimal_primes_comap_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    {I J : Ideal S} (h : J ∈ I.minimalPrimes) : J.comap f ∈ (I.comap f).minimalPrimes := by
  have := h.1.1
  refine ⟨⟨inferInstance, Ideal.comap_mono h.1.2⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f ≤ K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this, RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂
#align ideal.mimimal_primes_comap_of_surjective Ideal.minimal_primes_comap_of_surjective

theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes := by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimal_primes_comap_of_surjective hf hJ
#align ideal.comap_minimal_primes_eq_of_surjective Ideal.comap_minimalPrimes_eq_of_surjective

theorem Ideal.minimalPrimes_eq_comap :
    I.minimalPrimes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
  rw [minimalPrimes, ← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
#align ideal.minimal_primes_eq_comap Ideal.minimalPrimes_eq_comap

theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
  ext J
  constructor
  · exact fun H =>
      let e := H.1.1.radical_le_iff.mpr H.1.2
      (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ e).antisymm e
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩
#align ideal.minimal_primes_eq_subsingleton Ideal.minimalPrimes_eq_subsingleton

theorem Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {I} := by
  ext J
  constructor
  · exact fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.1.2).antisymm H.1.2
  · rintro (rfl : J = I)
    exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩
#align ideal.minimal_primes_eq_subsingleton_self Ideal.minimalPrimes_eq_subsingleton_self

end

namespace Localization.AtPrime

variable {R : Type*} [CommSemiring R] {I : Ideal R} [hI : I.IsPrime] (hMin : I ∈ minimalPrimes R)

theorem _root_.IsLocalization.AtPrime.prime_unique_of_minimal {S} [CommSemiring S] [Algebra R S]
    [IsLocalization.AtPrime S I] {J K : Ideal S} [J.IsPrime] [K.IsPrime] : J = K :=
  haveI : Subsingleton {i : Ideal R // i.IsPrime ∧ i ≤ I} := ⟨fun i₁ i₂ ↦ Subtype.ext <| by
    rw [minimalPrimes_eq_minimals] at hMin
    rw [← eq_of_mem_minimals hMin i₁.2.1 i₁.2.2, ← eq_of_mem_minimals hMin i₂.2.1 i₂.2.2]⟩
  Subtype.ext_iff.mp <| (IsLocalization.AtPrime.orderIsoOfPrime S I).injective
    (a₁ := ⟨J, ‹_›⟩) (a₂ := ⟨K, ‹_›⟩) (Subsingleton.elim _ _)

theorem prime_unique_of_minimal (J : Ideal (Localization I.primeCompl)) [J.IsPrime] :
    J = LocalRing.maximalIdeal (Localization I.primeCompl) :=
  IsLocalization.AtPrime.prime_unique_of_minimal hMin

theorem nilpotent_iff_mem_maximal_of_minimal {x : _} :
    IsNilpotent x ↔ x ∈ LocalRing.maximalIdeal (Localization I.primeCompl) := by
  rw [nilpotent_iff_mem_prime]
  exact ⟨(· (LocalRing.maximalIdeal _) (Ideal.IsMaximal.isPrime' _)), fun _ J _ =>
    by simpa [prime_unique_of_minimal hMin J]⟩

theorem nilpotent_iff_not_unit_of_minimal {x : Localization I.primeCompl} :
    IsNilpotent x ↔ x ∈ nonunits _ := by
  simpa only [← LocalRing.mem_maximalIdeal] using nilpotent_iff_mem_maximal_of_minimal hMin

end Localization.AtPrime
