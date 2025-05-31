/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.Order.Minimal

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

Further results that need the theory of localizations can be found in
`RingTheory/Ideal/Minimal/Localization.lean`.

-/

assert_not_exists Localization -- See `RingTheory/Ideal/Minimal/Localization.lean`

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (I J : Ideal R)

/-- `I.minimalPrimes` is the set of ideals that are minimal primes over `I`. -/
protected def Ideal.minimalPrimes : Set (Ideal R) :=
  {p | Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) p}

variable (R) in
/-- `minimalPrimes R` is the set of minimal primes of `R`.
This is defined as `Ideal.minimalPrimes ⊥`. -/
def minimalPrimes : Set (Ideal R) :=
  Ideal.minimalPrimes ⊥

lemma minimalPrimes_eq_minimals : minimalPrimes R = {x | Minimal Ideal.IsPrime x} :=
  congr_arg Minimal (by simp)

variable {I J}

theorem Ideal.minimalPrimes_isPrime {p : Ideal R} (h : p ∈ I.minimalPrimes) : p.IsPrime :=
  h.1.1

theorem Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I ≤ J) : ∃ p ∈ I.minimalPrimes, p ≤ J := by
  set S := { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I ≤ OrderDual.ofDual p }
  suffices h : ∃ m, OrderDual.toDual J ≤ m ∧ Maximal (· ∈ S) m by
    obtain ⟨p, hJp, hp⟩ := h
    exact ⟨p, ⟨hp.prop, fun q hq hle ↦ hp.le_of_ge hq hle⟩, hJp⟩
  apply zorn_le_nonempty₀
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

theorem Ideal.nonempty_minimalPrimes (h : I ≠ ⊤) : Nonempty I.minimalPrimes := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩

theorem Ideal.eq_bot_of_minimalPrimes_eq_empty (h : I.minimalPrimes = ∅) : I = ⊤ := by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)

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

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {I J : Ideal R}

theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
  ext J
  constructor
  · exact fun H =>
      let e := H.1.1.radical_le_iff.mpr H.1.2
      (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ e).antisymm e
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩

theorem Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {I} := by
  ext J
  constructor
  · exact fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.1.2).antisymm H.1.2
  · rintro (rfl : J = I)
    exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩

variable (R) in
theorem IsDomain.minimalPrimes_eq_singleton_bot [IsDomain R] :
    minimalPrimes R = {⊥} :=
  have := Ideal.bot_prime (α := R)
  Ideal.minimalPrimes_eq_subsingleton_self

end

section

variable {R : Type*} [CommSemiring R]

theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  simp only [Set.notMem_empty, iff_false]
  intro h
  exact h.1.1.ne_top (top_le_iff.mp h.1.2)

theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    rw [e] at hp
    apply Set.notMem_empty _ hp.1
  · rintro rfl
    exact Ideal.minimalPrimes_top

end
