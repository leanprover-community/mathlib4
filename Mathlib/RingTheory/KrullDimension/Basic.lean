/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring theoretic Krull dimension is the order theoretic Krull dimension
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.
-/

open Order

/--
The ring theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot ℕ∞ :=
  krullDim (PrimeSpectrum R)

/-- Type class for rings with krull dimension at most `n`. -/
abbrev Ring.KrullDimLE (n : ℕ) (R : Type*) [CommSemiring R] : Prop :=
  Order.KrullDimLE n (PrimeSpectrum R)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

@[nontriviality]
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot

lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
    0 ≤ ringKrullDim R :=
  krullDim_nonneg

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (fun I ↦ ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab ↦ Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

instance {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ)
    [Ring.KrullDimLE n R] : Ring.KrullDimLE n (R ⧸ I) :=
  ⟨(ringKrullDim_quotient_le I).trans KrullDimLE.krullDim_le⟩

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

section Zero

lemma Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

lemma Ring.KrullDimLE.mk₀ (H : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) : Ring.KrullDimLE 0 R := by
  rwa [Ring.krullDimLE_zero_iff]

instance (priority := 100) Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R]
    (I : Ideal R) [I.IsPrime] : I.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

end Zero

section One

lemma Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔
    ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl

lemma Ideal.mem_minimalPrimes_or_isMaximal [Ring.KrullDimLE 1 R] (I : Ideal R) [I.IsPrime] :
    I ∈ minimalPrimes R ∨ I.IsMaximal :=
  Ring.krullDimLE_one_iff.mp ‹_› I ‹_›

lemma Ring.KrullDimLE.mk₁ (H : ∀ I : Ideal R, I.IsPrime → I ∈ minimalPrimes R ∨ I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  rwa [Ring.krullDimLE_one_iff]

lemma Ring.krullDimLE_one_iff_of_isPrime_bot [(⊥ : Ideal R).IsPrime] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  letI : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, forall_comm (α := _ ≠ ⊥),
    ne_eq, PrimeSpectrum.ext_iff]
  rfl

attribute [local instance] Ideal.bot_prime in
lemma Ring.krullDimLE_one_iff_of_isDomain [IsDomain R] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
  Ring.krullDimLE_one_iff_of_isPrime_bot

/-- Alternative constructor for `Ring.KrullDimLE 1`, convenient for domains. -/
lemma Ring.KrullDimLE.mk₁' (H : ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from .mono zero_le_one _
  exact .mk₀ fun I hI ↦ H I (fun e ↦ hR (e ▸ hI)) hI

lemma Ideal.IsPrime.isMaximal_of_ne_bot [IsDomain R] [Ring.KrullDimLE 1 R]
    {I : Ideal R} (hI : I.IsPrime) (hI' : I ≠ ⊥) : I.IsMaximal :=
  Ring.krullDimLE_one_iff_of_isDomain.mp ‹_› I hI' hI

lemma Ideal.isMaximal_of_isPrime_of_ne_bot [IsDomain R] [Ring.KrullDimLE 1 R]
    (I : Ideal R) [I.IsPrime] (hI' : I ≠ ⊥) : I.IsMaximal :=
  Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hI'

theorem Ring.KrullDimLE.not_lt_lt [Ring.KrullDimLE 1 R] (p₀ p₁ p₂ : Ideal R)
    [p₀.IsPrime] [p₁.IsPrime] [p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂) := by
  rintro ⟨H₁, H₂⟩
  cases' p₁.mem_minimalPrimes_or_isMaximal with h h
  · exact (h.2 ⟨‹p₀.IsPrime›, bot_le⟩ H₁.le).not_lt H₁
  · exact ‹p₂.IsPrime›.ne_top (h.1.2 _ H₂)

@[deprecated (since := "2025-02-05")] alias DimensionLEOne.not_lt_lt := Ring.KrullDimLE.not_lt_lt

attribute [local instance] Ideal.bot_prime in
theorem Ring.KrullDimLE.eq_bot_of_lt [Ring.KrullDimLE 1 R] [IsDomain R] (p P : Ideal R) [p.IsPrime]
    [P.IsPrime] (hpP : p < P) : p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

@[deprecated (since := "2025-02-05")]
alias DimensionLEOne.eq_bot_of_lt := Ring.KrullDimLE.eq_bot_of_lt

theorem Ring.KrullDimLE.le_iff_eq [Ring.KrullDimLE 1 R] [IsDomain R] {p P : Ideal R} [p.IsPrime]
    [P.IsPrime] (hp0 : p ≠ ⊥) : p ≤ P ↔ p = P := by
  rw [le_iff_eq_or_lt, or_iff_left]
  exact fun h ↦ hp0 (eq_bot_of_lt _ _ h)

@[deprecated (since := "2025-02-05")]
alias Ring.DimensionLEOne.prime_le_prime_iff_eq := Ring.KrullDimLE.le_iff_eq

end One
