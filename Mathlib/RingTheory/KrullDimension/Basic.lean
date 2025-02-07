/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

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

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

/-- A ring has finite Krull dimension if its Krull dimension is not ⊤ -/
abbrev FiniteRingKrullDim (R : Type*) [CommRing R] := FiniteDimensionalOrder (PrimeSpectrum R)
-- ???

lemma ringKrullDim_ne_top [h : FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊤ := Order.krullDim_ne_top_iff_finiteDimensionalOrder.mpr ‹_›

lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
    ringKrullDim R < ⊤ := Ne.lt_top (ringKrullDim_ne_top)

lemma finiteRingKrullDim_iff_lt :
    FiniteRingKrullDim R ↔ ringKrullDim R < ⊤ := by
  rw [lt_top_iff_ne_top]
  exact (Order.krullDim_ne_top_iff_finiteDimensionalOrder (α := (PrimeSpectrum R))).symm

instance (priority := 100) finiteRingKrullDimOfSubsingleton [Subsingleton R] :
  FiniteRingKrullDim R := by
  rw [finiteRingKrullDim_iff_lt, ringKrullDim_eq_bot_of_subsingleton]
  exact bot_lt_top

proof_wanted Polynomial.ringKrullDim_le :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

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

end One
