/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Jacobson.Radical
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

lemma Ring.krullDimLE_iff {n : ℕ} :
    KrullDimLE n R ↔ ringKrullDim R ≤ n := Order.krullDimLE_iff n (PrimeSpectrum R)

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

/-- A ring has finite Krull dimension if its `PrimeSpectrum` is
finite-dimensional (and non-empty). -/
abbrev FiniteRingKrullDim (R : Type*) [CommSemiring R] :=
  FiniteDimensionalOrder (PrimeSpectrum R)

lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
    ringKrullDim R ≠ ⊤ :=
  (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2

lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
    ringKrullDim R < ⊤ := ringKrullDim_ne_top.lt_top

lemma finiteRingKrullDim_iff_ne_bot_and_top :
    FiniteRingKrullDim R ↔ (ringKrullDim R ≠ ⊥ ∧ ringKrullDim R ≠ ⊤) :=
  (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

section Zero

-- See `Mathlib/RingTheory/KrullDimension/Zero.lean` for further results.

lemma Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ ∀ I : Ideal R, I.IsPrime → I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

lemma Ring.KrullDimLE.mk₀ (H : ∀ I : Ideal R, I.IsPrime → I.IsMaximal) : Ring.KrullDimLE 0 R := by
  rwa [Ring.krullDimLE_zero_iff]

lemma Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

/-- Also see `Ideal.IsPrime.isMaximal` for the analogous statement for dedekind domains. -/
lemma Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

instance (priority := 100) (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R] : I.IsMaximal :=
  I.isMaximal_of_isPrime

lemma Ideal.isMaximal_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : I.IsMaximal ↔ I.IsPrime :=
  ⟨IsMaximal.isPrime, fun _ ↦ inferInstance⟩

lemma Ideal.mem_minimalPrimes_of_krullDimLE_zero [Ring.KrullDimLE 0 R]
    (I : Ideal R) [I.IsPrime] : I ∈ minimalPrimes R :=
  minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI ↦ (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩

lemma Ideal.mem_minimalPrimes_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} :
    I ∈ minimalPrimes R ↔ I.IsPrime :=
  ⟨(·.1.1), fun _ ↦ I.mem_minimalPrimes_of_krullDimLE_zero⟩

theorem nilradical_le_jacobson (R) [CommRing R] : nilradical R ≤ Ring.jacobson R :=
  nilradical_eq_sInf R ▸ le_sInf fun _I hI ↦ sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)

theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] :
    jacobson R = nilradical R :=
  (nilradical_le_jacobson R).antisymm' <| nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) ↦
    sInf_le Ideal.IsMaximal.out

end Zero

section One

instance [Ring.KrullDimLE 0 R] : Ring.KrullDimLE 1 R := .mono zero_le_one _

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

lemma Ring.krullDimLE_one_iff_of_noZeroDivisors [NoZeroDivisors R] :
    Ring.KrullDimLE 1 R ↔ ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal := by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h ↦ (h <| Subsingleton.elim ..).elim
  have := Ideal.bot_prime (α := R)
  exact Ring.krullDimLE_one_iff_of_isPrime_bot

/-- Alternative constructor for `Ring.KrullDimLE 1`, convenient for domains. -/
lemma Ring.KrullDimLE.mk₁' (H : ∀ I : Ideal R, I ≠ ⊥ → I.IsPrime → I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI ↦ H I (fun e ↦ hR (e ▸ hI)) hI

end One
