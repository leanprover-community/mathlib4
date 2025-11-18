/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!

# Krull dimension and non-zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r ∈ R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_length, ringKrullDim,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h ↦ Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r ∈ p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ ↦ id)).cons p' hp'))
  simp

/-- If `R →+* S` is surjective whose kernel contains a nonzero divisor, then `dim S + 1 ≤ dim R`. -/
lemma ringKrullDim_succ_le_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    {r : R} (hr : r ∈ R⁰) (hr' : f r = 0) : ringKrullDim S + 1 ≤ ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
    |>.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in
lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 ≤ ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
@[simp]
lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

open MvPolynomial in
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
    ringKrullDim R + Nat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

open MvPolynomial in
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
    ringKrullDim R + ENat.card σ ≤ ringKrullDim (MvPolynomial σ R) := by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [ENat.some_eq_coe, Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

open PowerSeries in
lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X
