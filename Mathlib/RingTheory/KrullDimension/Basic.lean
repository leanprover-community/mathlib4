/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.PrimeSpectrum
import Mathlib.Order.KrullDimension

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
noncomputable def ringKrullDim (R : Type*) [CommRing R] : WithBot ENat :=
  krullDim (PrimeSpectrum R)

variable {R S : Type*} [CommRing R] [CommRing S]

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
theorem ringKrullDim_quotient_le (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

/-- A ring has finite Krull dimension if its Krull dimension is not ⊤ -/
class FiniteRingKrullDim (R : Type*) [CommRing R] : Prop where
  ringKrullDim_ne_top : ringKrullDim R ≠ ⊤

lemma ringKrullDim_ne_top [h : FiniteRingKrullDim R] :
  ringKrullDim R ≠ ⊤ := h.ringKrullDim_ne_top

lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
  ringKrullDim R < ⊤ := by
  exact Ne.lt_top (ringKrullDim_ne_top)

lemma finiteRingKrullDim_iff_lt :
  FiniteRingKrullDim R ↔ ringKrullDim R < ⊤ := by
  constructor
  · intro h
    exact ringKrullDim_lt_top
  · intro h
    exact ⟨ne_top_of_lt h⟩

instance (priority := 100) finiteRingKrullDimalOfSubsingleton [Subsingleton R] :
  FiniteRingKrullDim R := by
  rw [finiteRingKrullDim_iff_lt, ringKrullDim_eq_bot_of_subsingleton]
  exact bot_lt_top

proof_wanted Polynomial.ringKrullDim_le :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n
