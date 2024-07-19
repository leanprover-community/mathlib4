/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Topology.KrullDimension

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring theoretic Krull dimension is the order theoretic Krull dimension
applied to its prime spectrum. Unfolding this definition, it is the length of the longest series of
prime ideals ordered by inclusion.


## Main definitions and results

* `ringKrullDim`: the ring theoretic Krull dimension of a commutative ring.

* `ringKrullDim.eq_topologicalKrullDim`: the ring theoretic Krull dimension of a commutative ring
is equal to the topological Krull dimension of its prime spectrum.

* `ringKrullDim.eq_zero_of_field`: the Krull dimension of a field is zero.
-/

/--
The ring theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
noncomputable abbrev ringKrullDim (R : Type*) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

@[nontriviality]
lemma eq_bot_of_subsingleton (R : Type*) [CommRing R] [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot_of_isEmpty

lemma nonneg_of_nontrivial (R : Type*) [CommRing R] [Nontrivial R] :
    0 ≤ ringKrullDim R :=
  krullDim_nonneg_of_nonempty

theorem eq_topologicalKrullDim (R : Type*) [CommRing R] :
    ringKrullDim R = topologicalKrullDim (PrimeSpectrum R) :=
  Eq.symm $ krullDim_orderDual.symm.trans $ krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem le_of_surjective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (PrimeSpectrum.comap f) (Monotone.strictMono_of_injective
    (fun _ _ hab ↦ Ideal.comap_mono hab) (PrimeSpectrum.comap_injective_of_surjective f hf))

/-- If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`. -/
theorem quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim R :=
  le_of_surjective _ Ideal.Quotient.mk_surjective

/-- If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`. -/
theorem eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (le_of_surjective e.symm e.symm.surjective) (le_of_surjective e e.surjective)

section DimensionZero

variable {R : Type _} [CommRing R]

theorem _root_.Ideal.IsPrime.isMaximal_of_ringKrullDim_eq_zero
    {I : Ideal R} (hI : I.IsPrime) (hdim : ringKrullDim R = 0) :
    I.IsMaximal := by
  obtain ⟨J, hJ1, hJ2⟩ := I.exists_le_maximal hI.1
  by_cases hIJ : I = J
  · subst hIJ; exact hJ1
  · let x : LTSeries (PrimeSpectrum R) := ⟨1, ![⟨I, hI⟩, ⟨J, hJ1.isPrime⟩],
      fun i ↦ by fin_cases i; exact ⟨hJ2, fun r ↦ hIJ <| Eq.symm <| hJ1.eq_of_le hI.1 r⟩⟩
    have : 1 ≤ ringKrullDim R :=
      le_iSup (α := WithBot (WithTop ℕ)) (f := fun x : LTSeries _ ↦ x.length) x
    rw [hdim] at this
    norm_num at this

theorem _root_.Ideal.IsPrime.mem_minimalPrimes_of_ringKrullDim_eq_zero
    {I : Ideal R} (hI : I.IsPrime) (hdim : ringKrullDim R = 0) :
    I ∈ minimalPrimes R := by
  obtain ⟨p, hp, le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I) bot_le
  by_cases hIp : I = p
  · subst hIp; exact hp
  · let x : LTSeries (PrimeSpectrum R) := ⟨1, ![⟨p, hp.1.1⟩, ⟨I, hI⟩],
      fun i ↦ by fin_cases i; exact ⟨le, by contrapose! hIp; exact le_antisymm hIp le⟩⟩
    have : 1 ≤ ringKrullDim R :=
      le_iSup (α := WithBot (WithTop ℕ)) (f := fun x : LTSeries _ ↦ x.length) x
    rw [hdim] at this
    norm_num at this

end DimensionZero

section Field

theorem eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique

theorem eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) : ringKrullDim F = 0 :=
  @krullDim_eq_zero_of_unique _ _ <| @PrimeSpectrum.instUnique _ hF.toField

end Field

end ringKrullDim

proof_wanted Polynomial.ringKrullDim_le (R : Type*) [CommRing R] :
  ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
  ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n
