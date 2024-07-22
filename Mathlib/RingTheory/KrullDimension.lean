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
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.


## Main definitions and results

* `ringKrullDim`: The ring theoretic Krull dimension of a commutative ring.

* `ringKrullDim_eq_topologicalKrullDim`: The ring theoretic Krull dimension of a commutative ring
is equal to the topological Krull dimension of its prime spectrum.

* `ringKrullDim_eq_zero_iff_isField_of_isDomain`: The Krull dimension of an integral domain is zero
if and only if it is a field.
-/

/--
The ring theoretic Krull dimension is the Krull dimension of its spectrum ordered by inclusion.
-/
noncomputable def ringKrullDim (R : Type*) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

variable {R S : Type*} [CommRing R] [CommRing S]

@[nontriviality]
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot_of_isEmpty

lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
    0 ≤ ringKrullDim R :=
  krullDim_nonneg_of_nonempty

theorem ringKrullDim_eq_topologicalKrullDim :
    ringKrullDim R = topologicalKrullDim (PrimeSpectrum R) :=
  Eq.symm <| krullDim_orderDual.symm.trans <| krullDim_eq_of_orderIso
  (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm

/-- If `f : R →+* S` is surjective, then `ringKrullDim S ≤ ringKrullDim R`. -/
theorem ringKrullDim_le_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (PrimeSpectrum.comap f) (Monotone.strictMono_of_injective
    (fun _ _ hab ↦ Ideal.comap_mono hab) (PrimeSpectrum.comap_injective_of_surjective f hf))

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

section DimensionZero

theorem Ideal.IsPrime.isMaximal_of_ringKrullDim_eq_zero
    {I : Ideal R} (hI : I.IsPrime) (hdim : ringKrullDim R = 0) :
    I.IsMaximal :=
  (PrimeSpectrum.isMaximal_iff ⟨I, _⟩).2 <| mem_maximals_of_krullDim_eq_zero hdim ⟨I, hI⟩

theorem ringKrullDim_eq_zero_iff_forall_isMaximal [Nontrivial R] :
    ringKrullDim R = 0 ↔ ∀ (I : Ideal R), I.IsPrime → I.IsMaximal := by
  refine krullDim_eq_zero_iff_mem_maximals_of_nonempty.trans ?_
  simp_rw [← PrimeSpectrum.isMaximal_iff]
  exact ⟨(· ⟨·, ·⟩), (· _ <| PrimeSpectrum.isPrime ·)⟩

theorem Ideal.IsPrime.mem_minimalPrimes_of_ringKrullDim_eq_zero
    {I : Ideal R} (hI : I.IsPrime) (hdim : ringKrullDim R = 0) :
    I ∈ minimalPrimes R :=
  (PrimeSpectrum.mem_minimalPrimes_iff ⟨I, _⟩).2 <| mem_minimals_of_krullDim_eq_zero hdim ⟨I, hI⟩

theorem ringKrullDim_eq_zero_iff_forall_mem_minimalPrimes [Nontrivial R] :
    ringKrullDim R = 0 ↔ ∀ (I : Ideal R), I.IsPrime → I ∈ minimalPrimes R := by
  refine krullDim_eq_zero_iff_mem_minimals_of_nonempty.trans ?_
  simp_rw [← PrimeSpectrum.mem_minimalPrimes_iff]
  exact ⟨(· ⟨·, ·⟩), (· _ <| PrimeSpectrum.isPrime ·)⟩

end DimensionZero

section Field

@[simp]
theorem ringKrullDim_eq_zero_of_field (F : Type*) [Field F] : ringKrullDim F = 0 :=
  krullDim_eq_zero_of_unique

theorem ringKrullDim_eq_zero_of_isField {F : Type*} [CommRing F] (hF : IsField F) :
    ringKrullDim F = 0 :=
  @krullDim_eq_zero_of_unique _ _ <| @PrimeSpectrum.instUnique _ hF.toField

attribute [local instance] Ideal.bot_prime

theorem ringKrullDim_eq_zero_iff_isField_of_isDomain [IsDomain R] :
    ringKrullDim R = 0 ↔ IsField R := by
  simp only [ringKrullDim_eq_zero_iff_forall_mem_minimalPrimes, minimalPrimes,
    Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
    ← not_iff_comm.mp Ring.not_isField_iff_exists_prime, ne_eq, not_exists, not_and, not_imp_not]

end Field

proof_wanted Polynomial.ringKrullDim_le :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n
