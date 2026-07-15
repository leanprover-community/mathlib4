/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández, Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Polynomials and adjoining transcendental elements

This file establishes some basic properties about `R[s]` when `s` is transcendental over `R`.
These are mostly just carried over from the polynomial ring `R[X]`.

## Main definitions:
* `Polynomial.algEquivOfTranscendental`: Given a transcendental element `s : S` over `R`, the
  `R`-algebra equivalence between `R[X]` and `R[s]` given by sending `X` to `s`.
* `Algebra.adjoin.evalOfTranscendental`: If `s : S` is transcendental over `R`,
  we get an `R`-algebra homomorphism given by evaluation at some element `c`.

## Main results
* `Transcendental.euclideanDomainAdjoin`: Given a transcendental element `s : S` over `F`, `F[s]`
  is a euclidean domain.
* `Transcendental.uniqueFactorizationMonoid_adjoin`: Given a transcendental element `s : S` over
  `R`, a unique factorization monoid, `R[s]` is a unique factorization monoid as well.
-/

@[expose] public noncomputable section

variable {R S : Type*}

open Algebra

variable [CommRing R] [Ring S] [Algebra R S]

variable (s : S)

namespace Polynomial

variable (R) in
/-- Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `R[s]` given by sending `X` to `s`. -/
def algEquivOfTranscendental (h : Transcendental R s) :
    R[X] ≃ₐ[R] R[s] :=
  AlgEquiv.ofBijective (aeval (s : R[s])) <| by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
theorem algEquivOfTranscendental_coe (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* R[s]) = aeval (R := R) (A := R[s]) s :=
  rfl

@[simp]
theorem algEquivOfTranscendental_apply (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (s : R[s]) f := rfl

lemma algEquivOfTranscendental_apply_X (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = (s : R[s]) := by simp

@[simp]
theorem algEquivOfTranscendental_symm_aeval (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm (aeval (s : R[s]) f) = f :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

@[simp]
theorem algEquivOfTranscendental_symm_gen (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm s = X :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

end Polynomial

namespace Algebra

open Ideal Polynomial

variable {T : Type*} [CommRing T] [Algebra R T] {p : R[X]}

/-- If `s : S` is transcendental over `R`, we get an `R`-algebra homomorphism given by
evaluation at some element `c`.

For the more general case where `s` is not nec. transcendental see `Algebra.adjoin.liftSingleton`.
-/
def adjoin.evalOfTranscendental (ht : Transcendental R s) (c : T) : R[s] →ₐ[R] T :=
  (aeval c).comp (algEquivOfTranscendental R s ht).symm

@[simp]
theorem adjoin.evalOfTranscendental_aeval (ht : Transcendental R s) (c : T) :
    evalOfTranscendental s ht c (p.aeval (s : R[s])) = p.aeval c := by
  simp_all [evalOfTranscendental]

theorem adjoin.evalOfTranscendental_eq_zero_iff (ht : Transcendental R s) (x : R[s]) (c : R) :
    evalOfTranscendental s ht c x = 0 ↔ ((s : R[s]) - algebraMap R R[s] c) ∣ x := by
  simp [evalOfTranscendental, ← map_dvd_iff (algEquivOfTranscendental R s ht).symm,
    Polynomial.dvd_iff_isRoot]

end Algebra

/-! ### Instances
We can not directly get the instances on `R[s]` from `(h : Transcendental R s)` because
it is an explicit argument.

Since this can be cumbersome in a file where these instances are often needed,
we also provide `Fact` versions that are instances.
-/
section instances

open Polynomial

variable {s}

/-- Given a transcendental element `s : S` over `F`, `F[s]` is a euclidean domain. -/
abbrev Transcendental.euclideanDomainAdjoin {F : Type*} [Field F] [Algebra F S]
    (h : Transcendental F s) : EuclideanDomain F[s] :=
  (algEquivOfTranscendental F s h).symm.euclideanDomain

instance {F : Type*} [Field F] [Algebra F S] [h : Fact (Transcendental F s)] :
    EuclideanDomain F[s] :=
  h.out.euclideanDomainAdjoin

variable [UniqueFactorizationMonoid R]

/-- Given a transcendental element `s : S` over `R`, a unique factorization monoid,
`R[s]` is a unique factorization monoid as well. -/
theorem Transcendental.uniqueFactorizationMonoid_adjoin (h : Transcendental R s) :
    UniqueFactorizationMonoid R[s] :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

instance [h : Fact (Transcendental R s)] : UniqueFactorizationMonoid R[s] :=
  h.out.uniqueFactorizationMonoid_adjoin

theorem Transcendental.wfDvdMonoid_adjoin (ht : Transcendental R s) : WfDvdMonoid R[s] :=
  (uniqueFactorizationMonoid_adjoin ht).toIsWellFounded

end instances

end
