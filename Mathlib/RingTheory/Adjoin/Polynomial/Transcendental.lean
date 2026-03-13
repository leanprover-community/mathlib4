/-
Copyright (c) 2026 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández, Miriam Philipp, Justus Springer, Junyan Xu
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Polynomial.Quotient


/-!
# Polynomials and adjoining transcendental elements
-/

@[expose] public noncomputable section

variable {R S : Type*}

open Algebra

variable [CommRing R] [CommRing S] [Algebra R S]

variable (s : S)

namespace Polynomial

variable {p q : R[X]}

variable (R) in
set_option backward.isDefEq.respectTransparency false in
/-- Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `Algebra.adjoin R {s}` given by sending `X` to `s`. -/
noncomputable def algEquivOfTranscendental (h : Transcendental R s) :
    R[X] ≃ₐ[R] (adjoin R {s}) :=
  AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) <| by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
theorem algEquivOfTranscendental_coe (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* adjoin R {s}) =
    aeval (R := R) (A := adjoin R {s}) s := rfl

@[simp]
theorem algEquivOfTranscendental_apply (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (s : adjoin R {s}) f := rfl

lemma algEquivOfTranscendental_apply_X (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = (s : adjoin R {s}) := by simp

@[simp]
theorem algEquivOfTranscendental_symm_aeval (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm (aeval (s : adjoin R {s}) f) = f :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

@[simp]
theorem algEquivOfTranscendental_symm_gen (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm s = X :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

open Ideal

set_option backward.isDefEq.respectTransparency false in
/-- Given a transcendental element `s`, we have an isomorphism
  `R[X] / span X ≃ₐ[R] R[s] / span {s}`. -/
def algEquivQuotientXOfTranscendental (ht : Transcendental R s) :
    (R[X] ⧸ span {(X : R[X])}) ≃ₐ[R] adjoin R {s} ⧸ span {(s : adjoin R {s})} :=
  quotientEquivAlg _ _ (algEquivOfTranscendental R s ht) (by simp [map_span])

@[simp]
theorem algEquivQuotientXOfTranscendental_apply (ht : Transcendental R s) :
    algEquivQuotientXOfTranscendental s ht p = algEquivOfTranscendental R s ht p := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem adjoinTranscendentalquotientSpanXAlgEquiv_symm_apply (ht : Transcendental R s) :
    (algEquivQuotientXOfTranscendental s ht).symm (p.aeval s : adjoin R {s}) = p :=
  (algEquivQuotientXOfTranscendental s ht).injective (by simp)

end Polynomial

namespace Algebra

open Ideal Polynomial

set_option backward.isDefEq.respectTransparency false in
/-- Given a transcendental element `s`, we have an isomorphism `R[s] / span {s} ≃ₐ[R] R`.
This map is equal to evaluation by 0, see _. -/
def algEquivAdjoinQuotient (ht : Transcendental R s) :
    (adjoin R {s} ⧸ span {(s : adjoin R {s})}) ≃ₐ[R] R :=
  (algEquivQuotientXOfTranscendental s ht).symm.trans (quotientSpanXAlgEquiv)

theorem adjoin_irreducible_gen_of_transcendental (ht : Transcendental R s) [IsDomain R] :
    Irreducible (s : adjoin R {s}) := by
  simpa [← MulEquiv.irreducible_iff (algEquivOfTranscendental R s ht)]
    using irreducible_X (R := R)

set_option backward.isDefEq.respectTransparency false in
def adjoinQuotGen (ht : Transcendental R s) :=
  (algEquivAdjoinQuotient s ht).toRingHom.comp (Ideal.Quotient.mk _)

set_option backward.isDefEq.respectTransparency false in
/-- Given a transcendental element `s`, we have a map `R[s] →ₐ[R] R` given
This map is equal to evaluation by 0, see _. -/
@[simp]
theorem adjoinQuotGen_apply_polynomial (p : R[X]) (ht : Transcendental R s) :
    (adjoinQuotGen s ht) (p.aeval s : adjoin R {s}) = p.eval 0 := by
  simp [adjoinQuotGen, algEquivAdjoinQuotient]

set_option backward.isDefEq.respectTransparency false in
theorem adjoinQuotGen_eq_zero_iff_gen_dvd (ht : Transcendental R s) (x : adjoin R {s}) :
    ((adjoinQuotGen s ht) x = 0 ↔ (s : adjoin R {s}) ∣ x) := by
  simp only [adjoinQuotGen, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp, RingHom.coe_coe, (Function.comp_apply),
    EmbeddingLike.map_eq_zero_iff, Quotient.eq_zero_iff_dvd]

end Algebra

open Polynomial

theorem Transcendental.uniqueFactorizationMonoid_adjoin [UniqueFactorizationMonoid R] {s : S}
      (h : Transcendental R s) : UniqueFactorizationMonoid (Algebra.adjoin R {s}) :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

theorem Transcendental.wfDvdMonoid_adjoin [UniqueFactorizationMonoid R]
    (ht : Transcendental R s) : WfDvdMonoid (Algebra.adjoin R {s}) :=
  (Transcendental.uniqueFactorizationMonoid_adjoin ht).toIsWellFounded

instance [UniqueFactorizationMonoid R] {s : S} [h : Fact (Transcendental R s)] :
    UniqueFactorizationMonoid (Algebra.adjoin R {s}) :=
  (Transcendental.uniqueFactorizationMonoid_adjoin h.out)

end
