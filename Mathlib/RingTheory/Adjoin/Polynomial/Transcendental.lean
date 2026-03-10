import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Polynomial.Quotient

variable {R S : Type*}

noncomputable section

open Algebra

variable [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

variable {p q : R[X]}

variable (R) in
set_option backward.isDefEq.respectTransparency false in
/-- Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence
between `R[X]` and `Algebra.adjoin R {s}` given by sending `X` to `s`. -/
noncomputable def algEquivOfTranscendental (s : S) (h : Transcendental R s) :
    R[X] ≃ₐ[R] (adjoin R {s}) :=
  AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) <| by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top, _root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
theorem algEquivOfTranscendental_coe (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] →+* (adjoin R {s})) =
    aeval (R := R) (A := adjoin R {s}) ⟨s, self_mem_adjoin_singleton R s⟩ := rfl

@[simp]
theorem algEquivOfTranscendental_apply (s : S) (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (⟨s, self_mem_adjoin_singleton R s⟩) f := rfl

lemma algEquivOfTranscendental_apply_X (s : S) (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = ⟨s, self_mem_adjoin_singleton R s⟩ := by simp

@[simp]
theorem algEquivOfTranscendental_symm_aeval (s : S) (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm
      (aeval (⟨s, self_mem_adjoin_singleton R s⟩) f) = f :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

@[simp]
theorem algEquivOfTranscendental_symm_gen (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm ⟨s, self_mem_adjoin_singleton R s⟩ = X :=
  (algEquivOfTranscendental R s h).toEquiv.injective (by simp)

open Ideal

set_option backward.isDefEq.respectTransparency false in
def algEquivQuotientXOfTranscendental (s : S) (ht : Transcendental R s) :
    (R[X] ⧸ span {(X : R[X])}) ≃ₐ[R]
      adjoin R {s} ⧸ span {(⟨s, self_mem_adjoin_singleton R s⟩ : adjoin R {s})} :=
  quotientEquivAlg _ _ (algEquivOfTranscendental R s ht) (by simp [Ideal.map_span])

@[simp]
theorem algEquivQuotientXOfTranscendental_apply (s : S) (ht : Transcendental R s) :
    algEquivQuotientXOfTranscendental s ht p = algEquivOfTranscendental R s ht p := rfl

@[simp]
theorem Polynomial.aeval_adjoin_gen_eq (R : Type*) {A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] {p : Polynomial R} (x : A) :
    aeval (⟨x, sorry⟩ : Algebra.adjoin R {x}) p = (⟨aeval x p, sorry⟩ : Algebra.adjoin R {x}) := by
  ext; simp


set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem adjoinTranscendentalquotientSpanXAlgEquiv_symm_apply (s : S) (ht : Transcendental R s) :
    (algEquivQuotientXOfTranscendental s ht).symm
      (⟨p.aeval s, aeval_mem_adjoin_singleton R s⟩ : adjoin R {s})
    = (p : R[X] ⧸ span {(X : R[X])}) :=
  (algEquivQuotientXOfTranscendental s ht).injective
    (by simp only [AlgEquiv.apply_symm_apply, algEquivQuotientXOfTranscendental_apply,
      algEquivOfTranscendental_apply]; congr 1; sorry)

end Polynomial

namespace Algebra

open Ideal Polynomial

set_option backward.isDefEq.respectTransparency false in
def algEquivAdjoinQuotient (s : S) (ht : Transcendental R s) :
    (adjoin R {s} ⧸ span {(⟨s, self_mem_adjoin_singleton R s⟩ : adjoin R {s})}) ≃ₐ[R] R :=
  (algEquivQuotientXOfTranscendental s ht).symm.trans (quotientSpanXAlgEquiv)




-- TODO : PR these
theorem Algebra.adjoin_wfDvdMonoid_of_transcendental [UniqueFactorizationMonoid R]
    (ht : Transcendental R y) : WfDvdMonoid (Algebra.adjoin R {y}) :=
  ((algEquivOfTranscendental (R := R) y ht).toMulEquiv.uniqueFactorizationMonoid
    uniqueFactorizationMonoid).toIsWellFounded

instance [UniqueFactorizationMonoid R] [ht : Fact (Transcendental R y)] :
    WfDvdMonoid (Algebra.adjoin R {y}) :=
  Algebra.adjoin_wfDvdMonoid_of_transcendental ht.out

theorem Algebra.adjoin_irreducible_gen_of_transcendental (ht : Transcendental R y)
    [IsDomain R] : Irreducible y' := by
  simpa [← MulEquiv.irreducible_iff (Transcendental.equivPolynomialAdjoin
  (R := R) y ht).toMulEquiv] using irreducible_X (R := R)

def Algebra.adjoinQuotGen (ht : Transcendental R y) :=
  (algEquiv_adjoin_quotient_self ht).toRingHom.comp (Ideal.Quotient.mk (⟪(y : adjoin R {y})⟫))

theorem Algebra.adjoinQuotGen_apply_polynomial (ht : Transcendental R y) :
    (adjoinQuotGen ht) (p.aeval y : adjoin R {y}) = p.aeval 0 := by
  simp [Algebra.adjoinQuotGen, algEquiv_adjoin_quotient_self]

theorem Algebra.adjoinQuotGen_eq_zero_iff (ht : Transcendental R y) (x : adjoin R {y}) :
    ((adjoinQuotGen ht) x = 0 ↔ (y : adjoin R {y}) ∣ x) := by
  simp only [adjoinQuotGen, (AlgEquiv.toRingEquiv_eq_coe), (RingEquiv.toRingHom_eq_coe),
    (AlgEquiv.toRingEquiv_toRingHom), (RingHom.coe_comp), (RingHom.coe_coe), (comp_apply),
    (EmbeddingLike.map_eq_zero_iff), (Quotient.eq_zero_iff_dvd)]

--set_option trace.profiler true in
theorem _root_.Algebra.Quotient_mk_comp_algEquiv_adjoin_quotient_self
    (ht : Transcendental R y) (p : R[X]) :
    (algEquiv_adjoin_quotient_self ht) ((p.aeval y : adjoin R {y}) : _ ⧸ ⟪(y : adjoin R {y})⟫) =
      p.aeval 0 := by
  simp [algEquiv_adjoin_quotient_self, (AlgEquiv.trans_apply)]

end Algebra

open Polynomial

theorem Transcendental.uniqueFactorizationMonoid_adjoin [UniqueFactorizationMonoid R] {s : S}
      (h : Transcendental R s) : UniqueFactorizationMonoid (Algebra.adjoin R {s}) :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance


end
