import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingOfDefinition.BaseChange

namespace Algebra

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

lemma Ideal.mem_span' (S : Set R) (x : R) (hx : x ∈ Ideal.span S) : ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 1 ∧ MvPolynomial.eval Subtype.val p = x := by
  refine Submodule.span_induction hx ?_ ?_ ?_ ?_
  · intro s hs
    exact ⟨MvPolynomial.X ⟨s, hs⟩, MvPolynomial.isHomogeneous_X _ _, by simp⟩
  · exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, by simp⟩
  · rintro x y ⟨px, hpxhom, rfl⟩ ⟨py, hpyhom, rfl⟩
    exact ⟨px + py, MvPolynomial.IsHomogeneous.add hpxhom hpyhom, by simp⟩
  · rintro a x ⟨px, hpxhom, rfl⟩
    exact ⟨MvPolynomial.C a * px, MvPolynomial.IsHomogeneous.C_mul hpxhom a, by simp⟩

lemma Ideal.mem_span_pow' {n : ℕ} (S : Set R) (x : R) :
    x ∈ (Ideal.span S) ^ n ↔ ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p n ∧ MvPolynomial.eval Subtype.val p = x := by
  constructor
  · revert x
    apply Nat.caseStrongInductionOn n
    · intro x _
      exact ⟨MvPolynomial.C x, MvPolynomial.isHomogeneous_C _ _, by simp⟩
    · intro n ih x h
      refine Submodule.smul_induction_on h ?_ ?_
      · intro r hr t ht
        obtain ⟨pr, hprhom, rfl⟩ := ih n (by omega) r hr
        obtain ⟨pt, hpthom, rfl⟩ := Ideal.mem_span' S t ht
        exact ⟨pr * pt, MvPolynomial.IsHomogeneous.mul hprhom hpthom, by simp⟩
      · rintro x y ⟨px, hpxhom, rfl⟩ ⟨py, hpyhom, rfl⟩
        exact ⟨px + py, MvPolynomial.IsHomogeneous.add hpxhom hpyhom, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    rw [← p.sum_single, map_finsupp_sum, Finsupp.sum]
    apply sum_mem
    rintro c hc
    simp only [MvPolynomial.single_eq_monomial, MvPolynomial.eval_monomial]
    apply Ideal.mul_mem_left
    rw [← @hp c (by simpa using hc), MvPolynomial.weightedDegree_one,
      MvPolynomial.degree, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
    apply Ideal.prod_mem_prod
    exact fun x _ ↦ Ideal.pow_mem_pow (Ideal.subset_span x.2) _

lemma Ideal.mem_sq (I : Ideal R) (S : Set R) (hsp : I = Ideal.span S) (x : R) :
  x ∈ I ^ 2 ↔ ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 2 ∧ MvPolynomial.eval Subtype.val p = x := by
  subst hsp
  exact Ideal.mem_span_pow' S x

lemma Ideal.mem_span_iff (I : Ideal R) (S : Set R) (hsp : I = Ideal.span S) (x : R) :
  x ∈ I ↔ ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 1 ∧ MvPolynomial.eval Subtype.val p = x := by
  subst hsp
  have : Ideal.span S = Ideal.span S ^ 1 := by
    simp
  rw [this]
  exact Ideal.mem_span_pow' (n := 1) S x

theorem MvPolynomial.C_comp_subringSubtype {σ : Type*} (T : Subring R) :
    MvPolynomial.C.comp T.subtype = (MvPolynomial.map (σ := σ) T.subtype).comp MvPolynomial.C := by
  ext
  simp
