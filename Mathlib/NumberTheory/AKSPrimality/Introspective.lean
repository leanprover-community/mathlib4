/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt, Thomas Browning
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Introspective relation

This defines the main relation for the proof as defined in their original paper.

## References


<https://www.cse.iitk.ac.in/users/manindra/algebra/primality_v6.pdf>.

## Main Theorems

- `Introspective.of_multiset`

## Tags

prime number, polynomial prime number test, AKS, Agrawal-Kayal-Saxena, Introspective
-/

@[expose] public section Introspective

open Polynomial in
/-- TODO: Move to the proper file. -/
theorem Polynomial.comp_X_pow {R : Type*} [Semiring R] (k m : ℕ) :
    ((X : R[X]) ^ k).comp (X ^ m) = X ^ (k * m) := by
  simp [← pow_mul, mul_comm]

open Polynomial Nat Ideal Ideal.Quotient
/-- The introspective relation, currently only useful for the proof of the AKS primality theorem. -/
def Introspective {R : Type*} [CommRing R] (f : R[X]) (e r : ℕ) : Prop :=
  AdjoinRoot.mk (X ^ r - 1) (f ^ e)  = .mk _ (f.comp (X ^ e))

namespace Introspective

variable {b d r p a n e : ℕ} {R : Type*}

section CommRing

variable [CommRing R] {f g : R[X]}

protected theorem iff_dvd : Introspective f e r ↔ X ^ r - 1 ∣ f ^ e - f.comp (X ^ e) :=
  AdjoinRoot.mk_eq_mk

protected theorem map {S : Type*} [CommRing S] (h : Introspective f e r) (g : R →+* S) :
    Introspective (f.map g) e r := by
  rw [Introspective.iff_dvd] at *
  simpa [Polynomial.map_comp] using map_dvd g h

theorem dvd_aeval_sub {A : Type*} [CommRing A] [Algebra R A] (x : A) (h : Introspective f e r) :
    x ^ r - 1 ∣ (aeval x) f ^ e - (aeval (x ^ e)) f := by
  rw [Introspective.iff_dvd] at h
  simpa [aeval_comp] using map_dvd (aeval x) h

theorem aeval_of_pow_eq_one {A : Type*} [CommRing A] [Algebra R A]
    (h : Introspective f e r) {μ : A} (hμ : μ ^ r = 1) : f.aeval μ ^ e = f.aeval (μ ^ e) := by
  simpa [hμ, sub_eq_zero] using h.dvd_aeval_sub μ

@[simp]
protected theorem one (f : R[X]) : Introspective f 1 r := by
  simp [Introspective]

protected theorem X_sub_C {a : ℕ} [Fact n.Prime] [CharP R n] :
    Introspective (X - C (a : R)) n r := by
  simp [Introspective.iff_dvd, ← frobenius_def n]

/-- The product of two polynomials is introspective. -/
protected theorem mul (hf : Introspective f e r) (hg : Introspective g e r) :
    Introspective (f * g) e r := by
  simp_all only [Introspective, map_pow, map_mul, mul_comp]
  rw [← hf, ← hg]
  simp [mul_pow]

/-- The product of coprime exponents is Introspective. -/
theorem mul' (hf : Introspective f e r) (hg : Introspective f d r) : Introspective f (e * d) r := by
  simp only [Introspective.iff_dvd] at hg
  simp only [Introspective] at *
  set I := AdjoinRoot.mk ((X : R[X]) ^ r - 1)
  have ⟨w, hw⟩ := hg
  have hw2 := congrArg₂ comp hw (Eq.refl (X ^ e))
  simp only [sub_comp, pow_comp, mul_comp, X_comp, one_comp, comp_assoc] at hw2
  obtain ⟨z, hz⟩ : (X : R[X]) ^ r - 1 ∣ (X ^ e) ^ r - 1 := by
    rw [pow_right_comm]
    exact sub_one_dvd_pow_sub_one (X ^ r) e
  have h : I ((f ^ e) ^ d) = I ((f.comp (X ^ e)) ^ d) := congrArg₂ HPow.hPow hf (Eq.refl d)
  simp only [pow_mul, h, pow_mul, I, AdjoinRoot.mk_eq_mk]
  use z * w.comp (X ^ e)
  grind

end CommRing

variable [Field R] [CharP R p] [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
private theorem _root_.Ring.isReduced_of_quot_X_pow_of_coprime_sub_one (hcprm : p.Coprime r) :
    IsReduced (AdjoinRoot ((X : R[X]) ^ r - 1)) := by
  simp only [AdjoinRoot, ← isRadical_iff_quotient_reduced,
      (Ideal.isRadical_iff_pow_one_lt 2 (by grind))]
  intro s hs
  rw [Ideal.mem_span_singleton] at *
  refine (Squarefree.dvd_pow_iff_dvd ?_ (by lia)).mp hs
  apply Separable.squarefree
  refine separable_X_pow_sub_C 1 ?_ (by simp)
  rw [← cast_zero (R := R)]
  apply ((CharP.natCast_eq_natCast R p).mp).mt
  grind [modEq_zero_iff_dvd, Nat.Prime.coprime_iff_not_dvd Fact.out]

private theorem _root_.Ring.charP_of_quot_X_pow_of_coprime_sub_one (hcprm : p.Coprime r) :
    CharP (AdjoinRoot ((X : R[X]) ^ r - 1)) p  := by
  have : r ≠ 0 := by grind [coprime_zero_right, prime_one_false, Fact.out]
  apply CharP.quotient'
  intro z hz
  by_contra!
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  by_cases hc : y = 0
  · grind
  · have : (z : R[X]).natDegree = 0 := by simp
    have : r ≤ (z : R[X]).natDegree := by
      rw [← hy, natDegree_mul]
      · suffices ((X : R[X]) ^ r - 1).natDegree = r by lia
        exact natDegree_X_pow_sub_C
      · exact hc
      exact X_pow_sub_C_ne_zero (show 0 < r by lia) _
    grind

set_option backward.isDefEq.respectTransparency false in
theorem of_mul {f : R[X]} (hf : f ^ p = f.comp (X ^ p)) {m : ℕ} (h : Introspective f (m * p) r)
    (hcprm : p.Coprime r) : Introspective f m r := by
  have hp : p.Prime := Fact.out
  simp only [Introspective] at h ⊢
  have rn0 : r ≠ 0 := by grind [coprime_zero_right, prime_one_false]
  rw [pow_mul] at h
  have := Ring.isReduced_of_quot_X_pow_of_coprime_sub_one (R := R) hcprm
  have := Ring.charP_of_quot_X_pow_of_coprime_sub_one (R := R) hcprm
  simp only [map_pow] at h
  replace h : (frobenius _ p) _ = _ := h
  have h2 : AdjoinRoot.mk (X ^ r - 1) (f.comp (X ^ (m * p))) =
      frobenius _ p (.mk _ (f.comp (X ^ m))) := by
    simp only [frobenius, RingHom.coe_mk, powMonoidHom_apply]
    rw [← map_pow]
    congr
    rw [mul_comm, ← comp_X_pow, ← comp_assoc, ← hf,pow_comp]
  grind

protected theorem div (h : Introspective (X - C (a : R)) n r)
    (hd : p ∣ n) (hcprm : p.Coprime r) : Introspective (X - C (a : R)) (n / p) r := by
  grind [of_mul, Nat.div_mul_cancel hd]

/-- Necessary condition for the auxilliary proof. TODO: Find right generality of `Fin b` -/
theorem of_multiset (s : Multiset (Fin b)) (hcprm : n.Coprime r)
    (hs : ∀ x : Fin b, Introspective (ofMultiset {(x.val : R)}) n r) (hdiv : p ∣ n) :
    Introspective (ofMultiset (s.map fun x ↦ (x.val : R))) (p ^ d * (n / p) ^ e) r := by
  simp only [ofMultiset_apply]
  have hcprm2 := Coprime.coprime_mul_right (Eq.symm (Nat.mul_div_cancel' hdiv) ▸ hcprm)
  induction s using Multiset.induction_on with
  | empty => simp [Introspective]
  | cons x l h1 =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine Introspective.mul ?_ h1
    clear h1
    refine mul' ?_ ?_
    · induction d with
      | zero => simp
      | succ i hi =>
        simp only [map_natCast, pow_succ, mul_comm]
        exact mul' Introspective.X_sub_C hi
    · induction e with
      | zero => simp
      | succ i hi =>
        simp only [pow_succ, mul_comm]
        refine mul' ?_ hi
        have hsx := hs x
        simp only [ofMultiset_apply, Multiset.map_singleton, Multiset.prod_singleton] at hsx
        exact Introspective.div hsx hdiv hcprm2

end Introspective
