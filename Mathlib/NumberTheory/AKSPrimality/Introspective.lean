/-
Copyright (c) 2026 metakunt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt
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

open Polynomial Nat Ideal Ideal.Quotient


/-- The introspective relation, currently only useful for the proof of the AKS primality theorem. -/
def Introspective {R : Type*} [CommRing R] (f : R[X]) (e r : ℕ) : Prop :=
  mk (span ({(X : R[X]) ^ r - C 1})) (f ^ e) =
  mk (span ({(X : R[X]) ^ r - C 1})) (f.comp (X ^ e))

namespace Introspective

variable {b d r p a n e : ℕ} {R : Type*}

protected theorem map {S : Type*} [CommRing S] [CommRing R] {f : S[X]}
    (h : Introspective f e r) (g : S →+* R) : Introspective (f.map g) e r := by
  simp only [Introspective] at *
  let g := lift (span {(X : S[X]) ^ r - C 1}) (RingHom.comp (mk (span
      ({(X : R[X]) ^ r - C 1})))  (Polynomial.mapRingHom g)) (by
    intro a ha
    simp only [RingHom.coe_comp, coe_mapRingHom, Function.comp_apply]
    apply eq_zero_iff_mem.mpr
    simp only [Ideal.mem_span_singleton'] at *
    obtain ⟨b , hb⟩ := ha
    use b.map g
    simp [← hb])
  convert congrArg g h
  · simp [g]
  · simp only [lift_mk, RingHom.coe_comp, coe_mapRingHom, Function.comp_apply, g, map_comp]
    congr
    simp

section CommRing

variable [CommRing R] {f g : R[X]}

theorem aeval_of_primitive_roots {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    (h : Introspective f e r) : ∀ μ ∈ (primitiveRoots r K), f.aeval μ ^ e = f.aeval (μ ^ e) := by
  intro μ hμ
  simp only [Introspective] at h
  have hg : ∀ a ∈ span {(X : R[X]) ^ r - C 1}, ((aeval (R := R) μ) : R[X] →+* K) a = 0 := by
    intro a ha
    simp only [RingHom.coe_coe]
    obtain ⟨l , ee⟩ := mem_span_singleton.mp ha
    grind [aeval_sub, aeval_X, (isPrimitiveRoot_of_mem_primitiveRoots hμ).pow_eq_one]
  let g := lift (S := K) (span ({(X : R[X]) ^ r - C 1})) (aeval (R := R) μ) hg
  exact (Iff.mp (Eq.congr (by simp [g]) (by simp [g, aeval_comp]))) (congrArg g h)

@[simp]
protected theorem one (f : R[X]) : Introspective f 1 r := by
  simp [Introspective]

protected theorem X_sub_C {a : ℕ} [Fact n.Prime] [CharP R n] :
    Introspective ((X : R[X]) - C (a : R)) n r := by
  simp only [Introspective]
  apply Ideal.Quotient.eq.mpr
  convert Ideal.zero_mem _
  suffices ((X : R[X]) - C (a : R)) ^ n = ((X : R[X]) ^ n) - C (a : R) by
    simp_all
  change (frobenius _ n) _ = (frobenius _ n) _ - _
  simp

/-- The product of two polynomials is introspective. -/
protected theorem mul (hf : Introspective f e r) (hg : Introspective g e r) :
    Introspective (f * g) e r := by
  simp_all only [Introspective, map_pow, map_mul, mul_comp]
  rw [← hf, ← hg]
  apply Ideal.Quotient.eq.mpr
  convert Ideal.zero_mem _
  grind [mul_pow]

/-- The product of coprime exponents is Introspective. -/
theorem mul_of_coprime (hf : Introspective f e r) (hg : Introspective f d r) (h : e.Coprime r) :
    Introspective f (e * d) r := by
  by_cases hr : r = 0
  · grind
  · simp only [Introspective] at *
    set I := mk (span {(X : R[X]) ^ r - C 1})
    have ⟨w, hw⟩ := mem_span_singleton.mp (Ideal.Quotient.eq.mp hg)
    have hw2 := congrArg₂ comp hw (Eq.refl (X ^ e))
    simp only [sub_comp, pow_comp, map_one, mul_comp, X_comp, one_comp, comp_assoc] at hw2
    obtain ⟨z, hz⟩  : ((X : R[X]) ^ r - 1 ) ∣ ((X ^ e) ^ r - 1) := by
      simp only [← pow_mul]
      by_cases he : 1 < e
      · exact X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd _ (by
          simp only [mem_properDivisors, dvd_mul_left, true_and]
          exact lt_mul_left (by lia) (by lia)) |> dvd_of_mul_right_dvd
      · by_cases he2 : e = 0
        · simp [he2]
        · grind [dvd_refl]
    have h : I ((f ^ e) ^ d) = I (f.comp (X ^ e)) ^ d := congrArg₂ HPow.hPow hf (Eq.refl d)
    rw [pow_mul, h, pow_mul]
    apply Ideal.Quotient.eq.mpr
    apply mem_span_singleton.mpr
    use z * w.comp (X ^ e)
    grind

end CommRing

variable [Field R] [CharP R p] [Fact p.Prime]

private theorem _root_.Ring.isReduced_of_quot_X_pow_of_coprime_sub_one (hcprm : p.Coprime r) :
    IsReduced (R[X] ⧸ span {(X : R[X]) ^ r - C 1}) := by
  apply (isRadical_iff_quotient_reduced _).mp
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by grind)).mpr
  intro s hs
  rw [Ideal.mem_span_singleton] at *
  refine (Squarefree.dvd_pow_iff_dvd ?_ (by lia)).mp hs
  apply Separable.squarefree
  refine separable_X_pow_sub_C 1 ?_ (by simp)
  rw [← cast_zero (R := R)]
  apply ((CharP.natCast_eq_natCast R p).mp).mt
  grind [modEq_zero_iff_dvd, Nat.Prime.coprime_iff_not_dvd Fact.out]

private theorem _root_.Ring.charP_of_quot_X_pow_of_coprime_sub_one (hcprm : p.Coprime r) :
    CharP (R[X] ⧸ span {(X : R[X]) ^ r - C 1}) p  := by
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
      · suffices ((X : R[X]) ^ r - C 1).natDegree = r by lia
        exact natDegree_X_pow_sub_C
      · exact hc
      exact X_pow_sub_C_ne_zero (show 0 < r by lia) _
    grind

set_option backward.isDefEq.respectTransparency false in
theorem of_mul {m : ℕ} (h : Introspective ((X : R[X]) - C (a : R)) (m * p) r)
    (hcprm : p.Coprime r) : Introspective ((X : R[X]) - C (a : R)) m r := by
  have hp : p.Prime := Fact.out
  simp only [Introspective] at h ⊢
  set g : R[X] := (X : R[X]) - C (a : R)
  have rn0 : r ≠ 0 := by grind [coprime_zero_right, prime_one_false]
  rw [pow_mul] at h
  have := Ring.isReduced_of_quot_X_pow_of_coprime_sub_one (R := R) hcprm
  have := Ring.charP_of_quot_X_pow_of_coprime_sub_one (R := R) hcprm
  simp only [map_pow] at h
  replace h : (frobenius _ p) _ = _ := h
  have h2 : mk (span {(X : R[X]) ^ r - C 1}) (g.comp (X ^ (m * p))) =
      frobenius _ p (mk (Ideal.span {(X : R[X]) ^ r - C 1}) (g.comp (X ^ m))) := by
    simp only [frobenius, RingHom.coe_mk, powMonoidHom_apply]
    rw [← map_pow]
    congr
    simp only [sub_comp, X_comp, g]
    nth_rw 1 [← CharP.pow_charP_of_nat a]
    simp [pow_mul, ← frobenius_def p _]
  grind

protected theorem div (h : Introspective ((X : R[X]) - C (a : R)) n r)
    (hd : p ∣ n) (hcprm : p.Coprime r) : Introspective ((X : R[X]) - C (a : R)) (n / p) r := by
  grind [of_mul, Nat.div_mul_cancel hd]

/-- Necessary condition for the auxilliary proof. -/
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
    refine mul_of_coprime ?_ ?_ (by grind [Coprime.pow_left])
    · induction d with
      | zero => simp
      | succ i hi =>
        simp only [map_natCast, pow_succ, mul_comm]
        exact mul_of_coprime Introspective.X_sub_C hi hcprm2
    · induction e with
      | zero => simp
      | succ i hi =>
        simp only [pow_succ, mul_comm]
        refine mul_of_coprime ?_ hi (by grind [Coprime.coprime_div_left])
        have hsx := hs x
        simp only [ofMultiset_apply, Multiset.map_singleton, Multiset.prod_singleton] at hsx
        exact Introspective.div hsx hdiv hcprm2

end Introspective
