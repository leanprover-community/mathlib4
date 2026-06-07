/-
Copyright (c) 2026 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!

# Existence of polynomials that can represent elements of a subring

-/

@[expose] public section

open MvPolynomial Polynomial

namespace Subring

section Polynomial

theorem exists_polynomial_of_le_range_of_mem_closure
    {A R : Type*} [CommRing A] [CommRing R] {x y : R} {B : Subring R}
    {h : A →+* R} (hB : B ≤ h.range) (hy : y ∈ closure (B.carrier.insert x)) :
    ∃ p : Polynomial A, (p.map h).eval x = y := by
  refine closure_induction (fun y hy => ?_) ?_ ?_ (fun y1 y2 hy1 hy2 ⟨p1, hpy1⟩ ⟨p2, hpy2⟩ => ?_)
    (fun y hy ⟨p, hpy⟩ => ?_) (fun y1 y2 hy1 hy2 ⟨p1, hpy1⟩ ⟨p2, hpy2⟩ => ?_) hy
  · by_cases hyx : y = x
    · exact hyx ▸ ⟨X, Polynomial.map_X h ▸ eval_X⟩
    · obtain ⟨a, hay⟩ := hB <| or_iff_not_imp_left.1 (B.carrier.mem_insert_iff.1 hy) hyx
      exact ⟨C a, Polynomial.map_C h ▸ Polynomial.eval_C (R := R) ▸ hay⟩
  · exact ⟨0, Polynomial.map_zero h ▸ eval_zero⟩
  · exact ⟨1, Polynomial.map_one h ▸ eval_one⟩
  · exact ⟨p1 + p2, p1.map_add h ▸ (p1.map h).eval_add ▸ hpy1 ▸ hpy2 ▸ rfl⟩
  · exact ⟨-p, p.map_neg h ▸ (p.map h).eval_neg x ▸ hpy ▸ rfl⟩
  · exact ⟨p1 * p2, p1.map_mul h ▸ (p1.map h).eval_mul ▸ hpy1 ▸ hpy2 ▸ rfl⟩

theorem exists_polynomial_of_mem_closure {R : Type*} [CommRing R]
    {A : Subring R} {x y : R} (hy : y ∈ closure (A.carrier.insert x)) :
    ∃ p : Polynomial A, (p.map A.subtype).eval x = y :=
  exists_polynomial_of_le_range_of_mem_closure (A.range_subtype.symm ▸ le_refl A) hy

theorem exists_polynomial_of_mem_closure₁ {R : Type*} [CommRing R]
    {A : Subring R} {x y : R} (hy : y ∈ closure (A.carrier.insert x)) :
    ∃ p : Polynomial R, p.eval x = y ∧ ∀ n : ℕ, p.coeff n ∈ A := by
  obtain ⟨p, hp⟩ := exists_polynomial_of_mem_closure hy
  exact ⟨p.map A.subtype, hp, fun n => p.coeff_map A.subtype n ▸
    (le_of_eq A.range_subtype <| RingHom.mem_range_self A.subtype (p.coeff n))⟩

end Polynomial

section MvPolynomial

lemma exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
    {A R σ : Type*} [CommRing A] [CommRing R] {r : R} {S : Set R} {B : Subring R}
    {h : A →+* R} (hB : B ≤ h.range) {f : σ → R} (hS : S ⊆ Set.range f)
    (hr : r ∈ closure (B.carrier ∪ S)) :
    ∃ p : MvPolynomial σ A, (p.map h).eval f = r := by
  refine closure_induction (fun r hr => ?_) ?_ ?_ (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_)
    (fun r _ ⟨p, hpr⟩ => ?_) (fun r s _ _ ⟨p, hpr⟩ ⟨q, hqs⟩ => ?_) hr
  · refine hr.elim (fun hr => ?_) (fun hr => ?_)
    · obtain ⟨a, har⟩ := hB hr
      exact ⟨C a, har ▸ map_C h a ▸ eval_C (h a)⟩
    · obtain ⟨s, _, _⟩ := hS hr
      exact ⟨X s, map_X h s ▸ eval_X s⟩
  · exact ⟨0, (MvPolynomial.map h).map_zero ▸ map_zero _⟩
  · exact ⟨1, (MvPolynomial.map h).map_one ▸ map_one _⟩
  · exact ⟨p + q, (MvPolynomial.map h).map_add p q ▸ MvPolynomial.eval_add (R := R) ▸
      hqs ▸ hpr ▸ rfl⟩
  · exact ⟨-p, (MvPolynomial.map h).map_neg p ▸ MvPolynomial.eval_neg (R := R) .. ▸ hpr ▸ rfl⟩
  · exact ⟨p * q, (MvPolynomial.map h).map_mul p q ▸ MvPolynomial.eval_mul (R := R) ▸
      hqs ▸ hpr ▸ rfl⟩

theorem exists_mvPolynomial_of_mem_closure {R : Type*} [CommRing R]
    {A : Subring R} {r : R} {S : Set R} (hr : r ∈ closure (A.carrier ∪ S)) :
    ∃ p : MvPolynomial S A, (p.map A.subtype).eval Subtype.val = r :=
  exists_mvPolynomial_of_le_range_of_subset_range_of_mem_closure
    (A.range_subtype.symm ▸ le_refl A) (Subtype.range_val ▸ le_refl S) hr

theorem exists_mvPolynomial_of_mem_closure₁ {R : Type*} [CommRing R]
    {A : Subring R} {r : R} {S : Set R} (hr : r ∈ closure (A.carrier ∪ S)) :
    ∃ p : MvPolynomial S R, p.eval Subtype.val = r ∧
      ∀ m : S →₀ ℕ, p.coeff m ∈ A := by
  obtain ⟨p, hp⟩ := exists_mvPolynomial_of_mem_closure hr
  exact ⟨p.map A.subtype, hp, fun m => p.coeff_map A.subtype m ▸ A.subtype_apply _ ▸
    SetLike.coe_mem (coeff m p)⟩

end MvPolynomial

end Subring
