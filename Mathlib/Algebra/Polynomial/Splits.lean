/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Factors
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Split polynomials

A polynomial `f : K[X]` splits over a field extension `L` of `K` if it is zero or all of its
irreducible factors over `L` have degree `1`.

## Main definitions

* `Polynomial.Splits i f`: A predicate on a homomorphism `i : K →+* L` from a commutative ring to a
  field and a polynomial `f` saying that `f.map i` factors in `L`.

-/

@[expose] public section

noncomputable section

open Polynomial

universe u v w

variable {R : Type*} {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

section Splits

section CommRing

variable [CommRing K] [Field L] [Field F]
variable (i : K →+* L)

@[deprecated (since := "2025-11-24")]
alias splits_zero := Splits.zero

@[deprecated "Use `Splits.C` instead." (since := "2025-11-24")]
theorem splits_of_map_eq_C {f : K[X]} {a : L} (h : f.map i = C a) : Splits (f.map i) :=
  h ▸ Splits.C a

@[deprecated (since := "2025-11-24")]
alias splits_C := Splits.C

@[deprecated (since := "2025-11-24")]
alias splits_of_map_degree_eq_one := Splits.of_degree_eq_one

@[deprecated (since := "2025-11-24")]
alias splits_of_degree_le_one := Splits.of_degree_le_one

@[deprecated (since := "2025-11-24")]
alias splits_of_degree_eq_one := Splits.of_degree_eq_one

@[deprecated (since := "2025-11-24")]
alias splits_of_natDegree_le_one := Splits.of_natDegree_le_one

@[deprecated (since := "2025-11-24")]
alias splits_of_natDegree_eq_one := Splits.of_natDegree_eq_one

@[deprecated (since := "2025-11-25")]
alias splits_mul := Splits.mul

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_mul' := splits_mul_iff

@[deprecated "Use `Polynomial.map_map` instead." (since := "2025-11-24")]
theorem splits_map_iff {L : Type*} [CommRing L] (i : K →+* L) (j : L →+* F) {f : K[X]} :
    Splits ((f.map i).map j) ↔ Splits (f.map (j.comp i)) := by
  rw [Polynomial.map_map]

@[deprecated (since := "2025-11-24")]
alias splits_one := Splits.one

@[deprecated (since := "2025-11-24")]
alias splits_X_sub_C := Splits.X_sub_C

@[deprecated (since := "2025-11-24")]
alias splits_X := Splits.X

@[deprecated (since := "2025-11-24")]
alias splits_prod := Splits.prod

@[deprecated (since := "2025-11-24")]
alias splits_pow := Splits.pow

@[deprecated (since := "2025-11-24")]
alias splits_X_pow := Splits.X_pow

@[deprecated "Use `Polynomial.map_id` instead." (since := "2025-11-24")]
theorem splits_id_iff_splits {f : K[X]} :
    ((f.map i).map (RingHom.id L)).Splits ↔ (f.map i).Splits := by
  rw [map_id]

variable {i}

@[deprecated (since := "2025-11-25")]
alias Splits.comp_of_map_degree_le_one := Splits.comp_of_degree_le_one

variable (i)

@[deprecated (since := "2025-12-01")]
alias exists_root_of_splits' := Splits.exists_eval_eq_zero

@[deprecated (since := "2025-12-01")]
alias roots_ne_zero_of_splits' := Splits.roots_ne_zero

@[deprecated (since := "2025-12-01")]
alias rootOfSplits' := rootOfSplits

@[deprecated (since := "2025-12-01")]
alias map_rootOfSplits' := eval_rootOfSplits

@[deprecated (since := "2025-12-01")]
alias natDegree_eq_card_roots' := Splits.natDegree_eq_card_roots

@[deprecated (since := "2025-12-01")]
alias degree_eq_card_roots' := Splits.degree_eq_card_roots

end CommRing

variable [CommRing R] [Field K] [Field L] [Field F]
variable (i : K →+* L)

/-- This lemma is for polynomials over a field. -/
@[deprecated (since := "2025-11-30")]
alias splits_iff := splits_iff_splits

/-- This lemma is for polynomials over a field. -/
@[deprecated (since := "2025-11-30")]
alias Splits.def := splits_iff_splits

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_mul := splits_mul_iff

@[deprecated (since := "2025-11-25")]
alias splits_of_splits_of_dvd := Splits.of_dvd

@[deprecated "Use `Splits.of_dvd` directly." (since := "2025-11-30")]
theorem splits_of_splits_gcd_left [DecidableEq K] {f g : K[X]} (hf0 : f ≠ 0)
    (hf : Splits f) : Splits (EuclideanDomain.gcd f g) :=
  Splits.of_dvd hf hf0 <| EuclideanDomain.gcd_dvd_left f g

@[deprecated "Use `Splits.of_dvd` directly." (since := "2025-11-30")]
theorem splits_of_splits_gcd_right [DecidableEq K] {f g : K[X]} (hg0 : g ≠ 0)
    (hg : Splits g) : Splits (EuclideanDomain.gcd f g) :=
  Splits.of_dvd hg hg0 <| EuclideanDomain.gcd_dvd_right f g

@[deprecated (since := "2025-11-30")]
alias degree_eq_one_of_irreducible_of_splits := Splits.degree_eq_one_of_irreducible

@[deprecated (since := "2025-12-01")]
alias exists_root_of_splits := Splits.exists_eval_eq_zero

@[deprecated (since := "2025-12-01")]
alias roots_ne_zero_of_splits := Splits.roots_ne_zero

@[deprecated (since := "2025-12-01")]
alias map_rootOfSplits := eval_rootOfSplits

/-- `rootOfSplits'` is definitionally equal to `rootOfSplits`. -/
@[deprecated "`rootOfSplits'` is now deprecated." (since := "2025-12-01")]
theorem rootOfSplits'_eq_rootOfSplits {f : K[X]} (hf : (f.map i).Splits) (hfd) :
    rootOfSplits hf hfd = rootOfSplits hf (f.degree_map i ▸ hfd) :=
  rfl

@[deprecated (since := "2025-11-30")]
alias natDegree_eq_card_roots := Splits.natDegree_eq_card_roots

@[deprecated (since := "2025-11-30")]
alias degree_eq_card_roots := Splits.degree_eq_card_roots

@[deprecated (since := "2025-12-02")]
alias roots_map := Splits.map_roots

@[deprecated (since := "2025-12-02")]
alias image_rootSet := Splits.image_rootSet

@[deprecated (since := "2025-12-06")]
alias adjoin_rootSet_eq_range := Splits.adjoin_rootSet_eq_range

@[deprecated (since := "2025-11-25")]
alias eq_prod_roots_of_splits := Splits.eq_prod_roots

@[deprecated (since := "2025-11-25")]
alias eq_prod_roots_of_splits_id := Splits.eq_prod_roots

@[deprecated (since := "2025-12-06")]
alias aeval_eq_prod_aroots_sub_of_splits := Splits.aeval_eq_prod_aroots

@[deprecated (since := "2025-12-06")]
alias eval_eq_prod_roots_sub_of_splits_id := Splits.eval_eq_prod_roots

@[deprecated (since := "2025-12-02")]
alias eq_prod_roots_of_monic_of_splits_id := Splits.eq_prod_roots_of_monic

@[deprecated (since := "2025-12-06")]
alias aeval_eq_prod_aroots_sub_of_monic_of_splits := Splits.aeval_eq_prod_aroots_of_monic

@[deprecated (since := "2025-12-06")]
alias eval_eq_prod_roots_sub_of_monic_of_splits_id := Splits.eval_eq_prod_roots_of_monic

@[deprecated (since := "2025-12-06")]
alias eq_X_sub_C_of_splits_of_single_root := Splits.eq_X_sub_C_of_single_root

@[deprecated (since := "2025-12-13")]
alias mem_lift_of_splits_of_roots_mem_range := Splits.mem_lift_of_roots_mem_range

@[deprecated (since := "2025-12-13")]
alias splits_of_natDegree_eq_two := Splits.of_natDegree_eq_two

@[deprecated (since := "2025-12-13")]
alias splits_of_degree_eq_two := Splits.of_degree_eq_two

section UFD

attribute [local instance] PrincipalIdealRing.to_uniqueFactorizationMonoid

local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

@[deprecated (since := "2025-12-02")]
alias splits_of_exists_multiset := splits_iff_exists_multiset

@[deprecated (since := "2025-11-30")]
alias splits_of_splits_id := Splits.map

end UFD

@[deprecated (since := "2025-12-09")]
alias splits_of_comp := Splits.of_splits_map

@[deprecated (since := "2025-12-09")]
alias splits_id_of_splits := Splits.of_splits_map

@[deprecated (since := "2025-12-09")]
alias splits_comp_of_splits := Splits.map

variable [Algebra R K] [Algebra R L]

@[deprecated (since := "2025-12-13")]
alias splits_of_algHom := Splits.of_algHom

@[deprecated (since := "2025-12-13")]
alias splits_of_isScalarTower := Splits.of_isScalarTower

@[deprecated (since := "2025-12-08")]
alias eval₂_derivative_of_splits := Splits.eval_derivative

@[deprecated (since := "2025-12-08")]
alias aeval_derivative_of_splits := Splits.eval_derivative

@[deprecated (since := "2025-12-08")]
alias eval_derivative_of_splits := Splits.eval_derivative

@[deprecated (since := "2025-12-08")]
alias aeval_root_derivative_of_splits := Splits.eval_root_derivative

@[deprecated (since := "2025-12-12")]
alias eval_derivative_eq_eval_mul_sum_of_splits := Splits.eval_derivative_eq_eval_mul_sum

@[deprecated (since := "2025-12-12")]
alias eval_derivative_div_eval_of_ne_zero_of_splits := Splits.eval_derivative_div_eval_of_ne_zero

@[deprecated (since := "2025-12-12")]
alias coeff_zero_eq_leadingCoeff_mul_prod_roots_of_splits :=
  Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots

@[deprecated (since := "2025-12-12")]
alias coeff_zero_eq_prod_roots_of_monic_of_splits := Splits.coeff_zero_eq_prod_roots_of_monic

@[deprecated (since := "2025-12-12")]
alias nextCoeff_eq_neg_sum_roots_mul_leadingCoeff_of_splits :=
  Splits.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff

@[deprecated (since := "2025-12-12")]
alias nextCoeff_eq_neg_sum_roots_of_monic_of_splits := Splits.nextCoeff_eq_neg_sum_roots_of_monic

@[deprecated (since := "2025-10-08")]
alias prod_roots_eq_coeff_zero_of_monic_of_splits := coeff_zero_eq_prod_roots_of_monic_of_splits

@[deprecated (since := "2025-10-08")]
alias sum_roots_eq_nextCoeff_of_monic_of_split := nextCoeff_eq_neg_sum_roots_of_monic_of_splits

end Splits

end Polynomial
