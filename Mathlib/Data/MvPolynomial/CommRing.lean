/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Data.MvPolynomial.Variables

#align_import data.mv_polynomial.comm_ring from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Multivariate polynomials over a ring

Many results about polynomials hold when the coefficient ring is a commutative semiring.
Some stronger results can be derived when we assume this semiring is a ring.

This file does not define any new operations, but proves some of these stronger results.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommRing R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

-/


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

universe u v

variable {R : Type u} {S : Type v}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommRing

variable [CommRing R]

variable {p q : MvPolynomial σ R}

instance instCommRingMvPolynomial : CommRing (MvPolynomial σ R) :=
  AddMonoidAlgebra.commRing

variable (σ a a')

-- @[simp] -- Porting note: simp can prove this
theorem C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a' :=
  RingHom.map_sub _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.C_sub MvPolynomial.C_sub

-- @[simp] -- Porting note: simp can prove this
theorem C_neg : (C (-a) : MvPolynomial σ R) = -C a :=
  RingHom.map_neg _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.C_neg MvPolynomial.C_neg

@[simp]
theorem coeff_neg (m : σ →₀ ℕ) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m p :=
  Finsupp.neg_apply _ _
#align mv_polynomial.coeff_neg MvPolynomial.coeff_neg

@[simp]
theorem coeff_sub (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  Finsupp.sub_apply _ _ _
#align mv_polynomial.coeff_sub MvPolynomial.coeff_sub

@[simp]
theorem support_neg : (-p).support = p.support :=
  Finsupp.support_neg p
#align mv_polynomial.support_neg MvPolynomial.support_neg

theorem support_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_sub
#align mv_polynomial.support_sub MvPolynomial.support_sub

variable {σ} (p)

section Degrees

theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees, support_neg]; rfl
  -- ⊢ (Finset.sup (support p) fun s => ↑toMultiset s) = degrees p
                             -- 🎉 no goals
#align mv_polynomial.degrees_neg MvPolynomial.degrees_neg

theorem degrees_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).degrees ≤ p.degrees ⊔ q.degrees := by
  simpa only [sub_eq_add_neg] using le_trans (degrees_add p (-q)) (by rw [degrees_neg])
  -- 🎉 no goals
#align mv_polynomial.degrees_sub MvPolynomial.degrees_sub

end Degrees

section Vars

@[simp]
theorem vars_neg : (-p).vars = p.vars := by simp [vars, degrees_neg]
                                            -- 🎉 no goals
#align mv_polynomial.vars_neg MvPolynomial.vars_neg

theorem vars_sub_subset [DecidableEq σ] : (p - q).vars ⊆ p.vars ∪ q.vars := by
  convert vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]
  -- ⊢ p - q = p + -q
                                             -- 🎉 no goals
                                             -- 🎉 no goals
#align mv_polynomial.vars_sub_subset MvPolynomial.vars_sub_subset

@[simp]
theorem vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) :
    (p - q).vars = p.vars ∪ q.vars := by
  rw [← vars_neg q] at hpq
  -- ⊢ vars (p - q) = vars p ∪ vars q
  convert vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]
  -- ⊢ p - q = p + -q
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align mv_polynomial.vars_sub_of_disjoint MvPolynomial.vars_sub_of_disjoint

end Vars

section Eval

variable [CommRing S]

variable (f : R →+* S) (g : σ → S)

@[simp]
theorem eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g :=
  (eval₂Hom f g).map_sub _ _
#align mv_polynomial.eval₂_sub MvPolynomial.eval₂_sub

theorem eval_sub (f : σ → R) : eval f (p - q) = eval f p - eval f q :=
  eval₂_sub _ _ _

@[simp]
theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g :=
  (eval₂Hom f g).map_neg _
#align mv_polynomial.eval₂_neg MvPolynomial.eval₂_neg

theorem eval_neg (f : σ → R) : eval f (-p) = -eval f p :=
  eval₂_neg _ _ _

theorem hom_C (f : MvPolynomial σ ℤ →+* S) (n : ℤ) : f (C n) = (n : S) :=
  eq_intCast (f.comp C) n
set_option linter.uppercaseLean3 false in
#align mv_polynomial.hom_C MvPolynomial.hom_C

/-- A ring homomorphism f : Z[X_1, X_2, ...] → R
is determined by the evaluations f(X_1), f(X_2), ... -/
@[simp]
theorem eval₂Hom_X {R : Type u} (c : ℤ →+* S) (f : MvPolynomial R ℤ →+* S) (x : MvPolynomial R ℤ) :
    eval₂ c (f ∘ X) x = f x := by
  apply MvPolynomial.induction_on x
    (fun n => by
      rw [hom_C f, eval₂_C]
      exact eq_intCast c n)
    (fun p q hp hq => by
      rw [eval₂_add, hp, hq]
      exact (f.map_add _ _).symm)
    (fun p n hp => by
      rw [eval₂_mul, eval₂_X, hp]
      exact (f.map_mul _ _).symm)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.eval₂_hom_X MvPolynomial.eval₂Hom_X

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`, -/
def homEquiv : (MvPolynomial σ ℤ →+* S) ≃ (σ → S) where
  toFun f := f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
  left_inv f := RingHom.ext <| eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]
                                    -- 🎉 no goals
#align mv_polynomial.hom_equiv MvPolynomial.homEquiv

end Eval

section DegreeOf

theorem degreeOf_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : ℕ} (h : 0 < k)
    (hf : ∀ m : σ →₀ ℕ, m ∈ f.support → k ≤ m x → coeff m f = coeff m g)
    (hg : ∀ m : σ →₀ ℕ, m ∈ g.support → k ≤ m x → coeff m f = coeff m g) :
    degreeOf x (f - g) < k := by
  classical
  rw [degreeOf_lt_iff h]
  intro m hm
  by_contra' hc
  have h := support_sub σ f g hm
  simp only [mem_support_iff, Ne.def, coeff_sub, sub_eq_zero] at hm
  cases' Finset.mem_union.1 h with cf cg
  · exact hm (hf m cf hc)
  · exact hm (hg m cg hc)
#align mv_polynomial.degree_of_sub_lt MvPolynomial.degreeOf_sub_lt

end DegreeOf

section TotalDegree

@[simp]
theorem totalDegree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree := by
  simp only [totalDegree, support_neg]
  -- 🎉 no goals
#align mv_polynomial.total_degree_neg MvPolynomial.totalDegree_neg

theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
                                                     -- 🎉 no goals
    _ ≤ max a.totalDegree (-b).totalDegree := (totalDegree_add a (-b))
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]
                                              -- 🎉 no goals
#align mv_polynomial.total_degree_sub MvPolynomial.totalDegree_sub

end TotalDegree

end CommRing

end MvPolynomial
