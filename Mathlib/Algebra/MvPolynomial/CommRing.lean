/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.MvPolynomial.Variables

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

@[simp]
theorem C_sub : (C (a - a') : MvPolynomial σ R) = C a - C a' :=
  RingHom.map_sub _ _ _

@[simp]
theorem C_neg : (C (-a) : MvPolynomial σ R) = -C a :=
  RingHom.map_neg _ _

@[simp]
theorem coeff_neg (m : σ →₀ ℕ) (p : MvPolynomial σ R) : coeff m (-p) = -coeff m p :=
  Finsupp.neg_apply _ _

@[simp]
theorem coeff_sub (m : σ →₀ ℕ) (p q : MvPolynomial σ R) : coeff m (p - q) = coeff m p - coeff m q :=
  Finsupp.sub_apply _ _ _

@[simp]
theorem support_neg : (-p).support = p.support :=
  Finsupp.support_neg p

theorem support_sub [DecidableEq σ] (p q : MvPolynomial σ R) :
    (p - q).support ⊆ p.support ∪ q.support :=
  Finsupp.support_sub

variable {σ} (p)

section Degrees

@[simp]
theorem degrees_neg (p : MvPolynomial σ R) : (-p).degrees = p.degrees := by
  rw [degrees, support_neg]; rfl

theorem degrees_sub_le [DecidableEq σ] {p q : MvPolynomial σ R} :
    (p - q).degrees ≤ p.degrees ∪ q.degrees := by
  simpa [degrees_def] using AddMonoidAlgebra.supDegree_sub_le

end Degrees

section Degrees

@[simp]
theorem degreeOf_neg (i : σ) (p : MvPolynomial σ R) : degreeOf i (-p) = degreeOf i p := by
  rw [degreeOf, degreeOf, degrees_neg]

theorem degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) :
    degreeOf i (p - q) ≤ max (degreeOf i p) (degreeOf i q) := by
  simpa only [sub_eq_add_neg, degreeOf_neg] using degreeOf_add_le i p (-q)

end Degrees

section Vars

@[simp]
theorem vars_neg : (-p).vars = p.vars := by simp [vars, degrees_neg]

theorem vars_sub_subset [DecidableEq σ] : (p - q).vars ⊆ p.vars ∪ q.vars := by
  convert vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

@[simp]
theorem vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) :
    (p - q).vars = p.vars ∪ q.vars := by
  rw [← vars_neg q] at hpq
  convert vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

end Vars

section Eval

variable [CommRing S]
variable (f : R →+* S) (g : σ → S)

@[simp]
theorem eval₂_sub : (p - q).eval₂ f g = p.eval₂ f g - q.eval₂ f g :=
  (eval₂Hom f g).map_sub _ _

theorem eval_sub (f : σ → R) : eval f (p - q) = eval f p - eval f q :=
  eval₂_sub _ _ _

@[simp]
theorem eval₂_neg : (-p).eval₂ f g = -p.eval₂ f g :=
  (eval₂Hom f g).map_neg _

theorem eval_neg (f : σ → R) : eval f (-p) = -eval f p :=
  eval₂_neg _ _ _

theorem hom_C (f : MvPolynomial σ ℤ →+* S) (n : ℤ) : f (C n) = (n : S) :=
  eq_intCast (f.comp C) n

/-- A ring homomorphism `f : Z[X_1, X_2, ...] → R`
is determined by the evaluations `f(X_1)`, `f(X_2)`, ... -/
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

/-- Ring homomorphisms out of integer polynomials on a type `σ` are the same as
functions out of the type `σ`. -/
def homEquiv : (MvPolynomial σ ℤ →+* S) ≃ (σ → S) where
  toFun f := f ∘ X
  invFun f := eval₂Hom (Int.castRingHom S) f
  left_inv _ := RingHom.ext <| eval₂Hom_X _ _
  right_inv f := funext fun x => by simp only [coe_eval₂Hom, Function.comp_apply, eval₂_X]

end Eval

section DegreeOf

theorem degreeOf_sub_lt {x : σ} {f g : MvPolynomial σ R} {k : ℕ} (h : 0 < k)
    (hf : ∀ m : σ →₀ ℕ, m ∈ f.support → k ≤ m x → coeff m f = coeff m g)
    (hg : ∀ m : σ →₀ ℕ, m ∈ g.support → k ≤ m x → coeff m f = coeff m g) :
    degreeOf x (f - g) < k := by
  rw [degreeOf_lt_iff h]
  grind [degreeOf_lt_iff, mem_support_iff, coeff_sub, Finset.mem_union]

end DegreeOf

section TotalDegree

@[simp]
theorem totalDegree_neg (a : MvPolynomial σ R) : (-a).totalDegree = a.totalDegree := by
  simp only [totalDegree, support_neg]

theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree :=
  calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ ≤ max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [totalDegree_neg]

theorem totalDegree_sub_C_le (p : MvPolynomial σ R) (r : R) :
    totalDegree (p - C r) ≤ totalDegree p :=
  (totalDegree_sub _ _).trans_eq <| by rw [totalDegree_C, Nat.max_zero]

end TotalDegree

end CommRing

end MvPolynomial
