/-
Copyright (c) 2026 Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elias Judin
-/
module

public import Mathlib.Algebra.MvPolynomial.HasseDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Hasse derivatives and homogeneous multivariate polynomials

This file records how multivariate Hasse derivatives interact with homogeneity.
In particular, it shows that differentiating by a multi-index `i` lowers degree by the total
order of `i` and commutes with taking the top homogeneous component.

## Main declarations

* `MvPolynomial.IsHomogeneous.hasseDeriv`
* `MvPolynomial.homogeneousComponent_hasseDeriv`
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ R : Type*} [CommSemiring R]

/-! ### Homogeneous polynomials -/

/-- If `P` is homogeneous of degree $n$, then `hasseDeriv i P` is homogeneous of degree
$n - \sum_j i_j$. -/
protected theorem IsHomogeneous.hasseDeriv {P : MvPolynomial σ R} {n : ℕ}
    (hP : P.IsHomogeneous n) (i : σ →₀ ℕ) :
    (hasseDeriv i P).IsHomogeneous (n - i.degree) := by
  classical
  rw [MvPolynomial.IsHomogeneous]
  intro d hd
  have hcoeff : coeff (d + i) P ≠ 0 := by
    intro hzero
    exact hd (by simp [hasseDeriv_coeff, hzero])
  have hdeg : (d + i).degree = n := by
    simpa [Finsupp.degree_eq_weight_one] using hP hcoeff
  by_cases hi : i.degree ≤ n
  · have hsum : d.degree + i.degree = n := by
      simpa [Finsupp.degree, map_add] using hdeg
    have hddeg : d.degree = n - i.degree := by
      calc
        d.degree = (d.degree + i.degree) - i.degree := by simp
        _ = n - i.degree := by rw [hsum]
    simpa [Finsupp.degree_eq_weight_one] using hddeg
  · have hlt : n < i.degree := lt_of_not_ge hi
    have hle : i.degree ≤ (d + i).degree := by
      simp [Finsupp.degree, map_add]
    exfalso
    exact not_lt_of_ge (hdeg ▸ hle) hlt

/-- Hasse differentiation commutes with taking the top homogeneous component. Equivalently,
it commutes with taking the homogeneous component in the highest possible degree. -/
theorem homogeneousComponent_hasseDeriv (P : MvPolynomial σ R) (i : σ →₀ ℕ) :
    MvPolynomial.homogeneousComponent (P.totalDegree - i.degree) (hasseDeriv i P) =
      hasseDeriv i (MvPolynomial.homogeneousComponent P.totalDegree P) := by
  classical
  ext x
  by_cases hi : i.degree ≤ P.totalDegree
  · by_cases hdeg : x.degree = P.totalDegree - i.degree
    · have hsum : x.degree + i.degree = P.totalDegree := by
        calc
          x.degree + i.degree = (P.totalDegree - i.degree) + i.degree := by simp [hdeg]
          _ = P.totalDegree := Nat.sub_add_cancel hi
      have hdeg' : (x + i).degree = P.totalDegree := by
        simpa [Finsupp.degree, map_add] using hsum
      simp [coeff_homogeneousComponent, hasseDeriv_coeff, hdeg, hdeg']
    · have hdeg' : (x + i).degree ≠ P.totalDegree := by
        intro hdeg'
        have hsum : x.degree + i.degree = P.totalDegree := by
          simpa [Finsupp.degree, map_add] using hdeg'
        have hx : x.degree = P.totalDegree - i.degree := by
          calc
            x.degree = (x.degree + i.degree) - i.degree :=
              (Nat.add_sub_cancel_right x.degree i.degree).symm
            _ = P.totalDegree - i.degree := by simp [hsum]
        exact hdeg hx
      have hdeg'' : x.degree + i.degree ≠ P.totalDegree := by
        simpa [Finsupp.degree, map_add] using hdeg'
      simp [coeff_homogeneousComponent, hasseDeriv_coeff, hdeg, hdeg'']
  · have hdeg_gt : (x + i).degree > P.totalDegree := by
      simpa [Finsupp.degree, map_add] using
        lt_of_lt_of_le (lt_of_not_ge hi) (Nat.le_add_left i.degree x.degree)
    have hcoeff_zero : coeff x (hasseDeriv i P) = 0 := by
      have hcoeff' : coeff (x + i) P = 0 := by
        by_contra hnonzero
        have hm : x + i ∈ P.support := MvPolynomial.mem_support_iff.mpr hnonzero
        have hle : (x + i).degree ≤ P.totalDegree := by
          simpa [Finsupp.degree] using (MvPolynomial.le_totalDegree (p := P) (s := x + i) hm)
        exact (not_lt_of_ge hle) hdeg_gt
      simp [hasseDeriv_coeff, hcoeff']
    have hdeg'' : x.degree + i.degree ≠ P.totalDegree := by
      rw [← (show (x + i).degree = x.degree + i.degree by simp [Finsupp.degree, map_add])]
      exact ne_of_gt hdeg_gt
    simp [coeff_homogeneousComponent, hasseDeriv_coeff, hcoeff_zero, hdeg'']

end MvPolynomial
