/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.FinsuppVectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

#align_import ring_theory.mv_polynomial.basic from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Multivariate polynomials over commutative rings

This file contains basic facts about multivariate polynomials over commutative rings, for example
that the monomials form a basis.

## Main definitions

* `restrictTotalDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` of total degree at most `m`.
* `restrictDegree σ R m`: the subspace of multivariate polynomials indexed by `σ` over the
  commutative ring `R` such that the degree in each individual variable is at most `m`.

## Main statements

* The multivariate polynomial ring over a commutative semiring of characteristic `p` has
  characteristic `p`, and similarly for `CharZero`.
* `basisMonomials`: shows that the monomials form a basis of the vector space of multivariate
  polynomials.

## TODO

Generalise to noncommutative (semi)rings
-/


noncomputable section

open Set LinearMap Submodule

open BigOperators Polynomial

universe u v

variable (σ : Type u) (R : Type v) [CommSemiring R] (p m : ℕ)

namespace MvPolynomial

section CharP

instance [CharP R p] : CharP (MvPolynomial σ R) p where
  cast_eq_zero_iff' n := by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

end CharP

section CharZero

instance [CharZero R] : CharZero (MvPolynomial σ R) where
  cast_injective x y hxy := by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

end CharZero

section Homomorphism

theorem mapRange_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
    (f : R →+* S) : Finsupp.mapRange f f.map_zero p = map f p := by
  rw [p.as_sum, Finsupp.mapRange_finset_sum, map_sum (map f)]
  refine' Finset.sum_congr rfl fun n _ => _
  rw [map_monomial, ← single_eq_monomial, Finsupp.mapRange_single, single_eq_monomial]
#align mv_polynomial.map_range_eq_map MvPolynomial.mapRange_eq_map

end Homomorphism

section Degree

variable {σ}

/-- The submodule of polynomials that are sum of monomials in the set `s`. -/
def restrictSupport (s : Set (σ →₀ ℕ)) : Submodule R (MvPolynomial σ R) :=
  Finsupp.supported _ _ s

/-- `restrictSupport R s` has a canonical `R`-basis indexed by `s`. -/
def basisRestrictSupport (s : Set (σ →₀ ℕ)) : Basis s R (restrictSupport R s) where
  repr := Finsupp.supportedEquivFinsupp s

theorem restrictSupport_mono {s t : Set (σ →₀ ℕ)} (h : s ⊆ t) :
    restrictSupport R s ≤ restrictSupport R t := Finsupp.supported_mono h

variable (σ)

/-- The submodule of polynomials of total degree less than or equal to `m`. -/
def restrictTotalDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | (n.sum fun _ e => e) ≤ m }
#align mv_polynomial.restrict_total_degree MvPolynomial.restrictTotalDegree

/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`. -/
def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ m }
#align mv_polynomial.restrict_degree MvPolynomial.restrictDegree

variable {R}

theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p ∈ restrictTotalDegree σ R m ↔ p.totalDegree ≤ m := by
  rw [totalDegree, Finset.sup_le_iff]
  rfl
#align mv_polynomial.mem_restrict_total_degree MvPolynomial.mem_restrictTotalDegree

theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ n := by
  rw [restrictDegree, restrictSupport, Finsupp.mem_supported]
  rfl
#align mv_polynomial.mem_restrict_degree MvPolynomial.mem_restrictDegree

theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degrees.count i ≤ n := by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩
#align mv_polynomial.mem_restrict_degree_iff_sup MvPolynomial.mem_restrictDegree_iff_sup

variable (R)

theorem restrictTotalDegree_le_restrictDegree (m : ℕ) :
    restrictTotalDegree σ R m ≤ restrictDegree σ R m :=
  fun p hp ↦ (mem_restrictDegree _ _ _).mpr fun s hs i ↦ (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

/-- The monomials form a basis on `MvPolynomial σ R`. -/
def basisMonomials : Basis (σ →₀ ℕ) R (MvPolynomial σ R) :=
  Finsupp.basisSingleOne
#align mv_polynomial.basis_monomials MvPolynomial.basisMonomials

@[simp]
theorem coe_basisMonomials :
    (basisMonomials σ R : (σ →₀ ℕ) → MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl
#align mv_polynomial.coe_basis_monomials MvPolynomial.coe_basisMonomials

/-- The `R`-module `MvPolynomial σ R` is free. -/
instance : Module.Free R (MvPolynomial σ R) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials σ R)

theorem linearIndependent_X : LinearIndependent R (X : σ → MvPolynomial σ R) :=
  (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)
set_option linter.uppercaseLean3 false in
#align mv_polynomial.linear_independent_X MvPolynomial.linearIndependent_X

private lemma finite_setOf_bounded (α) [Finite α] (n : ℕ) : Finite {f : α →₀ ℕ | ∀ a, f a ≤ n} :=
  ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage <|
    DFunLike.coe_injective.injOn _).to_subtype

instance [Finite σ] (N : ℕ) : Module.Finite R (restrictDegree σ R N) :=
  have := finite_setOf_bounded σ N
  Module.Finite.of_basis (basisRestrictSupport R _)

instance [Finite σ] (N : ℕ) : Module.Finite R (restrictTotalDegree σ R N) :=
  have := finite_setOf_bounded σ N
  have : Finite {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ N} := by
    rw [Set.finite_coe_iff] at this ⊢
    exact this.subset fun n hn i ↦ (eq_or_ne (n i) 0).elim
      (fun h ↦ h.trans_le N.zero_le) fun h ↦
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) <| Finsupp.mem_support_iff.mpr h).trans hn
  Module.Finite.of_basis (basisRestrictSupport R _)

end Degree

end MvPolynomial

-- this is here to avoid import cycle issues
namespace Polynomial

/-- The monomials form a basis on `R[X]`. -/
noncomputable def basisMonomials : Basis ℕ R R[X] :=
  Basis.ofRepr (toFinsuppIsoAlg R).toLinearEquiv
#align polynomial.basis_monomials Polynomial.basisMonomials

@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → R[X]) = fun s => monomial s 1 :=
  funext fun _ => ofFinsupp_single _ _
#align polynomial.coe_basis_monomials Polynomial.coe_basisMonomials

end Polynomial
