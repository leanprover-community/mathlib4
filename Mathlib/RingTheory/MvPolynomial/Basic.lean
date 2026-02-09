/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.DFinsupp.Small
public import Mathlib.Data.Fintype.Pi
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

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

@[expose] public section


noncomputable section

open Set LinearMap Module Submodule

universe u v

variable (σ : Type u) (R : Type v) [CommSemiring R] (p m : ℕ)

namespace MvPolynomial

instance {σ : Type*} {R : Type*} [CommSemiring R]
    [Small.{u} R] [Small.{u} σ] :
    Small.{u} (MvPolynomial σ R) :=
  inferInstanceAs (Small.{u} ((σ →₀ ℕ) →₀ R))

section CharP

instance [CharP R p] : CharP (MvPolynomial σ R) p where
  cast_eq_zero_iff n := by rw [← C_eq_coe_nat, ← C_0, C_inj, CharP.cast_eq_zero_iff R p]

end CharP

section CharZero

instance [CharZero R] : CharZero (MvPolynomial σ R) where
  cast_injective x y hxy := by rwa [← C_eq_coe_nat, ← C_eq_coe_nat, C_inj, Nat.cast_inj] at hxy

end CharZero

section ExpChar

variable [ExpChar R p]

instance : ExpChar (MvPolynomial σ R) p := by
  cases ‹ExpChar R p›; exacts [ExpChar.zero, ExpChar.prime ‹_›]

end ExpChar

section Homomorphism

theorem mapRange_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] (p : MvPolynomial σ R)
    (f : R →+* S) : Finsupp.mapRange f f.map_zero p = map f p := by
  rw [p.as_sum, Finsupp.mapRange_finset_sum, map_sum (map f)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_monomial, ← single_eq_monomial, Finsupp.mapRange_single, single_eq_monomial]

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

lemma restrictSupport_eq_span (s : Set (σ →₀ ℕ)) :
    restrictSupport R s = .span _ ((monomial · 1) '' s) := Finsupp.supported_eq_span_single ..

lemma mem_restrictSupport_iff {s : Set (σ →₀ ℕ)} {r : MvPolynomial σ R} :
    r ∈ restrictSupport R s ↔ ↑r.support ⊆ s := .rfl

@[simp]
lemma monomial_mem_restrictSupport {s : Set (σ →₀ ℕ)} {m} {r : R} :
    monomial m r ∈ restrictSupport R s ↔ m ∈ s ∨ r = 0 := by
  classical
  by_cases r = 0 <;> simp [mem_restrictSupport_iff, support_monomial, *]

open Pointwise in
lemma restrictSupport_add (s t : Set (σ →₀ ℕ)) :
    restrictSupport R (s + t) = restrictSupport R s * restrictSupport R t := by
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff, Set.add_subset_iff]
    intro x hx y hy
    simp [show monomial (x + y) (1 : R) = monomial x 1 * monomial y 1 by simp, -monomial_mul,
      *, Submodule.mul_mem_mul]
  · rw [restrictSupport_eq_span, restrictSupport_eq_span, Submodule.span_mul_span,
      Submodule.span_le, Set.mul_subset_iff]
    simp +contextual [Set.add_mem_add]

open Pointwise in
@[simp] lemma restrictSupport_zero : restrictSupport R (0 : Set (σ →₀ ℕ)) = 1 := by
  classical
  apply le_antisymm
  · rw [restrictSupport_eq_span, Submodule.span_le, Set.image_subset_iff]
    simpa using ⟨1, by simp⟩
  · rintro _ ⟨x, rfl⟩
    simp [mem_restrictSupport_iff, Set.subset_def, coeff_one]

@[simp]
lemma restrictSupport_univ : restrictSupport R (.univ : Set (σ →₀ ℕ)) = ⊤ := by
  ext; simp [mem_restrictSupport_iff]

open Pointwise in
lemma restrictSupport_nsmul (n : ℕ) (s : Set (σ →₀ ℕ)) :
    restrictSupport R (n • s) = restrictSupport R s ^ n := by
  induction n <;> simp [add_smul, restrictSupport_add, *, pow_succ]

/-- The ideal defined by `restrictSupport R s` when `s` is an upper set. -/
def restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs : IsUpperSet s) :
    Ideal (MvPolynomial σ R) where
  __ := restrictSupport R s
  smul_mem' x y hy m (hm : m ∈ (x * y).support) := by
    classical
    simp only [mem_support_iff, coeff_mul, ne_eq] at hm
    obtain ⟨⟨i, j⟩, hij, e⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    refine hs (by simp_all [eq_comm]) (hy (show j ∈ y.support by aesop))

@[simp]
lemma restrictScalars_restrictSupportIdeal (s : Set (σ →₀ ℕ)) (hs) :
  (restrictSupportIdeal (R := R) s hs).restrictScalars R = restrictSupport R s := by rfl

variable (σ)

/-- The submodule of polynomials of total degree less than or equal to `m`. -/
def restrictTotalDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | (n.sum fun _ e => e) ≤ m }

/-- The submodule of polynomials such that the degree with respect to each individual variable is
less than or equal to `m`. -/
def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ m }

variable {R}

theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p ∈ restrictTotalDegree σ R m ↔ p.totalDegree ≤ m := by
  rw [totalDegree, Finset.sup_le_iff]
  rfl

theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ n := by
  rw [restrictDegree, restrictSupport, Finsupp.mem_supported]
  rfl

theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degrees.count i ≤ n := by
  simp only [mem_restrictDegree, degrees_def, Multiset.count_finset_sup, Finsupp.count_toMultiset,
    Finset.sup_le_iff]
  exact ⟨fun h n s hs => h s hs n, fun h s hs n => h n s hs⟩

variable (R)

theorem restrictTotalDegree_le_restrictDegree (m : ℕ) :
    restrictTotalDegree σ R m ≤ restrictDegree σ R m :=
  fun p hp ↦ (mem_restrictDegree _ _ _).mpr fun s hs i ↦ (degreeOf_le_iff.mp
    (degreeOf_le_totalDegree p i) s hs).trans ((mem_restrictTotalDegree _ _ _).mp hp)

/-- The monomials form a basis on `MvPolynomial σ R`. -/
def basisMonomials : Basis (σ →₀ ℕ) R (MvPolynomial σ R) :=
  Finsupp.basisSingleOne

@[simp]
theorem coe_basisMonomials :
    (basisMonomials σ R : (σ →₀ ℕ) → MvPolynomial σ R) = fun s => monomial s 1 :=
  rfl

/-- The `R`-module `MvPolynomial σ R` is free. -/
instance : Module.Free R (MvPolynomial σ R) :=
  Module.Free.of_basis (MvPolynomial.basisMonomials σ R)

theorem linearIndependent_X : LinearIndependent R (X : σ → MvPolynomial σ R) :=
  (basisMonomials σ R).linearIndependent.comp (fun s : σ => Finsupp.single s 1)
    (Finsupp.single_left_injective one_ne_zero)

private lemma finite_setOf_bounded (α) [Finite α] (n : ℕ) : Finite {f : α →₀ ℕ | ∀ a, f a ≤ n} :=
  ((Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn).to_subtype

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
