/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Number-field specialization backbone for the NC2 algebraic descent

`the lowest-balanced-face theorem` first replaces a hypothetical complex torus zero by a torus zero
over a number field.  Once its localized coordinate algebra `A` is known to
be nontrivial and of finite type over `ℚ`, the remaining commutative-algebra
step is Zariski's lemma: choose a maximal ideal and pass to `A ⧸ m`, which is
finite over `ℚ`.  Coordinates are units in the localized algebra, hence remain
nonzero in the field quotient.

This module formalizes exactly that reusable backbone.  It does not construct
the localized moment coordinate ring or prove it nontrivial from a complex
point; those remain the explicit front-end interface.
-/

namespace GMC2.AlgebraicDescent

universe u v w

/-- A nontrivial finite-type `ℚ`-algebra has a maximal quotient that is finite
as a `ℚ`-module (and therefore is a number field after installing the maximal
quotient's field instance). -/
theorem exists_maximal_quotient_finite
    (A : Type*) [CommRing A] [Nontrivial A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A] :
    ∃ m : Ideal A, m.IsMaximal ∧ Module.Finite ℚ (A ⧸ m) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  refine ⟨m, hm, ?_⟩
  letI : m.IsMaximal := hm
  letI := Ideal.Quotient.field m
  exact finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ m)

/-- A unit cannot become zero in a maximal quotient.  This is the precise
reason localization keeps every torus coordinate nonzero after algebraic
descent. -/
theorem unit_ne_zero_in_maximal_quotient
    {A : Type*} [CommRing A] {m : Ideal A} [m.IsMaximal]
    {x : A} (hx : IsUnit x) :
    Ideal.Quotient.mk m x ≠ 0 := by
  exact (hx.map (Ideal.Quotient.mk m)).ne_zero

/-- Simultaneous finite specialization of any family of units.  This packages
the exact output needed from the localized coefficient torus before the
lowest-face argument begins. -/
theorem exists_finite_specialization_of_units
    {A ι : Type*} [CommRing A] [Nontrivial A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A]
    (c : ι → A) (hc : ∀ i, IsUnit (c i)) :
    ∃ m : Ideal A, m.IsMaximal ∧ Module.Finite ℚ (A ⧸ m) ∧
      ∀ i, Ideal.Quotient.mk m (c i) ≠ 0 := by
  obtain ⟨m, hm, hfinite⟩ := exists_maximal_quotient_finite A
  refine ⟨m, hm, hfinite, ?_⟩
  letI : m.IsMaximal := hm
  intro i
  exact unit_ne_zero_in_maximal_quotient (hc i)

/-- Relations already equal to zero in the coordinate algebra remain zero in
every quotient specialization. -/
theorem relation_zero_in_quotient
    {A κ : Type*} [CommRing A] (m : Ideal A)
    (rel : κ → A) (hrel : ∀ k, rel k = 0) :
    ∀ k, Ideal.Quotient.mk m (rel k) = 0 := by
  intro k
  rw [hrel k, map_zero]

/-- Packaged number-field specialization.  Starting from the already
constructed nontrivial finite-type coordinate algebra, this returns an actual
finite extension `K/ℚ`, an `ℚ`-algebra map into it, nonzero images of all torus
coordinates, and transport of all relations that hold in the coordinate
algebra.  The missing geometric front end is precisely the construction of
such an `A` from a complex torus zero. -/
theorem exists_numberField_specialization
    {A : Type u} {ι : Type v} {κ : Type w}
    [CommRing A] [Nontrivial A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A]
    (c : ι → A) (hc : ∀ i, IsUnit (c i))
    (rel : κ → A) (hrel : ∀ k, rel k = 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ φ : A →ₐ[ℚ] K,
          (∀ i, φ (c i) ≠ 0) ∧ (∀ k, φ (rel k) = 0) := by
  obtain ⟨m, hm, hfinite⟩ := exists_maximal_quotient_finite A
  letI : m.IsMaximal := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  refine ⟨A ⧸ m, inferInstance, inferInstance, hfinite,
    Ideal.Quotient.mkₐ ℚ m, ?_, ?_⟩
  · intro i
    exact unit_ne_zero_in_maximal_quotient (hc i)
  · intro k
    rw [hrel k, map_zero]

/-- Polynomial-relation transport in the form needed by the NC2 moment
scheme.  Once a nontrivial finite-type `ℚ`-algebra point with unit coordinates
has been constructed, every family of rational polynomial relations descends
simultaneously to a torus point over a finite extension of `ℚ`. -/
theorem exists_numberField_torus_point_of_relations
    {A : Type u} {ι : Type v} {κ : Type w}
    [CommRing A] [Nontrivial A] [Algebra ℚ A]
    [Algebra.FiniteType ℚ A]
    (c : ι → A) (hc : ∀ i, IsUnit (c i))
    (relation : κ → MvPolynomial ι ℚ)
    (hrelation : ∀ k, MvPolynomial.aeval c (relation k) = 0) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ cK : ι → K,
          (∀ i, cK i ≠ 0) ∧
            ∀ k, MvPolynomial.aeval cK (relation k) = 0 := by
  obtain ⟨m, hm, hfinite⟩ := exists_maximal_quotient_finite A
  letI : m.IsMaximal := hm
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let φ : A →ₐ[ℚ] A ⧸ m := Ideal.Quotient.mkₐ ℚ m
  refine ⟨A ⧸ m, inferInstance, inferInstance, hfinite,
    fun i => φ (c i), ?_, ?_⟩
  · intro i
    exact unit_ne_zero_in_maximal_quotient (hc i)
  · intro k
    rw [← MvPolynomial.comp_aeval_apply (f := c) φ (relation k),
      hrelation k, map_zero]

end GMC2.AlgebraicDescent

