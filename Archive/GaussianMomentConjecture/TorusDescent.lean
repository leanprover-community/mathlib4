/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.AlgebraicDescent
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.FiniteType

/-!
# Descent of a complex torus point to a number field

This module supplies the geometric front end left abstract by
`AlgebraicDescent`.  Given finitely many complex coordinates, adjoin the
coordinates and their inverses to `ℚ`.  The resulting subalgebra of `ℂ` is
nontrivial and of finite type, every coordinate is a unit, and rational
polynomial relations remain zero in it.  The maximal-quotient theorem then
specializes the point to a finite extension of `ℚ`.

The relation family itself may be arbitrary; only the variable type must be
finite.
-/

namespace GMC2.TorusDescent

universe u v

noncomputable section

local instance : Algebra ℚ ℂ := (Rat.castHom ℂ).toAlgebra

/-- Every complex torus point satisfying an arbitrary family of rational
multivariate-polynomial relations has a torus realization over some finite
extension of `ℚ`. -/
theorem exists_numberField_torus_point_of_complex_relations
    {ι : Type u} {κ : Type v} [Finite ι]
    (relation : κ → MvPolynomial ι ℚ)
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (hrelation : ∀ k, MvPolynomial.aeval z (relation k) = 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ zK : ι → K,
          (∀ i, zK i ≠ 0) ∧
            ∀ k, MvPolynomial.aeval zK (relation k) = 0 := by
  let generators : Set ℂ :=
    Set.range z ∪ Set.range (fun i ↦ (z i)⁻¹)
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ generators
  have hgenerators : generators.Finite := by
    exact (Set.finite_range z).union (Set.finite_range fun i ↦ (z i)⁻¹)
  letI : Algebra.FiniteType ℚ A :=
    Algebra.FiniteType.adjoin_of_finite hgenerators

  let c : ι → A := fun i ↦
    ⟨z i, Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_range_self i))⟩
  let cInv : ι → A := fun i ↦
    ⟨(z i)⁻¹, Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self i))⟩

  have hc : ∀ i, IsUnit (c i) := by
    intro i
    rw [isUnit_iff_exists]
    refine ⟨cInv i, ?_, ?_⟩
    · apply Subtype.ext
      simp [c, cInv, hz i]
    · apply Subtype.ext
      simp [c, cInv, hz i]

  have hrelationA : ∀ k, MvPolynomial.aeval c (relation k) = 0 := by
    intro k
    apply Subtype.ext
    change A.val (MvPolynomial.aeval c (relation k)) = A.val 0
    rw [MvPolynomial.comp_aeval_apply, map_zero]
    simpa [c] using hrelation k

  exact
    GMC2.AlgebraicDescent.exists_numberField_torus_point_of_relations
      c hc relation hrelationA

/-- A complex torus point can be specialized to a number field while
simultaneously preserving an arbitrary family of polynomial equalities and
the nonvanishing of one distinguished rational polynomial.  The extra
nonvanishing condition is encoded by adjoining the inverse of its value and
treating that value as one more unit during specialization. -/
theorem exists_numberField_torus_point_preserving_nonzero_of_complex_relations
    {ι : Type u} {κ : Type v} [Finite ι]
    (relation : κ → MvPolynomial ι ℚ) (q : MvPolynomial ι ℚ)
    (z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (hrelation : ∀ k, MvPolynomial.aeval z (relation k) = 0)
    (hq : MvPolynomial.aeval z q ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K),
      Module.Finite ℚ K ∧
        ∃ zK : ι → K,
          (∀ i, zK i ≠ 0) ∧
            (∀ k, MvPolynomial.aeval zK (relation k) = 0) ∧
              MvPolynomial.aeval zK q ≠ 0 := by
  let qValue : ℂ := MvPolynomial.aeval z q
  let generators : Set ℂ :=
    (Set.range z ∪ Set.range (fun i ↦ (z i)⁻¹)) ∪ {qValue⁻¹}
  let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ generators
  have hgenerators : generators.Finite := by
    exact
      ((Set.finite_range z).union (Set.finite_range fun i ↦ (z i)⁻¹)).union
        (Set.finite_singleton qValue⁻¹)
  letI : Algebra.FiniteType ℚ A :=
    Algebra.FiniteType.adjoin_of_finite hgenerators

  let c : ι → A := fun i ↦
    ⟨z i, Algebra.subset_adjoin
      (Set.mem_union_left _
        (Set.mem_union_left _ (Set.mem_range_self i)))⟩
  let cInv : ι → A := fun i ↦
    ⟨(z i)⁻¹, Algebra.subset_adjoin
      (Set.mem_union_left _
        (Set.mem_union_right _ (Set.mem_range_self i)))⟩

  have hc : ∀ i, IsUnit (c i) := by
    intro i
    rw [isUnit_iff_exists]
    refine ⟨cInv i, ?_, ?_⟩
    · apply Subtype.ext
      simp [c, cInv, hz i]
    · apply Subtype.ext
      simp [c, cInv, hz i]

  let qA : A := MvPolynomial.aeval c q
  have hqA_val : (qA : ℂ) = qValue := by
    change A.val (MvPolynomial.aeval c q) = qValue
    rw [MvPolynomial.comp_aeval_apply]
    simp [c, qValue]
  let qInv : A :=
    ⟨qValue⁻¹, Algebra.subset_adjoin
      (Set.mem_union_right _ (Set.mem_singleton qValue⁻¹))⟩
  have hqA : IsUnit qA := by
    rw [isUnit_iff_exists]
    refine ⟨qInv, ?_, ?_⟩
    · apply Subtype.ext
      change (qA : ℂ) * qValue⁻¹ = 1
      rw [hqA_val]
      simp [qValue, hq]
    · apply Subtype.ext
      change qValue⁻¹ * (qA : ℂ) = 1
      rw [hqA_val]
      simp [qValue, hq]

  have hrelationA : ∀ k, MvPolynomial.aeval c (relation k) = 0 := by
    intro k
    apply Subtype.ext
    change A.val (MvPolynomial.aeval c (relation k)) = A.val 0
    rw [MvPolynomial.comp_aeval_apply, map_zero]
    simpa [c] using hrelation k

  let units : Option ι → A
    | none => qA
    | some i => c i
  have hunits : ∀ j, IsUnit (units j) := by
    intro j
    cases j with
    | none => exact hqA
    | some i => exact hc i

  obtain ⟨K, fieldK, algebraK, hfinite, φ, hunitK, hrelationK⟩ :=
    GMC2.AlgebraicDescent.exists_numberField_specialization
      units hunits (fun k ↦ MvPolynomial.aeval c (relation k)) hrelationA
  letI : Field K := fieldK
  letI : Algebra ℚ K := algebraK
  refine ⟨K, fieldK, algebraK, hfinite, fun i ↦ φ (c i), ?_, ?_, ?_⟩
  · intro i
    simpa [units] using hunitK (some i)
  · intro k
    rw [← MvPolynomial.comp_aeval_apply (f := c) φ (relation k)]
    exact hrelationK k
  · rw [← MvPolynomial.comp_aeval_apply (f := c) φ q]
    simpa [units, qA] using hunitK none

end

end GMC2.TorusDescent

