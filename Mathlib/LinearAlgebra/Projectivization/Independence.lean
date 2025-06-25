/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Independence in Projective Space

In this file we define independence and dependence of families of elements in projective space.

## Implementation Details

We use an inductive definition to define the independence of points in projective
space, where the only constructor assumes an independent family of vectors from the
ambient vector space. Similarly for the definition of dependence.

## Results

- A family of elements is dependent if and only if it is not independent.
- Two elements are dependent if and only if they are equal.

# Future Work

- Define collinearity in projective space.
- Prove the axioms of a projective geometry are satisfied by the dependence relation.
- Define projective linear subspaces.
-/

open scoped LinearAlgebra.Projectivization

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

/-- A linearly independent family of nonzero vectors gives an independent family of points
in projective space. -/
inductive Independent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : LinearIndependent K f) :
    Independent fun i => mk K (f i) (hf i)

/-- A family of points in a projective space is independent if and only if the representative
vectors determined by the family are linearly independent. -/
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh⟩
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh.units_smul a
    ext i
    exact (ha i).symm
  · convert Independent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · intro i
      apply rep_nonzero

/-- A family of points in projective space is independent if and only if the family of
submodules which the points determine is independent in the lattice-theoretic sense. -/
theorem independent_iff_iSupIndep : Independent f ↔ iSupIndep fun i => (f i).submodule := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨f, hf, hi⟩
    simp only [submodule_mk]
    exact (iSupIndep_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
  · rw [independent_iff]
    refine h.linearIndependent (Projectivization.submodule ∘ f) (fun i => ?_) fun i => ?_
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
    · exact rep_nonzero (f i)

@[deprecated (since := "2024-11-24")]
alias independent_iff_completeLattice_independent := independent_iff_iSupIndep

/-- A linearly dependent family of nonzero vectors gives a dependent family of points
in projective space. -/
inductive Dependent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬LinearIndependent K f) :
    Dependent fun i => mk K (f i) (hf i)

/-- A family of points in a projective space is dependent if and only if their
representatives are linearly dependent. -/
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ff, hff, hh1⟩
    contrapose! hh1
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    convert hh1.units_smul a⁻¹
    ext i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
  · convert Dependent.mk _ _ h
    · simp only [mk_rep, Function.comp_apply]
    · exact fun i => rep_nonzero (f i)

/-- Dependence is the negation of independence. -/
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]

/-- Independence is the negation of dependence. -/
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]

/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp]
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2]
  dsimp only [Function.comp_def, Matrix.cons_val]
  simp only [not_and, not_forall, not_not, ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v),
    mk_rep, Classical.imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)

/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp]
theorem independent_pair_iff_ne (u v : ℙ K V) : Independent ![u, v] ↔ u ≠ v := by
  rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]

@[deprecated (since := "2025-04-27")]
alias independent_pair_iff_neq := independent_pair_iff_ne

end Projectivization
