/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
import Mathlib.LinearAlgebra.ProjectiveSpace.Basic

#align_import linear_algebra.projective_space.independence from "leanprover-community/mathlib"@"1e82f5ec4645f6a92bb9e02fce51e44e3bc3e1fe"

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


variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : ι → ℙ K V}

namespace Projectivization

/-- A linearly independent family of nonzero vectors gives an independent family of points
in projective space. -/
inductive Independent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (hl : LinearIndependent K f) :
    Independent fun i => mk K (f i) (hf i)
#align projectivization.independent Projectivization.Independent

/-- A family of points in a projective space is independent if and only if the representative
vectors determined by the family are linearly independent. -/
theorem independent_iff : Independent f ↔ LinearIndependent K (Projectivization.rep ∘ f) := by
  refine' ⟨_, fun h => _⟩
  -- ⊢ Independent f → LinearIndependent K (Projectivization.rep ∘ f)
  · rintro ⟨ff, hff, hh⟩
    -- ⊢ LinearIndependent K (Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ …
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    -- ⊢ LinearIndependent K (Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ …
    convert hh.units_smul a
    -- ⊢ (Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ 0)) = a • ff
    ext i
    -- ⊢ (Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ 0)) i = (a • ff) i
    exact (ha i).symm
    -- 🎉 no goals
  · convert Independent.mk _ _ h
    -- ⊢ f x✝ = mk K ((Projectivization.rep ∘ f) x✝) (_ : ?m.12147 x✝ ≠ 0)
    · simp only [mk_rep, Function.comp_apply]
      -- 🎉 no goals
    · intro i
      -- ⊢ (Projectivization.rep ∘ f) i ≠ 0
      apply rep_nonzero
      -- 🎉 no goals
#align projectivization.independent_iff Projectivization.independent_iff

/-- A family of points in projective space is independent if and only if the family of
submodules which the points determine is independent in the lattice-theoretic sense. -/
theorem independent_iff_completeLattice_independent :
    Independent f ↔ CompleteLattice.Independent fun i => (f i).submodule := by
  refine' ⟨_, fun h => _⟩
  -- ⊢ Independent f → CompleteLattice.Independent fun i => Projectivization.submod …
  · rintro ⟨f, hf, hi⟩
    -- ⊢ CompleteLattice.Independent fun i => Projectivization.submodule ((fun i => m …
    simp only [submodule_mk]
    -- ⊢ CompleteLattice.Independent fun i => Submodule.span K {f i}
    exact (CompleteLattice.independent_iff_linearIndependent_of_ne_zero (R := K) hf).mpr hi
    -- 🎉 no goals
  · rw [independent_iff]
    -- ⊢ LinearIndependent K (Projectivization.rep ∘ f)
    refine' h.linearIndependent (Projectivization.submodule ∘ f) (fun i => _) fun i => _
    -- ⊢ (Projectivization.rep ∘ f) i ∈ (Projectivization.submodule ∘ f) i
    · simpa only [Function.comp_apply, submodule_eq] using Submodule.mem_span_singleton_self _
      -- 🎉 no goals
    · exact rep_nonzero (f i)
      -- 🎉 no goals
#align projectivization.independent_iff_complete_lattice_independent Projectivization.independent_iff_completeLattice_independent

/-- A linearly dependent family of nonzero vectors gives a dependent family of points
in projective space. -/
inductive Dependent : (ι → ℙ K V) → Prop
  | mk (f : ι → V) (hf : ∀ i : ι, f i ≠ 0) (h : ¬LinearIndependent K f) :
    Dependent fun i => mk K (f i) (hf i)
#align projectivization.dependent Projectivization.Dependent

/-- A family of points in a projective space is dependent if and only if their
representatives are linearly dependent. -/
theorem dependent_iff : Dependent f ↔ ¬LinearIndependent K (Projectivization.rep ∘ f) := by
  refine' ⟨_, fun h => _⟩
  -- ⊢ Dependent f → ¬LinearIndependent K (Projectivization.rep ∘ f)
  · rintro ⟨ff, hff, hh1⟩
    -- ⊢ ¬LinearIndependent K (Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i  …
    contrapose! hh1
    -- ⊢ LinearIndependent K ff
    choose a ha using fun i : ι => exists_smul_eq_mk_rep K (ff i) (hff i)
    -- ⊢ LinearIndependent K ff
    convert hh1.units_smul a⁻¹
    -- ⊢ ff = a⁻¹ • Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ 0)
    ext i
    -- ⊢ ff i = (a⁻¹ • Projectivization.rep ∘ fun i => mk K (ff i) (_ : ff i ≠ 0)) i
    simp only [← ha, inv_smul_smul, Pi.smul_apply', Pi.inv_apply, Function.comp_apply]
    -- 🎉 no goals
  · convert Dependent.mk _ _ h
    -- ⊢ f x✝ = mk K ((Projectivization.rep ∘ f) x✝) (_ : ?m.30442 x✝ ≠ 0)
    · simp only [mk_rep, Function.comp_apply]
      -- 🎉 no goals
    · exact fun i => rep_nonzero (f i)
      -- 🎉 no goals
#align projectivization.dependent_iff Projectivization.dependent_iff

/-- Dependence is the negation of independence. -/
theorem dependent_iff_not_independent : Dependent f ↔ ¬Independent f := by
  rw [dependent_iff, independent_iff]
  -- 🎉 no goals
#align projectivization.dependent_iff_not_independent Projectivization.dependent_iff_not_independent

/-- Independence is the negation of dependence. -/
theorem independent_iff_not_dependent : Independent f ↔ ¬Dependent f := by
  rw [dependent_iff_not_independent, Classical.not_not]
  -- 🎉 no goals
#align projectivization.independent_iff_not_dependent Projectivization.independent_iff_not_dependent

/-- Two points in a projective space are dependent if and only if they are equal. -/
@[simp]
theorem dependent_pair_iff_eq (u v : ℙ K V) : Dependent ![u, v] ↔ u = v := by
  rw [dependent_iff_not_independent, independent_iff, linearIndependent_fin2,
    Function.comp_apply, Matrix.cons_val_one, Matrix.head_cons, Ne.def]
  simp only [Matrix.cons_val_zero, not_and, not_forall, Classical.not_not, Function.comp_apply,
    ← mk_eq_mk_iff' K _ _ (rep_nonzero u) (rep_nonzero v), mk_rep, imp_iff_right_iff]
  exact Or.inl (rep_nonzero v)
  -- 🎉 no goals
#align projectivization.dependent_pair_iff_eq Projectivization.dependent_pair_iff_eq

/-- Two points in a projective space are independent if and only if the points are not equal. -/
@[simp]
theorem independent_pair_iff_neq (u v : ℙ K V) : Independent ![u, v] ↔ u ≠ v := by
  rw [independent_iff_not_dependent, dependent_pair_iff_eq u v]
  -- 🎉 no goals
#align projectivization.independent_pair_iff_neq Projectivization.independent_pair_iff_neq

end Projectivization
