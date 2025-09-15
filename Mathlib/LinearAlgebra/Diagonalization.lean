/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Semisimple

/-!
# (Simultaneous) Diagonalization of linear maps

Given an `R`-module `M`, a *simultaneous diagonalization* of a family of `R`-linear endomorphisms
`f : α → End R M` is a basis of `M` consisting of simultaneous eigenvectors of `f`.
We define *diagonalization* as the special case where `α` is `Unit`.

## Main definitions / results:

* `LinearMap.diagonalization_of_isDiag_toMatrix`:
  a basis for which the matrix representation is diagonal is a diagonalization.
* `LinearMap.exists_diagonalization_iff_directSum_eigenspace`:
  a linear map is diagonalizable iff the direct sum of the eigenspaces is the whole space.
* `LinearMap.exists_diagonalization_iff_iSup_eigenspace`:
  a linear map is diagonalizable iff the eigenspaces span the whole space.
* `LinearMap.Diagonalization.μ_equiv`:
  all diagonalizations of a linear map have the same eigenvalues up to permutation.

## TODO

* `LinearMap.exists_diagonalization_iff_minpoly_splits_and_squarefree`:
  a linear map is diagonalizable iff the minimal polynomial splits and is squarefree.
* `LinearMap.Diagonalization.isSemisimple`: all diagonalizable linear maps are semisimple.
* `LinearMap.exists_simultaneousDiagonalization_iff_commute`: a family of linear maps is
  simultaneously diagonalizable iff they commute and are individually diagonalizable.
* `IsIdempotentElem` implies diagonalizable (https://math.stackexchange.com/a/1017060/315369)
* Treatment of normal endomorphisms
-/

namespace LinearMap

open Module End Matrix Polynomial

universe u v

variable {α : Type*} {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {K : Type u} [Field K] [Module K M]

/--
A diagonalization of a family of linear maps $T_i : V \to V$ is a basis of $V$
consisting of simultaneous eigenvectors of $T_i$.
-/
structure SimultaneousDiagonalization (ι : Type*) (f : α → End R M) extends Basis ι R M where
  μ : α → ι → R
  hasEigenVector_μ (a : α) (i : ι) : (f a).HasEigenvector (μ a i) (toBasis i)

/--
A diagonalization of a linear map $T : V \to V$ is a basis of $V$ consisting of eigenvectors of $T$.
-/
abbrev Diagonalization (ι : Type*) (f : End R M) := SimultaneousDiagonalization ι fun _ : Unit ↦ f

/-- The eigenvalues of the diagonalization. -/
def Diagonalization.μ {ι : Type*} {f : End R M} (self : f.Diagonalization ι) :=
  SimultaneousDiagonalization.μ self ()

theorem Diagonalization.hasEigenVector_μ {ι : Type*} {f : End R M}
    (self : f.Diagonalization ι) (i : ι) : f.HasEigenvector (self.μ i) (self.toBasis i) :=
  SimultaneousDiagonalization.hasEigenVector_μ self () i

/-- Cpnstruct `LinearMap.Diagonalization` from a basis of eigenvectors and eigenvalues. -/
def Diagonalization.mk {ι : Type*} {f : End R M} {b : Basis ι R M} {μ : ι → R}
    (hasEigenVector_μ : ∀ i, f.HasEigenvector (μ i) (b i)) : f.Diagonalization ι where
  toBasis := b
  μ := fun _ ↦ μ
  hasEigenVector_μ := fun _ => hasEigenVector_μ

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
existence of eigenvalues.
-/
noncomputable def Diagonalization.mk' {ι : Type*} {f : End R M} {b : Basis ι R M}
    (exists_hasEigenVector : ∀ i, ∃ μ, f.HasEigenvector μ (b i)) : f.Diagonalization ι where
  toBasis := b
  μ := fun _ i ↦ (exists_hasEigenVector i).choose
  hasEigenVector_μ := fun _ i => (exists_hasEigenVector i).choose_spec

/-- A basis for the module gives a diagonalization for the zero map. -/
def diagonalization_zero [Nontrivial R] {ι : Type*} (b : Basis ι R M) :
    (0 : End R M).Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := 0) (by simp [hasEigenvector_iff, b.ne_zero])

/-- A basis for the module gives a diagonalization for the identity map. -/
def diagonalization_one [Nontrivial R] {ι : Type*} (b : Basis ι R M) :
    (1 : End R M).Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := 1) (by simp [hasEigenvector_iff, b.ne_zero])

/-- A diagonalization of `f` can be scaled to give a diagonalization of `c • f`. -/
def SimultaneousDiagonalization.smul {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (c : R) : SimultaneousDiagonalization ι (c • f) where
  toBasis := D.toBasis
  μ := fun a i ↦ c * D.μ a i
  hasEigenVector_μ a i := by
    have := D.hasEigenVector_μ a i
    simp_all [hasEigenvector_iff, smul_smul]

def Diagonalization.smul {ι : Type*} {f : End R M} (D : f.Diagonalization ι) (c : R) :
    (c • f).Diagonalization ι :=
  SimultaneousDiagonalization.smul D c

def SimultaneousDiagonalization.diagonalization_sum [Fintype α] {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) : (∑ a, f a).Diagonalization ι :=
  Diagonalization.mk (b := D.toBasis) (μ := fun i ↦ ∑ a, D.μ a i) <| by
    sorry

def SimultaneousDiagonalization.diagonalization_mul [Fintype α] {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (i j : α) : (f i * f j).Diagonalization ι :=
  Diagonalization.mk (b := D.toBasis) (μ := fun k ↦ D.μ i k * D.μ j k) <| by
    sorry

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def diagonalization_of_isDiag_toMatrix [Nontrivial R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : End R M} {b : Basis ι R M} (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := fun i ↦ f.toMatrix b b i i) <| by
    intro i
    have : f (b i) = ∑ j, f.toMatrix b b j i • b j := by simp [toMatrix_apply, b.sum_repr]
    have (j : ι) (hj : j ≠ i) : f.toMatrix b b j i = 0 := h hj
    simp_all [hasEigenvector_iff, Finset.sum_eq_single i, b.ne_zero]

/-- The diagonalization of the endomorphism indexed by `a`. -/
def SimultaneousDiagonalization.diagonalization {ι : Type*} {f : α → Module.End R M}
    (D : SimultaneousDiagonalization ι f) (a : α) : (f a).Diagonalization ι :=
  Diagonalization.mk (D.hasEigenVector_μ a)

@[ext]
theorem SimultaneousDiagonalization.ext {ι : Type*} {f : α → End R M}
    {D₁ D₂ : SimultaneousDiagonalization ι f} (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  ext a i
  suffices D₁.μ a i • D₁.toBasis i = D₂.μ a i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← (D₁.hasEigenVector_μ a i).apply_eq_smul, h, ← (D₂.hasEigenVector_μ a i).apply_eq_smul]

example {ι} {f : Module.End R M} {D₁ D₂ : f.Diagonalization ι} (h : D₁.toBasis = D₂.toBasis) :
    D₁ = D₂ := by
  ext : 1
  exact h

lemma Diagonalization.toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : End R M} (D : f.Diagonalization ι) : f.toMatrix D.toBasis D.toBasis = diagonal D.μ := by
  ext i j
  simp [toMatrix_apply, (D.hasEigenVector_μ j).apply_eq_smul]
  grind [Finsupp.single_apply, diagonal_apply]

-- note: [Nontrivial R] golfed in #29420
lemma Diagonalization.charpoly_eq [Nontrivial R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Free R M]
    [Module.Finite R M] {f : End R M} (D : f.Diagonalization ι) :
    f.charpoly = ∏ i, (X - C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, charpoly_diagonal]

lemma Diagonalization.splits_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite K M]
    {f : End K M} (D : f.Diagonalization ι) : f.charpoly.Splits (RingHom.id K) := by
  simp [D.charpoly_eq, splits_prod_iff, X_sub_C_ne_zero, splits_X_sub_C]

lemma Diagonalization.isRoot_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite K M]
    {f : End K M} (D : f.Diagonalization ι) (i : ι) : f.charpoly.IsRoot (D.μ i) := by
  rw [D.charpoly_eq, Polynomial.isRoot_prod]
  use i
  simp

lemma Diagonalization.iSup_eigenspace {ι : Type*} {f : End R M} (D : f.Diagonalization ι) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  rw [eq_top_iff, ← Basis.span_eq D.toBasis, Submodule.span_le, Set.range_subset_iff]
  exact fun i ↦ Submodule.mem_iSup_of_mem (D.μ i) (hasEigenvector_iff.mp (D.hasEigenVector_μ i)).1

/--
TODO: This proof also goes through for
`[IsPrincipalIdealRing R] [IsDomain R] [Module.Finite R M] [NoZeroSMulDivisors R M]`,
but the f.g. condition is unnecessary for fields. If the
`proof_wanted Submodule.free_of_free_of_pid` is resolved, then we can change the assumption here to
`[IsPrincipalIdealRing R] [IsDomain R] [Free R M] [NoZeroSMulDivisors R M]` which handles both the
field and PID cases.
-/
lemma exists_diagonalization_iff_directSum_eigenspace [DecidableEq K] [Free K M] {f : End K M} :
    (∃ ι : Type v, Nonempty (f.Diagonalization ι)) ↔ DirectSum.IsInternal f.eigenspace := by
  constructor <;> intro h
  · obtain ⟨ι, ⟨D⟩⟩ := h
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f,
      D.iSup_eigenspace]
  · let v := fun i ↦ (Free.exists_basis K (f.eigenspace i)).some.2
    let B' := h.collectedBasis v -- universe (max u v)
    let e := B'.indexEquiv (Free.exists_basis K M).some.2
    let B := B'.reindex e -- move to universe v
    refine ⟨_, ⟨Diagonalization.mk (b := B) (μ := (e.symm · |>.1)) fun i ↦ ?_⟩⟩
    rw [hasEigenvector_iff, B'.reindex_apply]
    exact ⟨h.collectedBasis_mem v _, B'.ne_zero _⟩

lemma exists_diagonalization_iff_iSup_eigenspace [Free K M] {f : End K M} :
    (∃ ι : Type v, Nonempty (f.Diagonalization ι)) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by classical calc
  _ ↔ DirectSum.IsInternal f.eigenspace := exists_diagonalization_iff_directSum_eigenspace
  _ ↔ _ := by
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f]

proof_wanted exists_diagonalization_iff_minpoly_splits_and_squarefree {f : End K M} :
    (∃ ι : Type v, Nonempty (f.Diagonalization ι)) ↔
    (minpoly K f).Splits (RingHom.id K) ∧ Squarefree (minpoly K f)

proof_wanted Diagonalization.isSemisimple {ι : Type*} [IsSemisimpleModule R M]
    {f : End R M} (D : f.Diagonalization ι) : f.IsSemisimple

-- This is proved: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/diagonalizable.20linear.20maps/near/539282397
theorem LinearMap.Diagonalization.μ_equiv {ι ι' R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} {D₁ : f.Diagonalization ι} {D₂ : f.Diagonalization ι'} :
    ∃ e : ι ≃ ι', D₁.μ = D₂.μ ∘ e := by
  sorry

proof_wanted exists_simultaneousDiagonalization_iff_commute {f : α → End R M} :
    (∃ ι : Type v, Nonempty (SimultaneousDiagonalization ι f)) ↔
    (∀ i : α, ∃ ι : Type v, Nonempty (Diagonalization ι (f i))) ∧
    ∀ i j : α, Commute (f i) (f j)

end LinearMap
