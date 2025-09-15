/-
Copyright (c) 2025 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# (Simultaneous) Diagonalization of linear maps

Given an `R`-module `M`, a *simultaneous diagonalization* of a family of `R`-linear endomorphisms
`f : α → End R M` is a basis of `M` consisting of simultaneous eigenvectors of `f`.
We define *diagonalization* as the special case where `α` is `Unit`.

## Main definitions / results:

* `LinearMap.exists_diagonalization_iff_directSum_eigenspace`:
  a linear map is diagonalizable iff the direct sum of the eigenspaces is the whole space.
* `LinearMap.exists_diagonalization_iff_iSup_eigenspace`:
  a linear map is diagonalizable iff the eigenspaces span the whole space.

## TODO

* a linear map is diagonalizable iff the minimal polynomial splits and is squarefree.
* all diagonalizable linear maps are semisimple.
* a family of linear maps is simultaneously diagonalizable iff they commute and are
  individually diagonalizable.
* `IsIdempotentElem` implies diagonalizable (https://math.stackexchange.com/a/1017060/315369)
* Generalize `exists_diagonalization_iff_directSum_eigenspace` and
  `exists_diagonalization_iff_iSup_eigenspace` to PIDs pending
  `proof_wanted Submodule.free_of_free_of_pid` in LinearAlgebra.FreeModule.PID.
  Otherwise would need separate theorems for fields and f.g. over PIDs.
* Treatment of normal endomorphisms
-/

namespace LinearMap

open Module End Matrix Polynomial

universe uR uM uK uV

variable {α : Type*} {R : Type uR} {M : Type uM} [CommRing R] [AddCommGroup M] [Module R M]
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

/--
A diagonalization of a family of linear maps $T_i : V \to V$ is a basis of $V$
consisting of simultaneous eigenvectors of $T_i$.
-/
structure SimultaneousDiagonalization (ι : Type*) (f : α → End R M) extends Basis ι R M where
  /-- The eigenvalues of the diagonalization. -/
  μ : α → ι → R
  hasEigenVector_μ (a : α) (i : ι) : (f a).HasEigenvector (μ a i) (toBasis i)

@[ext]
lemma SimultaneousDiagonalization.ext {ι : Type*} {f : α → End R M}
    {D₁ D₂ : SimultaneousDiagonalization ι f} (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  ext a i
  suffices D₁.μ a i • D₁.toBasis i = D₂.μ a i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← (D₁.hasEigenVector_μ a i).apply_eq_smul, h, ← (D₂.hasEigenVector_μ a i).apply_eq_smul]

/--
A diagonalization of a linear map $T : V \to V$ is a basis of $V$ consisting of eigenvectors of $T$.
-/
def Diagonalization (ι : Type*) (f : End R M) := SimultaneousDiagonalization ι fun _ : Unit ↦ f

@[ext]
lemma Diagonalization.ext {ι : Type*} {f : Module.End R M} {D₁ D₂ : f.Diagonalization ι}
    (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ :=
  SimultaneousDiagonalization.ext h

/-- The eigenvalues of the diagonalization. -/
def Diagonalization.μ {ι : Type*} {f : End R M} (self : f.Diagonalization ι) : R :=
  SimultaneousDiagonalization.μ self ()

lemma Diagonalization.hasEigenVector_μ {ι : Type*} {f : End R M}
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

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def diagonalization_of_isDiag_toMatrix [Nontrivial R] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : End R M} {b : Basis ι R M} (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := fun i ↦ f.toMatrix b b i i) <| fun i ↦ by
    have : f (b i) = ∑ j, f.toMatrix b b j i • b j := by simp [toMatrix_apply, b.sum_repr]
    have (j : ι) (hj : j ≠ i) : f.toMatrix b b j i = 0 := h hj
    simp_all [hasEigenvector_iff, Finset.sum_eq_single i, b.ne_zero]

/-- Get individual diagonalizations from a simultaneous diagonalization. -/
def SimultaneousDiagonalization.diagonalization {ι : Type*} {f : α → Module.End R M}
    (D : SimultaneousDiagonalization ι f) (a : α) : (f a).Diagonalization ι :=
  Diagonalization.mk (D.hasEigenVector_μ a)

/-- Construct a simultaneous diagonalization from a family of diagonalizations. -/
def SimultaneousDiagonalization.of_diagonalization {ι : Type*} {f : α → Module.End R M}
    {b : Basis ι R M} {D : (a : α) → (f a).Diagonalization ι} (h : ∀ a, (D a).toBasis = b) :
    SimultaneousDiagonalization ι f where
  toBasis := b
  μ a i := (D a).μ i
  hasEigenVector_μ a i := h a ▸ (D a).hasEigenVector_μ i

/-- Any basis diagonalizes the zero map. -/
def Diagonalization.zero [Nontrivial R] {ι : Type*} (b : Basis ι R M) :
    (0 : End R M).Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := 0) (by simp [hasEigenvector_iff, b.ne_zero])

/-- Any basis diagonalizes the identity map. -/
def diagonalization_one [Nontrivial R] {ι : Type*} (b : Basis ι R M) :
    (1 : End R M).Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := 1) (by simp [hasEigenvector_iff, b.ne_zero])

/-- Any simultaneous diagonalization of `f` also diagonalizes `c • f`. -/
def SimultaneousDiagonalization.smul {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (c : α → R) : SimultaneousDiagonalization ι (c • f) where
  toBasis := D.toBasis
  μ := c • D.μ
  hasEigenVector_μ a i := by
    have := D.hasEigenVector_μ a i
    simp_all [hasEigenvector_iff, smul_smul]

/-- Any diagonalization of `f` also diagonalizes `c • f`. -/
def Diagonalization.smul {ι : Type*} {f : End R M} (D : f.Diagonalization ι) (c : R) :
    (c • f).Diagonalization ι :=
  SimultaneousDiagonalization.smul D fun _ ↦ c

/-- Any simultaneous diagonalization of `f` also diagonalizes `f - c • 1`. -/
def SimultaneousDiagonalization.sub_smul {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (c : α → R) :
    SimultaneousDiagonalization ι (f - c • 1) where
  toBasis := D.toBasis
  μ := fun a i ↦ D.μ a i - c a
  hasEigenVector_μ a i := by
    have := D.hasEigenVector_μ a i
    simp_all [hasEigenvector_iff, _root_.sub_smul]

/-- Any diagonalization of `f` also diagonalizes `f - c • 1`. -/
def Diagonalization.sub_smul {ι : Type*} {f : End R M} (D : f.Diagonalization ι) (c : R) :
    (f - c • 1).Diagonalization ι :=
  SimultaneousDiagonalization.sub_smul D fun _ ↦ c

/-- Any simultaneous diagonalization of `f` also diagonalizes `f i + f j` for any `i` and `j`. -/
def SimultaneousDiagonalization.diagonalization_add {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (i j : α) : (f i + f j).Diagonalization ι :=
  Diagonalization.mk (b := D.toBasis) (μ := fun k ↦ D.μ i k + D.μ j k) <| fun k ↦ by
    have := D.hasEigenVector_μ i k
    have := D.hasEigenVector_μ j k
    simp_all [hasEigenvector_iff, _root_.add_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `∑ a, f a`. -/
def SimultaneousDiagonalization.diagonalization_sum [Fintype α] [Nontrivial R]
    {ι : Type*} {f : α → End R M} (D : SimultaneousDiagonalization ι f) :
    (∑ a, f a).Diagonalization ι :=
  Diagonalization.mk (b := D.toBasis) (μ := fun i ↦ ∑ a, D.μ a i) <| fun k ↦ by
    have := (D.hasEigenVector_μ · k)
    simp_all [hasEigenvector_iff, D.toBasis.ne_zero, Finset.sum_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `f i * f j` for any `i` and `j`. -/
def SimultaneousDiagonalization.diagonalization_mul {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (i j : α) : (f i * f j).Diagonalization ι :=
  Diagonalization.mk (b := D.toBasis) (μ := fun k ↦ D.μ i k * D.μ j k) <| fun k ↦ by
    have := D.hasEigenVector_μ i k
    have := D.hasEigenVector_μ j k
    simp_all [hasEigenvector_iff, smul_smul, mul_comm]

lemma Diagonalization.toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : End R M} (D : f.Diagonalization ι) : f.toMatrix D.toBasis D.toBasis = diagonal D.μ := by
  ext i j
  simp [toMatrix_apply, (D.hasEigenVector_μ j).apply_eq_smul]
  grind [Finsupp.single_apply, diagonal_apply]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma Diagonalization.charpoly_eq [Nontrivial R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Free R M]
    [Module.Finite R M] {f : End R M} (D : f.Diagonalization ι) :
    f.charpoly = ∏ i, (X - C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, charpoly_diagonal]

lemma Diagonalization.splits_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite K V]
    {f : End K V} (D : f.Diagonalization ι) : f.charpoly.Splits (RingHom.id K) := by
  simp [D.charpoly_eq, splits_prod_iff, X_sub_C_ne_zero, splits_X_sub_C]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma Diagonalization.isRoot_charpoly [Nontrivial R] [IsDomain R] [Module.Finite R M] [Free R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : End R M} (D : f.Diagonalization ι) (i : ι) :
    f.charpoly.IsRoot (D.μ i) := by
  rw [D.charpoly_eq, Polynomial.isRoot_prod]
  use i
  simp

lemma Diagonalization.iSup_eigenspace {ι : Type*} {f : End R M} (D : f.Diagonalization ι) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  rw [eq_top_iff, ← Basis.span_eq D.toBasis, Submodule.span_le, Set.range_subset_iff]
  exact fun i ↦ Submodule.mem_iSup_of_mem (D.μ i) (hasEigenvector_iff.mp (D.hasEigenVector_μ i)).1

lemma exists_diagonalization_iff_directSum_eigenspace [DecidableEq K] {f : End K V} :
    (∃ ι : Type uV, Nonempty (f.Diagonalization ι)) ↔ DirectSum.IsInternal f.eigenspace := by
  -- There may be a shorter proof for fields, but this proof should work over PIDs too;
  -- see TODO notes for this file.
  constructor <;> intro h
  · obtain ⟨ι, ⟨D⟩⟩ := h
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f,
      D.iSup_eigenspace]
  · let v := fun i ↦ (Free.exists_basis K (f.eigenspace i)).some.2
    let B' := h.collectedBasis v -- universe (max u v)
    let e := B'.indexEquiv (Free.exists_basis K V).some.2
    let B := B'.reindex e -- move to universe v
    refine ⟨_, ⟨Diagonalization.mk (b := B) (μ := (e.symm · |>.1)) fun i ↦ ?_⟩⟩
    rw [hasEigenvector_iff, B'.reindex_apply]
    exact ⟨h.collectedBasis_mem v _, B'.ne_zero _⟩

lemma exists_diagonalization_iff_iSup_eigenspace {f : End K V} :
    (∃ ι : Type uV, Nonempty (f.Diagonalization ι)) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by classical calc
  _ ↔ DirectSum.IsInternal f.eigenspace := exists_diagonalization_iff_directSum_eigenspace
  _ ↔ _ := by
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f]

lemma SimultaneousDiagonalization.commute {ι : Type*} {f : α → End R M}
    (D : SimultaneousDiagonalization ι f) (i j : α) : Commute (f i) (f j) := by
  refine D.toBasis.ext fun k ↦ ?_
  have := D.hasEigenVector_μ i k
  have := D.hasEigenVector_μ j k
  simp_all [hasEigenvector_iff, smul_smul, mul_comm]

end LinearMap
