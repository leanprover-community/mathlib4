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

universe uS uM uC uM' uR uG uK uV

variable {α : Type*}
variable {S : Type uS} {M : Type uM} [Semiring S] [AddCommMonoid M] [Module S M]
variable {C : Type uC} {M' : Type uM'} [CommSemiring C] [AddCommMonoid M'] [Module C M']
variable {R : Type uR} {G : Type uG} [CommRing R] [AddCommGroup G] [Module R G]
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

/--
A diagonalization of a family of linear maps $T_i : V \to V$ is a basis of $V$
consisting of simultaneous eigenvectors of $T_i$.
-/
structure SimultaneousDiagonalization (ι : Type*) (f : α → End S M) extends Basis ι S M where
  /-- The eigenvalues of the diagonalization. -/
  μ : α → ι → S
  /--
  We don't use `Module.End.HasEigenvector`, as it's slightly more convenient for all bases
  of modules over the trivial ring to be considered eigenbases, even the degenerate ones like
  `![0, 0, 0, ...]`.
  -/
  apply_toBasis (a : α) (i : ι) : f a (toBasis i) = μ a i • toBasis i

/--
A diagonalization of a linear map $T : V \to V$ is a basis of $V$ consisting of eigenvectors of $T$.
-/
def Diagonalization (ι : Type*) (f : End S M) := SimultaneousDiagonalization ι fun _ : Unit ↦ f

/-- Cpnstruct `LinearMap.Diagonalization` from a basis of eigenvectors and eigenvalues. -/
def Diagonalization.mk {ι : Type*} {f : End S M} {b : Basis ι S M} {μ : ι → S}
    (apply_toBasis : ∀ i, f (b i) = μ i • b i) : f.Diagonalization ι where
  toBasis := b
  μ := fun _ ↦ μ
  apply_toBasis := fun _ => apply_toBasis

/-- The eigenvalues of the diagonalization. -/
def Diagonalization.μ {ι : Type*} {f : End S M} (self : f.Diagonalization ι) : ι → S :=
  SimultaneousDiagonalization.μ self ()

lemma Diagonalization.apply_toBasis {ι : Type*} {f : End S M} (self : f.Diagonalization ι)
    (i : ι) : f (self.toBasis i) = self.μ i • self.toBasis i :=
  SimultaneousDiagonalization.apply_toBasis self () i

namespace SimultaneousDiagonalization

@[ext]
lemma ext {ι : Type*} {f : α → End S M} {D₁ D₂ : SimultaneousDiagonalization ι f}
    (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  ext a i
  suffices D₁.μ a i • D₁.toBasis i = D₂.μ a i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← D₁.apply_toBasis a i, h, ← D₂.apply_toBasis a i]

/--
Alternative constructor for `LinearMap.SimultaneousDiagonalization` from existence of eigenvalues.
-/
noncomputable def ofExists {ι : Type*} {f : α → End S M} {b : Basis ι S M}
    (exists_apply_toBasis : ∀ a i, ∃ μ : S, f a (b i) = μ • b i) :
    SimultaneousDiagonalization ι f where
  toBasis := b
  μ := fun a i ↦ (exists_apply_toBasis a i).choose
  apply_toBasis := fun a i => (exists_apply_toBasis a i).choose_spec

/--
Alternative constructor for `LinearMap.SimultaneousDiagonalization`
using `Module.End.HasEigenvector`.
-/
noncomputable def ofHasEigenVector {ι : Type*} {f : α → End R G} {b : Basis ι R G}
    {μ : α → ι → R} (hasEigenvector_μ : ∀ a i, (f a).HasEigenvector (μ a i) (b i)) :
    SimultaneousDiagonalization ι f where
  toBasis := b
  μ := μ
  apply_toBasis a i := (hasEigenvector_μ a i).apply_eq_smul

/--
Alternative constructor for `LinearMap.SimultaneousDiagonalization`
using existence of eigenvalues and `Module.End.HasEigenvector`.
-/
noncomputable def ofExistsHasEigenVector {ι : Type*} {f : α → End R G} {b : Basis ι R G}
    (exists_hasEigenvector_μ : ∀ a i, ∃ μ : R, (f a).HasEigenvector μ (b i)) :
    SimultaneousDiagonalization ι f :=
  ofHasEigenVector (exists_hasEigenvector_μ · · |>.choose_spec)

/--
Alternative constructor for `LinearMap.SimultaneousDiagonalization` from a basis of eigenvectors and
diagonality of the matrix representations.
-/
noncomputable def ofIsDiagToMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : α → End C M'} {b : Basis ι C M'} (h : ∀ a, ((f a).toMatrix b b).IsDiag) :
    SimultaneousDiagonalization ι f where
  toBasis := b
  μ := fun a i ↦ (f a).toMatrix b b i i
  apply_toBasis a i := calc
    f a (b i) = ∑ j, (f a).toMatrix b b j i • b j := by simp [toMatrix_apply, b.sum_repr]
    _ = _ := by rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [h a hj]) (by simp)]

theorem hasEigenVector_μ [Nontrivial R] {ι : Type*} {f : α → End R G}
    (D : SimultaneousDiagonalization ι f) (a : α) (i : ι) :
    (f a).HasEigenvector (D.μ a i) (D.toBasis i) :=
  hasEigenvector_iff.mpr ⟨mem_eigenspace_iff.mpr (D.apply_toBasis a i), D.toBasis.ne_zero i⟩

/-- Get individual diagonalizations from a simultaneous diagonalization. -/
def diagonalization {ι : Type*} {f : α → Module.End S M}
    (D : SimultaneousDiagonalization ι f) (a : α) : (f a).Diagonalization ι :=
  .mk (D.apply_toBasis a)

/-- Construct a simultaneous diagonalization from a family of diagonalizations. -/
def ofDiagonalization {ι : Type*} {f : α → Module.End S M}
    {b : Basis ι S M} {D : (a : α) → (f a).Diagonalization ι} (h : ∀ a, (D a).toBasis = b) :
    SimultaneousDiagonalization ι f where
  toBasis := b
  μ a i := (D a).μ i
  apply_toBasis a i := h a ▸ (D a).apply_toBasis i

/-- Any simultaneous diagonalization of `f` also diagonalizes `c • f`. -/
def smul {ι : Type*} {f : α → End C M'} (D : SimultaneousDiagonalization ι f) (c : α → C) :
    SimultaneousDiagonalization ι (c • f) where
  toBasis := D.toBasis
  μ := c • D.μ
  apply_toBasis a i := by simp [D.apply_toBasis, smul_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `f - c • 1`. -/
def subSmulOne {ι : Type*} {f : α → End R G} (D : SimultaneousDiagonalization ι f) (c : α → R) :
    SimultaneousDiagonalization ι (f - c • 1) where
  toBasis := D.toBasis
  μ := fun a i ↦ D.μ a i - c a
  apply_toBasis a i := by simp [D.apply_toBasis, sub_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `f i + f j` for any `i` and `j`. -/
def diagonalizationAdd {ι : Type*} {f : α → End S M} (D : SimultaneousDiagonalization ι f)
    (i j : α) : (f i + f j).Diagonalization ι :=
  .mk (b := D.toBasis) (μ := D.μ i + D.μ j) <| fun k ↦ by simp [D.apply_toBasis, add_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `∑ a, f a`. -/
def diagonalizationSum [Fintype α] {ι : Type*} {f : α → End S M}
    (D : SimultaneousDiagonalization ι f) : (∑ a, f a).Diagonalization ι :=
  .mk (b := D.toBasis) (μ := ∑ a, D.μ a) <| fun k ↦ by simp [D.apply_toBasis, Finset.sum_smul]

/-- Any simultaneous diagonalization of `f` also diagonalizes `f i * f j` for any `i` and `j`. -/
def diagonalizationMul {ι : Type*} {f : α → End S M} (D : SimultaneousDiagonalization ι f)
    (i j : α) : (f i * f j).Diagonalization ι :=
  .mk (b := D.toBasis) (μ := D.μ j * D.μ i) <| fun k ↦ by simp [D.apply_toBasis, smul_smul]

lemma commute {ι : Type*} {f : α → End C M'} (D : SimultaneousDiagonalization ι f) (i j : α) :
    Commute (f i) (f j) :=
  D.toBasis.ext fun k ↦ by simp [D.apply_toBasis, smul_smul, mul_comm]

end SimultaneousDiagonalization

namespace Diagonalization

@[ext]
lemma ext {ι : Type*} {f : Module.End S M} {D₁ D₂ : f.Diagonalization ι}
    (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ :=
  SimultaneousDiagonalization.ext h

/-- Alternative constructor for `LinearMap.Diagonalization` from existence of eigenvalues. -/
noncomputable def ofExists {ι : Type*} {f : End S M} {b : Basis ι S M}
    (exists_apply_toBasis : ∀ i, ∃ μ : S, f (b i) = μ • b i) : f.Diagonalization ι :=
  SimultaneousDiagonalization.ofExists fun _ ↦ exists_apply_toBasis

/-- Alternative constructor for `LinearMap.Diagonalization` using `Module.End.HasEigenvector`. -/
noncomputable def ofHasEigenVector {ι : Type*} {f : End R G} {b : Basis ι R G} {μ : ι → R}
    (hasEigenvector_μ : ∀ i, f.HasEigenvector (μ i) (b i)) : f.Diagonalization ι :=
  SimultaneousDiagonalization.ofHasEigenVector fun _ ↦ hasEigenvector_μ

/--
Alternative constructor for `LinearMap.SimultaneousDiagonalization`
using existence of eigenvalues and `Module.End.HasEigenvector`.
-/
noncomputable def ofExistsHasEigenVector {ι : Type*} {f : End R G} {b : Basis ι R G}
    (exists_hasEigenvector_μ : ∀ i, ∃ μ : R, f.HasEigenvector μ (b i)) : f.Diagonalization ι :=
  SimultaneousDiagonalization.ofExistsHasEigenVector fun _ ↦ exists_hasEigenvector_μ

theorem hasEigenVector_μ [Nontrivial R] {ι : Type*} {f : End R G} (D : f.Diagonalization ι)
    (i : ι) : f.HasEigenvector (D.μ i) (D.toBasis i) :=
  SimultaneousDiagonalization.hasEigenVector_μ D () i

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def ofIsDiagToMatrix {ι : Type*} [Fintype ι]
    [DecidableEq ι] {f : End C M'} {b : Basis ι C M'} (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι :=
  SimultaneousDiagonalization.ofIsDiagToMatrix fun _ ↦ h

/-- Any basis diagonalizes the zero map. -/
def zero {ι : Type*} (b : Basis ι S M) : (0 : End S M).Diagonalization ι :=
  .mk (b := b) (μ := 0) (by simp)

/-- Any basis diagonalizes the identity map. -/
def one {ι : Type*} (b : Basis ι S M) : (1 : End S M).Diagonalization ι :=
  .mk (b := b) (μ := 1) (by simp)

/-- Any diagonalization of `f` also diagonalizes `c • f`. -/
def smul {ι : Type*} {f : End C M'} (D : f.Diagonalization ι) (c : C) : (c • f).Diagonalization ι :=
  SimultaneousDiagonalization.smul D fun _ ↦ c

/-- Any diagonalization of `f` also diagonalizes `f - c • 1`. -/
def subSmulOne {ι : Type*} {f : End R G} (D : f.Diagonalization ι) (c : R) :
    (f - c • 1).Diagonalization ι :=
  SimultaneousDiagonalization.subSmulOne D fun _ ↦ c

lemma toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] {f : End C M'}
    (D : f.Diagonalization ι) : f.toMatrix D.toBasis D.toBasis = diagonal D.μ := by
  ext i j
  simp [toMatrix_apply, D.apply_toBasis j]
  grind [Finsupp.single_apply, diagonal_apply]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma charpoly_eq [Nontrivial R] {ι : Type*} [Fintype ι] [DecidableEq ι] [Free R G]
    [Module.Finite R G] {f : End R G} (D : f.Diagonalization ι) :
    f.charpoly = ∏ i, (X - .C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, charpoly_diagonal]

lemma splits_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι] [Module.Finite K V] {f : End K V}
    (D : f.Diagonalization ι) : f.charpoly.Splits (RingHom.id K) := by
  simp [D.charpoly_eq, splits_prod_iff, X_sub_C_ne_zero, splits_X_sub_C]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma isRoot_charpoly [Nontrivial R] [IsDomain R] [Module.Finite R G] [Free R G] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {f : End R G} (D : f.Diagonalization ι) (i : ι) :
    f.charpoly.IsRoot (D.μ i) := by
  rw [D.charpoly_eq, Polynomial.isRoot_prod]
  use i
  simp

lemma iSup_eigenspace {ι : Type*} {f : End R G} (D : f.Diagonalization ι) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  nontriviality R
  rw [eq_top_iff, ← Basis.span_eq D.toBasis, Submodule.span_le, Set.range_subset_iff]
  exact fun i ↦ Submodule.mem_iSup_of_mem (D.μ i) (hasEigenvector_iff.mp (D.hasEigenVector_μ i)).1

end Diagonalization

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
    refine ⟨_, ⟨.mk (b := B) (μ := (e.symm · |>.1)) fun i ↦ ?_⟩⟩
    rw [B'.reindex_apply, ← mem_eigenspace_iff]
    exact h.collectedBasis_mem v _

lemma exists_diagonalization_iff_iSup_eigenspace {f : End K V} :
    (∃ ι : Type uV, Nonempty (f.Diagonalization ι)) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by classical calc
  _ ↔ DirectSum.IsInternal f.eigenspace := exists_diagonalization_iff_directSum_eigenspace
  _ ↔ _ := by
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f]

end LinearMap
