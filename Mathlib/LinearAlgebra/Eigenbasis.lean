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
# (Common) eigenbases / (simultaneous) diagonalization of linear maps

Given an `R`-module `M`, a *common eigenbasis* of a family of `R`-linear endomorphisms
`f : α → End R M` is a basis of `M` consisting of common eigenvectors of `f`.

If the family is of a single map `f : End R M`, then we call this an *eigenbasis* of `f`.

*Diagonalization* and *simultaneous diagonalization* are considered synonyms for *eigenbasis*
and *common eigenbasis* respectively. *Diagonalizability* is the existence of an eigenbasis,
spelled as `∃ ι : Type u, Nonempty (f.Eigenbasis ι)` with the naming convention `exists_eigenbasis`.

## Main definitions / results:

* `LinearMap.CommonEigenbasis`: extension of `Module.Basis` with the common eigenvector property.
* `LinearMap.Eigenbasis`:
  special case of `LinearMap.CommonEigenbasis` where the family is indexed by `Unit`.
* `LinearMap.exists_eigenbasis_iff_directSum_eigenspace`:
  a linear map is diagonalizable iff the direct sum of the eigenspaces is the whole space.
* `LinearMap.exists_eigenbasis_iff_iSup_eigenspace`:
  a linear map is diagonalizable iff the eigenspaces span the whole space.

## TODO

* a linear map is diagonalizable iff the minimal polynomial splits and is squarefree.
* all diagonalizable linear maps are semisimple.
* a family of linear maps is simultaneously diagonalizable iff they commute and are
  individually diagonalizable.
* `IsIdempotentElem` implies diagonalizable (https://math.stackexchange.com/a/1017060/315369)
* Generalize `exists_eigenbasis_iff_directSum_eigenspace` and
  `exists_eigenbasis_iff_iSup_eigenspace` to PIDs pending
  `proof_wanted Submodule.free_of_free_of_pid` in LinearAlgebra.FreeModule.PID.
  Otherwise would need separate theorems for fields and f.g. over PIDs.
* Treatment of normal endomorphisms
-/

namespace LinearMap

open Module End Matrix Polynomial

universe uS uM uC uM' uR uG uK uV

variable {α ι : Type*}
variable {S : Type uS} {M : Type uM} [Semiring S] [AddCommMonoid M] [Module S M]
variable {C : Type uC} {M' : Type uM'} [CommSemiring C] [AddCommMonoid M'] [Module C M']
variable {R : Type uR} {G : Type uG} [CommRing R] [AddCommGroup G] [Module R G]
variable {K : Type uK} {V : Type uV} [Field K] [AddCommGroup V] [Module K V]

/--
An common eigenbasis (a.k.a. simultaneous diagonalization) of a family of linear maps
$T_i : V \to V$ is a basis of $V$ consisting of common eigenvectors of $T_i$.

Simultaneous diagonalizability is the existence of a common eigenbasis, spelled as
`∃ ι : Type u, Nonempty (CommonEigenbasis ι f)` with the naming convention
`exists_commonEigenbasis`.
-/
structure CommonEigenbasis (ι : Type*) (f : α → End S M) extends Basis ι S M where
  /-- The eigenvalues of the eigenbasis. -/
  μ : α → ι → S
  /--
  The eigenvector property. The definition matches `Module.End.HasEigenvector.apply_eq_smul`,
  but don't use `Module.End.HasEigenvector`, as it's slightly more convenient to admit the
  degenerate bases over the trivial ring; for `Nontrivial R`, we can still get
  `CommonEigenbasis.ofHasEigenVector` and `CommonEigenbasis.hasEigenVector_μ`.
  -/
  apply_eq_smul (a : α) (i : ι) : f a (toBasis i) = μ a i • toBasis i

/--
An eigenbasis (a.k.a. diagonalization) of a linear map $T : V \to V$ is a basis of $V$
consisting of eigenvectors of $T$.

Diagonalizability is the existence of an eigenbasis, spelled as
`∃ ι : Type u, Nonempty (f.Eigenbasis ι)` with the naming convention `exists_eigenbasis`.
-/
def Eigenbasis (ι : Type*) (f : End S M) := CommonEigenbasis ι fun _ : Unit ↦ f

/-- Cpnstruct `LinearMap.Eigenbasis` from a basis of eigenvectors and eigenvalues. -/
def Eigenbasis.mk {ι : Type*} {f : End S M} {b : Basis ι S M} {μ : ι → S}
    (apply_eq_smul : ∀ i, f (b i) = μ i • b i) : f.Eigenbasis ι where
  toBasis := b
  μ := fun _ ↦ μ
  apply_eq_smul := fun _ => apply_eq_smul

/-- The eigenvalues of the eigenbasis. -/
def Eigenbasis.μ {ι : Type*} {f : End S M} (self : f.Eigenbasis ι) : ι → S :=
  CommonEigenbasis.μ self ()

lemma Eigenbasis.apply_eq_smul {ι : Type*} {f : End S M} (self : f.Eigenbasis ι)
    (i : ι) : f (self.toBasis i) = self.μ i • self.toBasis i :=
  CommonEigenbasis.apply_eq_smul self () i

namespace CommonEigenbasis

variable {ι : Type*} {f : α → End S M} {b : Basis ι S M} {D D₁ D₂ : CommonEigenbasis ι f}

@[ext]
lemma ext (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  ext a i
  suffices D₁.μ a i • D₁.toBasis i = D₂.μ a i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← D₁.apply_eq_smul a i, h, ← D₂.apply_eq_smul a i]

/-- Alternative constructor for `LinearMap.CommonEigenbasis` from existence of eigenvalues. -/
noncomputable def ofExists (exists_apply_eq_smul : ∀ a i, ∃ μ : S, f a (b i) = μ • b i) :
    CommonEigenbasis ι f where
  toBasis := b
  μ := fun a i ↦ (exists_apply_eq_smul a i).choose
  apply_eq_smul := fun a i => (exists_apply_eq_smul a i).choose_spec

/-- Alternative constructor for `LinearMap.CommonEigenbasis` using `Module.End.HasEigenvector`. -/
noncomputable def ofHasEigenVector {f : α → End R G} {b : Basis ι R G} {μ : α → ι → R}
   (hasEigenvector_μ : ∀ a i, (f a).HasEigenvector (μ a i) (b i)) :
    CommonEigenbasis ι f where
  toBasis := b
  μ := μ
  apply_eq_smul a i := (hasEigenvector_μ a i).apply_eq_smul

/--
Alternative constructor for `LinearMap.CommonEigenbasis` using existence of eigenvalues and
`Module.End.HasEigenvector`.
-/
noncomputable def ofExistsHasEigenVector {f : α → End R G} {b : Basis ι R G}
    (exists_hasEigenvector_μ : ∀ a i, ∃ μ : R, (f a).HasEigenvector μ (b i)) :
    CommonEigenbasis ι f :=
  ofHasEigenVector (exists_hasEigenvector_μ · · |>.choose_spec)

/--
Alternative constructor for `LinearMap.CommonEigenbasis` from a basis of eigenvectors and
diagonality of the matrix representations.
-/
noncomputable def ofIsDiagToMatrix [Fintype ι] [DecidableEq ι] {f : α → End C M'} {b : Basis ι C M'}
    (h : ∀ a, ((f a).toMatrix b b).IsDiag) : CommonEigenbasis ι f where
  toBasis := b
  μ := fun a i ↦ (f a).toMatrix b b i i
  apply_eq_smul a i := calc
    f a (b i) = ∑ j, (f a).toMatrix b b j i • b j := by simp [toMatrix_apply, b.sum_repr]
    _ = _ := by rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [h a hj]) (by simp)]

theorem hasEigenVector_μ [Nontrivial R] {f : α → End R G}
    (D : CommonEigenbasis ι f) (a : α) (i : ι) :
    (f a).HasEigenvector (D.μ a i) (D.toBasis i) :=
  hasEigenvector_iff.mpr ⟨mem_eigenspace_iff.mpr (D.apply_eq_smul a i), D.toBasis.ne_zero i⟩

variable (D) in
/-- Get individual eigenbases from a common eigenbasis. -/
def eigenbasis (a : α) : (f a).Eigenbasis ι := .mk (D.apply_eq_smul a)

/-- Construct a common eigenbasis from a family of eigenbases. -/
def ofEigenbasis {D : (a : α) → (f a).Eigenbasis ι} (h : ∀ a, (D a).toBasis = b) :
    CommonEigenbasis ι f where
  toBasis := b
  μ a i := (D a).μ i
  apply_eq_smul a i := h a ▸ (D a).apply_eq_smul i

/-- Any common eigenbasis of `f` is also a common eigenbasis of `c • f`. -/
def smul {f : α → End C M'} (D : CommonEigenbasis ι f) (c : α → C) :
    CommonEigenbasis ι (c • f) where
  toBasis := D.toBasis
  μ := c • D.μ
  apply_eq_smul a i := by simp [D.apply_eq_smul, smul_smul]

/-- Any common eigenbasis of `f` is also a common eigenbasis of `f - c • 1`. -/
def subSmulOne {f : α → End R G} (D : CommonEigenbasis ι f) (c : α → R) :
    CommonEigenbasis ι (f - c • 1) where
  toBasis := D.toBasis
  μ := fun a i ↦ D.μ a i - c a
  apply_eq_smul a i := by simp [D.apply_eq_smul, sub_smul]

variable (D) in
/-- Any common eigenbasis of `f` is also a common eigenbasis of `f i + f j` for any `i` and `j`. -/
def eigenbasisAdd (i j : α) : (f i + f j).Eigenbasis ι :=
  .mk (b := D.toBasis) (μ := D.μ i + D.μ j) <| fun k ↦ by simp [D.apply_eq_smul, add_smul]

variable (D) in
/-- Any common eigenbasis of `f` is also a common eigenbasis of `∑ a, f a`. -/
def eigenbasisSum [Fintype α] : (∑ a, f a).Eigenbasis ι :=
  .mk (b := D.toBasis) (μ := ∑ a, D.μ a) <| fun k ↦ by simp [D.apply_eq_smul, Finset.sum_smul]

variable (D) in
/-- Any common eigenbasis of `f` is also a common eigenbasis of `f i * f j` for any `i` and `j`. -/
def eigenbasisMul (i j : α) : (f i * f j).Eigenbasis ι :=
  .mk (b := D.toBasis) (μ := D.μ j * D.μ i) <| fun k ↦ by simp [D.apply_eq_smul, smul_smul]

lemma commute {f : α → End C M'} (D : CommonEigenbasis ι f) (i j : α) :
    Commute (f i) (f j) :=
  D.toBasis.ext fun k ↦ by simp [D.apply_eq_smul, smul_smul, mul_comm]

end CommonEigenbasis

namespace Eigenbasis

variable {ι : Type*} {f : End S M} {b : Basis ι S M} {D D₁ D₂ : f.Eigenbasis ι}

@[ext]
lemma ext (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := CommonEigenbasis.ext h

/-- Alternative constructor for `LinearMap.Eigenbasis` from existence of eigenvalues. -/
noncomputable def ofExists (exists_apply_eq_smul : ∀ i, ∃ μ : S, f (b i) = μ • b i) :
    f.Eigenbasis ι :=
  CommonEigenbasis.ofExists fun _ ↦ exists_apply_eq_smul

/-- Alternative constructor for `LinearMap.Eigenbasis` using `Module.End.HasEigenvector`. -/
noncomputable def ofHasEigenVector {f : End R G} {b : Basis ι R G} {μ : ι → R}
    (hasEigenvector_μ : ∀ i, f.HasEigenvector (μ i) (b i)) : f.Eigenbasis ι :=
  CommonEigenbasis.ofHasEigenVector fun _ ↦ hasEigenvector_μ

/--
Alternative constructor for `LinearMap.CommonEigenbasis`
using existence of eigenvalues and `Module.End.HasEigenvector`.
-/
noncomputable def ofExistsHasEigenVector {f : End R G} {b : Basis ι R G}
    (exists_hasEigenvector_μ : ∀ i, ∃ μ : R, f.HasEigenvector μ (b i)) : f.Eigenbasis ι :=
  CommonEigenbasis.ofExistsHasEigenVector fun _ ↦ exists_hasEigenvector_μ

theorem hasEigenVector_μ [Nontrivial R] {f : End R G} (D : f.Eigenbasis ι) (i : ι) :
    f.HasEigenvector (D.μ i) (D.toBasis i) :=
  CommonEigenbasis.hasEigenVector_μ D () i

/--
Alternative constructor for `LinearMap.Eigenbasis` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def ofIsDiagToMatrix [Fintype ι] [DecidableEq ι] {f : End C M'} {b : Basis ι C M'}
    (h : (f.toMatrix b b).IsDiag) : f.Eigenbasis ι :=
  CommonEigenbasis.ofIsDiagToMatrix fun _ ↦ h

variable (b) in
/-- Any basis is an eigenbasis of the zero map. -/
def zero : (0 : End S M).Eigenbasis ι :=
  .mk (b := b) (μ := 0) (by simp)

variable (b) in
/-- Any basis is an eigenbasis of the identity map. -/
def one : (1 : End S M).Eigenbasis ι :=
  .mk (b := b) (μ := 1) (by simp)

/-- Any eigenbasis of `f` is also an eigenbasis of `c • f`. -/
def smul {f : End C M'} (D : f.Eigenbasis ι) (c : C) : (c • f).Eigenbasis ι :=
  CommonEigenbasis.smul D fun _ ↦ c

/-- Any eigenbasis of `f` is also an eigenbasis of `f - c • 1`. -/
def subSmulOne {f : End R G} (D : f.Eigenbasis ι) (c : R) :
    (f - c • 1).Eigenbasis ι :=
  CommonEigenbasis.subSmulOne D fun _ ↦ c

lemma toMatrix_eq_diagonal [Fintype ι] [DecidableEq ι] {f : End C M'}
    (D : f.Eigenbasis ι) : f.toMatrix D.toBasis D.toBasis = diagonal D.μ := by
  ext i j
  simp [toMatrix_apply, D.apply_eq_smul j]
  grind [Finsupp.single_apply, diagonal_apply]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma charpoly_eq [Nontrivial R] [Fintype ι] [DecidableEq ι] [Free R G] [Module.Finite R G]
    {f : End R G} (D : f.Eigenbasis ι) :
    f.charpoly = ∏ i, (X - .C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, charpoly_diagonal]

lemma splits_charpoly [Fintype ι] [DecidableEq ι] [Module.Finite K V] {f : End K V}
    (D : f.Eigenbasis ι) : f.charpoly.Splits (RingHom.id K) := by
  simp [D.charpoly_eq, splits_prod_iff, X_sub_C_ne_zero, splits_X_sub_C]

/-- TODO: `[Nontrivial R]` golfed in #29420 -/
lemma isRoot_charpoly [Nontrivial R] [IsDomain R] [Module.Finite R G] [Free R G]
    [Fintype ι] [DecidableEq ι] {f : End R G} (D : f.Eigenbasis ι) (i : ι) :
    f.charpoly.IsRoot (D.μ i) := by
  rw [D.charpoly_eq, Polynomial.isRoot_prod]
  use i
  simp

lemma iSup_eigenspace {f : End R G} (D : f.Eigenbasis ι) : ⨆ μ, f.eigenspace μ = ⊤ := by
  nontriviality R
  rw [eq_top_iff, ← Basis.span_eq D.toBasis, Submodule.span_le, Set.range_subset_iff]
  exact fun i ↦ Submodule.mem_iSup_of_mem (D.μ i) (hasEigenvector_iff.mp (D.hasEigenVector_μ i)).1

end Eigenbasis

lemma exists_eigenbasis_iff_directSum_eigenspace [DecidableEq K] {f : End K V} :
    (∃ ι : Type uV, Nonempty (f.Eigenbasis ι)) ↔ DirectSum.IsInternal f.eigenspace := by
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

lemma exists_eigenbasis_iff_iSup_eigenspace {f : End K V} :
    (∃ ι : Type uV, Nonempty (f.Eigenbasis ι)) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by classical calc
  _ ↔ DirectSum.IsInternal f.eigenspace := exists_eigenbasis_iff_directSum_eigenspace
  _ ↔ _ := by
    simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, eigenspaces_iSupIndep f]

end LinearMap
