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
  a linear map is diagonalizable iff the indexed supremum of the eigenspaces is the whole space.

## Implementation notes

We could also have defined `CommonEigenbasis` on sets instead of indexed families,
which could make unions and pointwise operations more convenient,
though it may make `μ` more awkward.

## Tags

eigenbasis, common eigenbasis, diagonalization, simultaneous diagonalization, diagonalizability

## TODO

* a linear map is diagonalizable iff the minimal polynomial is a product of distinct linear factors.
* all diagonalizable linear maps are semisimple.
* a family of linear maps is simultaneously diagonalizable iff they commute and are
  individually diagonalizable.
  * there is some potentially relevant work in Analysis.InnerProductSpace.JointEigenspace,
    which may be possible to generalize/connect to this API.
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
  but we don't use `Module.End.HasEigenvector`, as it's slightly more convenient to admit the
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

variable {ι : Type*} {f : α → End S M} {b : Basis ι S M} {B B₁ B₂ : CommonEigenbasis ι f}

@[ext]
lemma ext (h : B₁.toBasis = B₂.toBasis) : B₁ = B₂ := by
  suffices B₁.μ = B₂.μ by cases B₁; cases B₂; simp_all only
  ext a i
  suffices B₁.μ a i • B₁.toBasis i = B₂.μ a i • B₁.toBasis i by
    simpa using congr(B₁.toBasis.repr $this i)
  rw [← B₁.apply_eq_smul a i, h, ← B₂.apply_eq_smul a i]

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
    (B : CommonEigenbasis ι f) (a : α) (i : ι) :
    (f a).HasEigenvector (B.μ a i) (B.toBasis i) :=
  hasEigenvector_iff.mpr ⟨mem_eigenspace_iff.mpr (B.apply_eq_smul a i), B.toBasis.ne_zero i⟩

variable (b B)

/-- Get individual eigenbases from a common eigenbasis. -/
def eigenbasis (a : α) : (f a).Eigenbasis ι := .mk (B.apply_eq_smul a)

/-- Construct a common eigenbasis from a family of eigenbases. -/
def ofEigenbasis {B : (a : α) → (f a).Eigenbasis ι} (h : ∀ a, (B a).toBasis = b) :
    CommonEigenbasis ι f where
  toBasis := b
  μ a := (B a).μ
  apply_eq_smul a i := h a ▸ (B a).apply_eq_smul i

/-- Any basis is a common eigenbasis of the zero map. -/
def zero (α : Type*) : CommonEigenbasis ι (fun _ : α ↦ (0 : End S M)) where
  toBasis := b
  μ := 0
  apply_eq_smul := by simp

/-- Any basis is a common eigenbasis of the identity map. -/
def one (α : Type*) : CommonEigenbasis ι (fun _ : α ↦ (1 : End S M)) where
  toBasis := b
  μ := 1
  apply_eq_smul := by simp

/-- Any common eigenbasis of `f` is also a common eigenbasis of `c • f`. -/
def smul {f : α → End C M'} (B : CommonEigenbasis ι f) (c : α → C) :
    CommonEigenbasis ι (c • f) where
  toBasis := B.toBasis
  μ := c • B.μ
  apply_eq_smul := by simp [B.apply_eq_smul, smul_smul]

/-- Any common eigenbasis of `f` is also a common eigenbasis of `f i + f j` for any `i` and `j`. -/
def add : CommonEigenbasis ι (fun a : α × α ↦ f a.1 + f a.2) where
  toBasis := B.toBasis
  μ a := B.μ a.1 + B.μ a.2
  apply_eq_smul := by simp [B.apply_eq_smul, add_smul]

/-- Any common eigenbasis of `f` is also an eigenbasis of `f i - f j` for any `i` and `j`. -/
def sub {f : α → End R G} (B : CommonEigenbasis ι f) :
    CommonEigenbasis ι (fun a : α × α ↦ f a.1 - f a.2) where
  toBasis := B.toBasis
  μ a := B.μ a.1 - B.μ a.2
  apply_eq_smul := by simp [B.apply_eq_smul, sub_smul]

/-- Any common eigenbasis of `f` is also an eigenbasis of `f i * f j` for any `i` and `j`. -/
def mul : CommonEigenbasis ι (fun a : α × α ↦ f a.1 * f a.2) where
  toBasis := B.toBasis
  μ a := B.μ a.2 * B.μ a.1
  apply_eq_smul := by simp [B.apply_eq_smul, smul_smul]

/-- Any common eigenbasis of `f` is also a common eigenbasis of `f ^ n`. -/
def pow (n : ℕ) : CommonEigenbasis ι (f ^ n) where
  toBasis := B.toBasis
  μ := (B.μ · · ^ n)
  apply_eq_smul _ _ := by
    induction n with
    | zero => simp
    | succ n h =>
      rw [pow_succ, Pi.mul_apply, End.mul_apply, B.apply_eq_smul, map_smul, h, smul_smul, pow_succ']

/-- Any common eigenbasis of `f` is also a common eigenbasis of any sum of a multiset of `f`. -/
def multisetSum : CommonEigenbasis ι (fun s : Multiset α ↦ (s.map f).sum) where
  toBasis := B.toBasis
  μ s := (s.map B.μ).sum
  apply_eq_smul s i := by
    induction s using Multiset.induction with
    | empty => simp
    | cons a as ih => simp [B.apply_eq_smul, ih, add_smul]

/-- Any common eigenbasis of `f` is also a common eigenbasis of any sum of a list of `f`. -/
def listSum : CommonEigenbasis ι (fun l : List α ↦ (l.map f).sum) where
  toBasis := B.toBasis
  μ l := (l.map B.μ).sum
  apply_eq_smul l := B.multisetSum.apply_eq_smul l

/-- Any common eigenbasis of `f` is also a common eigenbasis of any sum of a finset of `f`. -/
def finsetSum : CommonEigenbasis ι (fun s : Finset α ↦ ∑ a ∈ s, f a) where
  toBasis := B.toBasis
  μ s := ∑ a ∈ s, B.μ a
  apply_eq_smul _ := B.multisetSum.apply_eq_smul _

/-- Any common eigenbasis of `f` is also a common eigenbasis of any product of a list of `f`. -/
def listProd : CommonEigenbasis ι (fun l : List α ↦ (l.map f).prod) where
  toBasis := B.toBasis
  μ l := (l.map B.μ).reverse.prod
  apply_eq_smul l i := by
    induction l with
    | nil => simp
    | cons a as ih => simp [B.apply_eq_smul, ih, smul_smul]

variable {b}

/-- Any common eigenbasis of `f` is also a common eigenbasis of any subfamily of `f`. -/
def comp {α' : Type*} {g : α' → α} : CommonEigenbasis ι (f ∘ g) where
  toBasis := B.toBasis
  μ := B.μ ∘ g
  apply_eq_smul a := B.apply_eq_smul (g a)

/-- Any common eigenbasis of `f` is also a common eigenbasis of any subset of `f`. -/
def restrict {a' : Set α} : CommonEigenbasis ι (fun a : a' ↦ f a) where
  toBasis := B.toBasis
  μ := B.μ ∘ Subtype.val
  apply_eq_smul a := B.apply_eq_smul a

/-- `B.reindex (e : ι ≃ ι')` is a common eigenbasis indexed by `ι'`. -/
def reindex {ι' : Type*} (e : ι ≃ ι') : CommonEigenbasis ι' f where
  toBasis := B.toBasis.reindex e
  μ a := B.μ a ∘ e.symm
  apply_eq_smul := by simp [B.apply_eq_smul]

/-- Construct a common eigenbasis from a family of common eigenbases. -/
def sigma {ι' : Type*} {α : ι' → Type*} {f : (i : ι') → α i → End S M}
    {B : (i : ι') → CommonEigenbasis ι (f i)} (h : ∀ i, (B i).toBasis = b) :
    CommonEigenbasis ι fun a : Σ i, α i ↦ f a.1 a.2 where
  toBasis := b
  μ a := (B a.1).μ a.2
  apply_eq_smul a := h a.1 ▸ (B a.1).apply_eq_smul a.2

lemma commute {f : α → End C M'} (B : CommonEigenbasis ι f) (i j : α) :
    Commute (f i) (f j) :=
  B.toBasis.ext fun k ↦ by simp [B.apply_eq_smul, smul_smul, mul_comm]

end CommonEigenbasis

namespace Eigenbasis

variable {ι : Type*} {f : End S M} {b : Basis ι S M} {B B₁ B₂ : f.Eigenbasis ι}

@[ext]
lemma ext (h : B₁.toBasis = B₂.toBasis) : B₁ = B₂ := CommonEigenbasis.ext h

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

theorem hasEigenVector_μ [Nontrivial R] {f : End R G} (B : f.Eigenbasis ι) (i : ι) :
    f.HasEigenvector (B.μ i) (B.toBasis i) :=
  CommonEigenbasis.hasEigenVector_μ B () i

/--
Alternative constructor for `LinearMap.Eigenbasis` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def ofIsDiagToMatrix [Fintype ι] [DecidableEq ι] {f : End C M'} {b : Basis ι C M'}
    (h : (f.toMatrix b b).IsDiag) : f.Eigenbasis ι :=
  CommonEigenbasis.ofIsDiagToMatrix fun _ ↦ h

variable (b D)

/-- Any basis is an eigenbasis of the zero map. -/
def zero : (0 : End S M).Eigenbasis ι := CommonEigenbasis.zero b Unit

/-- Any basis is an eigenbasis of the identity map. -/
def one : (1 : End S M).Eigenbasis ι := CommonEigenbasis.one b Unit

/-- Any eigenbasis of `f` is also an eigenbasis of `c • f`. -/
def smul {f : End C M'} (B : f.Eigenbasis ι) (c : C) : (c • f).Eigenbasis ι :=
  CommonEigenbasis.smul B fun _ ↦ c

/-- Any eigenbasis of `f` is also an eigenbasis of `f ^ n`. -/
def pow (n : ℕ) : (f ^ n).Eigenbasis ι := CommonEigenbasis.pow B n

/-- `B.reindex (e : ι ≃ ι')` is an eigenbasis indexed by `ι'`. -/
def reindex {ι' : Type*} (e : ι ≃ ι') : f.Eigenbasis ι' := CommonEigenbasis.reindex B e

lemma toMatrix_eq_diagonal [Fintype ι] [DecidableEq ι] {f : End C M'}
    (B : f.Eigenbasis ι) : f.toMatrix B.toBasis B.toBasis = diagonal B.μ := by
  ext i j
  simp [toMatrix_apply, B.apply_eq_smul j]
  grind [Finsupp.single_apply, diagonal_apply]

lemma charpoly_eq [Fintype ι] [DecidableEq ι] [Free R G] [Module.Finite R G] {f : End R G}
    (B : f.Eigenbasis ι) : f.charpoly = ∏ i, (X - .C (B.μ i)) := by
  rw [← f.charpoly_toMatrix B.toBasis, B.toMatrix_eq_diagonal, charpoly_diagonal]

lemma splits_charpoly [Fintype ι] [DecidableEq ι] [Module.Finite K V] {f : End K V}
    (B : f.Eigenbasis ι) : f.charpoly.Splits (RingHom.id K) := by
  simp [B.charpoly_eq, splits_prod_iff, X_sub_C_ne_zero, splits_X_sub_C]

lemma isRoot_charpoly [Module.Finite R G] [Free R G] [Fintype ι] [DecidableEq ι]
    {f : End R G} (B : f.Eigenbasis ι) (i : ι) : f.charpoly.IsRoot (B.μ i) := by
  simp [B.charpoly_eq, IsRoot, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]

lemma iSup_eigenspace {f : End R G} (B : f.Eigenbasis ι) : ⨆ μ, f.eigenspace μ = ⊤ := by
  nontriviality R
  rw [eq_top_iff, ← Basis.span_eq B.toBasis, Submodule.span_le, Set.range_subset_iff]
  exact fun i ↦ Submodule.mem_iSup_of_mem (B.μ i) (hasEigenvector_iff.mp (B.hasEigenVector_μ i)).1

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
