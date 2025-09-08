/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `Basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : Basis ι R M` are available as `b i`, where `i : ι`

* `Basis.repr` is the isomorphism sending `x : M` to its coordinates `Basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `Basis.ofRepr`.
* If `ι` is finite, there is a variant of `repr` called `Basis.equivFun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `Finsupp`). The converse, turning this isomorphism into
  a basis, is called `Basis.ofEquivFun`.

* `Basis.reindex` uses an equiv to map a basis to a different indexing set.

* `Basis.map` uses a linear equiv to map a basis to a different module.

* `Basis.constr`: given `b : Basis ι R M` and `f : ι → M`, construct a linear map `g` so that
  `g (b i) = f i`.

* `Basis.coord`: `b.coord i x` is the `i`-th coordinate of a vector `x` with respect to the basis
  `b`.

## Main results

* `Basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

assert_not_exists LinearMap.pi LinearIndependent Cardinal
-- TODO: assert_not_exists Submodule
-- (should be possible after splitting `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`)

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

namespace Module

variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (ι R M) in
/-- A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `Basis.repr`.
-/
structure Basis where
  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/
  ofRepr ::
    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:
    the `c`s such that `x = ∑ i, c i`. -/
    repr : M ≃ₗ[R] ι →₀ R

namespace Basis

instance : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨.ofRepr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

theorem repr_injective : Injective (repr : Basis ι R M → M ≃ₗ[R] ι →₀ R) := fun f g h => by
  cases f; cases g; congr

/-- `b i` is the `i`th basis vector. -/
instance instFunLike : FunLike (Basis ι R M) ι M where
  coe b i := b.repr.symm (Finsupp.single i 1)
  coe_injective' f g h := repr_injective <| LinearEquiv.symm_bijective.injective <|
    LinearEquiv.toLinearMap_injective <| by ext; exact congr_fun h _

@[simp]
theorem coe_ofRepr (e : M ≃ₗ[R] ι →₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl

protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp

theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl

theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [LinearEquiv.map_smul, repr_symm_single_one]

@[simp]
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _

theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self, Finsupp.single_apply]

@[simp]
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.linearCombination R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsuppSum ..
    _ = Finsupp.linearCombination R b v := by simp only [repr_symm_single,
                                                         Finsupp.linearCombination_apply]

@[simp]
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.linearCombination R b :=
  LinearMap.ext fun v => b.repr_symm_apply v

@[simp]
theorem repr_linearCombination (v) : b.repr (Finsupp.linearCombination _ b v) = v := by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v

@[simp]
theorem linearCombination_repr : Finsupp.linearCombination _ b (b.repr x) = x := by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x

end repr

section Map

variable (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
protected def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)

@[simp]
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl

theorem coe_map : (b.map f : ι → M') = f ∘ b :=
  rfl

end Map

section Reindex

variable (b' : Basis ι' R M')
variable (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : Basis ι' R M :=
  .ofRepr (b.repr.trans (Finsupp.domLCongr e))

theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]

@[simp]
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)

theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp

@[simp]
theorem repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e :=
  DFunLike.ext _ _ <| by simp [repr_reindex_apply]

@[simp]
theorem reindex_refl : b.reindex (Equiv.refl ι) = b := by
  simp [reindex]

/-- `simp` can prove this as `Basis.coe_reindex` + `EquivLike.range_comp` -/
theorem range_reindex : Set.range (b.reindex e) = Set.range b := by
  simp [coe_reindex, range_comp]

end Reindex

end Basis

section Fintype

open Basis

open Fintype

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def Basis.equivFun [Finite ι] (b : Basis ι R M) : M ≃ₗ[R] ι → R :=
  LinearEquiv.trans b.repr
    ({ Finsupp.equivFunOnFinite with
        toFun := (↑)
        map_add' := Finsupp.coe_add
        map_smul' := Finsupp.coe_smul } :
      (ι →₀ R) ≃ₗ[R] ι → R)

/-- A module over a finite ring that admits a finite basis is finite. -/
def fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm

theorem card_fintype [Fintype ι] (b : Basis ι R M) [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι → R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
theorem Basis.equivFun_symm_apply [Fintype ι] (b : Basis ι R M) (x : ι → R) :
    b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.linearCombination_apply, sum_fintype, equivFunOnFinite]

@[simp]
theorem Basis.equivFun_apply [Finite ι] (b : Basis ι R M) (u : M) : b.equivFun u = b.repr u :=
  rfl

@[simp]
theorem Basis.map_equivFun [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl

theorem Basis.sum_equivFun [Fintype ι] (b : Basis ι R M) (u : M) :
    ∑ i, b.equivFun u i • b i = u := by
  rw [← b.equivFun_symm_apply, b.equivFun.symm_apply_apply]

@[simp]
theorem Basis.sum_repr [Fintype ι] (b : Basis ι R M) (u : M) : ∑ i, b.repr u i • b i = u :=
  b.sum_equivFun u

@[simp]
theorem Basis.equivFun_self [Finite ι] [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    b.equivFun (b i) j = if i = j then 1 else 0 := by rw [b.equivFun_apply, b.repr_self_apply]

theorem Basis.repr_sum_self [Fintype ι] (b : Basis ι R M) (c : ι → R) :
    b.repr (∑ i, c i • b i) = c := by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  .ofRepr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι

@[simp]
theorem Basis.ofEquivFun_repr_apply [Finite ι] (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl

@[simp]
theorem Basis.coe_ofEquivFun [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Pi.single i 1) :=
  funext fun i =>
    e.injective <|
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single]

@[simp]
theorem Basis.ofEquivFun_equivFun [Finite ι] (v : Basis ι R M) :
    Basis.ofEquivFun v.equivFun = v :=
  Basis.repr_injective <| by ext; rfl

@[simp]
theorem Basis.equivFun_ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e).equivFun = e := by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]

end Fintype

variable {ι R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

namespace Basis

variable (b : Basis ι R M)

section Ext

variable {R₁ : Type*} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, LinearMap.map_smulₛₗ, h]

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, LinearEquiv.map_smulₛₗ, h]

/-- Two elements are equal iff their coordinates are equal. -/
theorem ext_elem_iff {x y : M} : x = y ↔ ∀ i, b.repr x i = b.repr y i := by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]

alias ⟨_, ext_elem⟩ := ext_elem_iff

theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} :
    ↑b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩

theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩

theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩

/-- An unbundled version of `repr_eq_iff` -/
theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M →ₗ[R] R :=
    { toFun x := f x i
      map_add' _ _ := by rw [hadd, Pi.add_apply]
      map_smul' _ _ := by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    change b.repr (b j) i = f (b j) i
    rw [b.repr_self, f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl

/-- Two bases are equal if they assign the same coordinates. -/
theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  repr_injective <| by ext; apply h

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (∀ i, b₁ i = b₂ i) → b₁ = b₂ :=
  DFunLike.ext _ _

end Ext

section MapCoeffs

variable {R' : Type*} [Semiring R'] [Module R' M] (f : R ≃+* R')

attribute [local instance] SMul.comp.isScalarTower

/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `Basis.algebraMapCoeffs` for the case where `f` is equal to `algebraMap`.
-/
@[simps +simpRhs]
def mapCoeffs (h : ∀ (c) (x : M), f c • x = c • x) : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul, ← h, f.apply_symm_apply] }
  exact ofRepr <| (b.repr.restrictScalars R').trans <|
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm

variable (h : ∀ (c) (x : M), f c • x = c • x)

theorem mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
  apply_eq_iff.mpr <| by simp

@[simp]
theorem coe_mapCoeffs : (b.mapCoeffs f h : ι → M) = b :=
  funext <| b.mapCoeffs_apply f h

end MapCoeffs

section ReindexRange

/-- `b.reindexRange` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    letI := h
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))

theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  by_cases htr : Nontrivial R
  · letI := htr
    simp [htr, reindexRange, reindex_apply]
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp htr
    letI := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]

theorem reindexRange_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _

@[simp]
theorem reindexRange_apply (x : range b) : b.reindexRange x = x := by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i

theorem reindexRange_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
    b.reindexRange.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i := by
  nontriviality
  subst h
  apply (b.repr_apply_eq (fun x i => b.reindexRange.repr x ⟨b i, _⟩) _ _ _ x i).symm
  · intro x y
    ext i
    simp only [Pi.add_apply, LinearEquiv.map_add, Finsupp.coe_add]
  · intro c x
    ext i
    simp only [Pi.smul_apply, LinearEquiv.map_smul, Finsupp.coe_smul]
  · intro i
    ext j
    simp only [reindexRange_repr_self]
    apply Finsupp.single_apply_left (f := fun i => (⟨b i, _⟩ : Set.range b))
    exact fun i j h => b.injective (Subtype.mk.inj h)

@[simp]
theorem reindexRange_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindexRange_repr' _ rfl

section Fintype

variable [Fintype ι] [DecidableEq M]

/-- `b.reindexFinsetRange` is a basis indexed by `Finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))

theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [reindexFinsetRange, reindex_apply, reindexRange_apply]
  rfl

@[simp]
theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i

theorem reindexFinsetRange_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 := by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange, repr_reindex, Finsupp.mapDomain_equiv_apply, reindexRange_repr_self]
  simp [Finsupp.single_apply]

@[simp]
theorem reindexFinsetRange_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindexFinsetRange]

end Fintype

end ReindexRange

variable [Module R M']

section Constr

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

/-- Construct a linear map given the value at the basis, called `Basis.constr b S f` where `b` is
a basis, `f` is the value of the linear map over the elements of the basis, and `S` is an
extra semiring (typically `S = R` or `S = ℕ`).

This definition is parameterized over an extra `Semiring S`,
such that `SMulCommClass R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `AddEquiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] M →ₗ[R] M' where
  toFun f := (Finsupp.linearCombination R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
  invFun f i := f (b i)
  left_inv f := by
    ext
    simp
  right_inv f := by
    refine b.ext fun i => ?_
    simp
  map_add' f g := by
    refine b.ext fun i => ?_
    simp
  map_smul' c f := by
    refine b.ext fun i => ?_
    simp

theorem constr_def (f : ι → M') :
    constr (M' := M') b S f = linearCombination R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl

theorem constr_apply (f : ι → M') (x : M) :
    constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, lmapDomain_apply, linearCombination_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]

@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (constr (M' := M') b S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]

theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) :
    constr (M' := M') b S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)

theorem constr_self (f : M →ₗ[R] M') : (constr (M' := M') b S fun i => f (b i)) = f :=
  b.constr_eq S fun _ => rfl

theorem constr_range {f : ι → M'} :
    LinearMap.range (constr (M' := M') b S f) = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_linearCombination, Set.image_id]

@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
    constr (M' := M') b S (f ∘ v) = f.comp (constr (M' := M') b S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

@[simp]
theorem constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι → M') (x : M) :
    (constr (M' := M') b S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]

end Constr

section Equiv

variable (i : ι)
variable {M'' : Type*} (b' : Basis ι' R M') (e : ι ≃ ι')
variable [AddCommMonoid M''] [Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm

@[simp]
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]

@[simp]
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp

@[simp]
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext' fun i => (b.equiv b' e).injective (by simp)

@[simp]
theorem equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext' fun i => by simp

@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.equiv b' e) = b'.reindex e.symm := by
  ext i
  simp

section CommSemiring

variable {R M M' : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (b : Basis ι R M) (b' : Basis ι' R M')
variable [SMulCommClass R R M']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M) (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
    (hgf : ∀ i, g (f (b i)) = b i) (hfg : ∀ i, f (g (b' i)) = b' i) : M ≃ₗ[R] M' :=
  { constr (M' := M') b R (f ∘ b) with
    invFun := constr (M' := M) b' R (g ∘ b')
    left_inv :=
      have : (constr (M' := M) b' R (g ∘ b')).comp (constr (M' := M') b R (f ∘ b)) = LinearMap.id :=
        b.ext fun i =>
          Exists.elim (hf i) fun i' hi' => by
            rw [LinearMap.comp_apply, b.constr_basis, Function.comp_apply, ← hi', b'.constr_basis,
              Function.comp_apply, hi', hgf, LinearMap.id_apply]
      fun x => congr_arg (fun h : M →ₗ[R] M => h x) this
    right_inv :=
      have : (constr (M' := M') b R (f ∘ b)).comp (constr (M' := M) b' R (g ∘ b')) = LinearMap.id :=
        b'.ext fun i =>
          Exists.elim (hg i) fun i' hi' => by
            rw [LinearMap.comp_apply, b'.constr_basis, Function.comp_apply, ← hi', b.constr_basis,
              Function.comp_apply, hi', hfg, LinearMap.id_apply]
      fun x => congr_arg (fun h : M' →ₗ[R] M' => h x) this }

@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _

@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _

theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]

end CommSemiring

end Equiv

section Coord

variable (i : ι)

/-- `b.coord i` is the linear function giving the `i`-th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps!]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr

theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun _ => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)

@[simp]
theorem coe_sumCoords : (b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id :=
  rfl

@[simp high]
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.coord i := by
  ext m
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coeFn_sum]

@[simp]
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]

theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
  ⟨b.coord i m, by simp⟩

theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) :
    b.coord i (b.repr.symm f) = f i := by
  simp only [repr_symm_apply, coord_apply, repr_linearCombination]

theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

variable (e : ι ≃ ι')

@[simp]
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

theorem coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι → R) :
    b.coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)

end Coord

end Basis

end Module
