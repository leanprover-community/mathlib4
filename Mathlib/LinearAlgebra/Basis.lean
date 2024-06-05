/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.SetTheory.Cardinal.Cofinality

#align_import linear_algebra.basis from "leanprover-community/mathlib"@"13bce9a6b6c44f6b4c91ac1c1d2a816e2533d395"

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

* `Basis.constr b R f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `Basis.reindex` uses an equiv to map a basis to a different indexing set.
* `Basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `Basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

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


noncomputable section

universe u

open Function Set Submodule

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {K : Type*}
variable {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

section Module

variable [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

section

variable (ι R M)

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
#align basis Basis
#align basis.repr Basis.repr
#align basis.of_repr Basis.ofRepr

end

instance uniqueBasis [Subsingleton R] : Unique (Basis ι R M) :=
  ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩
#align unique_basis uniqueBasis

namespace Basis

instance : Inhabited (Basis ι R (ι →₀ R)) :=
  ⟨.ofRepr (LinearEquiv.refl _ _)⟩

variable (b b₁ : Basis ι R M) (i : ι) (c : R) (x : M)

section repr

theorem repr_injective : Injective (repr : Basis ι R M → M ≃ₗ[R] ι →₀ R) := fun f g h => by
  cases f; cases g; congr
#align basis.repr_injective Basis.repr_injective

/-- `b i` is the `i`th basis vector. -/
instance instFunLike : FunLike (Basis ι R M) ι M where
  coe b i := b.repr.symm (Finsupp.single i 1)
  coe_injective' f g h := repr_injective <| LinearEquiv.symm_bijective.injective <|
    LinearEquiv.toLinearMap_injective <| by ext; exact congr_fun h _
#align basis.fun_like Basis.instFunLike

@[simp]
theorem coe_ofRepr (e : M ≃ₗ[R] ι →₀ R) : ⇑(ofRepr e) = fun i => e.symm (Finsupp.single i 1) :=
  rfl
#align basis.coe_of_repr Basis.coe_ofRepr

protected theorem injective [Nontrivial R] : Injective b :=
  b.repr.symm.injective.comp fun _ _ => (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp
#align basis.injective Basis.injective

theorem repr_symm_single_one : b.repr.symm (Finsupp.single i 1) = b i :=
  rfl
#align basis.repr_symm_single_one Basis.repr_symm_single_one

theorem repr_symm_single : b.repr.symm (Finsupp.single i c) = c • b i :=
  calc
    b.repr.symm (Finsupp.single i c) = b.repr.symm (c • Finsupp.single i (1 : R)) := by
      { rw [Finsupp.smul_single', mul_one] }
    _ = c • b i := by rw [LinearEquiv.map_smul, repr_symm_single_one]
#align basis.repr_symm_single Basis.repr_symm_single

@[simp]
theorem repr_self : b.repr (b i) = Finsupp.single i 1 :=
  LinearEquiv.apply_symm_apply _ _
#align basis.repr_self Basis.repr_self

theorem repr_self_apply (j) [Decidable (i = j)] : b.repr (b i) j = if i = j then 1 else 0 := by
  rw [repr_self, Finsupp.single_apply]
#align basis.repr_self_apply Basis.repr_self_apply

@[simp]
theorem repr_symm_apply (v) : b.repr.symm v = Finsupp.total ι M R b v :=
  calc
    b.repr.symm v = b.repr.symm (v.sum Finsupp.single) := by simp
    _ = v.sum fun i vi => b.repr.symm (Finsupp.single i vi) := map_finsupp_sum ..
    _ = Finsupp.total ι M R b v := by simp only [repr_symm_single, Finsupp.total_apply]
#align basis.repr_symm_apply Basis.repr_symm_apply

@[simp]
theorem coe_repr_symm : ↑b.repr.symm = Finsupp.total ι M R b :=
  LinearMap.ext fun v => b.repr_symm_apply v
#align basis.coe_repr_symm Basis.coe_repr_symm

@[simp]
theorem repr_total (v) : b.repr (Finsupp.total _ _ _ b v) = v := by
  rw [← b.coe_repr_symm]
  exact b.repr.apply_symm_apply v
#align basis.repr_total Basis.repr_total

@[simp]
theorem total_repr : Finsupp.total _ _ _ b (b.repr x) = x := by
  rw [← b.coe_repr_symm]
  exact b.repr.symm_apply_apply x
#align basis.total_repr Basis.total_repr

theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]
#align basis.repr_range Basis.repr_range

theorem mem_span_repr_support (m : M) : m ∈ span R (b '' (b.repr m).support) :=
  (Finsupp.mem_span_image_iff_total _).2 ⟨b.repr m, by simp [Finsupp.mem_supported_support]⟩
#align basis.mem_span_repr_support Basis.mem_span_repr_support

theorem repr_support_subset_of_mem_span (s : Set ι) {m : M}
    (hm : m ∈ span R (b '' s)) : ↑(b.repr m).support ⊆ s := by
  rcases (Finsupp.mem_span_image_iff_total _).1 hm with ⟨l, hl, rfl⟩
  rwa [repr_total, ← Finsupp.mem_supported R l]
#align basis.repr_support_subset_of_mem_span Basis.repr_support_subset_of_mem_span

theorem mem_span_image {m : M} {s : Set ι} : m ∈ span R (b '' s) ↔ ↑(b.repr m).support ⊆ s :=
  ⟨repr_support_subset_of_mem_span _ _, fun h ↦
    span_mono (image_subset _ h) (mem_span_repr_support b _)⟩

@[simp]
theorem self_mem_span_image [Nontrivial R] {i : ι} {s : Set ι} :
    b i ∈ span R (b '' s) ↔ i ∈ s := by
  simp [mem_span_image, Finsupp.support_single_ne_zero]

end repr

section Coord

/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps!]
def coord : M →ₗ[R] R :=
  Finsupp.lapply i ∘ₗ ↑b.repr
#align basis.coord Basis.coord

theorem forall_coord_eq_zero_iff {x : M} : (∀ i, b.coord i x = 0) ↔ x = 0 :=
  Iff.trans (by simp only [b.coord_apply, DFunLike.ext_iff, Finsupp.zero_apply])
    b.repr.map_eq_zero_iff
#align basis.forall_coord_eq_zero_iff Basis.forall_coord_eq_zero_iff

/-- The sum of the coordinates of an element `m : M` with respect to a basis. -/
noncomputable def sumCoords : M →ₗ[R] R :=
  (Finsupp.lsum ℕ fun _ => LinearMap.id) ∘ₗ (b.repr : M →ₗ[R] ι →₀ R)
#align basis.sum_coords Basis.sumCoords

@[simp]
theorem coe_sumCoords : (b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id :=
  rfl
#align basis.coe_sum_coords Basis.coe_sumCoords

theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]
#align basis.coe_sum_coords_eq_finsum Basis.coe_sumCoords_eq_finsum

@[simp high]
theorem coe_sumCoords_of_fintype [Fintype ι] : (b.sumCoords : M → R) = ∑ i, b.coord i := by
  ext m
  -- Porting note: - `eq_self_iff_true`
  --               + `comp_apply` `LinearMap.coeFn_sum`
  simp only [sumCoords, Finsupp.sum_fintype, LinearMap.id_coe, LinearEquiv.coe_coe, coord_apply,
    id, Fintype.sum_apply, imp_true_iff, Finsupp.coe_lsum, LinearMap.coe_comp, comp_apply,
    LinearMap.coeFn_sum]
#align basis.coe_sum_coords_of_fintype Basis.coe_sumCoords_of_fintype

@[simp]
theorem sumCoords_self_apply : b.sumCoords (b i) = 1 := by
  simp only [Basis.sumCoords, LinearMap.id_coe, LinearEquiv.coe_coe, id, Basis.repr_self,
    Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp, Finsupp.sum_single_index]
#align basis.sum_coords_self_apply Basis.sumCoords_self_apply

theorem dvd_coord_smul (i : ι) (m : M) (r : R) : r ∣ b.coord i (r • m) :=
  ⟨b.coord i m, by simp⟩
#align basis.dvd_coord_smul Basis.dvd_coord_smul

theorem coord_repr_symm (b : Basis ι R M) (i : ι) (f : ι →₀ R) :
    b.coord i (b.repr.symm f) = f i := by
  simp only [repr_symm_apply, coord_apply, repr_total]
#align basis.coord_repr_symm Basis.coord_repr_symm

end Coord

section Ext

variable {R₁ : Type*} [Semiring R₁] {σ : R →+* R₁} {σ' : R₁ →+* R}
variable [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
variable {M₁ : Type*} [AddCommMonoid M₁] [Module R₁ M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [map_sum, LinearMap.map_smulₛₗ, h]
#align basis.ext Basis.ext

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₛₗ[σ] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ := by
  ext x
  rw [← b.total_repr x, Finsupp.total_apply, Finsupp.sum]
  simp only [map_sum, LinearEquiv.map_smulₛₗ, h]
#align basis.ext' Basis.ext'

/-- Two elements are equal iff their coordinates are equal. -/
theorem ext_elem_iff {x y : M} : x = y ↔ ∀ i, b.repr x i = b.repr y i := by
  simp only [← DFunLike.ext_iff, EmbeddingLike.apply_eq_iff_eq]
#align basis.ext_elem_iff Basis.ext_elem_iff

alias ⟨_, _root_.Basis.ext_elem⟩ := ext_elem_iff
#align basis.ext_elem Basis.ext_elem

theorem repr_eq_iff {b : Basis ι R M} {f : M →ₗ[R] ι →₀ R} :
    ↑b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff Basis.repr_eq_iff

theorem repr_eq_iff' {b : Basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
    b.repr = f ↔ ∀ i, f (b i) = Finsupp.single i 1 :=
  ⟨fun h i => h ▸ b.repr_self i, fun h => b.ext' fun i => (b.repr_self i).trans (h i).symm⟩
#align basis.repr_eq_iff' Basis.repr_eq_iff'

theorem apply_eq_iff {b : Basis ι R M} {x : M} {i : ι} : b i = x ↔ b.repr x = Finsupp.single i 1 :=
  ⟨fun h => h ▸ b.repr_self i, fun h => b.repr.injective ((b.repr_self i).trans h.symm)⟩
#align basis.apply_eq_iff Basis.apply_eq_iff

/-- An unbundled version of `repr_eq_iff` -/
theorem repr_apply_eq (f : M → ι → R) (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x) (f_eq : ∀ i, f (b i) = Finsupp.single i 1)
    (x : M) (i : ι) : b.repr x i = f x i := by
  let f_i : M →ₗ[R] R :=
    { toFun := fun x => f x i
      -- Porting note(#12129): additional beta reduction needed
      map_add' := fun _ _ => by beta_reduce; rw [hadd, Pi.add_apply]
      map_smul' := fun _ _ => by simp [hsmul, Pi.smul_apply] }
  have : Finsupp.lapply i ∘ₗ ↑b.repr = f_i := by
    refine b.ext fun j => ?_
    show b.repr (b j) i = f (b j) i
    rw [b.repr_self, f_eq]
  calc
    b.repr x i = f_i x := by
      { rw [← this]
        rfl }
    _ = f x i := rfl
#align basis.repr_apply_eq Basis.repr_apply_eq

/-- Two bases are equal if they assign the same coordinates. -/
theorem eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂ :=
  repr_injective <| by ext; apply h
#align basis.eq_of_repr_eq_repr Basis.eq_ofRepr_eq_repr

/-- Two bases are equal if their basis vectors are the same. -/
@[ext]
theorem eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (∀ i, b₁ i = b₂ i) → b₁ = b₂ :=
  DFunLike.ext _ _
#align basis.eq_of_apply_eq Basis.eq_of_apply_eq

end Ext

section Map

variable (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps]
protected def map : Basis ι R M' :=
  ofRepr (f.symm.trans b.repr)
#align basis.map Basis.map

@[simp]
theorem map_apply (i) : b.map f i = f (b i) :=
  rfl
#align basis.map_apply Basis.map_apply

theorem coe_map : (b.map f : ι → M') = f ∘ b :=
  rfl

end Map

section MapCoeffs

variable {R' : Type*} [Semiring R'] [Module R' M] (f : R ≃+* R')
  (h : ∀ (c) (x : M), f c • x = c • x)

attribute [local instance] SMul.comp.isScalarTower

/-- If `R` and `R'` are isomorphic rings that act identically on a module `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module.

See also `Basis.algebraMapCoeffs` for the case where `f` is equal to `algebraMap`.
-/
@[simps (config := { simpRhs := true })]
def mapCoeffs : Basis ι R' M := by
  letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
  haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        -- Porting note: `dsimp [(· • ·)]` is unavailable because
        --               `HSMul.hsmul` becomes `SMul.smul`.
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul, ← h, f.apply_symm_apply] }
  exact ofRepr <| (b.repr.restrictScalars R').trans <|
    Finsupp.mapRange.linearEquiv (Module.compHom.toLinearEquiv f.symm).symm
#align basis.map_coeffs Basis.mapCoeffs

theorem mapCoeffs_apply (i : ι) : b.mapCoeffs f h i = b i :=
  apply_eq_iff.mpr <| by
    -- Porting note: in Lean 3, these were automatically inferred from the definition of
    -- `mapCoeffs`.
    letI : Module R' R := Module.compHom R (↑f.symm : R' →+* R)
    haveI : IsScalarTower R' R M :=
    { smul_assoc := fun x y z => by
        -- Porting note: `dsimp [(· • ·)]` is unavailable because
        --               `HSMul.hsmul` becomes `SMul.smul`.
        change (f.symm x * y) • z = x • (y • z)
        rw [mul_smul, ← h, f.apply_symm_apply] }
    simp
#align basis.map_coeffs_apply Basis.mapCoeffs_apply

@[simp]
theorem coe_mapCoeffs : (b.mapCoeffs f h : ι → M) = b :=
  funext <| b.mapCoeffs_apply f h
#align basis.coe_map_coeffs Basis.coe_mapCoeffs

end MapCoeffs

section Reindex

variable (b' : Basis ι' R M')
variable (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : Basis ι' R M :=
  .ofRepr (b.repr.trans (Finsupp.domLCongr e))
#align basis.reindex Basis.reindex

theorem reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
  show (b.repr.trans (Finsupp.domLCongr e)).symm (Finsupp.single i' 1) =
    b.repr.symm (Finsupp.single (e.symm i') 1)
  by rw [LinearEquiv.symm_trans_apply, Finsupp.domLCongr_symm, Finsupp.domLCongr_single]
#align basis.reindex_apply Basis.reindex_apply

@[simp]
theorem coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
  funext (b.reindex_apply e)
#align basis.coe_reindex Basis.coe_reindex

theorem repr_reindex_apply (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
  show (Finsupp.domLCongr e : _ ≃ₗ[R] _) (b.repr x) i' = _ by simp
#align basis.repr_reindex_apply Basis.repr_reindex_apply

@[simp]
theorem repr_reindex : (b.reindex e).repr x = (b.repr x).mapDomain e :=
  DFunLike.ext _ _ <| by simp [repr_reindex_apply]
#align basis.repr_reindex Basis.repr_reindex

@[simp]
theorem reindex_refl : b.reindex (Equiv.refl ι) = b :=
  eq_of_apply_eq fun i => by simp
#align basis.reindex_refl Basis.reindex_refl

/-- `simp` can prove this as `Basis.coe_reindex` + `EquivLike.range_comp` -/
theorem range_reindex : Set.range (b.reindex e) = Set.range b := by
  simp [coe_reindex, range_comp]
#align basis.range_reindex Basis.range_reindex

@[simp]
theorem sumCoords_reindex : (b.reindex e).sumCoords = b.sumCoords := by
  ext x
  simp only [coe_sumCoords, repr_reindex]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) fun _ _ _ => rfl
#align basis.sum_coords_reindex Basis.sumCoords_reindex

/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindexRange : Basis (range b) R M :=
  haveI := Classical.dec (Nontrivial R)
  if h : Nontrivial R then
    letI := h
    b.reindex (Equiv.ofInjective b (Basis.injective b))
  else
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    .ofRepr (Module.subsingletonEquiv R M (range b))
#align basis.reindex_range Basis.reindexRange

theorem reindexRange_self (i : ι) (h := Set.mem_range_self i) : b.reindexRange ⟨b i, h⟩ = b i := by
  by_cases htr : Nontrivial R
  · letI := htr
    simp [htr, reindexRange, reindex_apply, Equiv.apply_ofInjective_symm b.injective,
      Subtype.coe_mk]
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp htr
    letI := Module.subsingleton R M
    simp [reindexRange, eq_iff_true_of_subsingleton]
#align basis.reindex_range_self Basis.reindexRange_self

theorem reindexRange_repr_self (i : ι) :
    b.reindexRange.repr (b i) = Finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
  calc
    b.reindexRange.repr (b i) = b.reindexRange.repr (b.reindexRange ⟨b i, mem_range_self i⟩) :=
      congr_arg _ (b.reindexRange_self _ _).symm
    _ = Finsupp.single ⟨b i, mem_range_self i⟩ 1 := b.reindexRange.repr_self _
#align basis.reindex_range_repr_self Basis.reindexRange_repr_self

@[simp]
theorem reindexRange_apply (x : range b) : b.reindexRange x = x := by
  rcases x with ⟨bi, ⟨i, rfl⟩⟩
  exact b.reindexRange_self i
#align basis.reindex_range_apply Basis.reindexRange_apply

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
#align basis.reindex_range_repr' Basis.reindexRange_repr'

@[simp]
theorem reindexRange_repr (x : M) (i : ι) (h := Set.mem_range_self i) :
    b.reindexRange.repr x ⟨b i, h⟩ = b.repr x i :=
  b.reindexRange_repr' _ rfl
#align basis.reindex_range_repr Basis.reindexRange_repr

section Fintype

variable [Fintype ι] [DecidableEq M]

/-- `b.reindexFinsetRange` is a basis indexed by `Finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindexFinsetRange : Basis (Finset.univ.image b) R M :=
  b.reindexRange.reindex ((Equiv.refl M).subtypeEquiv (by simp))
#align basis.reindex_finset_range Basis.reindexFinsetRange

theorem reindexFinsetRange_self (i : ι) (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange ⟨b i, h⟩ = b i := by
  rw [reindexFinsetRange, reindex_apply, reindexRange_apply]
  rfl
#align basis.reindex_finset_range_self Basis.reindexFinsetRange_self

@[simp]
theorem reindexFinsetRange_apply (x : Finset.univ.image b) : b.reindexFinsetRange x = x := by
  rcases x with ⟨bi, hbi⟩
  rcases Finset.mem_image.mp hbi with ⟨i, -, rfl⟩
  exact b.reindexFinsetRange_self i
#align basis.reindex_finset_range_apply Basis.reindexFinsetRange_apply

theorem reindexFinsetRange_repr_self (i : ι) :
    b.reindexFinsetRange.repr (b i) =
      Finsupp.single ⟨b i, Finset.mem_image_of_mem b (Finset.mem_univ i)⟩ 1 := by
  ext ⟨bi, hbi⟩
  rw [reindexFinsetRange, repr_reindex, Finsupp.mapDomain_equiv_apply, reindexRange_repr_self]
  -- Porting note: replaced a `convert; refl` with `simp`
  simp [Finsupp.single_apply]
#align basis.reindex_finset_range_repr_self Basis.reindexFinsetRange_repr_self

@[simp]
theorem reindexFinsetRange_repr (x : M) (i : ι)
    (h := Finset.mem_image_of_mem b (Finset.mem_univ i)) :
    b.reindexFinsetRange.repr x ⟨b i, h⟩ = b.repr x i := by simp [reindexFinsetRange]
#align basis.reindex_finset_range_repr Basis.reindexFinsetRange_repr

end Fintype

end Reindex

protected theorem linearIndependent : LinearIndependent R b :=
  linearIndependent_iff.mpr fun l hl =>
    calc
      l = b.repr (Finsupp.total _ _ _ b l) := (b.repr_total l).symm
      _ = 0 := by rw [hl, LinearEquiv.map_zero]
#align basis.linear_independent Basis.linearIndependent

protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.linearIndependent.ne_zero i
#align basis.ne_zero Basis.ne_zero

protected theorem mem_span (x : M) : x ∈ span R (range b) :=
  span_mono (image_subset_range _ _) (mem_span_repr_support b x)
#align basis.mem_span Basis.mem_span

@[simp]
protected theorem span_eq : span R (range b) = ⊤ :=
  eq_top_iff.mpr fun x _ => b.mem_span x
#align basis.span_eq Basis.span_eq

theorem index_nonempty (b : Basis ι R M) [Nontrivial M] : Nonempty ι := by
  obtain ⟨x, y, ne⟩ : ∃ x y : M, x ≠ y := Nontrivial.exists_pair_ne
  obtain ⟨i, _⟩ := not_forall.mp (mt b.ext_elem_iff.2 ne)
  exact ⟨i⟩
#align basis.index_nonempty Basis.index_nonempty

/-- If the submodule `P` has a basis, `x ∈ P` iff it is a linear combination of basis vectors. -/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
        ← Finsupp.range_total]
  simp [@eq_comm _ x, Function.comp, Finsupp.total_apply]
#align basis.mem_submodule_iff Basis.mem_submodule_iff

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
  toFun f := (Finsupp.total M' M' R id).comp <| Finsupp.lmapDomain R R f ∘ₗ ↑b.repr
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
#align basis.constr Basis.constr

theorem constr_def (f : ι → M') :
    constr (M' := M') b S f = Finsupp.total M' M' R id ∘ₗ Finsupp.lmapDomain R R f ∘ₗ ↑b.repr :=
  rfl
#align basis.constr_def Basis.constr_def

theorem constr_apply (f : ι → M') (x : M) :
    constr (M' := M') b S f x = (b.repr x).sum fun b a => a • f b := by
  simp only [constr_def, LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.total_apply]
  rw [Finsupp.sum_mapDomain_index] <;> simp [add_smul]
#align basis.constr_apply Basis.constr_apply

@[simp]
theorem constr_basis (f : ι → M') (i : ι) : (constr (M' := M') b S f : M → M') (b i) = f i := by
  simp [Basis.constr_apply, b.repr_self]
#align basis.constr_basis Basis.constr_basis

theorem constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (h : ∀ i, g i = f (b i)) :
    constr (M' := M') b S g = f :=
  b.ext fun i => (b.constr_basis S g i).trans (h i)
#align basis.constr_eq Basis.constr_eq

theorem constr_self (f : M →ₗ[R] M') : (constr (M' := M') b S fun i => f (b i)) = f :=
  b.constr_eq S fun _ => rfl
#align basis.constr_self Basis.constr_self

theorem constr_range {f : ι → M'} :
    LinearMap.range (constr (M' := M') b S f) = span R (range f) := by
  rw [b.constr_def S f, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, ←
    Finsupp.supported_univ, Finsupp.lmapDomain_supported, ← Set.image_univ, ←
    Finsupp.span_image_eq_map_total, Set.image_id]
#align basis.constr_range Basis.constr_range

@[simp]
theorem constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
    constr (M' := M') b S (f ∘ v) = f.comp (constr (M' := M') b S v) :=
  b.ext fun i => by simp only [Basis.constr_basis, LinearMap.comp_apply, Function.comp]
#align basis.constr_comp Basis.constr_comp

end Constr

section Equiv

variable (b' : Basis ι' R M') (e : ι ≃ ι')
variable [AddCommMonoid M''] [Module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
  b.repr.trans (b'.reindex e.symm).repr.symm
#align basis.equiv Basis.equiv

@[simp]
theorem equiv_apply : b.equiv b' e (b i) = b' (e i) := by simp [Basis.equiv]
#align basis.equiv_apply Basis.equiv_apply

@[simp]
theorem equiv_refl : b.equiv b (Equiv.refl ι) = LinearEquiv.refl R M :=
  b.ext' fun i => by simp
#align basis.equiv_refl Basis.equiv_refl

@[simp]
theorem equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
  b'.ext' fun i => (b.equiv b' e).injective (by simp)
#align basis.equiv_symm Basis.equiv_symm

@[simp]
theorem equiv_trans {ι'' : Type*} (b'' : Basis ι'' R M'') (e : ι ≃ ι') (e' : ι' ≃ ι'') :
    (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
  b.ext' fun i => by simp
#align basis.equiv_trans Basis.equiv_trans

@[simp]
theorem map_equiv (b : Basis ι R M) (b' : Basis ι' R M') (e : ι ≃ ι') :
    b.map (b.equiv b' e) = b'.reindex e.symm := by
  ext i
  simp
#align basis.map_equiv Basis.map_equiv

end Equiv

section Prod

variable (b' : Basis ι' R M')

/-- `Basis.prod` maps an `ι`-indexed basis for `M` and an `ι'`-indexed basis for `M'`
to an `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `Basis.finTwoProd`. -/
protected def prod : Basis (Sum ι ι') R (M × M') :=
  ofRepr ((b.repr.prod b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)
#align basis.prod Basis.prod

@[simp]
theorem prod_repr_inl (x) (i) : (b.prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl
#align basis.prod_repr_inl Basis.prod_repr_inl

@[simp]
theorem prod_repr_inr (x) (i) : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl
#align basis.prod_repr_inr Basis.prod_repr_inr

theorem prod_apply_inl_fst (i) : (b.prod b' (Sum.inl i)).1 = b i :=
  b.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inl_injective
#align basis.prod_apply_inl_fst Basis.prod_apply_inl_fst

theorem prod_apply_inr_fst (i) : (b.prod b' (Sum.inr i)).1 = 0 :=
  b.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl
#align basis.prod_apply_inr_fst Basis.prod_apply_inr_fst

theorem prod_apply_inl_snd (i) : (b.prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr
#align basis.prod_apply_inl_snd Basis.prod_apply_inl_snd

theorem prod_apply_inr_snd (i) : (b.prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inr_injective
#align basis.prod_apply_inr_snd Basis.prod_apply_inr_snd

@[simp]
theorem prod_apply (i) :
    b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, Function.comp]
#align basis.prod_apply Basis.prod_apply

end Prod

section NoZeroSMulDivisors

-- Can't be an instance because the basis can't be inferred.
protected theorem noZeroSMulDivisors [NoZeroDivisors R] (b : Basis ι R M) :
    NoZeroSMulDivisors R M :=
  ⟨fun {c x} hcx => by
    exact or_iff_not_imp_right.mpr fun hx => by
      rw [← b.total_repr x, ← LinearMap.map_smul] at hcx
      have := linearIndependent_iff.mp b.linearIndependent (c • b.repr x) hcx
      rw [smul_eq_zero] at this
      exact this.resolve_right fun hr => hx (b.repr.map_eq_zero_iff.mp hr)⟩
#align basis.no_zero_smul_divisors Basis.noZeroSMulDivisors

protected theorem smul_eq_zero [NoZeroDivisors R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 :=
  @smul_eq_zero _ _ _ _ _ b.noZeroSMulDivisors _ _
#align basis.smul_eq_zero Basis.smul_eq_zero

theorem eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  cases' i with _ hi
  simp only [Function.const_apply, Fin.default_eq_zero, Submodule.coe_mk, Finset.univ_unique,
    Function.comp_const, Finset.sum_singleton] at sum_eq
  convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne
#align eq_bot_of_rank_eq_zero Basis.eq_bot_of_rank_eq_zero

end NoZeroSMulDivisors

section Singleton

/-- `Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
#align basis.singleton Basis.singleton

@[simp]
theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])
#align basis.singleton_apply Basis.singleton_apply

@[simp]
theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]
#align basis.singleton_repr Basis.singleton_repr

theorem basis_singleton_iff {R M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (ι : Type*) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine ⟨ofRepr <| LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec
#align basis.basis_singleton_iff Basis.basis_singleton_iff

end Singleton

section Empty

variable (M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0
#align basis.empty Basis.empty

instance emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) where
  default := Basis.empty M
  uniq := fun _ => congr_arg ofRepr <| Subsingleton.elim _ _
#align basis.empty_unique Basis.emptyUnique

end Empty

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
#align basis.equiv_fun Basis.equivFun

/-- A module over a finite ring that admits a finite basis is finite. -/
def Module.fintypeOfFintype [Fintype ι] (b : Basis ι R M) [Fintype R] : Fintype M :=
  haveI := Classical.decEq ι
  Fintype.ofEquiv _ b.equivFun.toEquiv.symm
#align module.fintype_of_fintype Module.fintypeOfFintype

theorem Module.card_fintype [Fintype ι] (b : Basis ι R M) [Fintype R] [Fintype M] :
    card M = card R ^ card ι := by
  classical
    calc
      card M = card (ι → R) := card_congr b.equivFun.toEquiv
      _ = card R ^ card ι := card_fun
#align module.card_fintype Module.card_fintype

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp]
theorem Basis.equivFun_symm_apply [Fintype ι] (b : Basis ι R M) (x : ι → R) :
    b.equivFun.symm x = ∑ i, x i • b i := by
  simp [Basis.equivFun, Finsupp.total_apply, Finsupp.sum_fintype, Finsupp.equivFunOnFinite]
#align basis.equiv_fun_symm_apply Basis.equivFun_symm_apply

@[simp]
theorem Basis.equivFun_apply [Finite ι] (b : Basis ι R M) (u : M) : b.equivFun u = b.repr u :=
  rfl
#align basis.equiv_fun_apply Basis.equivFun_apply

@[simp]
theorem Basis.map_equivFun [Finite ι] (b : Basis ι R M) (f : M ≃ₗ[R] M') :
    (b.map f).equivFun = f.symm.trans b.equivFun :=
  rfl
#align basis.map_equiv_fun Basis.map_equivFun

theorem Basis.sum_equivFun [Fintype ι] (b : Basis ι R M) (u : M) :
    ∑ i, b.equivFun u i • b i = u := by
  rw [← b.equivFun_symm_apply, b.equivFun.symm_apply_apply]
#align basis.sum_equiv_fun Basis.sum_equivFun

theorem Basis.sum_repr [Fintype ι] (b : Basis ι R M) (u : M) : ∑ i, b.repr u i • b i = u :=
  b.sum_equivFun u
#align basis.sum_repr Basis.sum_repr

@[simp]
theorem Basis.equivFun_self [Finite ι] [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    b.equivFun (b i) j = if i = j then 1 else 0 := by rw [b.equivFun_apply, b.repr_self_apply]
#align basis.equiv_fun_self Basis.equivFun_self

theorem Basis.repr_sum_self [Fintype ι] (b : Basis ι R M) (c : ι → R) :
    b.repr (∑ i, c i • b i) = c := by
  simp_rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]
#align basis.repr_sum_self Basis.repr_sum_self

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def Basis.ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) : Basis ι R M :=
  .ofRepr <| e.trans <| LinearEquiv.symm <| Finsupp.linearEquivFunOnFinite R R ι
#align basis.of_equiv_fun Basis.ofEquivFun

@[simp]
theorem Basis.ofEquivFun_repr_apply [Finite ι] (e : M ≃ₗ[R] ι → R) (x : M) (i : ι) :
    (Basis.ofEquivFun e).repr x i = e x i :=
  rfl
#align basis.of_equiv_fun_repr_apply Basis.ofEquivFun_repr_apply

@[simp]
theorem Basis.coe_ofEquivFun [Finite ι] [DecidableEq ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e : ι → M) = fun i => e.symm (Function.update 0 i 1) :=
  funext fun i =>
    e.injective <|
      funext fun j => by
        simp [Basis.ofEquivFun, ← Finsupp.single_eq_pi_single, Finsupp.single_eq_update]
#align basis.coe_of_equiv_fun Basis.coe_ofEquivFun

@[simp]
theorem Basis.ofEquivFun_equivFun [Finite ι] (v : Basis ι R M) :
    Basis.ofEquivFun v.equivFun = v :=
  Basis.repr_injective <| by ext; rfl
#align basis.of_equiv_fun_equiv_fun Basis.ofEquivFun_equivFun

@[simp]
theorem Basis.equivFun_ofEquivFun [Finite ι] (e : M ≃ₗ[R] ι → R) :
    (Basis.ofEquivFun e).equivFun = e := by
  ext j
  simp_rw [Basis.equivFun_apply, Basis.ofEquivFun_repr_apply]
#align basis.equiv_fun_of_equiv_fun Basis.equivFun_ofEquivFun

variable (S : Type*) [Semiring S] [Module S M']
variable [SMulCommClass R S M']

@[simp]
theorem Basis.constr_apply_fintype [Fintype ι] (b : Basis ι R M) (f : ι → M') (x : M) :
    (constr (M' := M') b S f : M → M') x = ∑ i, b.equivFun x i • f i := by
  simp [b.constr_apply, b.equivFun_apply, Finsupp.sum_fintype]
#align basis.constr_apply_fintype Basis.constr_apply_fintype

/-- If the submodule `P` has a finite basis,
`x ∈ P` iff it is a linear combination of basis vectors. -/
theorem Basis.mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι → R, x = ∑ i, c i • (b i : M) :=
  b.mem_submodule_iff.trans <|
    Finsupp.equivFunOnFinite.exists_congr_left.trans <|
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]
#align basis.mem_submodule_iff' Basis.mem_submodule_iff'

theorem Basis.coord_equivFun_symm [Finite ι] (b : Basis ι R M) (i : ι) (f : ι → R) :
    b.coord i (b.equivFun.symm f) = f i :=
  b.coord_repr_symm i (Finsupp.equivFunOnFinite.symm f)
#align basis.coord_equiv_fun_symm Basis.coord_equivFun_symm

end Fintype

end Module

section CommSemiring

namespace Basis

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
variable (b : Basis ι R M) (b' : Basis ι' R M')

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
#align basis.equiv' Basis.equiv'

@[simp]
theorem equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
    b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
  b.constr_basis R _ _
#align basis.equiv'_apply Basis.equiv'_apply

@[simp]
theorem equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
    (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
  b'.constr_basis R _ _
#align basis.equiv'_symm_apply Basis.equiv'_symm_apply

theorem sum_repr_mul_repr {ι'} [Fintype ι'] (b' : Basis ι' R M) (x : M) (i : ι) :
    (∑ j : ι', b.repr (b' j) i * b'.repr x j) = b.repr x i := by
  conv_rhs => rw [← b'.sum_repr x]
  simp_rw [map_sum, map_smul, Finset.sum_apply']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm]
#align basis.sum_repr_mul_repr Basis.sum_repr_mul_repr

end Basis

end CommSemiring

section Module

open LinearMap

variable {v : ι → M}
variable [Ring R] [CommRing R₂] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
variable [Module R M] [Module R₂ M] [Module R M'] [Module R M'']
variable {c d : R} {x y : M}
variable (b : Basis ι R M)

namespace Basis

/-- Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.total_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.total_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)), ← Finsupp.total_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.total_ne_of_not_mem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩
#align basis.maximal Basis.maximal

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.total _ _ _ v
      left_inv := fun x => hli.total_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }
#align basis.mk Basis.mk

@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl
#align basis.mk_repr Basis.mk_repr

theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.total _ _ _ v _ = v i by simp
#align basis.mk_apply Basis.mk_apply

@[simp]
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)
#align basis.coe_mk Basis.coe_mk

variable {hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]
#align basis.mk_coord_apply_eq Basis.mk_coord_apply_eq

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]
#align basis.mk_coord_apply_ne Basis.mk_coord_apply_ne

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]
#align basis.mk_coord_apply Basis.mk_coord_apply

end Mk

section Span

variable (hli : LinearIndependent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have : ∀ i, v i ∈ span R (range v) := fun i ↦ subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) → M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [SetLike.coe_sort_coe, ← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image, Submodule.coeSubtype]
      -- Porting note: why doesn't `rw [h₁]` work here?
      exact congr_arg _ h₁
    have h₃ : (x : M) ∈ map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) _)) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]
#align basis.span Basis.span

protected theorem span_apply (i : ι) : (Basis.span hli i : M) = v i :=
  congr_arg ((↑) : span R (range v) → M) <| Basis.mk_apply _ _ _
#align basis.span_apply Basis.span_apply

end Span

theorem groupSMul_span_eq_top {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this
#align basis.group_smul_span_eq_top Basis.groupSMul_span_eq_top

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`groupSMul` provides the basis corresponding to `w • v`. -/
def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge
#align basis.group_smul Basis.groupSMul

theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i :=
  mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i
#align basis.group_smul_apply Basis.groupSMul_apply

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSMul_span_eq_top hv
#align basis.units_smul_span_eq_top Basis.units_smul_span_eq_top

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `unitsSMul`
provides the basis corresponding to `w • v`. -/
def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge
#align basis.units_smul Basis.unitsSMul

theorem unitsSMul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : unitsSMul v w i = w i • v i :=
  mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i
#align basis.units_smul_apply Basis.unitsSMul_apply

@[simp]
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · congr
      simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]
#align basis.coord_units_smul Basis.coord_unitsSMul

@[simp]
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)
#align basis.repr_units_smul Basis.repr_unitsSMul

/-- A version of `unitsSMul` that uses `IsUnit`. -/
def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit
#align basis.is_unit_smul Basis.isUnitSMul

theorem isUnitSMul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i
#align basis.is_unit_smul_apply Basis.isUnitSMul_apply

section Fin

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).fin_cons' _ _
      (by
        rintro c ⟨x, hx⟩ hc
        rw [span_b] at hx
        exact hli c x hx hc))
    fun x _ => by
      rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
      exact hsp x
#align basis.mk_fin_cons Basis.mkFinCons

@[simp]
theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y ((↑) ∘ b) := by
  -- Porting note: without `unfold`, Lean can't reuse the proofs included in the definition
  -- `mkFinCons`
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _
#align basis.coe_mk_fin_cons Basis.coe_mkFinCons

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2
#align basis.mk_fin_cons_of_le Basis.mkFinConsOfLE

@[simp]
theorem coe_mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) :=
  coe_mkFinCons _ _ _ _
#align basis.coe_mk_fin_cons_of_le Basis.coe_mkFinConsOfLE

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
protected def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm
#align basis.fin_two_prod Basis.finTwoProd

@[simp]
theorem finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]
#align basis.fin_two_prod_zero Basis.finTwoProd_zero

@[simp]
theorem finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]
#align basis.fin_two_prod_one Basis.finTwoProd_one

@[simp]
theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl
#align basis.coe_fin_two_prod_repr Basis.coe_finTwoProd_repr

end Fin

end Basis

end Module

section Induction

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m ≤ n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction' n with n rank_ih generalizing N
  · suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m hv => Nat.le_zero.mp (rank_le _ hv)
  apply ih
  intro N' N'_le x x_mem x_ortho
  apply rank_ih
  intro m v hli
  refine Nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) ?_)
  convert hli.fin_cons' x _ ?_
  · ext i
    refine Fin.cases ?_ ?_ i <;> simp
  · intro c y hcy
    refine x_ortho c y (Submodule.span_le.mpr ?_ y.2) hcy
    rintro _ ⟨z, rfl⟩
    exact (v z).2
#align submodule.induction_on_rank_aux Submodule.inductionOnRankAux

end Induction

/-- An element of a non-unital-non-associative algebra is in the center exactly when it commutes
with the basis elements. -/
lemma Basis.mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Basis ι R A) {z : A} :
    z ∈ Set.center A ↔
      (∀ i, Commute (b i) z) ∧ ∀ i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * z) * b j = b i * (z * b j)
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, ⟨h.3 _ _, h.4 _ _⟩⟩
  · intro h
    rw [center, mem_setOf_eq]
    constructor
    case comm =>
      intro y
      rw [← b.total_repr y, Finsupp.total_apply, Finsupp.sum, Finset.sum_mul, Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.total_repr c, ← b.total_repr d, Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum,
        Finsupp.sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case mid_assoc =>
      intro c d
      rw [← b.total_repr c, ← b.total_repr d, Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum,
        Finsupp.sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, (h.2 _ _).2.1]
    case right_assoc =>
      intro c d
      rw [← b.total_repr c, ← b.total_repr d, Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum,
        Finsupp.sum, Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
        (h.2 _ _).2.2]

section RestrictScalars

variable {S : Type*} [CommRing R] [Ring S] [Nontrivial S] [AddCommGroup M]
variable [Algebra R S] [Module S M] [Module R M]
variable [IsScalarTower R S M] [NoZeroSMulDivisors R S] (b : Basis ι S M)
variable (R)

open Submodule

/-- Let `b` be an `S`-basis of `M`. Let `R` be a CommRing such that `Algebra R S` has no zero smul
divisors, then the submodule of `M` spanned by `b` over `R` admits `b` as an `R`-basis. -/
noncomputable def Basis.restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))
#align basis.restrict_scalars Basis.restrictScalars

@[simp]
theorem Basis.restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Basis.restrictScalars, Basis.span_apply]
#align basis.restrict_scalars_apply Basis.restrictScalars_apply

@[simp]
theorem Basis.restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply, LinearEquiv.coe_coe,
    Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]
#align basis.restrict_scalars_repr_apply Basis.restrictScalars_repr_apply

/-- Let `b` be an `S`-basis of `M`. Then `m : M` lies in the `R`-module spanned by `b` iff all the
coordinates of `m` on the basis `b` are in `R` (see `Basis.mem_span` for the case `R = S`). -/
theorem Basis.mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.total_repr m, Finsupp.total_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))
#align basis.mem_span_iff_repr_mem Basis.mem_span_iff_repr_mem

end RestrictScalars

section Finite

open Basis Cardinal

universe v v' v'' u₁' w w'

variable {R : Type u} {M M₁ : Type v} {M' : Type v'} {ι : Type w}
variable [Ring R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁] [Nontrivial R]
variable [Module R M] [Module R M'] [Module R M₁]

-- One might hope that a finite spanning set implies that any linearly independent set is finite.
-- While this is true over a division ring
-- (simply because any linearly independent set can be extended to a basis),
-- or more generally over a ring satisfying the strong rank condition
-- (which covers all commutative rings; see `LinearIndependent.finite_of_le_span_finite`),
-- this is not true in general.
-- For example, the left ideal generated by the variables in a noncommutative polynomial ring
-- (`FreeAlgebra R ι`) in infinitely many variables (indexed by `ι`) is free
-- with an infinite basis (consisting of the variables).
-- As another example, for any commutative ring R, the ring of column-finite matrices
-- `Module.End R (ℕ →₀ R)` is isomorphic to `ℕ → Module.End R (ℕ →₀ R)` as a module over itself,
-- which also clearly contains an infinite linearly independent set.
/--
Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
lemma basis_finite_of_finite_spans (w : Set M) (hw : w.Finite) (s : span R w = ⊤) {ι : Type w}
    (b : Basis ι R M) : Finite ι := by
  classical
  haveI := hw.to_subtype
  cases nonempty_fintype w
  -- We'll work by contradiction, assuming `ι` is infinite.
  rw [← not_infinite_iff_finite]
  intro i
  -- Let `S` be the union of the supports of `x ∈ w` expressed as linear combinations of `b`.
  -- This is a finite set since `w` is finite.
  let S : Finset ι := Finset.univ.sup fun x : w => (b.repr x).support
  let bS : Set M := b '' S
  have h : ∀ x ∈ w, x ∈ span R bS := by
    intro x m
    rw [← b.total_repr x, Finsupp.span_image_eq_map_total, Submodule.mem_map]
    use b.repr x
    simp only [and_true_iff, eq_self_iff_true, Finsupp.mem_supported]
    rw [Finset.coe_subset, ← Finset.le_iff_subset]
    exact Finset.le_sup (f := fun x : w ↦ (b.repr ↑x).support) (Finset.mem_univ (⟨x, m⟩ : w))
  -- Thus this finite subset of the basis elements spans the entire module.
  have k : span R bS = ⊤ := eq_top_iff.2 (le_trans s.ge (span_le.2 h))
  -- Now there is some `x : ι` not in `S`, since `ι` is infinite.
  obtain ⟨x, nm⟩ := Infinite.exists_not_mem_finset S
  -- However it must be in the span of the finite subset,
  have k' : b x ∈ span R bS := by
    rw [k]
    exact mem_top
  -- giving the desire contradiction.
  exact b.linearIndependent.not_mem_span_image nm k'
#align basis_fintype_of_finite_spans basis_finite_of_finite_spansₓ

-- From [Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
/-- Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
theorem union_support_maximal_linearIndependent_eq_range_basis {ι : Type w} (b : Basis ι R M)
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    ⋃ k, ((b.repr (v k)).support : Set ι) = Set.univ := by
  -- If that's not the case,
  by_contra h
  simp only [← Ne.eq_def, ne_univ_iff_exists_not_mem, mem_iUnion, not_exists_not,
    Finsupp.mem_support_iff, Finset.mem_coe] at h
  -- We have some basis element `b b'` which is not in the support of any of the `v i`.
  obtain ⟨b', w⟩ := h
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b b'`.
  let v' : Option κ → M := fun o => o.elim (b b') v
  have r : range v ⊆ range v' := by
    rintro - ⟨k, rfl⟩
    use some k
    simp only [v', Option.elim_some]
  have r' : b b' ∉ range v := by
    rintro ⟨k, p⟩
    simpa [w] using congr_arg (fun m => (b.repr m) b') p
  have r'' : range v ≠ range v' := by
    intro e
    have p : b b' ∈ range v' := by
      use none
      simp only [v', Option.elim_none]
    rw [← e] at p
    exact r' p
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : LinearIndependent R ((↑) : range v' → M) := by
    apply LinearIndependent.to_subtype_range
    rw [linearIndependent_iff]
    intro l z
    rw [Finsupp.total_option] at z
    simp only [v', Option.elim'] at z
    change _ + Finsupp.total κ M R v l.some = 0 at z
    -- We have some linear combination of `b b'` and the `v i`, which we want to show is trivial.
    -- We'll first show the coefficient of `b b'` is zero,
    -- by expressing the `v i` in the basis `b`, and using that the `v i` have no `b b'` term.
    have l₀ : l none = 0 := by
      rw [← eq_neg_iff_add_eq_zero] at z
      replace z := neg_eq_iff_eq_neg.mpr z
      apply_fun fun x => b.repr x b' at z
      simp only [repr_self, map_smul, mul_one, Finsupp.single_eq_same, Pi.neg_apply,
        Finsupp.smul_single', map_neg, Finsupp.coe_neg] at z
      erw [DFunLike.congr_fun (Finsupp.apply_total R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b'] at z
      simpa [Finsupp.total_apply, w] using z
    -- Then all the other coefficients are zero, because `v` is linear independent.
    have l₁ : l.some = 0 := by
      rw [l₀, zero_smul, zero_add] at z
      exact linearIndependent_iff.mp i _ z
    -- Finally we put those facts together to show the linear combination is trivial.
    ext (_ | a)
    · simp only [l₀, Finsupp.coe_zero, Pi.zero_apply]
    · erw [DFunLike.congr_fun l₁ a]
      simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [LinearIndependent.Maximal] at m
  specialize m (range v') i' r
  exact r'' m
#align union_support_maximal_linear_independent_eq_range_basis union_support_maximal_linearIndependent_eq_range_basis

/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linearIndependent' {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w'} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) :
    Cardinal.lift.{w'} #ι ≤ Cardinal.lift.{w} #κ := by
  let Φ := fun k : κ => (b.repr (v k)).support
  have w₁ : #ι ≤ #(Set.range Φ) := by
    apply Cardinal.le_range_of_union_finset_eq_top
    exact union_support_maximal_linearIndependent_eq_range_basis b v i m
  have w₂ : Cardinal.lift.{w'} #(Set.range Φ) ≤ Cardinal.lift.{w} #κ := Cardinal.mk_range_le_lift
  exact (Cardinal.lift_le.mpr w₁).trans w₂
#align infinite_basis_le_maximal_linear_independent' infinite_basis_le_maximal_linearIndependent'

-- (See `infinite_basis_le_maximal_linearIndependent'` for the more general version
-- where the index types can live in different universes.)
/-- Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
theorem infinite_basis_le_maximal_linearIndependent {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ → M) (i : LinearIndependent R v) (m : i.Maximal) : #ι ≤ #κ :=
  Cardinal.lift_le.mp (infinite_basis_le_maximal_linearIndependent' b v i m)
#align infinite_basis_le_maximal_linear_independent infinite_basis_le_maximal_linearIndependent

end Finite
