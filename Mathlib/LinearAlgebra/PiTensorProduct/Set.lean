/-
Copyright (c) 2025 Davood H.H. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H. H. Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.PiTensorProduct

/-!
# PiTensorProducts indexed by sets

Given a family of modules `M : ι → Type*`, this module considers tensors of type
`⨂ (i : S), M i`, where `S : Set ι`. The binary tensor product of
`PiTensorProducts` indexed by disjoint sets is related to `PiTensorProduct`s
indexed by their union.

## Main definitions

* `tmulUnionEquiv` : the equivalence between the tensor product of `PiTensorProduct`s indexed
  by disjoint sets `S₁` and `S₂`, and the `PiTensorProduct` indexed by `S₁ ∪ S₂`.
* `tmulBipartitionEquiv` : Variant of `tmulUnionEquiv` where the sets are each other's complement.
* `tmulDiffEquiv` : Variant of `tmulUnionEquiv` where the two are given as `S` and `T \ S`
  for some `T : Set ι`
* `tmulInsertEquiv` : for `i₀ ∉ S`, the equivalence between the tensor product of `M i₀` with the
  `PiTensorProduct` indexed by `S`, and the `PiTensorProduct` indexed by `insert i₀ S`.

* `extendLinear` : Extends a linear map on the `PiTensorProduct` indexed by a set `S` to a linear
  map on the `PiTensorProduct` indexed by a superset `T`, by taking the tensor product with the
  identity map on `T \ S`.
* `extendTensor` : Given a family `m₀` of vectors, extend an element of the `PiTensorProduct`
  indexed by a set `S` to an element of the `PiTensorProduct` indexed by a superset `T`, by taking
  tensor products with vectors provided by `m₀` on `T \ S`.

## TODO

* Injectivity lemmas: Give sufficient conditions under which `extendLinear`, `extendEnd`,
  `extendFunctional`, and `extendTensor` are injective.
* We currently treat only pairs of subsets of the index type. The generalization
  to finite collections is PR #32609.

-/

open PiTensorProduct
open scoped TensorProduct

@[expose] public section

namespace PiTensorProduct

variable {ι : Type*} {R : Type*} {M : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

open Set

/-- The tensor product of a family of modules indexed by `ι` is isomorphic
to the tensor product of the same family indexed by `univ : Set ι`. -/
def univEquiv : (⨂[R] i, M i) ≃ₗ[R] ⨂[R] i : ↥univ, M i.val := reindex R M (Equiv.Set.univ ι).symm

@[simp]
theorem univEquiv_tprod (f : (i : ι) → M i) : univEquiv (⨂ₜ[R] i, f i) = ⨂ₜ[R] i : ↥univ, f i.val :=
  reindex_tprod (Equiv.Set.univ ι).symm f

theorem univEquiv_symm_tprod (f : (i : univ) → M i.val) :
    univEquiv.symm (⨂ₜ[R] i : ↥univ, f i) = (⨂ₜ[R] i, f ⟨i, by simp⟩) := by
  simp [LinearEquiv.symm_apply_eq]

/-- The tensor product of a family `M` of modules indexed by a singleton set `{i₀}` is isomorphic
to `M i₀` -/
def singletonSetEquiv (i₀ : ι) : (⨂[R] i : ({i₀} : Set ι), M i) ≃ₗ[R] M i₀ :=
  subsingletonEquiv (⟨i₀, by simp⟩ : ({i₀} : Set ι))

@[simp]
theorem singletonEquiv_tprod (i₀ : ι) (f : (i : ({i₀} : Set ι)) → M i) :
    singletonSetEquiv i₀ (⨂ₜ[R] i, f i) = f ⟨i₀, by simp⟩ := by simp [singletonSetEquiv]

@[simp]
theorem singletonEquiv_symm_tprod (i₀ : ι) (x : M i₀) :
    (singletonSetEquiv i₀).symm x = (⨂ₜ[R] i : ({i₀} : Set ι), cast (by grind) x) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod, cast_eq]

section tmulUnionEquiv

variable {S₁ S₂ : Set ι} (H : Disjoint S₁ S₂) [(i : ι) → Decidable (i ∈ S₁)]

/-- Consider a family of modules indexed by `ι`, and disjoint sets `S₁, S₂ : Set ι`.
`tmulUnionEquiv` is the equivalence between the binary tensor product of
`PiTensorProduct`s indexed by `S₁` and `S₂`, and the `PiTensorProduct` indexed
by `S₁ ∪ S₂`. -/
def tmulUnionEquiv :
    ((⨂[R] (i₁ : S₁), M i₁) ⊗[R] (⨂[R] (i₂ : S₂), M i₂)) ≃ₗ[R] ⨂[R] (i : ↥(S₁ ∪ S₂)), M i :=
  (tmulEquivDep R (fun i ↦ M ((Equiv.Set.union H).symm i))) ≪≫ₗ
  (reindex R (fun i : ↥(S₁ ∪ S₂) ↦ M i) (Equiv.Set.union H)).symm

@[simp]
theorem tmulUnionEquiv_symm_tprod (f : (i : ↥(S₁ ∪ S₂)) → M i) :
    (tmulUnionEquiv H).symm (⨂ₜ[R] i, f i) =
      (⨂ₜ[R] i : S₁, f ⟨i, by grind⟩) ⊗ₜ (⨂ₜ[R] i : S₂, f ⟨i, by grind⟩) := by
  simp only [tmulUnionEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, reindex_tprod]
  apply tmulEquivDep_symm_apply

@[simp]
theorem tmulUnionEquiv_tprod (lv : (i : S₁) → M i) (rv : (i : S₂) → M i) :
    (tmulUnionEquiv H) ((⨂ₜ[R] i : S₁, lv i) ⊗ₜ (⨂ₜ[R] i : S₂, rv i)) =
      ⨂ₜ[R] j : ↥(S₁ ∪ S₂), if h : ↑j ∈ S₁ then lv ⟨j, h⟩ else rv ⟨j, by grind⟩ := by
  rw [←LinearEquiv.eq_symm_apply, tmulUnionEquiv_symm_tprod]
  congr with i
  · simp
  · simp [disjoint_right.mp H i.property]

end tmulUnionEquiv


section tmulBipartitionEquiv

variable {S T : Set ι} (hST : IsCompl S T) [(i : ι) → Decidable (i ∈ S)]

/-- Consider a family of modules indexed by `ι` and a set `S : Set ι`.
`tmulBipartitionEquiv` is the equivalence between the binary tensor product of
`PiTensorProduct`s indexed by `S` and its complement `T = Sᶜ`, and the
`PiTensorProduct` indexed by `ι`. -/
def tmulBipartitionEquiv :
    (⨂[R] i₁ : S, M i₁) ⊗[R] (⨂[R] i₂ : T, M i₂) ≃ₗ[R] ⨂[R] i, M i :=
  tmulUnionEquiv hST.disjoint ≪≫ₗ
    (reindex _ _ ((Equiv.subtypeEquivProp hST.sup_eq_top).trans (Equiv.Set.univ _)))

@[simp]
theorem tmulBipartitionEquiv_tprod (lv : (i : S) → M i) (rv : (i : T) → M i) :
    tmulBipartitionEquiv hST ((⨂ₜ[R] i : S, lv i) ⊗ₜ (⨂ₜ[R] i : T, rv i)) =
    ⨂ₜ[R] j, if h : j ∈ S then lv ⟨j, h⟩ else rv ⟨j, by aesop (add safe forward hST.compl_eq)⟩ := by
  rw [tmulBipartitionEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulBipartition_symm_tprod (f : (i : ι) → M i) :
    (tmulBipartitionEquiv hST).symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i : S, f i) ⊗ₜ (⨂ₜ[R] i : T, f i) := by
  simp [LinearEquiv.symm_apply_eq]

end tmulBipartitionEquiv


section tmulDiffEquiv

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

/-- Consider a family of modules indexed by `ι` and sets `S ⊆ T` of type `Set ι`.
`tmulDiffEquiv` is the equivalence between the binary tensor product of
`PiTensorProduct`s indexed by `S` and `T \ S`, and the `PiTensorProduct`
indexed by `T`. -/
def tmulDiffEquiv :
    (⨂[R] i₁ : S, M i₁) ⊗[R] (⨂[R] i₂ : ↥(T \ S), M i₂) ≃ₗ[R] ⨂[R] i : T, M i :=
  (tmulUnionEquiv (disjoint_sdiff_right)) ≪≫ₗ
    (reindex R (fun i : ↥(S ∪ T \ S) ↦ M i) (Equiv.subtypeEquivProp (union_diff_cancel hsub)))

@[simp]
theorem tmulDiffEquiv_tprod (lv : (i : S) → M i) (rv : (i : ↑(T \ S)) → M i) :
    tmulDiffEquiv hsub ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i, rv i)) =
      ⨂ₜ[R] i : T, if h : ↑i ∈ S then lv ⟨i, by grind⟩ else rv ⟨i, by grind⟩ := by
  rw [tmulDiffEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulDiffEquiv_tprod_symm (av : (i : T) → M i) :
    (tmulDiffEquiv hsub).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : S, av ⟨i, by grind⟩) ⊗ₜ (⨂ₜ[R] i : ↥(T \ S), av ⟨i, by grind⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulDiffEquiv_tprod]
  grind

end tmulDiffEquiv

section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

/-- Consider a family of modules indexed by `ι`, a set `S : Set ι`, and an element `i₀ ∉ S`.
`tmulInsertEquiv` is the equivalence between the binary tensor product of
`M i₀` with the `PiTensorProduct` indexed by `S`, and the `PiTensorProduct`
indexed by `insert i₀ S`. -/
def tmulInsertEquiv :
    ((M i₀) ⊗[R] (⨂[R] i₁ : S, M i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), M i₁) :=
  (TensorProduct.congr (singletonSetEquiv i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_left.mpr h₀))

@[simp]
theorem tmulInsertEquiv_tprod (x : M i₀) (f : (i : S) → M i) :
    (tmulInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ S),
      if h : i = i₀ then cast (by grind) x else f ⟨i, by grind⟩ := by
  rw [tmulInsertEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, singletonEquiv_symm_tprod]
  apply tmulUnionEquiv_tprod

@[simp]
theorem tmulInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ S)) → M i) :
    (tmulInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : S, f ⟨i, by simp⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulInsertEquiv_tprod]
  grind

end tmulInsertEquiv


section Extensions

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

variable (R)

section LinearMap

open Module

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- Consider a family of modules indexed by `ι`, sets `S ⊆ T` of type `Set ι` and a module `N`.
A linear map from the `PiTensorProduct` indexed by `S` to `N` can be extended to a linear map from
the `PiTensorProduct` indexed by `T` to the tensor product of `N` with the `PiTensorProduct` indexed
by `T \ S`. Bundled as a homomorphism of linear maps. -/
def extendLinear : ((⨂[R] i : S, M i) →ₗ[R] N) →ₗ[R]
    (⨂[R] i : T, M i) →ₗ[R] (N ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), M i₂)) :=
  let TmS := ⨂[R] (i : ↑(T \ S)), M i
  ((tmulDiffEquiv hsub).congrLeft (M:=N ⊗[R] TmS) R).toLinearMap ∘ₗ LinearMap.rTensorHom TmS

/-- Consider a family of modules indexed by `ι` and sets `S ⊆ T` of type `Set ι`.
An endomorphism of the `PiTensorProduct` indexed by `S` can be extended to an endomorphism of the
`PiTensorProduct` indexed by `T`, by taking the tensor product with the identity map on `T \ S`.
Bundled as a homomorphism of linear maps. -/
def extendEnd : End R (⨂[R] i : S, M i) →ₗ[R] End R (⨂[R] i : T, M i) :=
  (tmulDiffEquiv hsub).congrRight.toLinearMap ∘ₗ extendLinear R hsub

/-- Consider a family of modules indexed by `ι` and sets `S ⊆ T` of type `Set ι`.
A linear functional on the `PiTensorProduct` indexed by `S` can be extended to a linear map from
the `PiTensorProduct` indexed by `T` to the `PiTensorProduct` indexed by `T \ S`.
Bundled as a homomorphism of linear maps. -/
def extendFunctional :
    ((⨂[R] i : S, M i) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, M i) →ₗ[R] ⨂[R] (i₂ : ↑(T \ S)), M i₂ :=
  (TensorProduct.lid R _).congrRight.toLinearMap ∘ₗ (extendLinear R hsub)

@[simp]
theorem extendLinear_tprod (l : (⨂[R] i : S, M i) →ₗ[R] N) (f : (i : T) → M i) :
    extendLinear R hsub l (⨂ₜ[R] i, f i)
    = l (⨂ₜ[R] i₁ : S, f ⟨i₁, by grind⟩) ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by grind⟩) := by
  simp [extendLinear, LinearEquiv.congrLeft]

@[simp]
theorem extendEnd_tprod (l : End _ (⨂[R] i : S, M i)) (f : (i : T) → M i) :
    extendEnd R hsub l (⨂ₜ[R] i, f i)
    = (tmulDiffEquiv hsub) (l (⨂ₜ[R] i₁ : S, f ⟨i₁, by grind⟩)
      ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by grind⟩)) := by
  simp [extendEnd, LinearEquiv.congrRight]

@[simp]
theorem extendFunctional_tprod (l : (⨂[R] i : S, M i) →ₗ[R] R) (f : (i : T) → M i) :
    extendFunctional R hsub l (⨂ₜ[R] i, f i)
    = (l (⨂ₜ[R] i : S, f ⟨i, by grind⟩)) • ⨂ₜ[R] i : ↑(T \ S), f ⟨i, by grind⟩ := by
  simp [extendFunctional, LinearEquiv.congrRight]

end LinearMap

section ExtendTensor

variable {m₀ : (i : ι) → M i}

/-- Consider a family of modules indexed by `ι`, a family of distinguished elements
`m₀ : (i : ι) → M i`, and sets `S ⊆ T`. An element of the `PiTensorProduct` indexed by `S`
can be extended to the `PiTensorProduct` indexed by `T` by taking tensor products with the
vectors `m₀ i` for `i : T \ S`. -/
def extendTensor (m₀ : (i : ι) → M i) : (⨂[R] (i : S), M i) →ₗ[R] ⨂[R] (i : T), M i where
  toFun t := (tmulDiffEquiv hsub) (t ⊗ₜ[R] (⨂ₜ[R] i : ↥(T \ S), m₀ i))
  map_add' := by simp [TensorProduct.add_tmul]
  map_smul' := by simp [←TensorProduct.smul_tmul']

@[simp]
lemma extendTensor_tprod (f : (i : S) → M i) : extendTensor R hsub m₀ (⨂ₜ[R] i, f i)
    = ⨂ₜ[R] i : T, if h : ↑i ∈ S then f ⟨i, by grind⟩ else m₀ i := by
  simp [extendTensor]

@[simp]
theorem extendTensor_self : extendTensor R (subset_refl S) m₀ = LinearMap.id (R:=R) :=
  by ext; simp [extendTensor]

/-- Extending the index set of a tensor along a chain `S ⊆ T ⊆ U` is the same as
directly extending from `S` to `U`. -/
@[simp]
theorem extendTensor_trans [(i : ι) → Decidable (i ∈ T)] {U : Set ι} (hsub₂ : T ⊆ U) :
    (extendTensor R hsub₂ m₀) ∘ₗ (extendTensor R hsub m₀) =
    (extendTensor R (subset_trans hsub hsub₂) m₀) := by
  ext f
  simp only [extendTensor, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, tmulDiffEquiv_tprod]
  grind

end ExtendTensor

end Extensions

end PiTensorProduct
