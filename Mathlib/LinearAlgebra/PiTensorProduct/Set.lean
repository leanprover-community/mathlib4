/-
Copyright (c) 2025 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.PiTensorProduct

/-!
# PiTensorProducts indexed by sets

Given a family of modules `s : ι → Type*`, we consider tensors of type `⨂ (i : S), s i`,
where `S : Set ι`.

## Main definitions

* Equivalences for `PiTensorproduct`s over sets:

Definition...           ...pertains to
`univEquiv`             `univ : Set ι`
`singletonEquiv`        `{i₀}`

* Equivalences relating binary tensor products to union of sets:

Definition...           ...pertains to
`tmulUnionEquiv`        `S₁ ∪ S₂`
`tmulBipartitionEquiv`  `S ∪ Sᶜ`
`tmulUnifyEquiv`        `S ∪ (T \ S)`
`tmulInsertEquiv`       `{i₀} ∪ S`

* Given sets `S ⊆ T`, linear functions defined on tensors indexed by `S` can be
extended to tensors indexed by `T`, by acting trivially on `T \ S`:

Definition...           ...pertains to
`extendLinear`          `⨂ S → M`
`extendEnd`             `⨂ S → ⨂ S`
`extendFunctional`      `⨂ S → R`

* `extendTensor`: Given a family of distinguished elements `s₀ : (i : ι) → s i`,
a tensor with index set `S` can be extended to a tensor with index set `T`, by
padding with the vectors provided by `s₀` on `T \ S`.

## TODO

* Injectivity lemmas for the extensions. These are easy for vector spaces, but
can become quite subtle for `AddCommMonoid`s.
-/

open PiTensorProduct
open scoped TensorProduct

@[expose] public section

namespace PiTensorProduct

variable {ι : Type*} {R : Type*} {s : ι → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

open Set

/-- Tensors indexed by `ι` are isomorphic to tensors indexed by `univ : Set ι`. -/
def univEquiv : (⨂[R] i, s i) ≃ₗ[R] ⨂[R] i : ↥univ, s i.val := reindex R s (Equiv.Set.univ ι).symm

@[simp]
theorem univEquiv_tprod (f : (i : ι) → s i) : univEquiv (⨂ₜ[R] i, f i) = ⨂ₜ[R] i : ↥univ, f i.val :=
  reindex_tprod (Equiv.Set.univ ι).symm f

@[simp]
theorem univEquiv_symm_tprod (f : (i : ι) → s i) :
    univEquiv.symm (⨂ₜ[R] i : ↥univ, f i) = (⨂ₜ[R] i, f i) := by simp [LinearEquiv.symm_apply_eq]

/-- Tensors indexed by a singleton set `{i₀}` are equivalent to vectors in `s i₀`. -/
def singletonSetEquiv (i₀ : ι) : (⨂[R] i : ({i₀} : Set ι), s i) ≃ₗ[R] s i₀ :=
  subsingletonEquivDep (⟨i₀, by simp⟩ : ({i₀} : Set ι))

@[simp]
theorem singletonEquiv_tprod (i₀ : ι) (f : (i : ({i₀} : Set ι)) → s i) :
    singletonSetEquiv i₀ (⨂ₜ[R] i, f i) = f ⟨i₀, by simp⟩ := by simp [singletonSetEquiv]

@[simp]
theorem singletonEquiv_symm_tprod (i₀ : ι) (x : s i₀) :
    (singletonSetEquiv i₀).symm x = (⨂ₜ[R] i : ({i₀} : Set ι), cast (by grind) x) := by
  rw [LinearEquiv.symm_apply_eq, singletonEquiv_tprod, cast_eq]

section tmulUnionEquiv

variable {S₁ S₂ : Set ι} (H : Disjoint S₁ S₂) [(i : ι) → Decidable (i ∈ S₁)]

/-- Tensors indexed by a set `S₁` times tensors indexed by a disjoint set `S₂`
are isomorphic to tensors indexed by the union `S₁ ∪ S₂`. -/
def tmulUnionEquiv :
    ((⨂[R] (i₁ : S₁), s i₁) ⊗[R] (⨂[R] (i₂ : S₂), s i₂)) ≃ₗ[R] ⨂[R] (i : ↥(S₁ ∪ S₂)), s i :=
  (tmulEquivDep R (fun i ↦ s ((Equiv.Set.union H).symm i))) ≪≫ₗ
  (reindex R (fun i : ↥(S₁ ∪ S₂) ↦ s i) (Equiv.Set.union H)).symm

@[simp]
theorem tmulUnionEquiv_symm_tprod (f : (i : ↥(S₁ ∪ S₂)) → s i) :
    (tmulUnionEquiv H).symm (⨂ₜ[R] i, f i) =
      (⨂ₜ[R] i : S₁, f ⟨i, by grind⟩) ⊗ₜ (⨂ₜ[R] i : S₂, f ⟨i, by grind⟩) := by
  simp only [tmulUnionEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
      LinearEquiv.trans_apply, reindex_tprod]
  apply tmulEquivDep_symm_apply

@[simp]
theorem tmulUnionEquiv_tprod (lv : (i : S₁) → s i) (rv : (i : S₂) → s i) :
    (tmulUnionEquiv H) ((⨂ₜ[R] i : S₁, lv i) ⊗ₜ (⨂ₜ[R] i : S₂, rv i)) =
      ⨂ₜ[R] j : ↥(S₁ ∪ S₂), if h : ↑j ∈ S₁ then lv ⟨j, h⟩ else rv ⟨j, by grind⟩ := by
  rw [←LinearEquiv.eq_symm_apply, tmulUnionEquiv_symm_tprod]
  congr with i
  · simp
  · simp [disjoint_right.mp H i.property]

end tmulUnionEquiv


section tmulBipartitionEquiv

variable {S : Set ι} [(i : ι) → Decidable (i ∈ S)]

/-- Tensors indexed by a set `S` times tensors indexed by its complement `Sᶜ`
are isomorphic to the space of all tensors. -/
def tmulBipartitionEquiv : (⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥Sᶜ, s i₂) ≃ₗ[R] ⨂[R] i, s i :=
  (tmulUnionEquiv (disjoint_compl_right)) ≪≫ₗ (reindex R (fun i : ↥(S ∪ Sᶜ) ↦ s i)
    (Equiv.trans (Equiv.subtypeEquivProp (Set.union_compl_self S)) (Equiv.Set.univ ι)))

@[simp]
theorem tmulBipartitionEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↥Sᶜ) → s i) :
    tmulBipartitionEquiv ((⨂ₜ[R] i : S, lv i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, rv i)) =
      ⨂ₜ[R] j, if h : j ∈ S then lv ⟨j, h⟩ else rv ⟨j, by grind⟩ := by
  rw [tmulBipartitionEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulBipartition_symm_tprod (f : (i : ι) → s i) :
    tmulBipartitionEquiv.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i : S, f i) ⊗ₜ (⨂ₜ[R] i : ↥Sᶜ, f i) := by
  simp [LinearEquiv.symm_apply_eq]

end tmulBipartitionEquiv


section tmulUnifyEquiv

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

/-- For sets `S ⊆ T`, tensors indexed by `S` times tensors indexed by `T \ S`
are isomorphic to tensors indexed by `T`. -/
def tmulUnifyEquiv :
    (⨂[R] i₁ : S, s i₁) ⊗[R] (⨂[R] i₂ : ↥(T \ S), s i₂) ≃ₗ[R] ⨂[R] i : T, s i :=
  (tmulUnionEquiv (disjoint_sdiff_right)) ≪≫ₗ
    (reindex R (fun i : ↥(S ∪ T \ S) ↦ s i) (Equiv.subtypeEquivProp (union_diff_cancel hsub)))

@[simp]
theorem tmulUnifyEquiv_tprod (lv : (i : S) → s i) (rv : (i : ↑(T \ S)) → s i) :
    tmulUnifyEquiv hsub ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i, rv i)) =
      ⨂ₜ[R] i : T, if h : ↑i ∈ S then lv ⟨i, by grind⟩ else rv ⟨i, by grind⟩ := by
  rw [tmulUnifyEquiv, LinearEquiv.trans_apply, tmulUnionEquiv_tprod]
  apply reindex_tprod

@[simp]
theorem tmulUnifyEquiv_tprod_symm (av : (i : T) → s i) :
    (tmulUnifyEquiv hsub).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : S, av ⟨i, by grind⟩) ⊗ₜ (⨂ₜ[R] i : ↥(T \ S), av ⟨i, by grind⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulUnifyEquiv_tprod]
  grind

end tmulUnifyEquiv

section tmulInsertEquiv

variable {S : Set ι} {i₀} (h₀ : i₀ ∉ S)
variable [DecidableEq ι]

/-- Vectors in `s i₀` times tensors indexed by `S` are equivalent to tensors
indexed by `insert i₀ S`, assuming `i₀ ∉ S`. -/
def tmulInsertEquiv :
    ((s i₀) ⊗[R] (⨂[R] i₁ : S, s i₁)) ≃ₗ[R] (⨂[R] i₁ : ↥(insert i₀ S), s i₁) :=
  (TensorProduct.congr (singletonSetEquiv i₀).symm (LinearEquiv.refl _ _)) ≪≫ₗ
  (tmulUnionEquiv (Set.disjoint_singleton_left.mpr h₀))

@[simp]
theorem tmulInsertEquiv_tprod (x : s i₀) (f : (i : S) → s i) :
    (tmulInsertEquiv h₀) (x ⊗ₜ[R] (⨂ₜ[R] i, f i)) = ⨂ₜ[R] i : ↥(insert i₀ S),
      if h : i.val ∈ ({i₀} : Set ι) then cast (by grind) x else f ⟨i, by grind⟩ := by
  rw [tmulInsertEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, singletonEquiv_symm_tprod]
  apply tmulUnionEquiv_tprod

@[simp]
theorem tmulInsertEquiv_symm_tprod (f : (i : ↥(insert i₀ S)) → s i) :
    (tmulInsertEquiv h₀).symm (⨂ₜ[R] i, f i) =
    (f ⟨i₀, by simp⟩) ⊗ₜ[R](⨂ₜ[R] i : S, f ⟨i, by simp⟩) := by
  rw [LinearEquiv.symm_apply_eq, tmulInsertEquiv_tprod]
  grind

end tmulInsertEquiv

section Perm

variable {S : Set ι}
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (e : Equiv.Perm ι)

/-- An equivalence `e : Equiv.Perm ι` maps tensors indexed by a set `S` to
tensors indexed by `e '' S`. -/
def permSetEquiv : (⨂[R] _ : S, M) ≃ₗ[R] ⨂[R] _ : (e '' S), M :=
  reindex R (fun _ ↦ M) (Equiv.image e S)

@[simp]
theorem permSetEquiv_tprod (f : S → M) :
  (permSetEquiv e) (⨂ₜ[R] i, f i) = ⨂ₜ[R] i, f ((Equiv.image e S).symm i) := by simp [permSetEquiv]

@[simp]
theorem permSetEquiv_symm_tprod (f : (e '' S) → M) :
  (permSetEquiv e).symm (⨂ₜ[R] i, f i) = ⨂ₜ[R] i, f ((Equiv.image e S) i) := by simp [permSetEquiv]

end Perm

section Extensions

variable {S T : Set ι} (hsub : S ⊆ T) [(i : ι) → Decidable (i ∈ S)]

section LinearMap

open Module

variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- A linear map on tensors with index set `S ⊆ T` extends to a linear map
on tensors with index set `T`. Bundled as a homomorphism of linear maps. -/
def extendLinearHom : ((⨂[R] i : S, s i) →ₗ[R] M) →ₗ[R]
    (⨂[R] i : T, s i) →ₗ[R] (M ⊗[R] (⨂[R] (i₂ : ↑(T \ S)), s i₂)) :=
  let TmS := ⨂[R] (i : ↑(T \ S)), s i
  ((tmulUnifyEquiv hsub).congrLeft (M:=M ⊗[R] TmS) R).toLinearMap ∘ₗ LinearMap.rTensorHom TmS

/-- An endomorphism on tensors with index set `S ⊆ T` extends to an endomorphism
on tensors with index set `T`. Bundled as a homomorphism of linear maps. -/
def extendEnd : End R (⨂[R] i : S, s i) →ₗ[R] End R (⨂[R] i : T, s i) :=
  (tmulUnifyEquiv hsub).congrRight.toLinearMap ∘ₗ extendLinearHom hsub

/-- A functional on tensors with index set `S ⊆ T` contracts tensors with index
set `T` to tensors with index set `T \ S`. Bundled as a linear map. -/
def extendFunctional :
    ((⨂[R] i : S, s i) →ₗ[R] R) →ₗ[R] (⨂[R] i : T, s i) →ₗ[R] ⨂[R] (i₂ : ↑(T \ S)), s i₂ :=
  (TensorProduct.lid R _).congrRight.toLinearMap ∘ₗ (extendLinearHom hsub)

@[simp]
theorem extendLinear_tprod (l : (⨂[R] i : S, s i) →ₗ[R] M) (f : (i : T) → s i) :
    extendLinearHom hsub l (⨂ₜ[R] i, f i)
    = l (⨂ₜ[R] i₁ : S, f ⟨i₁, by grind⟩) ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by grind⟩) := by
  simp [extendLinearHom, LinearEquiv.congrLeft]

@[simp]
theorem extendEnd_tprod (l : End _ (⨂[R] i : S, s i)) (f : (i : T) → s i) :
    extendEnd hsub l (⨂ₜ[R] i, f i)
    = (tmulUnifyEquiv hsub) (l (⨂ₜ[R] i₁ : S, f ⟨i₁, by grind⟩)
      ⊗ₜ[R] (⨂ₜ[R] i₂ : ↑(T \ S), f ⟨i₂, by grind⟩)) := by
  simp [extendEnd, LinearEquiv.congrRight]

@[simp]
theorem extendFunctional_tprod (l : (⨂[R] i : S, s i) →ₗ[R] R) (f : (i : T) → s i) :
    extendFunctional hsub l (⨂ₜ[R] i, f i)
    = (l (⨂ₜ[R] i : S, f ⟨i, by grind⟩)) • ⨂ₜ[R] i : ↑(T \ S), f ⟨i, by grind⟩ := by
  simp [extendFunctional, LinearEquiv.congrRight]

end LinearMap

section ExtendTensor

variable {s₀ : (i : ι) → s i}

/-- Given a family of distinguished elements `s₀ : (i : ι) → s i` and sets `S ⊆ T`,
map a tensor with index set `S` to a tensor with index set `T`, by padding with vectors
provided by `s₀` on `T \ S`. -/
def extendTensor (s₀ : (i : ι) → s i) : (⨂[R] (i : S), s i) →ₗ[R] ⨂[R] (i : T), s i where
  toFun t := (tmulUnifyEquiv hsub) (t ⊗ₜ[R] (⨂ₜ[R] i : ↥(T \ S), s₀ i))
  map_add' := by simp [TensorProduct.add_tmul]
  map_smul' := by simp [←TensorProduct.smul_tmul']

@[simp]
theorem extendTensor_self : extendTensor (subset_refl S) s₀ = LinearMap.id (R:=R) :=
  by ext; simp [extendTensor]

/-- Extending the index set of a tensor along a chain `S ⊆ T ⊆ U` is the same as
directly extending from `S` to `U`. -/
@[simp]
theorem extendTensor_trans [(i : ι) → Decidable (i ∈ T)] {U : Set ι} (hsub₂ : T ⊆ U) :
    (extendTensor hsub₂ s₀) ∘ₗ (extendTensor hsub s₀) =
    (extendTensor (R:=R) (subset_trans hsub hsub₂) s₀) := by
  ext f
  simp only [extendTensor, LinearMap.compMultilinearMap_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, tmulUnifyEquiv_tprod]
  grind

end ExtendTensor

end Extensions

end PiTensorProduct
