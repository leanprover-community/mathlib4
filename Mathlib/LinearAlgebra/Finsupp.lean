/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Finsupp.Encodable
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span
import Mathlib.Data.Set.Countable

#align_import linear_algebra.finsupp from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`Data.Finsupp.Basic`.

In this file we define `Finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `LinearMap` versions of various maps:

* `Finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `Finsupp.single a` as a linear map;
* `Finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `fun f ↦ f a` as a linear map;
* `Finsupp.lsubtypeDomain (s : Set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;
* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
* `Finsupp.lsum`: `Finsupp.sum` or `Finsupp.liftAddHom` as a `LinearMap`;
* `Finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;
* `Finsupp.totalOn`: a restricted version of `Finsupp.total` with domain `Finsupp.supported R R s`
  and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.lmapDomain`: a linear map version of `Finsupp.mapDomain`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;
* `Finsupp.lcongr`: a `LinearEquiv`alence between `α →₀ M` and `β →₀ N` constructed using
  `e : α ≃ β` and `e' : M ≃ₗ[R] N`.

## Tags

function with finite support, module, linear algebra
-/


noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section SMul

variable {α : Type*} {β : Type*} {R : Type*} {M : Type*} {M₂ : Type*}

theorem smul_sum [Zero β] [AddCommMonoid M] [DistribSMul R M] {v : α →₀ β} {c : R} {h : α → β → M} :
    c • v.sum h = v.sum fun a b => c • h a b :=
  Finset.smul_sum
#align finsupp.smul_sum Finsupp.smul_sum

@[simp]
theorem sum_smul_index_linearMap' [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]
    [Module R M₂] {v : α →₀ M} {c : R} {h : α → M →ₗ[R] M₂} :
    ((c • v).sum fun a => h a) = c • v.sum fun a => h a := by
  rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
  · simp only [map_smul]
  · intro i
    exact (h i).map_zero
#align finsupp.sum_smul_index_linear_map' Finsupp.sum_smul_index_linearMap'

end SMul

section LinearEquivFunOnFinite

variable (R : Type*) {S : Type*} (M : Type*) (α : Type*)
variable [Finite α] [AddCommMonoid M] [Semiring R] [Module R M]

/-- Given `Finite α`, `linearEquivFunOnFinite R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply]
noncomputable def linearEquivFunOnFinite : (α →₀ M) ≃ₗ[R] α → M :=
  { equivFunOnFinite with
    toFun := (⇑)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv_fun_on_finite Finsupp.linearEquivFunOnFinite

@[simp]
theorem linearEquivFunOnFinite_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α) (single x m) = Pi.single x m :=
  equivFunOnFinite_single x m
#align finsupp.linear_equiv_fun_on_finite_single Finsupp.linearEquivFunOnFinite_single

@[simp]
theorem linearEquivFunOnFinite_symm_single [DecidableEq α] (x : α) (m : M) :
    (linearEquivFunOnFinite R M α).symm (Pi.single x m) = single x m :=
  equivFunOnFinite_symm_single x m
#align finsupp.linear_equiv_fun_on_finite_symm_single Finsupp.linearEquivFunOnFinite_symm_single

@[simp]
theorem linearEquivFunOnFinite_symm_coe (f : α →₀ M) : (linearEquivFunOnFinite R M α).symm f = f :=
  (linearEquivFunOnFinite R M α).symm_apply_apply f
#align finsupp.linear_equiv_fun_on_finite_symm_coe Finsupp.linearEquivFunOnFinite_symm_coe

end LinearEquivFunOnFinite

section LinearEquiv.finsuppUnique

variable (R : Type*) {S : Type*} (M : Type*)
variable [AddCommMonoid M] [Semiring R] [Module R M]
variable (α : Type*) [Unique α]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
noncomputable def LinearEquiv.finsuppUnique : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align finsupp.linear_equiv.finsupp_unique Finsupp.LinearEquiv.finsuppUnique

variable {R M}

@[simp]
theorem LinearEquiv.finsuppUnique_apply (f : α →₀ M) :
    LinearEquiv.finsuppUnique R M α f = f default :=
  rfl
#align finsupp.linear_equiv.finsupp_unique_apply Finsupp.LinearEquiv.finsuppUnique_apply

variable {α}

@[simp]
theorem LinearEquiv.finsuppUnique_symm_apply [Unique α] (m : M) :
    (LinearEquiv.finsuppUnique R M α).symm m = Finsupp.single default m := by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]
#align finsupp.linear_equiv.finsupp_unique_symm_apply Finsupp.LinearEquiv.finsuppUnique_symm_apply

end LinearEquiv.finsuppUnique

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Interpret `Finsupp.single a` as a linear map. -/
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun _ _ => (smul_single _ _ _).symm }
#align finsupp.lsingle Finsupp.lsingle

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
#align finsupp.lhom_ext Finsupp.lhom_ext

/-- Two `R`-linear maps from `Finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
-- Porting note: The priority should be higher than `LinearMap.ext`.
@[ext high]
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)
#align finsupp.lhom_ext' Finsupp.lhom_ext'

/-- Interpret `fun f : α →₀ M ↦ f a` as a linear map. -/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun _ _ => rfl }
#align finsupp.lapply Finsupp.lapply

section CompatibleSMul

variable (R S M N ι : Type*)
variable [Semiring S] [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]

instance _root_.LinearMap.CompatibleSMul.finsupp_dom [SMulZeroClass R M] [DistribSMul R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul (ι →₀ M) N R S where
  map_smul f r m := by
    conv_rhs => rw [← sum_single m, map_finsupp_sum, smul_sum]
    erw [← sum_single (r • m), sum_mapRange_index single_zero, map_finsupp_sum]
    congr; ext i m; exact (f.comp <| lsingle i).map_smul_of_tower r m

instance _root_.LinearMap.CompatibleSMul.finsupp_cod [SMul R M] [SMulZeroClass R N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι →₀ N) R S where
  map_smul f r m := by ext i; apply ((lapply i).comp f).map_smul_of_tower

end CompatibleSMul

/-- Forget that a function is finitely supported.

This is the linear version of `Finsupp.toFun`. -/
@[simps]
def lcoeFun : (α →₀ M) →ₗ[R] α → M where
  toFun := (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
#align finsupp.lcoe_fun Finsupp.lcoeFun

section LSubtypeDomain

variable (s : Set α)

/-- Interpret `Finsupp.subtypeDomain s` as a linear map. -/
def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' _ _ := subtypeDomain_add
  map_smul' _ _ := ext fun _ => rfl
#align finsupp.lsubtype_domain Finsupp.lsubtypeDomain

theorem lsubtypeDomain_apply (f : α →₀ M) :
    (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtypeDomain (fun x => x ∈ s) f :=
  rfl
#align finsupp.lsubtype_domain_apply Finsupp.lsubtypeDomain_apply

end LSubtypeDomain

@[simp]
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl
#align finsupp.lsingle_apply Finsupp.lsingle_apply

@[simp]
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl
#align finsupp.lapply_apply Finsupp.lapply_apply

@[simp]
theorem lapply_comp_lsingle_same (a : α) : lapply a ∘ₗ lsingle a = (.id : M →ₗ[R] M) := by ext; simp

@[simp]
theorem lapply_comp_lsingle_of_ne (a a' : α) (h : a ≠ a') :
    lapply a ∘ₗ lsingle a' = (0 : M →ₗ[R] M) := by ext; simp [h.symm]

@[simp]
theorem ker_lsingle (a : α) : ker (lsingle a : M →ₗ[R] α →₀ M) = ⊥ :=
  ker_eq_bot_of_injective (single_injective a)
#align finsupp.ker_lsingle Finsupp.ker_lsingle

theorem lsingle_range_le_ker_lapply (s t : Set α) (h : Disjoint s t) :
    ⨆ a ∈ s, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M) ≤
      ⨅ a ∈ t, ker (lapply a : (α →₀ M) →ₗ[R] M) := by
  refine iSup_le fun a₁ => iSup_le fun h₁ => range_le_iff_comap.2 ?_
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  intro b _ a₂ h₂
  have : a₁ ≠ a₂ := fun eq => h.le_bot ⟨h₁, eq.symm ▸ h₂⟩
  exact single_eq_of_ne this
#align finsupp.lsingle_range_le_ker_lapply Finsupp.lsingle_range_le_ker_lapply

theorem iInf_ker_lapply_le_bot : ⨅ a, ker (lapply a : (α →₀ M) →ₗ[R] M) ≤ ⊥ := by
  simp only [SetLike.le_def, mem_iInf, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h
#align finsupp.infi_ker_lapply_le_bot Finsupp.iInf_ker_lapply_le_bot

theorem iSup_lsingle_range : ⨆ a, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M) = ⊤ := by
  refine eq_top_iff.2 <| SetLike.le_def.2 fun f _ => ?_
  rw [← sum_single f]
  exact sum_mem fun a _ => Submodule.mem_iSup_of_mem a ⟨_, rfl⟩
#align finsupp.supr_lsingle_range Finsupp.iSup_lsingle_range

theorem disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) :
    Disjoint (⨆ a ∈ s, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M))
      (⨆ a ∈ t, LinearMap.range (lsingle a : M →ₗ[R] α →₀ M)) := by
  -- Porting note: 2 placeholders are added to prevent timeout.
  refine
    (Disjoint.mono
      (lsingle_range_le_ker_lapply s sᶜ ?_)
      (lsingle_range_le_ker_lapply t tᶜ ?_))
      ?_
  · apply disjoint_compl_right
  · apply disjoint_compl_right
  rw [disjoint_iff_inf_le]
  refine le_trans (le_iInf fun i => ?_) iInf_ker_lapply_le_bot
  classical
    by_cases his : i ∈ s
    · by_cases hit : i ∈ t
      · exact (hs.le_bot ⟨his, hit⟩).elim
      exact inf_le_of_right_le (iInf_le_of_le i <| iInf_le _ hit)
    exact inf_le_of_left_le (iInf_le_of_le i <| iInf_le _ his)
#align finsupp.disjoint_lsingle_lsingle Finsupp.disjoint_lsingle_lsingle

theorem span_single_image (s : Set M) (a : α) :
    Submodule.span R (single a '' s) = (Submodule.span R s).map (lsingle a : M →ₗ[R] α →₀ M) := by
  rw [← span_image]; rfl
#align finsupp.span_single_image Finsupp.span_single_image

variable (M R)

/-- `Finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
def supported (s : Set α) : Submodule R (α →₀ M) where
  carrier := { p | ↑p.support ⊆ s }
  add_mem' {p q} hp hq := by
    classical
    refine Subset.trans (Subset.trans (Finset.coe_subset.2 support_add) ?_) (union_subset hp hq)
    rw [Finset.coe_union]
  zero_mem' := by
    simp only [subset_def, Finset.mem_coe, Set.mem_setOf_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  smul_mem' a p hp := Subset.trans (Finset.coe_subset.2 support_smul) hp
#align finsupp.supported Finsupp.supported

variable {M}

theorem mem_supported {s : Set α} (p : α →₀ M) : p ∈ supported M R s ↔ ↑p.support ⊆ s :=
  Iff.rfl
#align finsupp.mem_supported Finsupp.mem_supported

theorem mem_supported' {s : Set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ x ∉ s, p x = 0 := by
  haveI := Classical.decPred fun x : α => x ∈ s; simp [mem_supported, Set.subset_def, not_imp_comm]
#align finsupp.mem_supported' Finsupp.mem_supported'

theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]
#align finsupp.mem_supported_support Finsupp.mem_supported_support

theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)
#align finsupp.single_mem_supported Finsupp.single_mem_supported

theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) := by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
  -- Porting note: Needed to help this convert quite a bit replacing underscores
    convert smul_mem (M := α →₀ R) (x := single i 1) (span R ((fun i => single i 1) '' s)) (l i) ?_
    · simp [span]
    · apply subset_span
      apply Set.mem_image_of_mem _ (hl il)
#align finsupp.supported_eq_span_single Finsupp.supported_eq_span_single

variable (M)

/-- Interpret `Finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrictDom (s : Set α) [DecidablePred (· ∈ s)] : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· ∈ s) l
#align finsupp.restrict_dom Finsupp.restrictDom

variable {M R}

section

@[simp]
theorem restrictDom_apply (s : Set α) (l : α →₀ M) [DecidablePred (· ∈ s)]:
    (restrictDom M R s l : α →₀ M) = Finsupp.filter (· ∈ s) l := rfl
#align finsupp.restrict_dom_apply Finsupp.restrictDom_apply

end

theorem restrictDom_comp_subtype (s : Set α) [DecidablePred (· ∈ s)] :
    (restrictDom M R s).comp (Submodule.subtype _) = LinearMap.id := by
  ext l a
  by_cases h : a ∈ s <;> simp [h]
  exact ((mem_supported' R l.1).1 l.2 a h).symm
#align finsupp.restrict_dom_comp_subtype Finsupp.restrictDom_comp_subtype

theorem range_restrictDom (s : Set α) [DecidablePred (· ∈ s)] :
    LinearMap.range (restrictDom M R s) = ⊤ :=
  range_eq_top.2 <|
    Function.RightInverse.surjective <| LinearMap.congr_fun (restrictDom_comp_subtype s)
#align finsupp.range_restrict_dom Finsupp.range_restrictDom

theorem supported_mono {s t : Set α} (st : s ⊆ t) : supported M R s ≤ supported M R t := fun _ h =>
  Set.Subset.trans h st
#align finsupp.supported_mono Finsupp.supported_mono

@[simp]
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
  eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 <| by ext; simp_all [mem_supported']
#align finsupp.supported_empty Finsupp.supported_empty

@[simp]
theorem supported_univ : supported M R (Set.univ : Set α) = ⊤ :=
  eq_top_iff.2 fun _ _ => Set.subset_univ _
#align finsupp.supported_univ Finsupp.supported_univ

theorem supported_iUnion {δ : Type*} (s : δ → Set α) :
    supported M R (⋃ i, s i) = ⨆ i, supported M R (s i) := by
  refine le_antisymm ?_ (iSup_le fun i => supported_mono <| Set.subset_iUnion _ _)
  haveI := Classical.decPred fun x => x ∈ ⋃ i, s i
  suffices
    LinearMap.range ((Submodule.subtype _).comp (restrictDom M R (⋃ i, s i))) ≤
      ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_restrictDom, Submodule.map_top, range_subtype] at this
  rw [range_le_iff_comap, eq_top_iff]
  rintro l ⟨⟩
  -- Porting note: Was ported as `induction l using Finsupp.induction`
  refine Finsupp.induction l ?_ ?_
  · exact zero_mem _
  · refine fun x a l _ _ => add_mem ?_
    by_cases h : ∃ i, x ∈ s i <;> simp [h]
    cases' h with i hi
    exact le_iSup (fun i => supported M R (s i)) i (single_mem_supported R _ hi)
#align finsupp.supported_Union Finsupp.supported_iUnion

theorem supported_union (s t : Set α) :
    supported M R (s ∪ t) = supported M R s ⊔ supported M R t := by
  erw [Set.union_eq_iUnion, supported_iUnion, iSup_bool_eq]; rfl
#align finsupp.supported_union Finsupp.supported_union

theorem supported_iInter {ι : Type*} (s : ι → Set α) :
    supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
  Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]
#align finsupp.supported_Inter Finsupp.supported_iInter

theorem supported_inter (s t : Set α) :
    supported M R (s ∩ t) = supported M R s ⊓ supported M R t := by
  rw [Set.inter_eq_iInter, supported_iInter, iInf_bool_eq]; rfl
#align finsupp.supported_inter Finsupp.supported_inter

theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) :
    Disjoint (supported M R s) (supported M R t) :=
  disjoint_iff.2 <| by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]
#align finsupp.disjoint_supported_supported Finsupp.disjoint_supported_supported

theorem disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Disjoint (supported M R s) (supported M R t) ↔ Disjoint s t := by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot, single_eq_zero] at this
  exact hy this
#align finsupp.disjoint_supported_supported_iff Finsupp.disjoint_supported_supported_iff

/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s →₀ M := by
  let F : supported M R s ≃ (s →₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s → ↥s →₀ M) =
      (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _
#align finsupp.supported_equiv_finsupp Finsupp.supportedEquivFinsupp

section LSum

variable (S)
variable [Module S N] [SMulCommClass R S N]

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `Finsupp.sum`. This is an upgraded version of `Finsupp.liftAddHom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
def lsum : (α → M →ₗ[R] N) ≃ₗ[S] (α →₀ M) →ₗ[R] N where
  toFun F :=
    { toFun := fun d => d.sum fun i => F i
      map_add' := (liftAddHom (α := α) (M := M) (N := N) fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext x y
    simp
  right_inv F := by
    ext x y
    simp
  map_add' F G := by
    ext x y
    simp
  map_smul' F G := by
    ext x y
    simp
#align finsupp.lsum Finsupp.lsum

@[simp]
theorem coe_lsum (f : α → M →ₗ[R] N) : (lsum S f : (α →₀ M) → N) = fun d => d.sum fun i => f i :=
  rfl
#align finsupp.coe_lsum Finsupp.coe_lsum

theorem lsum_apply (f : α → M →ₗ[R] N) (l : α →₀ M) : Finsupp.lsum S f l = l.sum fun b => f b :=
  rfl
#align finsupp.lsum_apply Finsupp.lsum_apply

theorem lsum_single (f : α → M →ₗ[R] N) (i : α) (m : M) :
    Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero
#align finsupp.lsum_single Finsupp.lsum_single

@[simp] theorem lsum_comp_lsingle (f : α → M →ₗ[R] N) (i : α) :
    Finsupp.lsum S f ∘ₗ lsingle i = f i := by ext; simp

theorem lsum_symm_apply (f : (α →₀ M) →ₗ[R] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl
#align finsupp.lsum_symm_apply Finsupp.lsum_symm_apply

end LSum

section

variable (M) (R) (X : Type*) (S)
variable [Module S M] [SMulCommClass R S M]

/-- A slight rearrangement from `lsum` gives us
the bijection underlying the free-forgetful adjunction for R-modules.
-/
noncomputable def lift : (X → M) ≃+ ((X →₀ R) →ₗ[R] M) :=
  (AddEquiv.arrowCongr (Equiv.refl X) (ringLmapEquivSelf R ℕ M).toAddEquiv.symm).trans
    (lsum _ : _ ≃ₗ[ℕ] _).toAddEquiv
#align finsupp.lift Finsupp.lift

@[simp]
theorem lift_symm_apply (f) (x) : ((lift M R X).symm f) x = f (single x 1) :=
  rfl
#align finsupp.lift_symm_apply Finsupp.lift_symm_apply

@[simp]
theorem lift_apply (f) (g) : ((lift M R X) f) g = g.sum fun x r => r • f x :=
  rfl
#align finsupp.lift_apply Finsupp.lift_apply

/-- Given compatible `S` and `R`-module structures on `M` and a type `X`, the set of functions
`X → M` is `S`-linearly equivalent to the `R`-linear maps from the free `R`-module
on `X` to `M`. -/
noncomputable def llift : (X → M) ≃ₗ[S] (X →₀ R) →ₗ[R] M :=
  { lift M R X with
    map_smul' := by
      intros
      dsimp
      ext
      simp only [coe_comp, Function.comp_apply, lsingle_apply, lift_apply, Pi.smul_apply,
        sum_single_index, zero_smul, one_smul, LinearMap.smul_apply] }
#align finsupp.llift Finsupp.llift

@[simp]
theorem llift_apply (f : X → M) (x : X →₀ R) : llift M R S X f x = lift M R X f x :=
  rfl
#align finsupp.llift_apply Finsupp.llift_apply

@[simp]
theorem llift_symm_apply (f : (X →₀ R) →ₗ[R] M) (x : X) :
    (llift M R S X).symm f x = f (single x 1) :=
  rfl
#align finsupp.llift_symm_apply Finsupp.llift_symm_apply

end

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

/-- Interpret `Finsupp.mapDomain` as a linear map. -/
def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M where
  toFun := mapDomain f
  map_add' _ _ := mapDomain_add
  map_smul' := mapDomain_smul
#align finsupp.lmap_domain Finsupp.lmapDomain

@[simp]
theorem lmapDomain_apply (f : α → α') (l : α →₀ M) :
    (lmapDomain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = mapDomain f l :=
  rfl
#align finsupp.lmap_domain_apply Finsupp.lmapDomain_apply

@[simp]
theorem lmapDomain_id : (lmapDomain M R _root_.id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext fun _ => mapDomain_id
#align finsupp.lmap_domain_id Finsupp.lmapDomain_id

theorem lmapDomain_comp (f : α → α') (g : α' → α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun _ => mapDomain_comp
#align finsupp.lmap_domain_comp Finsupp.lmapDomain_comp

theorem supported_comap_lmapDomain (f : α → α') (s : Set α') :
    supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmapDomain M R f) := by
  classical
  intro l (hl : (l.support : Set α) ⊆ f ⁻¹' s)
  show ↑(mapDomain f l).support ⊆ s
  rw [← Set.image_subset_iff, ← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl
#align finsupp.supported_comap_lmap_domain Finsupp.supported_comap_lmapDomain

theorem lmapDomain_supported (f : α → α') (s : Set α) :
    (supported M R s).map (lmapDomain M R f) = supported M R (f '' s) := by
  classical
  cases isEmpty_or_nonempty α
  · simp [s.eq_empty_of_isEmpty]
  refine
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmapDomain M R _ _))
      ?_
  intro l hl
  refine ⟨(lmapDomain M R (Function.invFunOn f s) : (α' →₀ M) →ₗ[R] α →₀ M) l, fun x hx => ?_, ?_⟩
  · rcases Finset.mem_image.1 (mapDomain_support hx) with ⟨c, hc, rfl⟩
    exact Function.invFunOn_mem (by simpa using hl hc)
  · rw [← LinearMap.comp_apply, ← lmapDomain_comp]
    refine (mapDomain_congr fun c hc => ?_).trans mapDomain_id
    exact Function.invFunOn_eq (by simpa using hl hc)
#align finsupp.lmap_domain_supported Finsupp.lmapDomain_supported

theorem lmapDomain_disjoint_ker (f : α → α') {s : Set α}
    (H : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    Disjoint (supported M R s) (ker (lmapDomain M R f)) := by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe, mem_ker, lmapDomain_apply, mapDomain] at h₂
  simp; ext x
  haveI := Classical.decPred fun x => x ∈ s
  by_cases xs : x ∈ s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by
      rw [h₂]
      rfl
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single x, single_eq_same] at this
    · simpa
    · intro y hy xy
      simp only [SetLike.mem_coe, mem_supported, subset_def, Finset.mem_coe, mem_support_iff] at h₁
      simp [mt (H _ (h₁ _ hy) _ xs) xy]
    · simp (config := { contextual := true })
  · by_contra h
    exact xs (h₁ <| Finsupp.mem_support_iff.2 h)
#align finsupp.lmap_domain_disjoint_ker Finsupp.lmapDomain_disjoint_ker

end LMapDomain

section LComapDomain

variable {β : Type*}

/-- Given `f : α → β` and a proof `hf` that `f` is injective, `lcomapDomain f hf` is the linear map
sending `l : β →₀ M` to the finitely supported function from `α` to `M` given by composing
`l` with `f`.

This is the linear version of `Finsupp.comapDomain`. -/
def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M where
  toFun l := Finsupp.comapDomain f l (hf.injOn _)
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
#align finsupp.lcomap_domain Finsupp.lcomapDomain

end LComapDomain

section Total

variable (α) (M) (R)
variable {α' : Type*} {M' : Type*} [AddCommMonoid M'] [Module R M'] (v : α → M) {v' : α' → M'}

/-- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
protected def total : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smulRight (v i)
#align finsupp.total Finsupp.total

variable {α M v}

theorem total_apply (l : α →₀ R) : Finsupp.total α M R v l = l.sum fun i a => a • v i :=
  rfl
#align finsupp.total_apply Finsupp.total_apply

theorem total_apply_of_mem_supported {l : α →₀ R} {s : Finset α}
    (hs : l ∈ supported R R (↑s : Set α)) : Finsupp.total α M R v l = s.sum fun i => l i • v i :=
  Finset.sum_subset hs fun x _ hxg =>
    show l x • v x = 0 by rw [not_mem_support_iff.1 hxg, zero_smul]
#align finsupp.total_apply_of_mem_supported Finsupp.total_apply_of_mem_supported

@[simp]
theorem total_single (c : R) (a : α) : Finsupp.total α M R v (single a c) = c • v a := by
  simp [total_apply, sum_single_index]
#align finsupp.total_single Finsupp.total_single

theorem total_zero_apply (x : α →₀ R) : (Finsupp.total α M R 0) x = 0 := by
  simp [Finsupp.total_apply]
#align finsupp.total_zero_apply Finsupp.total_zero_apply

variable (α M)

@[simp]
theorem total_zero : Finsupp.total α M R 0 = 0 :=
  LinearMap.ext (total_zero_apply R)
#align finsupp.total_zero Finsupp.total_zero

variable {α M}

theorem apply_total (f : M →ₗ[R] M') (v) (l : α →₀ R) :
    f (Finsupp.total α M R v l) = Finsupp.total α M' R (f ∘ v) l := by
  apply Finsupp.induction_linear l <;> simp (config := { contextual := true })
#align finsupp.apply_total Finsupp.apply_total

theorem apply_total_id (f : M →ₗ[R] M') (l : M →₀ R) :
    f (Finsupp.total M M R _root_.id l) = Finsupp.total M M' R f l :=
  apply_total ..

theorem total_unique [Unique α] (l : α →₀ R) (v) :
    Finsupp.total α M R v l = l default • v default := by rw [← total_single, ← unique_single l]
#align finsupp.total_unique Finsupp.total_unique

theorem total_surjective (h : Function.Surjective v) :
    Function.Surjective (Finsupp.total α M R v) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨Finsupp.single y 1, by simp [hy]⟩
#align finsupp.total_surjective Finsupp.total_surjective

theorem total_range (h : Function.Surjective v) : LinearMap.range (Finsupp.total α M R v) = ⊤ :=
  range_eq_top.2 <| total_surjective R h
#align finsupp.total_range Finsupp.total_range

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`Finsupp.total M M R id : (M →₀ R) →ₗ[R] M`. -/
theorem total_id_surjective (M) [AddCommMonoid M] [Module R M] :
    Function.Surjective (Finsupp.total M M R _root_.id) :=
  total_surjective R Function.surjective_id
#align finsupp.total_id_surjective Finsupp.total_id_surjective

theorem range_total : LinearMap.range (Finsupp.total α M R v) = span R (range v) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [Finsupp.total_apply]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    use Finsupp.single i 1
    simp [hi]
#align finsupp.range_total Finsupp.range_total

theorem lmapDomain_total (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
    (Finsupp.total α' M' R v').comp (lmapDomain R R f) = g.comp (Finsupp.total α M R v) := by
  ext l
  simp [total_apply, Finsupp.sum_mapDomain_index, add_smul, h]
#align finsupp.lmap_domain_total Finsupp.lmapDomain_total

theorem total_comp_lmapDomain (f : α → α') :
    (Finsupp.total α' M' R v').comp (Finsupp.lmapDomain R R f) = Finsupp.total α M' R (v' ∘ f) := by
  ext
  simp
#align finsupp.total_comp_lmap_domain Finsupp.total_comp_lmapDomain

@[simp]
theorem total_embDomain (f : α ↪ α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (embDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l := by
  simp [total_apply, Finsupp.sum, support_embDomain, embDomain_apply]
#align finsupp.total_emb_domain Finsupp.total_embDomain

@[simp]
theorem total_mapDomain (f : α → α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (mapDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l :=
  LinearMap.congr_fun (total_comp_lmapDomain _ _) l
#align finsupp.total_map_domain Finsupp.total_mapDomain

@[simp]
theorem total_equivMapDomain (f : α ≃ α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (equivMapDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l := by
  rw [equivMapDomain_eq_mapDomain, total_mapDomain]
#align finsupp.total_equiv_map_domain Finsupp.total_equivMapDomain

/-- A version of `Finsupp.range_total` which is useful for going in the other direction -/
theorem span_eq_range_total (s : Set M) : span R s = LinearMap.range (Finsupp.total s M R (↑)) := by
  rw [range_total, Subtype.range_coe_subtype, Set.setOf_mem_eq]
#align finsupp.span_eq_range_total Finsupp.span_eq_range_total

theorem mem_span_iff_total (s : Set M) (x : M) :
    x ∈ span R s ↔ ∃ l : s →₀ R, Finsupp.total s M R (↑) l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_total _ _) x
#align finsupp.mem_span_iff_total Finsupp.mem_span_iff_total

variable {R}

theorem mem_span_range_iff_exists_finsupp {v : α → M} {x : M} :
    x ∈ span R (range v) ↔ ∃ c : α →₀ R, (c.sum fun i a => a • v i) = x := by
  simp only [← Finsupp.range_total, LinearMap.mem_range, Finsupp.total_apply]
#align finsupp.mem_span_range_iff_exists_finsupp Finsupp.mem_span_range_iff_exists_finsupp

variable (R)

theorem span_image_eq_map_total (s : Set α) :
    span R (v '' s) = Submodule.map (Finsupp.total α M R v) (supported R R s) := by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine map_le_iff_le_comap.2 fun z hz => ?_
    have : ∀ i, z i • v i ∈ span R (v '' s) := by
      intro c
      haveI := Classical.decPred fun x => x ∈ s
      by_cases h : c ∈ s
      · exact smul_mem _ _ (subset_span (Set.mem_image_of_mem _ h))
      · simp [(Finsupp.mem_supported' R _).1 hz _ h]
    -- Porting note: `rw` is required to infer metavariables in `sum_mem`.
    rw [mem_comap, total_apply]
    refine sum_mem ?_
    simp [this]
#align finsupp.span_image_eq_map_total Finsupp.span_image_eq_map_total

theorem mem_span_image_iff_total {s : Set α} {x : M} :
    x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, Finsupp.total α M R v l = x := by
  rw [span_image_eq_map_total]
  simp
#align finsupp.mem_span_image_iff_total Finsupp.mem_span_image_iff_total

theorem total_option (v : Option α → M) (f : Option α →₀ R) :
    Finsupp.total (Option α) M R v f =
      f none • v none + Finsupp.total α M R (v ∘ Option.some) f.some := by
  rw [total_apply, sum_option_index_smul, total_apply]; simp
#align finsupp.total_option Finsupp.total_option

theorem total_total {α β : Type*} (A : α → M) (B : β → α →₀ R) (f : β →₀ R) :
    Finsupp.total α M R A (Finsupp.total β (α →₀ R) R B f) =
      Finsupp.total β M R (fun b => Finsupp.total α M R A (B b)) f := by
  classical
  simp only [total_apply]
  apply induction_linear f
  · simp only [sum_zero_index]
  · intro f₁ f₂ h₁ h₂
    simp [sum_add_index, h₁, h₂, add_smul]
  · simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]
#align finsupp.total_total Finsupp.total_total

@[simp]
theorem total_fin_zero (f : Fin 0 → M) : Finsupp.total (Fin 0) M R f = 0 := by
  ext i
  apply finZeroElim i
#align finsupp.total_fin_zero Finsupp.total_fin_zero

variable (α) (M) (v)

/-- `Finsupp.totalOn M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : Set α` of indices.
-/
protected def totalOn (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((Finsupp.total _ _ _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_total _).2 ⟨l, hl, rfl⟩
#align finsupp.total_on Finsupp.totalOn

variable {α} {M} {v}

theorem totalOn_range (s : Set α) : LinearMap.range (Finsupp.totalOn α M R v s) = ⊤ := by
  rw [Finsupp.totalOn, LinearMap.range_eq_map, LinearMap.map_codRestrict,
    ← LinearMap.range_le_iff_comap, range_subtype, Submodule.map_top, LinearMap.range_comp,
    range_subtype]
  exact (span_image_eq_map_total _ _).le
#align finsupp.total_on_range Finsupp.totalOn_range

theorem total_comp (f : α' → α) :
    Finsupp.total α' M R (v ∘ f) = (Finsupp.total α M R v).comp (lmapDomain R R f) := by
  ext
  simp [total_apply]
#align finsupp.total_comp Finsupp.total_comp

theorem total_comapDomain (f : α → α') (l : α' →₀ R) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) :
    Finsupp.total α M R v (Finsupp.comapDomain f l hf) =
      (l.support.preimage f hf).sum fun i => l (f i) • v i := by
  rw [Finsupp.total_apply]; rfl
#align finsupp.total_comap_domain Finsupp.total_comapDomain

theorem total_onFinset {s : Finset α} {f : α → R} (g : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) :
    Finsupp.total α M R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x := by
  classical
  simp only [Finsupp.total_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x _ h
  contrapose! h
  simp [h]
#align finsupp.total_on_finset Finsupp.total_onFinset

end Total

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `Finsupp.domCongr` as a `LinearEquiv`.
See also `LinearMap.funCongrLeft` for the case of arbitrary functions. -/
protected def domLCongr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv <| by
    simpa only [equivMapDomain_eq_mapDomain, domCongr_apply] using (lmapDomain M R e).map_smul
#align finsupp.dom_lcongr Finsupp.domLCongr

@[simp]
theorem domLCongr_apply {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl
#align finsupp.dom_lcongr_apply Finsupp.domLCongr_apply

@[simp]
theorem domLCongr_refl : Finsupp.domLCongr (Equiv.refl α) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext fun _ => equivMapDomain_refl _
#align finsupp.dom_lcongr_refl Finsupp.domLCongr_refl

theorem domLCongr_trans {α₁ α₂ α₃ : Type*} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
    (Finsupp.domLCongr f).trans (Finsupp.domLCongr f₂) =
      (Finsupp.domLCongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm
#align finsupp.dom_lcongr_trans Finsupp.domLCongr_trans

@[simp]
theorem domLCongr_symm {α₁ α₂ : Type*} (f : α₁ ≃ α₂) :
    ((Finsupp.domLCongr f).symm : (_ →₀ M) ≃ₗ[R] _) = Finsupp.domLCongr f.symm :=
  LinearEquiv.ext fun _ => rfl
#align finsupp.dom_lcongr_symm Finsupp.domLCongr_symm

-- @[simp] -- Porting note (#10618): simp can prove this
theorem domLCongr_single {α₁ : Type*} {α₂ : Type*} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    (Finsupp.domLCongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m := by
  simp
#align finsupp.dom_lcongr_single Finsupp.domLCongr_single

/-- An equivalence of sets induces a linear equivalence of `Finsupp`s supported on those sets. -/
noncomputable def congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t := by
  haveI := Classical.decPred fun x => x ∈ s
  haveI := Classical.decPred fun x => x ∈ t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)
#align finsupp.congr Finsupp.congr

/-- `Finsupp.mapRange` as a `LinearMap`. -/
def mapRange.linearMap (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] α →₀ N :=
  { mapRange.addMonoidHom f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    -- Porting note: `hf` should be specified.
    map_smul' := fun c v => mapRange_smul (hf := f.map_zero) c v (f.map_smul c) }
#align finsupp.map_range.linear_map Finsupp.mapRange.linearMap

-- Porting note: This was generated by `simps!`.
@[simp]
theorem mapRange.linearMap_apply (f : M →ₗ[R] N) (g : α →₀ M) :
    mapRange.linearMap f g = mapRange f f.map_zero g := rfl
#align finsupp.map_range.linear_map_apply Finsupp.mapRange.linearMap_apply

@[simp]
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext mapRange_id
#align finsupp.map_range.linear_map_id Finsupp.mapRange.linearMap_id

theorem mapRange.linearMap_comp (f : N →ₗ[R] P) (f₂ : M →ₗ[R] N) :
    (mapRange.linearMap (f.comp f₂) : (α →₀ _) →ₗ[R] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  -- Porting note: Placeholders should be filled.
  LinearMap.ext <| mapRange_comp f f.map_zero f₂ f₂.map_zero (comp f f₂).map_zero
#align finsupp.map_range.linear_map_comp Finsupp.mapRange.linearMap_comp

@[simp]
theorem mapRange.linearMap_toAddMonoidHom (f : M →ₗ[R] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext fun _ => rfl
#align finsupp.map_range.linear_map_to_add_monoid_hom Finsupp.mapRange.linearMap_toAddMonoidHom

/-- `Finsupp.mapRange` as a `LinearEquiv`. -/
def mapRange.linearEquiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }
#align finsupp.map_range.linear_equiv Finsupp.mapRange.linearEquiv

-- Porting note: This was generated by `simps`.
@[simp]
theorem mapRange.linearEquiv_apply (e : M ≃ₗ[R] N) (g : α →₀ M) :
    mapRange.linearEquiv e g = mapRange.linearMap e.toLinearMap g := rfl
#align finsupp.map_range.linear_equiv_apply Finsupp.mapRange.linearEquiv_apply

@[simp]
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext mapRange_id
#align finsupp.map_range.linear_equiv_refl Finsupp.mapRange.linearEquiv_refl

theorem mapRange.linearEquiv_trans (f : M ≃ₗ[R] N) (f₂ : N ≃ₗ[R] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α →₀ _) ≃ₗ[R] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  -- Porting note: Placeholders should be filled.
  LinearEquiv.ext <| mapRange_comp f₂ f₂.map_zero f f.map_zero (f.trans f₂).map_zero
#align finsupp.map_range.linear_equiv_trans Finsupp.mapRange.linearEquiv_trans

@[simp]
theorem mapRange.linearEquiv_symm (f : M ≃ₗ[R] N) :
    ((mapRange.linearEquiv f).symm : (α →₀ _) ≃ₗ[R] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun _x => rfl
#align finsupp.map_range.linear_equiv_symm Finsupp.mapRange.linearEquiv_symm

-- Porting note: This priority should be higher than `LinearEquiv.coe_toAddEquiv`.
@[simp 1500]
theorem mapRange.linearEquiv_toAddEquiv (f : M ≃ₗ[R] N) :
    (mapRange.linearEquiv f).toAddEquiv = (mapRange.addEquiv f.toAddEquiv : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => rfl
#align finsupp.map_range.linear_equiv_to_add_equiv Finsupp.mapRange.linearEquiv_toAddEquiv

@[simp]
theorem mapRange.linearEquiv_toLinearMap (f : M ≃ₗ[R] N) :
    (mapRange.linearEquiv f).toLinearMap = (mapRange.linearMap f.toLinearMap : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext fun _ => rfl
#align finsupp.map_range.linear_equiv_to_linear_map Finsupp.mapRange.linearEquiv_toLinearMap

/-- An equivalence of domain and a linear equivalence of codomain induce a linear equivalence of the
corresponding finitely supported functions. -/
def lcongr {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) : (ι →₀ M) ≃ₗ[R] κ →₀ N :=
  (Finsupp.domLCongr e₁).trans (mapRange.linearEquiv e₂)
#align finsupp.lcongr Finsupp.lcongr

@[simp]
theorem lcongr_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (i : ι) (m : M) :
    lcongr e₁ e₂ (Finsupp.single i m) = Finsupp.single (e₁ i) (e₂ m) := by simp [lcongr]
#align finsupp.lcongr_single Finsupp.lcongr_single

@[simp]
theorem lcongr_apply_apply {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (f : ι →₀ M) (k : κ) :
    lcongr e₁ e₂ f k = e₂ (f (e₁.symm k)) :=
  rfl
#align finsupp.lcongr_apply_apply Finsupp.lcongr_apply_apply

theorem lcongr_symm_single {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) (k : κ) (n : N) :
    (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) := by
  apply_fun (lcongr e₁ e₂ : (ι →₀ M) → (κ →₀ N)) using (lcongr e₁ e₂).injective
  simp
#align finsupp.lcongr_symm_single Finsupp.lcongr_symm_single

@[simp]
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) :
    (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm := by
  ext
  rfl
#align finsupp.lcongr_symm Finsupp.lcongr_symm

section Sum

variable (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sumFinsuppEquivProdFinsupp`. -/
@[simps apply symm_apply]
def sumFinsuppLEquivProdFinsupp {α β : Type*} : (Sum α β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        -- Porting note: `add_equiv.to_fun_eq_coe` →
        --               `Equiv.toFun_as_coe` & `AddEquiv.toEquiv_eq_coe` & `AddEquiv.coe_toEquiv`
        simp only [Equiv.toFun_as_coe, AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv, Prod.smul_fst,
          Prod.smul_snd, smul_apply,
          snd_sumFinsuppAddEquivProdFinsupp, fst_sumFinsuppAddEquivProdFinsupp,
          RingHom.id_apply] }
#align finsupp.sum_finsupp_lequiv_prod_finsupp Finsupp.sumFinsuppLEquivProdFinsupp

theorem fst_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : Sum α β →₀ M) (x : α) :
    (sumFinsuppLEquivProdFinsupp R f).1 x = f (Sum.inl x) :=
  rfl
#align finsupp.fst_sum_finsupp_lequiv_prod_finsupp Finsupp.fst_sumFinsuppLEquivProdFinsupp

theorem snd_sumFinsuppLEquivProdFinsupp {α β : Type*} (f : Sum α β →₀ M) (y : β) :
    (sumFinsuppLEquivProdFinsupp R f).2 y = f (Sum.inr y) :=
  rfl
#align finsupp.snd_sum_finsupp_lequiv_prod_finsupp Finsupp.snd_sumFinsuppLEquivProdFinsupp

theorem sumFinsuppLEquivProdFinsupp_symm_inl {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inl x) = fg.1 x :=
  rfl
#align finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inl Finsupp.sumFinsuppLEquivProdFinsupp_symm_inl

theorem sumFinsuppLEquivProdFinsupp_symm_inr {α β : Type*} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    ((sumFinsuppLEquivProdFinsupp R).symm fg) (Sum.inr y) = fg.2 y :=
  rfl
#align finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inr Finsupp.sumFinsuppLEquivProdFinsupp_symm_inr

end Sum

section Sigma

variable {η : Type*} [Fintype η] {ιs : η → Type*} [Zero α]
variable (R)

/-- On a `Fintype η`, `Finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `(j : η) → (ιs j →₀ M)`.

This is the `LinearEquiv` version of `Finsupp.sigmaFinsuppAddEquivPiFinsupp`. -/
noncomputable def sigmaFinsuppLEquivPiFinsupp {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] : ((Σ j, ιs j) →₀ M) ≃ₗ[R] (j : _) → (ιs j →₀ M) :=
  -- Porting note: `ιs` should be specified.
  { sigmaFinsuppAddEquivPiFinsupp (ιs := ιs) with
    map_smul' := fun c f => by
      ext
      simp }
#align finsupp.sigma_finsupp_lequiv_pi_finsupp Finsupp.sigmaFinsuppLEquivPiFinsupp

@[simp]
theorem sigmaFinsuppLEquivPiFinsupp_apply {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] (f : (Σj, ιs j) →₀ M) (j i) : sigmaFinsuppLEquivPiFinsupp R f j i = f ⟨j, i⟩ :=
  rfl
#align finsupp.sigma_finsupp_lequiv_pi_finsupp_apply Finsupp.sigmaFinsuppLEquivPiFinsupp_apply

@[simp]
theorem sigmaFinsuppLEquivPiFinsupp_symm_apply {M : Type*} {ιs : η → Type*} [AddCommMonoid M]
    [Module R M] (f : (j : _) → (ιs j →₀ M)) (ji) :
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm f ji = f ji.1 ji.2 :=
  rfl
#align finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply Finsupp.sigmaFinsuppLEquivPiFinsupp_symm_apply

end Sigma

section Prod

/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `LinearEquiv` version of `Finsupp.finsuppProdEquiv`. -/
noncomputable def finsuppProdLEquiv {α β : Type*} (R : Type*) {M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M :=
  { finsuppProdEquiv with
    map_add' := fun f g => by
      ext
      simp [finsuppProdEquiv, curry_apply]
    map_smul' := fun c f => by
      ext
      simp [finsuppProdEquiv, curry_apply] }
#align finsupp.finsupp_prod_lequiv Finsupp.finsuppProdLEquiv

@[simp]
theorem finsuppProdLEquiv_apply {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α × β →₀ M) (x y) : finsuppProdLEquiv R f x y = f (x, y) := by
  rw [finsuppProdLEquiv, LinearEquiv.coe_mk, finsuppProdEquiv, Finsupp.curry_apply]
#align finsupp.finsupp_prod_lequiv_apply Finsupp.finsuppProdLEquiv_apply

@[simp]
theorem finsuppProdLEquiv_symm_apply {α β R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α →₀ β →₀ M) (xy) : (finsuppProdLEquiv R).symm f xy = f xy.1 xy.2 := by
  conv_rhs =>
    rw [← (finsuppProdLEquiv R).apply_symm_apply f, finsuppProdLEquiv_apply]
#align finsupp.finsupp_prod_lequiv_symm_apply Finsupp.finsuppProdLEquiv_symm_apply

end Prod

/-- If `R` is countable, then any `R`-submodule spanned by a countable family of vectors is
countable. -/
instance {ι : Type*} [Countable R] [Countable ι] (v : ι → M) :
    Countable (Submodule.span R (Set.range v)) := by
  refine Set.countable_coe_iff.mpr (Set.Countable.mono ?_ (Set.countable_range
      (fun c : (ι →₀ R) => c.sum fun i _ => (c i) • v i)))
  exact fun _ h => Finsupp.mem_span_range_iff_exists_finsupp.mp (SetLike.mem_coe.mp h)

end Finsupp

section Fintype

variable {α M : Type*} (R : Type*) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [Semiring S] [Module S M] [SMulCommClass R S M]
variable (v : α → M)

/-- `Fintype.total R S v f` is the linear combination of vectors in `v` with weights in `f`.
This variant of `Finsupp.total` is defined on fintype indexed vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
protected def Fintype.total : (α → M) →ₗ[S] (α → R) →ₗ[R] M where
  toFun v :=
    { toFun := fun f => ∑ i, f i • v i
      map_add' := fun f g => by simp_rw [← Finset.sum_add_distrib, ← add_smul]; rfl
      map_smul' := fun r f => by simp_rw [Finset.smul_sum, smul_smul]; rfl }
  map_add' u v := by ext; simp [Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by ext; simp [Finset.smul_sum, smul_comm]
#align fintype.total Fintype.total

variable {S}

theorem Fintype.total_apply (f) : Fintype.total R S v f = ∑ i, f i • v i :=
  rfl
#align fintype.total_apply Fintype.total_apply

@[simp]
theorem Fintype.total_apply_single [DecidableEq α] (i : α) (r : R) :
    Fintype.total R S v (Pi.single i r) = r • v i := by
  simp_rw [Fintype.total_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
#align fintype.total_apply_single Fintype.total_apply_single

variable (S)

theorem Finsupp.total_eq_fintype_total_apply (x : α → R) : Finsupp.total α M R v
    ((Finsupp.linearEquivFunOnFinite R R α).symm x) = Fintype.total R S v x := by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [Finsupp.not_mem_support_iff.mp hx]
    exact zero_smul _ _
#align finsupp.total_eq_fintype_total_apply Finsupp.total_eq_fintype_total_apply

theorem Finsupp.total_eq_fintype_total :
    (Finsupp.total α M R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap =
      Fintype.total R S v :=
  LinearMap.ext <| Finsupp.total_eq_fintype_total_apply R S v
#align finsupp.total_eq_fintype_total Finsupp.total_eq_fintype_total

variable {S}

@[simp]
theorem Fintype.range_total :
    LinearMap.range (Fintype.total R S v) = Submodule.span R (Set.range v) := by
  rw [← Finsupp.total_eq_fintype_total, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, Finsupp.range_total]
#align fintype.range_total Fintype.range_total

section SpanRange

variable {v} {x : M}

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem mem_span_range_iff_exists_fun :
    x ∈ span R (range v) ↔ ∃ c : α → R, ∑ i, c i • v i = x := by
  -- Porting note: `Finsupp.equivFunOnFinite.surjective.exists` should be come before `simp`.
  rw [Finsupp.equivFunOnFinite.surjective.exists]
  simp only [Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.equivFunOnFinite_apply]
  exact exists_congr fun c => Eq.congr_left <| Finsupp.sum_fintype _ _ fun i => zero_smul _ _
#align mem_span_range_iff_exists_fun mem_span_range_iff_exists_fun

/-- A family `v : α → V` is generating `V` iff every element `(x : V)`
can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem top_le_span_range_iff_forall_exists_fun :
    ⊤ ≤ span R (range v) ↔ ∀ x, ∃ c : α → R, ∑ i, c i • v i = x := by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩
#align top_le_span_range_iff_forall_exists_fun top_le_span_range_iff_forall_exists_fun

end SpanRange

end Fintype

variable {R : Type*} {M : Type*} {N : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section

variable (R)

/-- Pick some representation of `x : span R w` as a linear combination in `w`,
using the axiom of choice.
-/
irreducible_def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_total _ _ _).mp x.2).choose
#align span.repr Span.repr

@[simp]
theorem Span.finsupp_total_repr {w : Set M} (x : span R w) :
    Finsupp.total w M R (↑) (Span.repr R w x) = x := by
  rw [Span.repr_def]
  exact ((Finsupp.mem_span_iff_total _ _ _).mp x.2).choose_spec
#align span.finsupp_total_repr Span.finsupp_total_repr

end

protected theorem Submodule.finsupp_sum_mem {ι β : Type*} [Zero β] (S : Submodule R M) (f : ι →₀ β)
    (g : ι → β → M) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
  AddSubmonoidClass.finsupp_sum_mem S f g h
#align submodule.finsupp_sum_mem Submodule.finsupp_sum_mem

theorem LinearMap.map_finsupp_total (f : M →ₗ[R] N) {ι : Type*} {g : ι → M} (l : ι →₀ R) :
    f (Finsupp.total ι M R g l) = Finsupp.total ι N R (f ∘ g) l := by
  -- Porting note: `(· ∘ ·)` is required.
  simp only [Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum, map_sum, map_smul, (· ∘ ·)]
#align linear_map.map_finsupp_total LinearMap.map_finsupp_total

theorem Submodule.exists_finset_of_mem_iSup {ι : Sort _} (p : ι → Submodule R M) {m : M}
    (hm : m ∈ ⨆ i, p i) : ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i := by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm
#align submodule.exists_finset_of_mem_supr Submodule.exists_finset_of_mem_iSup

/-- `Submodule.exists_finset_of_mem_iSup` as an `iff` -/
theorem Submodule.mem_iSup_iff_exists_finset {ι : Sort _} {p : ι → Submodule R M} {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i :=
  ⟨Submodule.exists_finset_of_mem_iSup p, fun ⟨_, hs⟩ =>
    iSup_mono (fun i => (iSup_const_le : _ ≤ p i)) hs⟩
#align submodule.mem_supr_iff_exists_finset Submodule.mem_iSup_iff_exists_finset

theorem Submodule.mem_sSup_iff_exists_finset {S : Set (Submodule R M)} {m : M} :
    m ∈ sSup S ↔ ∃ s : Finset (Submodule R M), ↑s ⊆ S ∧ m ∈ ⨆ i ∈ s, i := by
  rw [sSup_eq_iSup, iSup_subtype', Submodule.mem_iSup_iff_exists_finset]
  refine ⟨fun ⟨s, hs⟩ ↦ ⟨s.map (Function.Embedding.subtype S), ?_, ?_⟩,
          fun ⟨s, hsS, hs⟩ ↦ ⟨s.preimage (↑) (Subtype.coe_injective.injOn _), ?_⟩⟩
  · simpa using fun x _ ↦ x.property
  · suffices m ∈ ⨆ (i) (hi : i ∈ S) (_ : ⟨i, hi⟩ ∈ s), i by simpa
    rwa [iSup_subtype']
  · have : ⨆ (i) (_ : i ∈ S ∧ i ∈ s), i = ⨆ (i) (_ : i ∈ s), i := by convert rfl; aesop
    simpa only [Finset.mem_preimage, iSup_subtype, iSup_and', this]

theorem mem_span_finset {s : Finset M} {x : M} :
    x ∈ span R (↑s : Set M) ↔ ∃ f : M → R, ∑ i ∈ s, f i • i = x :=
  ⟨fun hx =>
    let ⟨v, hvs, hvx⟩ :=
      (Finsupp.mem_span_image_iff_total _).1
        (show x ∈ span R (_root_.id '' (↑s : Set M)) by rwa [Set.image_id])
    ⟨v, hvx ▸ (Finsupp.total_apply_of_mem_supported _ hvs).symm⟩,
    fun ⟨f, hf⟩ => hf ▸ sum_mem fun i hi => smul_mem _ _ <| subset_span hi⟩
#align mem_span_finset mem_span_finset

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `Finsupp.sum`. -/
theorem mem_span_set {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔
      ∃ c : M →₀ R, (c.support : Set M) ⊆ s ∧ (c.sum fun mi r => r • mi) = m := by
  conv_lhs => rw [← Set.image_id s]
  exact Finsupp.mem_span_image_iff_total R (v := _root_.id (α := M))
#align mem_span_set mem_span_set

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses a sum indexed by `Fin n` for some `n`. -/
lemma mem_span_set' {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔ ∃ (n : ℕ) (f : Fin n → R) (g : Fin n → s),
      ∑ i, f i • (g i : M) = m := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases mem_span_set.1 h with ⟨c, cs, rfl⟩
    have A : c.support ≃ Fin c.support.card := Finset.equivFin _
    refine ⟨_, fun i ↦ c (A.symm i), fun i ↦ ⟨A.symm i, cs (A.symm i).2⟩, ?_⟩
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support]
    exact Fintype.sum_equiv A.symm _ (fun j ↦ c j • (j : M)) (fun i ↦ rfl)
  · rintro ⟨n, f, g, rfl⟩
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span (g i).2))

/-- The span of a subset `s` is the union over all `n` of the set of linear combinations of at most
`n` terms belonging to `s`. -/
lemma span_eq_iUnion_nat (s : Set M) :
    (Submodule.span R s : Set M) = ⋃ (n : ℕ),
      (fun (f : Fin n → (R × M)) ↦ ∑ i, (f i).1 • (f i).2) '' ({f | ∀ i, (f i).2 ∈ s}) := by
  ext m
  simp only [SetLike.mem_coe, mem_iUnion, mem_image, mem_setOf_eq, mem_span_set']
  refine exists_congr (fun n ↦ ⟨?_, ?_⟩)
  · rintro ⟨f, g, rfl⟩
    exact ⟨fun i ↦ (f i, g i), fun i ↦ (g i).2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i ↦ (f i).1, fun i ↦ ⟨(f i).2, (hf i)⟩, rfl⟩

/-- If `Subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
def Module.subsingletonEquiv (R M ι : Type*) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun _ := 0
  invFun _ := 0
  left_inv m := by
    letI := Module.subsingleton R M
    simp only [eq_iff_true_of_subsingleton]
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' _ _ := (add_zero 0).symm
  map_smul' r _ := (smul_zero r).symm
#align module.subsingleton_equiv Module.subsingletonEquiv

namespace LinearMap

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFunOnFintypeSurjective`
/-- A surjective linear map to finitely supported functions has a splitting. -/
def splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose
#align linear_map.splitting_of_finsupp_surjective LinearMap.splittingOfFinsuppSurjective

theorem splittingOfFinsuppSurjective_splits (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id := by
  -- Porting note: `ext` can't find appropriate theorems.
  refine lhom_ext' fun x => ext_ring <| Finsupp.ext fun y => ?_
  dsimp [splittingOfFinsuppSurjective]
  congr
  rw [sum_single_index, one_smul]
  · exact (s (Finsupp.single x 1)).choose_spec
  · rw [zero_smul]
#align linear_map.splitting_of_finsupp_surjective_splits LinearMap.splittingOfFinsuppSurjective_splits

theorem leftInverse_splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    LeftInverse f (splittingOfFinsuppSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFinsuppSurjective_splits f s) g
#align linear_map.left_inverse_splitting_of_finsupp_surjective LinearMap.leftInverse_splittingOfFinsuppSurjective

theorem splittingOfFinsuppSurjective_injective (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    Injective (splittingOfFinsuppSurjective f s) :=
  (leftInverse_splittingOfFinsuppSurjective f s).injective
#align linear_map.splitting_of_finsupp_surjective_injective LinearMap.splittingOfFinsuppSurjective_injective

-- See also `LinearMap.splittingOfFinsuppSurjective`
/-- A surjective linear map to functions on a finite type has a splitting. -/
def splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R) (s : Surjective f) :
    (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap
#align linear_map.splitting_of_fun_on_fintype_surjective LinearMap.splittingOfFunOnFintypeSurjective

theorem splittingOfFunOnFintypeSurjective_splits [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.id := by
  classical
  -- Porting note: `ext` can't find appropriate theorems.
  refine pi_ext' fun x => ext_ring <| funext fun y => ?_
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single, Finsupp.sum_single_index, one_smul,
    (s (Finsupp.single x 1)).choose_spec, Finsupp.single_eq_pi_single]
  rw [zero_smul]
#align linear_map.splitting_of_fun_on_fintype_surjective_splits LinearMap.splittingOfFunOnFintypeSurjective_splits

theorem leftInverse_splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g
#align linear_map.left_inverse_splitting_of_fun_on_fintype_surjective LinearMap.leftInverse_splittingOfFunOnFintypeSurjective

theorem splittingOfFunOnFintypeSurjective_injective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s) :=
  (leftInverse_splittingOfFunOnFintypeSurjective f s).injective
#align linear_map.splitting_of_fun_on_fintype_surjective_injective LinearMap.splittingOfFunOnFintypeSurjective_injective

end LinearMap

namespace LinearMap

section AddCommMonoid

variable {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} {ι : Type*}
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] {σ₁₂ : R →+* R₂}
variable [Module R M] [Module R₂ M₂]
variable {γ : Type*} [Zero γ]

section Finsupp

#align linear_map.map_finsupp_sum map_finsupp_sumₓ
#align linear_equiv.map_finsupp_sum map_finsupp_sumₓ

theorem coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) :
    ⇑(t.sum g) = t.sum fun i d => g i d := rfl
#align linear_map.coe_finsupp_sum LinearMap.coe_finsupp_sum

@[simp]
theorem finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (t.sum g) b = t.sum fun i d => g i d b :=
  sum_apply _ _ _
#align linear_map.finsupp_sum_apply LinearMap.finsupp_sum_apply

end Finsupp

end AddCommMonoid

end LinearMap
