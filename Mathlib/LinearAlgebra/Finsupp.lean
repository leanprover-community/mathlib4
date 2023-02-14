/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module linear_algebra.finsupp
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Defs
import Mathbin.LinearAlgebra.Pi
import Mathbin.LinearAlgebra.Span

/-!
# Properties of the module `α →₀ M`

Given an `R`-module `M`, the `R`-module structure on `α →₀ M` is defined in
`data.finsupp.basic`.

In this file we define `finsupp.supported s` to be the set `{f : α →₀ M | f.support ⊆ s}`
interpreted as a submodule of `α →₀ M`. We also define `linear_map` versions of various maps:

* `finsupp.lsingle a : M →ₗ[R] ι →₀ M`: `finsupp.single a` as a linear map;

* `finsupp.lapply a : (ι →₀ M) →ₗ[R] M`: the map `λ f, f a` as a linear map;

* `finsupp.lsubtype_domain (s : set α) : (α →₀ M) →ₗ[R] (s →₀ M)`: restriction to a subtype as a
  linear map;

* `finsupp.restrict_dom`: `finsupp.filter` as a linear map to `finsupp.supported s`;

* `finsupp.lsum`: `finsupp.sum` or `finsupp.lift_add_hom` as a `linear_map`;

* `finsupp.total α M R (v : ι → M)`: sends `l : ι → R` to the linear combination of `v i` with
  coefficients `l i`;

* `finsupp.total_on`: a restricted version of `finsupp.total` with domain `finsupp.supported R R s`
  and codomain `submodule.span R (v '' s)`;

* `finsupp.supported_equiv_finsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;

* `finsupp.lmap_domain`: a linear map version of `finsupp.map_domain`;

* `finsupp.dom_lcongr`: a `linear_equiv` version of `finsupp.dom_congr`;

* `finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

* `finsupp.lcongr`: a `linear_equiv`alence between `α →₀ M` and `β →₀ N` constructed using `e : α ≃
  β` and `e' : M ≃ₗ[R] N`.

## Tags

function with finite support, module, linear algebra
-/


noncomputable section

open Set LinearMap Submodule

open Classical BigOperators

namespace Finsupp

variable {α : Type _} {M : Type _} {N : Type _} {P : Type _} {R : Type _} {S : Type _}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]

variable [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

/-- Interpret `finsupp.single a` as a linear map. -/
def lsingle (a : α) : M →ₗ[R] α →₀ M :=
  { Finsupp.singleAddHom a with map_smul' := fun a b => (smul_single _ _ _).symm }
#align finsupp.lsingle Finsupp.lsingle

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere. -/
theorem lhom_ext ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a b, φ (single a b) = ψ (single a b)) : φ = ψ :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext h
#align finsupp.lhom_ext Finsupp.lhom_ext

/-- Two `R`-linear maps from `finsupp X M` which agree on each `single x y` agree everywhere.

We formulate this fact using equality of linear maps `φ.comp (lsingle a)` and `ψ.comp (lsingle a)`
so that the `ext` tactic can apply a type-specific extensionality lemma to prove equality of these
maps. E.g., if `M = R`, then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext]
theorem lhom_ext' ⦃φ ψ : (α →₀ M) →ₗ[R] N⦄ (h : ∀ a, φ.comp (lsingle a) = ψ.comp (lsingle a)) :
    φ = ψ :=
  lhom_ext fun a => LinearMap.congr_fun (h a)
#align finsupp.lhom_ext' Finsupp.lhom_ext'

/-- Interpret `λ (f : α →₀ M), f a` as a linear map. -/
def lapply (a : α) : (α →₀ M) →ₗ[R] M :=
  { Finsupp.applyAddHom a with map_smul' := fun a b => rfl }
#align finsupp.lapply Finsupp.lapply

/-- Forget that a function is finitely supported.

This is the linear version of `finsupp.to_fun`. -/
@[simps]
def lcoeFun : (α →₀ M) →ₗ[R] α → M where
  toFun := coeFn
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
#align finsupp.lcoe_fun Finsupp.lcoeFun

section LsubtypeDomain

variable (s : Set α)

/-- Interpret `finsupp.subtype_domain s` as a linear map. -/
def lsubtypeDomain : (α →₀ M) →ₗ[R] s →₀ M
    where
  toFun := subtypeDomain fun x => x ∈ s
  map_add' a b := subtypeDomain_add
  map_smul' c a := ext fun a => rfl
#align finsupp.lsubtype_domain Finsupp.lsubtypeDomain

theorem lsubtypeDomain_apply (f : α →₀ M) :
    (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M) f = subtypeDomain (fun x => x ∈ s) f :=
  rfl
#align finsupp.lsubtype_domain_apply Finsupp.lsubtypeDomain_apply

end LsubtypeDomain

@[simp]
theorem lsingle_apply (a : α) (b : M) : (lsingle a : M →ₗ[R] α →₀ M) b = single a b :=
  rfl
#align finsupp.lsingle_apply Finsupp.lsingle_apply

@[simp]
theorem lapply_apply (a : α) (f : α →₀ M) : (lapply a : (α →₀ M) →ₗ[R] M) f = f a :=
  rfl
#align finsupp.lapply_apply Finsupp.lapply_apply

@[simp]
theorem ker_lsingle (a : α) : (lsingle a : M →ₗ[R] α →₀ M).ker = ⊥ :=
  ker_eq_bot_of_injective (single_injective a)
#align finsupp.ker_lsingle Finsupp.ker_lsingle

theorem lsingle_range_le_ker_lapply (s t : Set α) (h : Disjoint s t) :
    (⨆ a ∈ s, (lsingle a : M →ₗ[R] α →₀ M).range) ≤ ⨅ a ∈ t, ker (lapply a : (α →₀ M) →ₗ[R] M) :=
  by
  refine' supᵢ_le fun a₁ => supᵢ_le fun h₁ => range_le_iff_comap.2 _
  simp only [(ker_comp _ _).symm, eq_top_iff, SetLike.le_def, mem_ker, comap_infi, mem_infi]
  intro b hb a₂ h₂
  have : a₁ ≠ a₂ := fun eq => h.le_bot ⟨h₁, Eq.symm ▸ h₂⟩
  exact single_eq_of_ne this
#align finsupp.lsingle_range_le_ker_lapply Finsupp.lsingle_range_le_ker_lapply

theorem infᵢ_ker_lapply_le_bot : (⨅ a, ker (lapply a : (α →₀ M) →ₗ[R] M)) ≤ ⊥ :=
  by
  simp only [SetLike.le_def, mem_infi, mem_ker, mem_bot, lapply_apply]
  exact fun a h => Finsupp.ext h
#align finsupp.infi_ker_lapply_le_bot Finsupp.infᵢ_ker_lapply_le_bot

theorem supᵢ_lsingle_range : (⨆ a, (lsingle a : M →ₗ[R] α →₀ M).range) = ⊤ :=
  by
  refine' eq_top_iff.2 <| SetLike.le_def.2 fun f _ => _
  rw [← sum_single f]
  exact sum_mem fun a ha => Submodule.mem_supᵢ_of_mem a ⟨_, rfl⟩
#align finsupp.supr_lsingle_range Finsupp.supᵢ_lsingle_range

theorem disjoint_lsingle_lsingle (s t : Set α) (hs : Disjoint s t) :
    Disjoint (⨆ a ∈ s, (lsingle a : M →ₗ[R] α →₀ M).range)
      (⨆ a ∈ t, (lsingle a : M →ₗ[R] α →₀ M).range) :=
  by
  refine'
    (Disjoint.mono (lsingle_range_le_ker_lapply _ _ <| disjoint_compl_right)
        (lsingle_range_le_ker_lapply _ _ <| disjoint_compl_right))
      _
  rw [disjoint_iff_inf_le]
  refine' le_trans (le_infᵢ fun i => _) infi_ker_lapply_le_bot
  classical
    by_cases his : i ∈ s
    · by_cases hit : i ∈ t
      · exact (hs.le_bot ⟨his, hit⟩).elim
      exact inf_le_of_right_le (infᵢ_le_of_le i <| infᵢ_le _ hit)
    exact inf_le_of_left_le (infᵢ_le_of_le i <| infᵢ_le _ his)
#align finsupp.disjoint_lsingle_lsingle Finsupp.disjoint_lsingle_lsingle

theorem span_single_image (s : Set M) (a : α) :
    Submodule.span R (single a '' s) = (Submodule.span R s).map (lsingle a : M →ₗ[R] α →₀ M) := by
  rw [← span_image] <;> rfl
#align finsupp.span_single_image Finsupp.span_single_image

variable (M R)

/-- `finsupp.supported M R s` is the `R`-submodule of all `p : α →₀ M` such that `p.support ⊆ s`. -/
def supported (s : Set α) : Submodule R (α →₀ M) :=
  by
  refine' ⟨{ p | ↑p.support ⊆ s }, _, _, _⟩
  · intro p q hp hq
    refine' subset.trans (subset.trans (Finset.coe_subset.2 support_add) _) (union_subset hp hq)
    rw [Finset.coe_union]
  · simp only [subset_def, Finset.mem_coe, Set.mem_setOf_eq, mem_support_iff, zero_apply]
    intro h ha
    exact (ha rfl).elim
  · intro a p hp
    refine' subset.trans (Finset.coe_subset.2 support_smul) hp
#align finsupp.supported Finsupp.supported

variable {M}

theorem mem_supported {s : Set α} (p : α →₀ M) : p ∈ supported M R s ↔ ↑p.support ⊆ s :=
  Iff.rfl
#align finsupp.mem_supported Finsupp.mem_supported

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem mem_supported' {s : Set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ (x) (_ : x ∉ s), p x = 0 := by
  haveI := Classical.decPred fun x : α => x ∈ s <;>
    simp [mem_supported, Set.subset_def, not_imp_comm]
#align finsupp.mem_supported' Finsupp.mem_supported'

theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]
#align finsupp.mem_supported_support Finsupp.mem_supported_support

theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)
#align finsupp.single_mem_supported Finsupp.single_mem_supported

theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) :=
  by
  refine' (span_eq_of_le _ _ (SetLike.le_def.2 fun l hl => _)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine' sum_mem fun i il => _
    convert @smul_mem R (α →₀ R) _ _ _ _ (single i 1) (l i) _
    · simp
    apply subset_span
    apply Set.mem_image_of_mem _ (hl il)
#align finsupp.supported_eq_span_single Finsupp.supported_eq_span_single

variable (M R)

/-- Interpret `finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrictDom (s : Set α) : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun l₁ l₂ => filter_add
      map_smul' := fun a l => filter_smul } fun l =>
    (mem_supported' _ _).2 fun x => filter_apply_neg (· ∈ s) l
#align finsupp.restrict_dom Finsupp.restrictDom

variable {M R}

section

@[simp]
theorem restrictDom_apply (s : Set α) (l : α →₀ M) :
    ((restrictDom M R s : (α →₀ M) →ₗ[R] supported M R s) l : α →₀ M) = Finsupp.filter (· ∈ s) l :=
  rfl
#align finsupp.restrict_dom_apply Finsupp.restrictDom_apply

end

theorem restrictDom_comp_subtype (s : Set α) :
    (restrictDom M R s).comp (Submodule.subtype _) = LinearMap.id :=
  by
  ext (l a)
  by_cases a ∈ s <;> simp [h]
  exact ((mem_supported' R l.1).1 l.2 a h).symm
#align finsupp.restrict_dom_comp_subtype Finsupp.restrictDom_comp_subtype

theorem range_restrictDom (s : Set α) : (restrictDom M R s).range = ⊤ :=
  range_eq_top.2 <|
    Function.RightInverse.surjective <| LinearMap.congr_fun (restrictDom_comp_subtype s)
#align finsupp.range_restrict_dom Finsupp.range_restrictDom

theorem supported_mono {s t : Set α} (st : s ⊆ t) : supported M R s ≤ supported M R t := fun l h =>
  Set.Subset.trans h st
#align finsupp.supported_mono Finsupp.supported_mono

@[simp]
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
  eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 <| by ext <;> simp_all [mem_supported']
#align finsupp.supported_empty Finsupp.supported_empty

@[simp]
theorem supported_univ : supported M R (Set.univ : Set α) = ⊤ :=
  eq_top_iff.2 fun l _ => Set.subset_univ _
#align finsupp.supported_univ Finsupp.supported_univ

theorem supported_unionᵢ {δ : Type _} (s : δ → Set α) :
    supported M R (⋃ i, s i) = ⨆ i, supported M R (s i) :=
  by
  refine' le_antisymm _ (supᵢ_le fun i => supported_mono <| Set.subset_unionᵢ _ _)
  haveI := Classical.decPred fun x => x ∈ ⋃ i, s i
  suffices
    ((Submodule.subtype _).comp (restrict_dom M R (⋃ i, s i))).range ≤ ⨆ i, supported M R (s i) by
    rwa [LinearMap.range_comp, range_restrict_dom, map_top, range_subtype] at this
  rw [range_le_iff_comap, eq_top_iff]
  rintro l ⟨⟩
  apply Finsupp.induction l
  · exact zero_mem _
  refine' fun x a l hl a0 => add_mem _
  by_cases ∃ i, x ∈ s i <;> simp [h]
  · cases' h with i hi
    exact le_supᵢ (fun i => supported M R (s i)) i (single_mem_supported R _ hi)
#align finsupp.supported_Union Finsupp.supported_unionᵢ

theorem supported_union (s t : Set α) : supported M R (s ∪ t) = supported M R s ⊔ supported M R t :=
  by erw [Set.union_eq_unionᵢ, supported_Union, supᵢ_bool_eq] <;> rfl
#align finsupp.supported_union Finsupp.supported_union

theorem supported_interᵢ {ι : Type _} (s : ι → Set α) :
    supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
  Submodule.ext fun x => by simp [mem_supported, subset_Inter_iff]
#align finsupp.supported_Inter Finsupp.supported_interᵢ

theorem supported_inter (s t : Set α) : supported M R (s ∩ t) = supported M R s ⊓ supported M R t :=
  by rw [Set.inter_eq_interᵢ, supported_Inter, infᵢ_bool_eq] <;> rfl
#align finsupp.supported_inter Finsupp.supported_inter

theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) :
    Disjoint (supported M R s) (supported M R t) :=
  disjoint_iff.2 <| by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]
#align finsupp.disjoint_supported_supported Finsupp.disjoint_supported_supported

theorem disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Disjoint (supported M R s) (supported M R t) ↔ Disjoint s t :=
  by
  refine' ⟨fun h => set.disjoint_left.mpr fun x hx1 hx2 => _, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot, single_eq_zero] at this
  exact hy this
#align finsupp.disjoint_supported_supported_iff Finsupp.disjoint_supported_supported_iff

/-- Interpret `finsupp.restrict_support_equiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s →₀ M :=
  by
  let F : supported M R s ≃ (s →₀ M) := restrict_support_equiv s M
  refine' F.to_linear_equiv _
  have :
    (F : supported M R s → ↥s →₀ M) =
      (lsubtype_domain s : (α →₀ M) →ₗ[R] s →₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _
#align finsupp.supported_equiv_finsupp Finsupp.supportedEquivFinsupp

section Lsum

variable (S) [Module S N] [SMulCommClass R S N]

/-- Lift a family of linear maps `M →ₗ[R] N` indexed by `x : α` to a linear map from `α →₀ M` to
`N` using `finsupp.sum`. This is an upgraded version of `finsupp.lift_add_hom`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
def lsum : (α → M →ₗ[R] N) ≃ₗ[S] (α →₀ M) →ₗ[R] N
    where
  toFun F :=
    { toFun := fun d => d.Sum fun i => F i
      map_add' := (liftAddHom fun x => (F x).toAddMonoidHom).map_add
      map_smul' := fun c f => by simp [sum_smul_index', smul_sum] }
  invFun F x := F.comp (lsingle x)
  left_inv F := by
    ext (x y)
    simp
  right_inv F := by
    ext (x y)
    simp
  map_add' F G := by
    ext (x y)
    simp
  map_smul' F G := by
    ext (x y)
    simp
#align finsupp.lsum Finsupp.lsum

@[simp]
theorem coe_lsum (f : α → M →ₗ[R] N) : (lsum S f : (α →₀ M) → N) = fun d => d.Sum fun i => f i :=
  rfl
#align finsupp.coe_lsum Finsupp.coe_lsum

theorem lsum_apply (f : α → M →ₗ[R] N) (l : α →₀ M) : Finsupp.lsum S f l = l.Sum fun b => f b :=
  rfl
#align finsupp.lsum_apply Finsupp.lsum_apply

theorem lsum_single (f : α → M →ₗ[R] N) (i : α) (m : M) :
    Finsupp.lsum S f (Finsupp.single i m) = f i m :=
  Finsupp.sum_single_index (f i).map_zero
#align finsupp.lsum_single Finsupp.lsum_single

theorem lsum_symm_apply (f : (α →₀ M) →ₗ[R] N) (x : α) : (lsum S).symm f x = f.comp (lsingle x) :=
  rfl
#align finsupp.lsum_symm_apply Finsupp.lsum_symm_apply

end Lsum

section

variable (M) (R) (X : Type _)

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
theorem lift_apply (f) (g) : ((lift M R X) f) g = g.Sum fun x r => r • f x :=
  rfl
#align finsupp.lift_apply Finsupp.lift_apply

end

section LmapDomain

variable {α' : Type _} {α'' : Type _} (M R)

/-- Interpret `finsupp.map_domain` as a linear map. -/
def lmapDomain (f : α → α') : (α →₀ M) →ₗ[R] α' →₀ M
    where
  toFun := mapDomain f
  map_add' a b := mapDomain_add
  map_smul' := mapDomain_smul
#align finsupp.lmap_domain Finsupp.lmapDomain

@[simp]
theorem lmapDomain_apply (f : α → α') (l : α →₀ M) :
    (lmapDomain M R f : (α →₀ M) →ₗ[R] α' →₀ M) l = mapDomain f l :=
  rfl
#align finsupp.lmap_domain_apply Finsupp.lmapDomain_apply

@[simp]
theorem lmapDomain_id : (lmapDomain M R id : (α →₀ M) →ₗ[R] α →₀ M) = LinearMap.id :=
  LinearMap.ext fun l => mapDomain_id
#align finsupp.lmap_domain_id Finsupp.lmapDomain_id

theorem lmapDomain_comp (f : α → α') (g : α' → α'') :
    lmapDomain M R (g ∘ f) = (lmapDomain M R g).comp (lmapDomain M R f) :=
  LinearMap.ext fun l => mapDomain_comp
#align finsupp.lmap_domain_comp Finsupp.lmapDomain_comp

theorem supported_comap_lmapDomain (f : α → α') (s : Set α') :
    supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmapDomain M R f) :=
  fun l (hl : ↑l.support ⊆ f ⁻¹' s) =>
  show ↑(mapDomain f l).support ⊆ s
    by
    rw [← Set.image_subset_iff, ← Finset.coe_image] at hl
    exact Set.Subset.trans map_domain_support hl
#align finsupp.supported_comap_lmap_domain Finsupp.supported_comap_lmapDomain

theorem lmapDomain_supported [Nonempty α] (f : α → α') (s : Set α) :
    (supported M R s).map (lmapDomain M R f) = supported M R (f '' s) :=
  by
  inhabit α
  refine'
    le_antisymm
      (map_le_iff_le_comap.2 <|
        le_trans (supported_mono <| Set.subset_preimage_image _ _)
          (supported_comap_lmap_domain _ _ _ _))
      _
  intro l hl
  refine' ⟨(lmap_domain M R (Function.invFunOn f s) : (α' →₀ M) →ₗ[R] α →₀ M) l, fun x hx => _, _⟩
  · rcases Finset.mem_image.1 (map_domain_support hx) with ⟨c, hc, rfl⟩
    exact Function.invFunOn_mem (by simpa using hl hc)
  · rw [← LinearMap.comp_apply, ← lmap_domain_comp]
    refine' (map_domain_congr fun c hc => _).trans map_domain_id
    exact Function.invFunOn_eq (by simpa using hl hc)
#align finsupp.lmap_domain_supported Finsupp.lmapDomain_supported

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a b «expr ∈ » s) -/
theorem lmapDomain_disjoint_ker (f : α → α') {s : Set α}
    (H : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), f a = f b → a = b) :
    Disjoint (supported M R s) (lmapDomain M R f).ker :=
  by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe, mem_ker, lmap_domain_apply, map_domain] at h₂
  simp; ext x
  haveI := Classical.decPred fun x => x ∈ s
  by_cases xs : x ∈ s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 :=
      by
      rw [h₂]
      rfl
    rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single x] at this
    · simpa [Finsupp.single_apply]
    · intro y hy xy
      simp [mt (H _ (h₁ hy) _ xs) xy]
    · simp (config := { contextual := true })
  · by_contra h
    exact xs (h₁ <| Finsupp.mem_support_iff.2 h)
#align finsupp.lmap_domain_disjoint_ker Finsupp.lmapDomain_disjoint_ker

end LmapDomain

section LcomapDomain

variable {β : Type _} {R M}

/-- Given `f : α → β` and a proof `hf` that `f` is injective, `lcomap_domain f hf` is the linear map
sending  `l : β →₀ M` to the finitely supported function from `α` to `M` given by composing
`l` with `f`.

This is the linear version of `finsupp.comap_domain`. -/
def lcomapDomain (f : α → β) (hf : Function.Injective f) : (β →₀ M) →ₗ[R] α →₀ M
    where
  toFun l := Finsupp.comapDomain f l (hf.InjOn _)
  map_add' x y := by
    ext
    simp
  map_smul' c x := by
    ext
    simp
#align finsupp.lcomap_domain Finsupp.lcomapDomain

end LcomapDomain

section Total

variable (α) {α' : Type _} (M) {M' : Type _} (R) [AddCommMonoid M'] [Module R M'] (v : α → M)
  {v' : α' → M'}

/-- Interprets (l : α →₀ R) as linear combination of the elements in the family (v : α → M) and
    evaluates this linear combination. -/
protected def total : (α →₀ R) →ₗ[R] M :=
  Finsupp.lsum ℕ fun i => LinearMap.id.smul_right (v i)
#align finsupp.total Finsupp.total

variable {α M v}

theorem total_apply (l : α →₀ R) : Finsupp.total α M R v l = l.Sum fun i a => a • v i :=
  rfl
#align finsupp.total_apply Finsupp.total_apply

theorem total_apply_of_mem_supported {l : α →₀ R} {s : Finset α}
    (hs : l ∈ supported R R (↑s : Set α)) : Finsupp.total α M R v l = s.Sum fun i => l i • v i :=
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

theorem total_unique [Unique α] (l : α →₀ R) (v) :
    Finsupp.total α M R v l = l default • v default := by rw [← total_single, ← unique_single l]
#align finsupp.total_unique Finsupp.total_unique

theorem total_surjective (h : Function.Surjective v) :
    Function.Surjective (Finsupp.total α M R v) :=
  by
  intro x
  obtain ⟨y, hy⟩ := h x
  exact ⟨Finsupp.single y 1, by simp [hy]⟩
#align finsupp.total_surjective Finsupp.total_surjective

theorem total_range (h : Function.Surjective v) : (Finsupp.total α M R v).range = ⊤ :=
  range_eq_top.2 <| total_surjective R h
#align finsupp.total_range Finsupp.total_range

/-- Any module is a quotient of a free module. This is stated as surjectivity of
`finsupp.total M M R id : (M →₀ R) →ₗ[R] M`. -/
theorem total_id_surjective (M) [AddCommMonoid M] [Module R M] :
    Function.Surjective (Finsupp.total M M R id) :=
  total_surjective R Function.surjective_id
#align finsupp.total_id_surjective Finsupp.total_id_surjective

theorem range_total : (Finsupp.total α M R v).range = span R (range v) :=
  by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_range] at hx
    rcases hx with ⟨l, hl⟩
    rw [← hl]
    rw [Finsupp.total_apply]
    exact sum_mem fun i hi => Submodule.smul_mem _ _ (subset_span (mem_range_self i))
  · apply span_le.2
    intro x hx
    rcases hx with ⟨i, hi⟩
    rw [SetLike.mem_coe, LinearMap.mem_range]
    use Finsupp.single i 1
    simp [hi]
#align finsupp.range_total Finsupp.range_total

theorem lmapDomain_total (f : α → α') (g : M →ₗ[R] M') (h : ∀ i, g (v i) = v' (f i)) :
    (Finsupp.total α' M' R v').comp (lmapDomain R R f) = g.comp (Finsupp.total α M R v) := by
  ext l <;> simp [total_apply, Finsupp.sum_mapDomain_index, add_smul, h]
#align finsupp.lmap_domain_total Finsupp.lmapDomain_total

theorem total_comp_lmapDomain (f : α → α') :
    (Finsupp.total α' M' R v').comp (Finsupp.lmapDomain R R f) = Finsupp.total α M' R (v' ∘ f) :=
  by
  ext
  simp
#align finsupp.total_comp_lmap_domain Finsupp.total_comp_lmapDomain

@[simp]
theorem total_embDomain (f : α ↪ α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (embDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l := by
  simp [total_apply, Finsupp.sum, support_emb_domain, emb_domain_apply]
#align finsupp.total_emb_domain Finsupp.total_embDomain

@[simp]
theorem total_mapDomain (f : α → α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (mapDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l :=
  LinearMap.congr_fun (total_comp_lmapDomain _ _) l
#align finsupp.total_map_domain Finsupp.total_mapDomain

@[simp]
theorem total_equivMapDomain (f : α ≃ α') (l : α →₀ R) :
    (Finsupp.total α' M' R v') (equivMapDomain f l) = (Finsupp.total α M' R (v' ∘ f)) l := by
  rw [equiv_map_domain_eq_map_domain, total_map_domain]
#align finsupp.total_equiv_map_domain Finsupp.total_equivMapDomain

/-- A version of `finsupp.range_total` which is useful for going in the other direction -/
theorem span_eq_range_total (s : Set M) : span R s = (Finsupp.total s M R coe).range := by
  rw [range_total, Subtype.range_coe_subtype, Set.setOf_mem_eq]
#align finsupp.span_eq_range_total Finsupp.span_eq_range_total

theorem mem_span_iff_total (s : Set M) (x : M) :
    x ∈ span R s ↔ ∃ l : s →₀ R, Finsupp.total s M R coe l = x :=
  (SetLike.ext_iff.1 <| span_eq_range_total _ _) x
#align finsupp.mem_span_iff_total Finsupp.mem_span_iff_total

variable {R}

theorem mem_span_range_iff_exists_finsupp {v : α → M} {x : M} :
    x ∈ span R (range v) ↔ ∃ c : α →₀ R, (c.Sum fun i a => a • v i) = x := by
  simp only [← Finsupp.range_total, LinearMap.mem_range, Finsupp.total_apply]
#align finsupp.mem_span_range_iff_exists_finsupp Finsupp.mem_span_range_iff_exists_finsupp

variable (R)

theorem span_image_eq_map_total (s : Set α) :
    span R (v '' s) = Submodule.map (Finsupp.total α M R v) (supported R R s) :=
  by
  apply span_eq_of_le
  · intro x hx
    rw [Set.mem_image] at hx
    apply Exists.elim hx
    intro i hi
    exact ⟨_, Finsupp.single_mem_supported R 1 hi.1, by simp [hi.2]⟩
  · refine' map_le_iff_le_comap.2 fun z hz => _
    have : ∀ i, z i • v i ∈ span R (v '' s) := by
      intro c
      haveI := Classical.decPred fun x => x ∈ s
      by_cases c ∈ s
      · exact smul_mem _ _ (subset_span (Set.mem_image_of_mem _ h))
      · simp [(Finsupp.mem_supported' R _).1 hz _ h]
    refine' sum_mem _
    simp [this]
#align finsupp.span_image_eq_map_total Finsupp.span_image_eq_map_total

theorem mem_span_image_iff_total {s : Set α} {x : M} :
    x ∈ span R (v '' s) ↔ ∃ l ∈ supported R R s, Finsupp.total α M R v l = x :=
  by
  rw [span_image_eq_map_total]
  simp
#align finsupp.mem_span_image_iff_total Finsupp.mem_span_image_iff_total

theorem total_option (v : Option α → M) (f : Option α →₀ R) :
    Finsupp.total (Option α) M R v f =
      f none • v none + Finsupp.total α M R (v ∘ Option.some) f.some :=
  by rw [total_apply, sum_option_index_smul, total_apply]
#align finsupp.total_option Finsupp.total_option

theorem total_total {α β : Type _} (A : α → M) (B : β → α →₀ R) (f : β →₀ R) :
    Finsupp.total α M R A (Finsupp.total β (α →₀ R) R B f) =
      Finsupp.total β M R (fun b => Finsupp.total α M R A (B b)) f :=
  by
  simp only [total_apply]
  apply induction_linear f
  · simp only [sum_zero_index]
  · intro f₁ f₂ h₁ h₂
    simp [sum_add_index, h₁, h₂, add_smul]
  · simp [sum_single_index, sum_smul_index, smul_sum, mul_smul]
#align finsupp.total_total Finsupp.total_total

@[simp]
theorem total_fin_zero (f : Fin 0 → M) : Finsupp.total (Fin 0) M R f = 0 :=
  by
  ext i
  apply finZeroElim i
#align finsupp.total_fin_zero Finsupp.total_fin_zero

variable (α) (M) (v)

/-- `finsupp.total_on M v s` interprets `p : α →₀ R` as a linear combination of a
subset of the vectors in `v`, mapping it to the span of those vectors.

The subset is indicated by a set `s : set α` of indices.
-/
protected def totalOn (s : Set α) : supported R R s →ₗ[R] span R (v '' s) :=
  LinearMap.codRestrict _ ((Finsupp.total _ _ _ v).comp (Submodule.subtype (supported R R s)))
    fun ⟨l, hl⟩ => (mem_span_image_iff_total _).2 ⟨l, hl, rfl⟩
#align finsupp.total_on Finsupp.totalOn

variable {α} {M} {v}

theorem totalOn_range (s : Set α) : (Finsupp.totalOn α M R v s).range = ⊤ :=
  by
  rw [Finsupp.totalOn, LinearMap.range_eq_map, LinearMap.map_codRestrict, ←
    LinearMap.range_le_iff_comap, range_subtype, map_top, LinearMap.range_comp, range_subtype]
  exact (span_image_eq_map_total _ _).le
#align finsupp.total_on_range Finsupp.totalOn_range

theorem total_comp (f : α' → α) :
    Finsupp.total α' M R (v ∘ f) = (Finsupp.total α M R v).comp (lmapDomain R R f) :=
  by
  ext
  simp [total_apply]
#align finsupp.total_comp Finsupp.total_comp

theorem total_comapDomain (f : α → α') (l : α' →₀ R) (hf : Set.InjOn f (f ⁻¹' ↑l.support)) :
    Finsupp.total α M R v (Finsupp.comapDomain f l hf) =
      (l.support.Preimage f hf).Sum fun i => l (f i) • v i :=
  by rw [Finsupp.total_apply] <;> rfl
#align finsupp.total_comap_domain Finsupp.total_comapDomain

theorem total_onFinset {s : Finset α} {f : α → R} (g : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) :
    Finsupp.total α M R g (Finsupp.onFinset s f hf) = Finset.sum s fun x : α => f x • g x :=
  by
  simp only [Finsupp.total_apply, Finsupp.sum, Finsupp.onFinset_apply, Finsupp.support_onFinset]
  rw [Finset.sum_filter_of_ne]
  intro x hx h
  contrapose! h
  simp [h]
#align finsupp.total_on_finset Finsupp.total_onFinset

end Total

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `finsupp.dom_congr` as a `linear_equiv`.
See also `linear_map.fun_congr_left` for the case of arbitrary functions. -/
protected def domLcongr {α₁ α₂ : Type _} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M :=
  (Finsupp.domCongr e : (α₁ →₀ M) ≃+ (α₂ →₀ M)).toLinearEquiv <| by
    simpa only [equiv_map_domain_eq_map_domain, dom_congr_apply] using (lmap_domain M R e).map_smul
#align finsupp.dom_lcongr Finsupp.domLcongr

@[simp]
theorem domLcongr_apply {α₁ : Type _} {α₂ : Type _} (e : α₁ ≃ α₂) (v : α₁ →₀ M) :
    (Finsupp.domLcongr e : _ ≃ₗ[R] _) v = Finsupp.domCongr e v :=
  rfl
#align finsupp.dom_lcongr_apply Finsupp.domLcongr_apply

@[simp]
theorem domLcongr_refl : Finsupp.domLcongr (Equiv.refl α) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext fun _ => equivMapDomain_refl _
#align finsupp.dom_lcongr_refl Finsupp.domLcongr_refl

theorem domLcongr_trans {α₁ α₂ α₃ : Type _} (f : α₁ ≃ α₂) (f₂ : α₂ ≃ α₃) :
    (Finsupp.domLcongr f).trans (Finsupp.domLcongr f₂) =
      (Finsupp.domLcongr (f.trans f₂) : (_ →₀ M) ≃ₗ[R] _) :=
  LinearEquiv.ext fun _ => (equivMapDomain_trans _ _ _).symm
#align finsupp.dom_lcongr_trans Finsupp.domLcongr_trans

@[simp]
theorem domLcongr_symm {α₁ α₂ : Type _} (f : α₁ ≃ α₂) :
    ((Finsupp.domLcongr f).symm : (_ →₀ M) ≃ₗ[R] _) = Finsupp.domLcongr f.symm :=
  LinearEquiv.ext fun x => rfl
#align finsupp.dom_lcongr_symm Finsupp.domLcongr_symm

@[simp]
theorem domLcongr_single {α₁ : Type _} {α₂ : Type _} (e : α₁ ≃ α₂) (i : α₁) (m : M) :
    (Finsupp.domLcongr e : _ ≃ₗ[R] _) (Finsupp.single i m) = Finsupp.single (e i) m := by
  simp [Finsupp.domLcongr, Finsupp.domCongr, equiv_map_domain_single]
#align finsupp.dom_lcongr_single Finsupp.domLcongr_single

/-- An equivalence of sets induces a linear equivalence of `finsupp`s supported on those sets. -/
noncomputable def congr {α' : Type _} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t :=
  by
  haveI := Classical.decPred fun x => x ∈ s
  haveI := Classical.decPred fun x => x ∈ t
  refine' Finsupp.supportedEquivFinsupp s ≪≫ₗ (_ ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)
  exact Finsupp.domLcongr e
#align finsupp.congr Finsupp.congr

/-- `finsupp.map_range` as a `linear_map`. -/
@[simps]
def mapRange.linearMap (f : M →ₗ[R] N) : (α →₀ M) →ₗ[R] α →₀ N :=
  {
    mapRange.addMonoidHom
      f.toAddMonoidHom with
    toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
    map_smul' := fun c v => mapRange_smul c v (f.map_smul c) }
#align finsupp.map_range.linear_map Finsupp.mapRange.linearMap

@[simp]
theorem mapRange.linearMap_id :
    mapRange.linearMap LinearMap.id = (LinearMap.id : (α →₀ M) →ₗ[R] _) :=
  LinearMap.ext mapRange_id
#align finsupp.map_range.linear_map_id Finsupp.mapRange.linearMap_id

theorem mapRange.linearMap_comp (f : N →ₗ[R] P) (f₂ : M →ₗ[R] N) :
    (mapRange.linearMap (f.comp f₂) : (α →₀ _) →ₗ[R] _) =
      (mapRange.linearMap f).comp (mapRange.linearMap f₂) :=
  LinearMap.ext <| mapRange_comp _ _ _ _ _
#align finsupp.map_range.linear_map_comp Finsupp.mapRange.linearMap_comp

@[simp]
theorem mapRange.linearMap_toAddMonoidHom (f : M →ₗ[R] N) :
    (mapRange.linearMap f).toAddMonoidHom =
      (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ M) →+ _) :=
  AddMonoidHom.ext fun _ => rfl
#align finsupp.map_range.linear_map_to_add_monoid_hom Finsupp.mapRange.linearMap_toAddMonoidHom

/-- `finsupp.map_range` as a `linear_equiv`. -/
@[simps apply]
def mapRange.linearEquiv (e : M ≃ₗ[R] N) : (α →₀ M) ≃ₗ[R] α →₀ N :=
  { mapRange.linearMap e.toLinearMap,
    mapRange.addEquiv e.toAddEquiv with
    toFun := mapRange e e.map_zero
    invFun := mapRange e.symm e.symm.map_zero }
#align finsupp.map_range.linear_equiv Finsupp.mapRange.linearEquiv

@[simp]
theorem mapRange.linearEquiv_refl :
    mapRange.linearEquiv (LinearEquiv.refl R M) = LinearEquiv.refl R (α →₀ M) :=
  LinearEquiv.ext mapRange_id
#align finsupp.map_range.linear_equiv_refl Finsupp.mapRange.linearEquiv_refl

theorem mapRange.linearEquiv_trans (f : M ≃ₗ[R] N) (f₂ : N ≃ₗ[R] P) :
    (mapRange.linearEquiv (f.trans f₂) : (α →₀ _) ≃ₗ[R] _) =
      (mapRange.linearEquiv f).trans (mapRange.linearEquiv f₂) :=
  LinearEquiv.ext <| mapRange_comp _ _ _ _ _
#align finsupp.map_range.linear_equiv_trans Finsupp.mapRange.linearEquiv_trans

@[simp]
theorem mapRange.linearEquiv_symm (f : M ≃ₗ[R] N) :
    ((mapRange.linearEquiv f).symm : (α →₀ _) ≃ₗ[R] _) = mapRange.linearEquiv f.symm :=
  LinearEquiv.ext fun x => rfl
#align finsupp.map_range.linear_equiv_symm Finsupp.mapRange.linearEquiv_symm

@[simp]
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
  (Finsupp.domLcongr e₁).trans (mapRange.linearEquiv e₂)
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
    (lcongr e₁ e₂).symm (Finsupp.single k n) = Finsupp.single (e₁.symm k) (e₂.symm n) :=
  by
  apply_fun lcongr e₁ e₂ using (lcongr e₁ e₂).Injective
  simp
#align finsupp.lcongr_symm_single Finsupp.lcongr_symm_single

@[simp]
theorem lcongr_symm {ι κ : Sort _} (e₁ : ι ≃ κ) (e₂ : M ≃ₗ[R] N) :
    (lcongr e₁ e₂).symm = lcongr e₁.symm e₂.symm :=
  by
  ext
  rfl
#align finsupp.lcongr_symm Finsupp.lcongr_symm

section Sum

variable (R)

/-- The linear equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `linear_equiv` version of `finsupp.sum_finsupp_equiv_prod_finsupp`. -/
@[simps apply symm_apply]
def sumFinsuppLequivProdFinsupp {α β : Type _} : (Sum α β →₀ M) ≃ₗ[R] (α →₀ M) × (β →₀ M) :=
  { sumFinsuppAddEquivProdFinsupp with
    map_smul' := by
      intros
      ext <;>
        simp only [[anonymous], Prod.smul_fst, Prod.smul_snd, smul_apply,
          snd_sum_finsupp_add_equiv_prod_finsupp, fst_sum_finsupp_add_equiv_prod_finsupp,
          RingHom.id_apply] }
#align finsupp.sum_finsupp_lequiv_prod_finsupp Finsupp.sumFinsuppLequivProdFinsupp

theorem fst_sumFinsuppLequivProdFinsupp {α β : Type _} (f : Sum α β →₀ M) (x : α) :
    (sumFinsuppLequivProdFinsupp R f).1 x = f (Sum.inl x) :=
  rfl
#align finsupp.fst_sum_finsupp_lequiv_prod_finsupp Finsupp.fst_sumFinsuppLequivProdFinsupp

theorem snd_sumFinsuppLequivProdFinsupp {α β : Type _} (f : Sum α β →₀ M) (y : β) :
    (sumFinsuppLequivProdFinsupp R f).2 y = f (Sum.inr y) :=
  rfl
#align finsupp.snd_sum_finsupp_lequiv_prod_finsupp Finsupp.snd_sumFinsuppLequivProdFinsupp

theorem sumFinsuppLequivProdFinsupp_symm_inl {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    ((sumFinsuppLequivProdFinsupp R).symm fg) (Sum.inl x) = fg.1 x :=
  rfl
#align finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inl Finsupp.sumFinsuppLequivProdFinsupp_symm_inl

theorem sumFinsuppLequivProdFinsupp_symm_inr {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    ((sumFinsuppLequivProdFinsupp R).symm fg) (Sum.inr y) = fg.2 y :=
  rfl
#align finsupp.sum_finsupp_lequiv_prod_finsupp_symm_inr Finsupp.sumFinsuppLequivProdFinsupp_symm_inr

end Sum

section Sigma

variable {η : Type _} [Fintype η] {ιs : η → Type _} [Zero α]

variable (R)

/-- On a `fintype η`, `finsupp.split` is a linear equivalence between
`(Σ (j : η), ιs j) →₀ M` and `Π j, (ιs j →₀ M)`.

This is the `linear_equiv` version of `finsupp.sigma_finsupp_add_equiv_pi_finsupp`. -/
noncomputable def sigmaFinsuppLequivPiFinsupp {M : Type _} {ιs : η → Type _} [AddCommMonoid M]
    [Module R M] : ((Σj, ιs j) →₀ M) ≃ₗ[R] ∀ j, ιs j →₀ M :=
  { sigmaFinsuppAddEquivPiFinsupp with
    map_smul' := fun c f => by
      ext
      simp }
#align finsupp.sigma_finsupp_lequiv_pi_finsupp Finsupp.sigmaFinsuppLequivPiFinsupp

@[simp]
theorem sigmaFinsuppLequivPiFinsupp_apply {M : Type _} {ιs : η → Type _} [AddCommMonoid M]
    [Module R M] (f : (Σj, ιs j) →₀ M) (j i) : sigmaFinsuppLequivPiFinsupp R f j i = f ⟨j, i⟩ :=
  rfl
#align finsupp.sigma_finsupp_lequiv_pi_finsupp_apply Finsupp.sigmaFinsuppLequivPiFinsupp_apply

@[simp]
theorem sigmaFinsuppLequivPiFinsupp_symm_apply {M : Type _} {ιs : η → Type _} [AddCommMonoid M]
    [Module R M] (f : ∀ j, ιs j →₀ M) (ji) :
    (Finsupp.sigmaFinsuppLequivPiFinsupp R).symm f ji = f ji.1 ji.2 :=
  rfl
#align finsupp.sigma_finsupp_lequiv_pi_finsupp_symm_apply Finsupp.sigmaFinsuppLequivPiFinsupp_symm_apply

end Sigma

section Prod

/-- The linear equivalence between `α × β →₀ M` and `α →₀ β →₀ M`.

This is the `linear_equiv` version of `finsupp.finsupp_prod_equiv`. -/
noncomputable def finsuppProdLequiv {α β : Type _} (R : Type _) {M : Type _} [Semiring R]
    [AddCommMonoid M] [Module R M] : (α × β →₀ M) ≃ₗ[R] α →₀ β →₀ M :=
  {
    finsuppProdEquiv with
    map_add' := fun f g => by
      ext
      simp [finsupp_prod_equiv, curry_apply]
    map_smul' := fun c f => by
      ext
      simp [finsupp_prod_equiv, curry_apply] }
#align finsupp.finsupp_prod_lequiv Finsupp.finsuppProdLequiv

@[simp]
theorem finsuppProdLequiv_apply {α β R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α × β →₀ M) (x y) : finsuppProdLequiv R f x y = f (x, y) := by
  rw [finsupp_prod_lequiv, LinearEquiv.coe_mk, finsupp_prod_equiv, Finsupp.curry_apply]
#align finsupp.finsupp_prod_lequiv_apply Finsupp.finsuppProdLequiv_apply

@[simp]
theorem finsuppProdLequiv_symm_apply {α β R M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]
    (f : α →₀ β →₀ M) (xy) : (finsuppProdLequiv R).symm f xy = f xy.1 xy.2 := by
  conv_rhs =>
    rw [← (finsupp_prod_lequiv R).apply_symm_apply f, finsupp_prod_lequiv_apply, Prod.mk.eta]
#align finsupp.finsupp_prod_lequiv_symm_apply Finsupp.finsuppProdLequiv_symm_apply

end Prod

end Finsupp

section Fintype

variable {α M : Type _} (R : Type _) [Fintype α] [Semiring R] [AddCommMonoid M] [Module R M]

variable (S : Type _) [Semiring S] [Module S M] [SMulCommClass R S M]

variable (v : α → M)

/-- `fintype.total R S v f` is the linear combination of vectors in `v` with weights in `f`.
This variant of `finsupp.total` is defined on fintype indexed vectors.

This map is linear in `v` if `R` is commutative, and always linear in `f`.
See note [bundled maps over different rings] for why separate `R` and `S` semirings are used.
-/
protected def Fintype.total : (α → M) →ₗ[S] (α → R) →ₗ[R] M
    where
  toFun v :=
    { toFun := fun f => ∑ i, f i • v i
      map_add' := fun f g => by
        simp_rw [← Finset.sum_add_distrib, ← add_smul]
        rfl
      map_smul' := fun r f => by
        simp_rw [Finset.smul_sum, smul_smul]
        rfl }
  map_add' u v := by
    ext
    simp [Finset.sum_add_distrib, Pi.add_apply, smul_add]
  map_smul' r v := by
    ext
    simp [Finset.smul_sum, smul_comm _ r]
#align fintype.total Fintype.total

variable {S}

theorem Fintype.total_apply (f) : Fintype.total R S v f = ∑ i, f i • v i :=
  rfl
#align fintype.total_apply Fintype.total_apply

@[simp]
theorem Fintype.total_apply_single (i : α) (r : R) :
    Fintype.total R S v (Pi.single i r) = r • v i :=
  by
  simp_rw [Fintype.total_apply, Pi.single_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
#align fintype.total_apply_single Fintype.total_apply_single

variable (S)

theorem Finsupp.total_eq_fintype_total_apply (x : α → R) :
    Finsupp.total α M R v ((Finsupp.linearEquivFunOnFinite R R α).symm x) = Fintype.total R S v x :=
  by
  apply Finset.sum_subset
  · exact Finset.subset_univ _
  · intro x _ hx
    rw [finsupp.not_mem_support_iff.mp hx]
    exact zero_smul _ _
#align finsupp.total_eq_fintype_total_apply Finsupp.total_eq_fintype_total_apply

theorem Finsupp.total_eq_fintype_total :
    (Finsupp.total α M R v).comp (Finsupp.linearEquivFunOnFinite R R α).symm.toLinearMap =
      Fintype.total R S v :=
  LinearMap.ext <| Finsupp.total_eq_fintype_total_apply R S v
#align finsupp.total_eq_fintype_total Finsupp.total_eq_fintype_total

variable {S}

@[simp]
theorem Fintype.range_total : (Fintype.total R S v).range = Submodule.span R (Set.range v) := by
  rw [← Finsupp.total_eq_fintype_total, LinearMap.range_comp, LinearEquiv.toLinearMap_eq_coe,
    LinearEquiv.range, Submodule.map_top, Finsupp.range_total]
#align fintype.range_total Fintype.range_total

section SpanRange

variable {v} {x : M}

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem mem_span_range_iff_exists_fun : x ∈ span R (range v) ↔ ∃ c : α → R, (∑ i, c i • v i) = x :=
  by
  simp only [Finsupp.mem_span_range_iff_exists_finsupp,
    finsupp.equiv_fun_on_finite.surjective.exists, Finsupp.equivFunOnFinite_apply]
  exact exists_congr fun c => Eq.congr_left <| Finsupp.sum_fintype _ _ fun i => zero_smul _ _
#align mem_span_range_iff_exists_fun mem_span_range_iff_exists_fun

/-- A family `v : α → V` is generating `V` iff every element `(x : V)`
can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem top_le_span_range_iff_forall_exists_fun :
    ⊤ ≤ span R (range v) ↔ ∀ x, ∃ c : α → R, (∑ i, c i • v i) = x :=
  by
  simp_rw [← mem_span_range_iff_exists_fun]
  exact ⟨fun h x => h trivial, fun h x _ => h x⟩
#align top_le_span_range_iff_forall_exists_fun top_le_span_range_iff_forall_exists_fun

end SpanRange

end Fintype

variable {R : Type _} {M : Type _} {N : Type _}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section

variable (R)

/-- Pick some representation of `x : span R w` as a linear combination in `w`,
using the axiom of choice.
-/
irreducible_def Span.repr (w : Set M) (x : span R w) : w →₀ R :=
  ((Finsupp.mem_span_iff_total _ _ _).mp x.2).some
#align span.repr Span.repr

@[simp]
theorem Span.finsupp_total_repr {w : Set M} (x : span R w) :
    Finsupp.total w M R coe (Span.repr R w x) = x :=
  by
  rw [Span.repr]
  exact ((Finsupp.mem_span_iff_total _ _ _).mp x.2).choose_spec
#align span.finsupp_total_repr Span.finsupp_total_repr

end

protected theorem Submodule.finsupp_sum_mem {ι β : Type _} [Zero β] (S : Submodule R M) (f : ι →₀ β)
    (g : ι → β → M) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.Sum g ∈ S :=
  AddSubmonoidClass.finsupp_sum_mem S f g h
#align submodule.finsupp_sum_mem Submodule.finsupp_sum_mem

theorem LinearMap.map_finsupp_total (f : M →ₗ[R] N) {ι : Type _} {g : ι → M} (l : ι →₀ R) :
    f (Finsupp.total ι M R g l) = Finsupp.total ι N R (f ∘ g) l := by
  simp only [Finsupp.total_apply, Finsupp.total_apply, Finsupp.sum, f.map_sum, f.map_smul]
#align linear_map.map_finsupp_total LinearMap.map_finsupp_total

theorem Submodule.exists_finset_of_mem_supᵢ {ι : Sort _} (p : ι → Submodule R M) {m : M}
    (hm : m ∈ ⨆ i, p i) : ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i :=
  by
  have :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_supᵢ (Submodule R M)
      (Submodule.singleton_span_isCompactElement m) p
  simp only [Submodule.span_singleton_le_iff_mem] at this
  exact this hm
#align submodule.exists_finset_of_mem_supr Submodule.exists_finset_of_mem_supᵢ

/-- `submodule.exists_finset_of_mem_supr` as an `iff` -/
theorem Submodule.mem_supᵢ_iff_exists_finset {ι : Sort _} {p : ι → Submodule R M} {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∃ s : Finset ι, m ∈ ⨆ i ∈ s, p i :=
  ⟨Submodule.exists_finset_of_mem_supᵢ p, fun ⟨_, hs⟩ =>
    supᵢ_mono (fun i => (supᵢ_const_le : _ ≤ p i)) hs⟩
#align submodule.mem_supr_iff_exists_finset Submodule.mem_supᵢ_iff_exists_finset

theorem mem_span_finset {s : Finset M} {x : M} :
    x ∈ span R (↑s : Set M) ↔ ∃ f : M → R, (∑ i in s, f i • i) = x :=
  ⟨fun hx =>
    let ⟨v, hvs, hvx⟩ :=
      (Finsupp.mem_span_image_iff_total _).1
        (show x ∈ span R (id '' (↑s : Set M)) by rwa [Set.image_id])
    ⟨v, hvx ▸ (Finsupp.total_apply_of_mem_supported _ hvs).symm⟩,
    fun ⟨f, hf⟩ => hf ▸ sum_mem fun i hi => smul_mem _ _ <| subset_span hi⟩
#align mem_span_finset mem_span_finset

/-- An element `m ∈ M` is contained in the `R`-submodule spanned by a set `s ⊆ M`, if and only if
`m` can be written as a finite `R`-linear combination of elements of `s`.
The implementation uses `finsupp.sum`. -/
theorem mem_span_set {m : M} {s : Set M} :
    m ∈ Submodule.span R s ↔
      ∃ c : M →₀ R, (c.support : Set M) ⊆ s ∧ (c.Sum fun mi r => r • mi) = m :=
  by
  conv_lhs => rw [← Set.image_id s]
  simp_rw [← exists_prop]
  exact Finsupp.mem_span_image_iff_total R
#align mem_span_set mem_span_set

/-- If `subsingleton R`, then `M ≃ₗ[R] ι →₀ R` for any type `ι`. -/
@[simps]
def Module.subsingletonEquiv (R M ι : Type _) [Semiring R] [Subsingleton R] [AddCommMonoid M]
    [Module R M] : M ≃ₗ[R] ι →₀ R where
  toFun m := 0
  invFun f := 0
  left_inv m := by
    letI := Module.subsingleton R M
    simp only [eq_iff_true_of_subsingleton]
  right_inv f := by simp only [eq_iff_true_of_subsingleton]
  map_add' m n := (add_zero 0).symm
  map_smul' r m := (smul_zero r).symm
#align module.subsingleton_equiv Module.subsingletonEquiv

namespace LinearMap

variable {R M} {α : Type _}

open Finsupp Function

-- See also `linear_map.splitting_of_fun_on_fintype_surjective`
/-- A surjective linear map to finitely supported functions has a splitting. -/
def splittingOfFinsuppSurjective (f : M →ₗ[R] α →₀ R) (s : Surjective f) : (α →₀ R) →ₗ[R] M :=
  Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).some
#align linear_map.splitting_of_finsupp_surjective LinearMap.splittingOfFinsuppSurjective

theorem splittingOfFinsuppSurjective_splits (f : M →ₗ[R] α →₀ R) (s : Surjective f) :
    f.comp (splittingOfFinsuppSurjective f s) = LinearMap.id :=
  by
  ext (x y)
  dsimp [splitting_of_finsupp_surjective]
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
  (leftInverse_splittingOfFinsuppSurjective f s).Injective
#align linear_map.splitting_of_finsupp_surjective_injective LinearMap.splittingOfFinsuppSurjective_injective

-- See also `linear_map.splitting_of_finsupp_surjective`
/-- A surjective linear map to functions on a finite type has a splitting. -/
def splittingOfFunOnFintypeSurjective [Fintype α] (f : M →ₗ[R] α → R) (s : Surjective f) :
    (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).some).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap
#align linear_map.splitting_of_fun_on_fintype_surjective LinearMap.splittingOfFunOnFintypeSurjective

theorem splittingOfFunOnFintypeSurjective_splits [Fintype α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.id :=
  by
  ext (x y)
  dsimp [splitting_of_fun_on_fintype_surjective]
  rw [linear_equiv_fun_on_finite_symm_single, Finsupp.sum_single_index, one_smul,
    (s (Finsupp.single x 1)).choose_spec, Finsupp.single_eq_pi_single]
  rw [zero_smul]
#align linear_map.splitting_of_fun_on_fintype_surjective_splits LinearMap.splittingOfFunOnFintypeSurjective_splits

theorem leftInverse_splittingOfFunOnFintypeSurjective [Fintype α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g
#align linear_map.left_inverse_splitting_of_fun_on_fintype_surjective LinearMap.leftInverse_splittingOfFunOnFintypeSurjective

theorem splittingOfFunOnFintypeSurjective_injective [Fintype α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s) :=
  (leftInverse_splittingOfFunOnFintypeSurjective f s).Injective
#align linear_map.splitting_of_fun_on_fintype_surjective_injective LinearMap.splittingOfFunOnFintypeSurjective_injective

end LinearMap

