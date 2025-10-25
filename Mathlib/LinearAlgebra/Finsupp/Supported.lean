/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Span.Defs

/-!
# `Finsupp`s supported on a given submodule

* `Finsupp.restrictDom`: `Finsupp.filter` as a linear map to `Finsupp.supported s`;
  `Finsupp.supported R R s` and codomain `Submodule.span R (v '' s)`;
* `Finsupp.supportedEquivFinsupp`: a linear equivalence between the functions `α →₀ M` supported
  on `s` and the functions `s →₀ M`;
* `Finsupp.domLCongr`: a `LinearEquiv` version of `Finsupp.domCongr`;
* `Finsupp.congr`: if the sets `s` and `t` are equivalent, then `supported M R s` is equivalent to
  `supported M R t`;

## Tags

function with finite support, module, linear algebra
-/

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

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
  smul_mem' _ _ hp := Subset.trans (Finset.coe_subset.2 support_smul) hp

variable {M}

theorem mem_supported {s : Set α} (p : α →₀ M) : p ∈ supported M R s ↔ ↑p.support ⊆ s :=
  Iff.rfl

theorem mem_supported' {s : Set α} (p : α →₀ M) :
    p ∈ supported M R s ↔ ∀ x ∉ s, p x = 0 := by
  simp [mem_supported, Set.subset_def, not_imp_comm]

theorem mem_supported_support (p : α →₀ M) : p ∈ Finsupp.supported M R (p.support : Set α) := by
  rw [Finsupp.mem_supported]

theorem single_mem_supported {s : Set α} {a : α} (b : M) (h : a ∈ s) :
    single a b ∈ supported M R s :=
  Set.Subset.trans support_single_subset (Finset.singleton_subset_set_iff.2 h)

theorem supported_eq_span_single (s : Set α) :
    supported R R s = span R ((fun i => single i 1) '' s) := by
  refine (span_eq_of_le _ ?_ (SetLike.le_def.2 fun l hl => ?_)).symm
  · rintro _ ⟨_, hp, rfl⟩
    exact single_mem_supported R 1 hp
  · rw [← l.sum_single]
    refine sum_mem fun i il => ?_
    rw [show single i (l i) = l i • single i 1 by simp]
    exact smul_mem _ (l i) (subset_span (mem_image_of_mem _ (hl il)))

theorem span_le_supported_biUnion_support (s : Set (α →₀ M)) :
    span R s ≤ supported M R (⋃ x ∈ s, x.support) :=
  span_le.mpr fun _ h ↦ subset_biUnion_of_mem h (u := (SetLike.coe ·.support))

variable (M)

/-- Interpret `Finsupp.filter s` as a linear map from `α →₀ M` to `supported M R s`. -/
def restrictDom (s : Set α) [DecidablePred (· ∈ s)] : (α →₀ M) →ₗ[R] supported M R s :=
  LinearMap.codRestrict _
    { toFun := filter (· ∈ s)
      map_add' := fun _ _ => filter_add
      map_smul' := fun _ _ => filter_smul } fun l =>
    (mem_supported' _ _).2 fun _ => filter_apply_neg (· ∈ s) l

variable {M R}

section

@[simp]
theorem restrictDom_apply (s : Set α) (l : α →₀ M) [DecidablePred (· ∈ s)] :
    (restrictDom M R s l : α →₀ M) = Finsupp.filter (· ∈ s) l := rfl

end

theorem restrictDom_comp_subtype (s : Set α) [DecidablePred (· ∈ s)] :
    (restrictDom M R s).comp (Submodule.subtype _) = LinearMap.id := by
  ext l a
  by_cases h : a ∈ s
  · simp [h]
  simpa [h] using ((mem_supported' R l.1).1 l.2 a h).symm

theorem range_restrictDom (s : Set α) [DecidablePred (· ∈ s)] :
    LinearMap.range (restrictDom M R s) = ⊤ :=
  range_eq_top.2 <|
    Function.RightInverse.surjective <| LinearMap.congr_fun (restrictDom_comp_subtype s)

theorem supported_mono {s t : Set α} (st : s ⊆ t) : supported M R s ≤ supported M R t := fun _ h =>
  Set.Subset.trans h st

@[simp]
theorem supported_empty : supported M R (∅ : Set α) = ⊥ :=
  eq_bot_iff.2 fun l h => (Submodule.mem_bot R).2 <| by ext; simp_all [mem_supported']

@[simp]
theorem supported_univ : supported M R (Set.univ : Set α) = ⊤ :=
  eq_top_iff.2 fun _ _ => Set.subset_univ _

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
  induction l using Finsupp.induction with
  | zero => exact zero_mem _
  | single_add x a l _ _ ih =>
    refine add_mem ?_ ih
    by_cases h : ∃ i, x ∈ s i
    · simp only [mem_comap, coe_comp, coe_subtype, Function.comp_apply, restrictDom_apply,
        mem_iUnion, h, filter_single_of_pos]
      obtain ⟨i, hi⟩ := h
      exact le_iSup (fun i => supported M R (s i)) i (single_mem_supported R _ hi)
    · simp [h]

theorem supported_union (s t : Set α) :
    supported M R (s ∪ t) = supported M R s ⊔ supported M R t := by
  rw [Set.union_eq_iUnion, supported_iUnion, iSup_bool_eq, cond_true, cond_false]

theorem supported_iInter {ι : Type*} (s : ι → Set α) :
    supported M R (⋂ i, s i) = ⨅ i, supported M R (s i) :=
  Submodule.ext fun x => by simp [mem_supported, subset_iInter_iff]

theorem supported_inter (s t : Set α) :
    supported M R (s ∩ t) = supported M R s ⊓ supported M R t := by
  rw [Set.inter_eq_iInter, supported_iInter, iInf_bool_eq]; rfl

theorem disjoint_supported_supported {s t : Set α} (h : Disjoint s t) :
    Disjoint (supported M R s) (supported M R t) :=
  disjoint_iff.2 <| by rw [← supported_inter, disjoint_iff_inter_eq_empty.1 h, supported_empty]

theorem disjoint_supported_supported_iff [Nontrivial M] {s t : Set α} :
    Disjoint (supported M R s) (supported M R t) ↔ Disjoint s t := by
  refine ⟨fun h => Set.disjoint_left.mpr fun x hx1 hx2 => ?_, disjoint_supported_supported⟩
  rcases exists_ne (0 : M) with ⟨y, hy⟩
  have := h.le_bot ⟨single_mem_supported R y hx1, single_mem_supported R y hx2⟩
  rw [mem_bot, single_eq_zero] at this
  exact hy this

lemma codisjoint_supported_supported {s t : Set α} (h : Codisjoint s t) :
    Codisjoint (supported M R s) (supported M R t) := by
  rw [codisjoint_iff, eq_top_iff, ← supported_union,
    show s ∪ t = .univ from codisjoint_iff.mp h, supported_univ]

/-- Interpret `Finsupp.restrictSupportEquiv` as a linear equivalence between
`supported M R s` and `s →₀ M`. -/
@[simps!] def supportedEquivFinsupp (s : Set α) : supported M R s ≃ₗ[R] s →₀ M := by
  let F : supported M R s ≃ (s →₀ M) := restrictSupportEquiv s M
  refine F.toLinearEquiv ?_
  have :
    (F : supported M R s → ↥s →₀ M) =
      (lsubtypeDomain s : (α →₀ M) →ₗ[R] s →₀ M).comp (Submodule.subtype (supported M R s)) :=
    rfl
  rw [this]
  exact LinearMap.isLinear _

@[simp] theorem supportedEquivFinsupp_symm_apply_coe (s : Set α) [DecidablePred (· ∈ s)]
    (f : s →₀ M) : (supportedEquivFinsupp (R := R) s).symm f = f.extendDomain := by
  convert restrictSupportEquiv_symm_apply_coe ..

@[simp] theorem supportedEquivFinsupp_symm_single (s : Set α) (i : s) (a : M) :
    ((supportedEquivFinsupp (R := R) s).symm (single i a) : α →₀ M) = single ↑i a := by
  classical simp

section LMapDomain

variable {α' : Type*} {α'' : Type*} (M R)

theorem supported_comap_lmapDomain (f : α → α') (s : Set α') :
    supported M R (f ⁻¹' s) ≤ (supported M R s).comap (lmapDomain M R f) := by
  classical
  intro l (hl : (l.support : Set α) ⊆ f ⁻¹' s)
  change ↑(mapDomain f l).support ⊆ s
  rw [← Set.image_subset_iff, ← Finset.coe_image] at hl
  exact Set.Subset.trans mapDomain_support hl

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

theorem lmapDomain_disjoint_ker (f : α → α') {s : Set α}
    (H : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    Disjoint (supported M R s) (ker (lmapDomain M R f)) := by
  rw [disjoint_iff_inf_le]
  rintro l ⟨h₁, h₂⟩
  rw [SetLike.mem_coe, mem_ker, lmapDomain_apply, mapDomain] at h₂
  simp only [mem_bot]; ext x
  haveI := Classical.decPred fun x => x ∈ s
  by_cases xs : x ∈ s
  · have : Finsupp.sum l (fun a => Finsupp.single (f a)) (f x) = 0 := by
      rw [h₂]
      rfl
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single x, single_eq_same] at this
    · simpa
    · intro y hy xy
      simp only [SetLike.mem_coe, mem_supported, subset_def, mem_support_iff] at h₁
      simp [mt (H _ (h₁ _ hy) _ xs) xy]
    · simp +contextual
  · by_contra h
    exact xs (h₁ <| Finsupp.mem_support_iff.2 h)

end LMapDomain

/-- An equivalence of sets induces a linear equivalence of `Finsupp`s supported on those sets. -/
noncomputable def congr {α' : Type*} (s : Set α) (t : Set α') (e : s ≃ t) :
    supported M R s ≃ₗ[R] supported M R t := by
  haveI := Classical.decPred fun x => x ∈ s
  haveI := Classical.decPred fun x => x ∈ t
  exact Finsupp.supportedEquivFinsupp s ≪≫ₗ
    (Finsupp.domLCongr e ≪≫ₗ (Finsupp.supportedEquivFinsupp t).symm)

end Finsupp
