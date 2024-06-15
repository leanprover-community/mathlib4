/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import Mathlib.Algebra.GroupWithZero.Indicator
import Mathlib.Algebra.Module.Basic
import Mathlib.Topology.Separation

#align_import topology.support from "leanprover-community/mathlib"@"d90e4e186f1d18e375dcd4e5b5f6364b01cb3e46"

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `tsupport f`, as the closure of
the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `mulTSupport` & `tsupport`
* `HasCompactMulSupport` & `HasCompactSupport`

## Implementation Notes

* We write all lemmas for multiplicative functions, and use `@[to_additive]` to get the more common
  additive versions.
* We do not put the definitions in the `Function` namespace, following many other topological
  definitions that are in the root namespace (compare `Embedding` vs `Function.Embedding`).
-/


open Function Set Filter Topology

variable {X α α' β γ δ M E R : Type*}

section One

variable [One α] [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive " The topological support of a function is the closure of its support. i.e. the
closure of the set of all elements where the function is nonzero. "]
def mulTSupport (f : X → α) : Set X := closure (mulSupport f)
#align mul_tsupport mulTSupport
#align tsupport tsupport

@[to_additive]
theorem subset_mulTSupport (f : X → α) : mulSupport f ⊆ mulTSupport f :=
  subset_closure
#align subset_mul_tsupport subset_mulTSupport
#align subset_tsupport subset_tsupport

@[to_additive]
theorem isClosed_mulTSupport (f : X → α) : IsClosed (mulTSupport f) :=
  isClosed_closure
#align is_closed_mul_tsupport isClosed_mulTSupport
#align is_closed_tsupport isClosed_tsupport

@[to_additive]
theorem mulTSupport_eq_empty_iff {f : X → α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport, closure_empty_iff, mulSupport_eq_empty_iff]
#align mul_tsupport_eq_empty_iff mulTSupport_eq_empty_iff
#align tsupport_eq_empty_iff tsupport_eq_empty_iff

@[to_additive]
theorem image_eq_one_of_nmem_mulTSupport {f : X → α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx
#align image_eq_one_of_nmem_mul_tsupport image_eq_one_of_nmem_mulTSupport
#align image_eq_zero_of_nmem_tsupport image_eq_zero_of_nmem_tsupport

@[to_additive]
theorem range_subset_insert_image_mulTSupport (f : X → α) :
    range f ⊆ insert 1 (f '' mulTSupport f) :=
  (range_subset_insert_image_mulSupport f).trans <|
    insert_subset_insert <| image_subset _ subset_closure
#align range_subset_insert_image_mul_tsupport range_subset_insert_image_mulTSupport
#align range_subset_insert_image_tsupport range_subset_insert_image_tsupport

@[to_additive]
theorem range_eq_image_mulTSupport_or (f : X → α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)
#align range_eq_image_mul_tsupport_or range_eq_image_mulTSupport_or
#align range_eq_image_tsupport_or range_eq_image_tsupport_or

theorem tsupport_mul_subset_left {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)
#align tsupport_mul_subset_left tsupport_mul_subset_left

theorem tsupport_mul_subset_right {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)
#align tsupport_mul_subset_right tsupport_mul_subset_right

end One

theorem tsupport_smul_subset_left {M α} [TopologicalSpace X] [Zero M] [Zero α] [SMulWithZero M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g
#align tsupport_smul_subset_left tsupport_smul_subset_left

theorem tsupport_smul_subset_right {M α} [TopologicalSpace X] [Zero α] [SMulZeroClass M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport g :=
  closure_mono <| support_smul_subset_right f g

@[to_additive]
theorem mulTSupport_mul [TopologicalSpace X] [Monoid α] {f g : X → α} :
    (mulTSupport fun x ↦ f x * g x) ⊆ mulTSupport f ∪ mulTSupport g :=
  closure_minimal
    ((mulSupport_mul f g).trans (union_subset_union (subset_mulTSupport _) (subset_mulTSupport _)))
    (isClosed_closure.union isClosed_closure)

section

variable [TopologicalSpace α] [TopologicalSpace α']
variable [One β] [One γ] [One δ]
variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

@[to_additive]
theorem not_mem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]
#align not_mem_mul_tsupport_iff_eventually_eq not_mem_mulTSupport_iff_eventuallyEq
#align not_mem_tsupport_iff_eventually_eq not_mem_tsupport_iff_eventuallyEq

@[to_additive]
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α → β}
    (hf : ∀ x ∈ mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (not_mem_mulTSupport_iff_eventuallyEq.mp hx).symm
#align continuous_of_mul_tsupport continuous_of_mulTSupport
#align continuous_of_tsupport continuous_of_tsupport

end

/-! ## Functions with compact support -/
section CompactSupport
variable [TopologicalSpace α] [TopologicalSpace α']
variable [One β] [One γ] [One δ]
variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive " A function `f` *has compact support* or is *compactly supported* if the closure of
the support of `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a
compact set. "]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)
#align has_compact_mul_support HasCompactMulSupport
#align has_compact_support HasCompactSupport

@[to_additive]
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl
#align has_compact_mul_support_def hasCompactMulSupport_def
#align has_compact_support_def hasCompactSupport_def

@[to_additive]
theorem exists_compact_iff_hasCompactMulSupport [R1Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ x, x ∉ K → f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]
#align exists_compact_iff_has_compact_mul_support exists_compact_iff_hasCompactMulSupport
#align exists_compact_iff_has_compact_support exists_compact_iff_hasCompactSupport

namespace HasCompactMulSupport
@[to_additive]
theorem intro [R1Space α] {K : Set α} (hK : IsCompact K)
    (hfK : ∀ x, x ∉ K → f x = 1) : HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩
#align has_compact_mul_support.intro HasCompactMulSupport.intro
#align has_compact_support.intro HasCompactSupport.intro

@[to_additive]
theorem intro' {K : Set α} (hK : IsCompact K) (h'K : IsClosed K)
    (hfK : ∀ x, x ∉ K → f x = 1) : HasCompactMulSupport f := by
  have : mulTSupport f ⊆ K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK ( isClosed_mulTSupport f) this

@[to_additive]
theorem of_mulSupport_subset_isCompact [R1Space α] {K : Set α}
    (hK : IsCompact K) (h : mulSupport f ⊆ K) : HasCompactMulSupport f :=
  hK.closure_of_subset h

@[to_additive]
theorem isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) :=
  hf
#align has_compact_mul_support.is_compact HasCompactMulSupport.isCompact
#align has_compact_support.is_compact HasCompactSupport.isCompact

@[to_additive]
theorem _root_.hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  mem_coclosedCompact_iff.symm
#align has_compact_mul_support_iff_eventually_eq hasCompactMulSupport_iff_eventuallyEq
#align has_compact_support_iff_eventually_eq hasCompactSupport_iff_eventuallyEq

@[to_additive]
theorem _root_.isCompact_range_of_mulSupport_subset_isCompact [TopologicalSpace β]
    (hf : Continuous f) {k : Set α} (hk : IsCompact k) (h'f : mulSupport f ⊆ k) :
    IsCompact (range f) := by
  cases' range_eq_image_or_of_mulSupport_subset h'f with h2 h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]
theorem isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)
#align has_compact_mul_support.is_compact_range HasCompactMulSupport.isCompact_range
#align has_compact_support.is_compact_range HasCompactSupport.isCompact_range

@[to_additive]
theorem mono' {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulTSupport f) : HasCompactMulSupport f' :=
  IsCompact.of_isClosed_subset hf isClosed_closure <| closure_minimal hff' isClosed_closure
#align has_compact_mul_support.mono' HasCompactMulSupport.mono'
#align has_compact_support.mono' HasCompactSupport.mono'

@[to_additive]
theorem mono {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulSupport f) : HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure
#align has_compact_mul_support.mono HasCompactMulSupport.mono
#align has_compact_support.mono HasCompactSupport.mono

@[to_additive]
theorem comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mulSupport_comp_subset hg f
#align has_compact_mul_support.comp_left HasCompactMulSupport.comp_left
#align has_compact_support.comp_left HasCompactSupport.comp_left

@[to_additive]
theorem _root_.hasCompactMulSupport_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]
#align has_compact_mul_support_comp_left hasCompactMulSupport_comp_left
#align has_compact_support_comp_left hasCompactSupport_comp_left

@[to_additive]
theorem comp_closedEmbedding (hf : HasCompactMulSupport f) {g : α' → α}
    (hg : ClosedEmbedding g) : HasCompactMulSupport (f ∘ g) := by
  rw [hasCompactMulSupport_def, Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.toEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)
#align has_compact_mul_support.comp_closed_embedding HasCompactMulSupport.comp_closedEmbedding
#align has_compact_support.comp_closed_embedding HasCompactSupport.comp_closedEmbedding

@[to_additive]
theorem comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  #adaptation_note /-- `nightly-2024-03-11`
  If we *either* (1) remove the type annotations on the
  binders in the following `fun` or (2) revert `simp only` to `simp_rw`, `to_additive` fails
  because an `OfNat.ofNat 1` is not replaced with `0`. Notably, as of this nightly, what used to
  look like `OfNat.ofNat (nat_lit 1) x` in the proof term now looks like
  `OfNat.ofNat (OfNat.ofNat (α := ℕ) (nat_lit 1)) x`, and this seems to trip up `to_additive`.
  -/
  filter_upwards [hf, hf₂] using fun x (hx : f x = (1 : α → β) x) (hx₂ : f₂ x = (1 : α → γ) x) => by
    simp only [hx, hx₂, Pi.one_apply, hm]
#align has_compact_mul_support.comp₂_left HasCompactMulSupport.comp₂_left
#align has_compact_support.comp₂_left HasCompactSupport.comp₂_left

@[to_additive]
lemma isCompact_preimage [TopologicalSpace β]
    (h'f : HasCompactMulSupport f) (hf : Continuous f) {k : Set β} (hk : IsClosed k)
    (h'k : 1 ∉ k) : IsCompact (f ⁻¹' k) := by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx ↦ ?_)
  apply subset_mulTSupport
  aesop

variable [T2Space α'] (hf : HasCompactMulSupport f) {g : α → α'} (cont : Continuous g)

@[to_additive]
theorem mulTSupport_extend_one_subset :
    mulTSupport (g.extend f 1) ⊆ g '' mulTSupport f :=
  (hf.image cont).isClosed.closure_subset_iff.mpr <|
    mulSupport_extend_one_subset.trans (image_subset g subset_closure)

@[to_additive]
theorem extend_one : HasCompactMulSupport (g.extend f 1) :=
  HasCompactMulSupport.of_mulSupport_subset_isCompact (hf.image cont)
    (subset_closure.trans <| hf.mulTSupport_extend_one_subset cont)

@[to_additive]
theorem mulTSupport_extend_one (inj : g.Injective) :
    mulTSupport (g.extend f 1) = g '' mulTSupport f :=
  (hf.mulTSupport_extend_one_subset cont).antisymm <|
    (image_closure_subset_closure_image cont).trans
      (closure_mono (mulSupport_extend_one inj).superset)

@[to_additive]
theorem continuous_extend_one [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f : U → β}
    (cont : Continuous f) (supp : HasCompactMulSupport f) :
    Continuous (Subtype.val.extend f 1) :=
  continuous_of_mulTSupport fun x h ↦ by
    rw [show x = ↑(⟨x, Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl,
      ← (hU.openEmbedding_subtype_val).continuousAt_iff, extend_comp Subtype.val_injective]
    exact cont.continuousAt

end HasCompactMulSupport

end CompactSupport

/-! ## Functions with compact support: algebraic operations -/
section CompactSupport2
section Monoid

variable [TopologicalSpace α] [Monoid β]
variable {f f' : α → β} {x : α}

@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := hf.comp₂_left hf' (mul_one 1)
#align has_compact_mul_support.mul HasCompactMulSupport.mul
#align has_compact_support.add HasCompactSupport.add

end Monoid

section DistribMulAction

variable [TopologicalSpace α] [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left HasCompactSupport.smul_left

end DistribMulAction

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]
variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]
#align has_compact_support.smul_right HasCompactSupport.smul_right

theorem HasCompactSupport.smul_left' (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left' HasCompactSupport.smul_left'

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]
variable {f f' : α → β} {x : α}

theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]
#align has_compact_support.mul_right HasCompactSupport.mul_right

theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]
#align has_compact_support.mul_left HasCompactSupport.mul_left

end MulZeroClass

end CompactSupport2

section LocallyFinite

variable {ι : Type*} [TopologicalSpace X]

-- Porting note (#11215): TODO: reformulate for any locally finite family of sets
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive " If a family of functions `f` has locally-finite support, subordinate to a family of
open sets, then for any point we can find a neighbourhood on which only finitely-many members of `f`
are non-zero. "]
theorem LocallyFinite.exists_finset_nhd_mulSupport_subset {U : ι → Set X} [One R] {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι), ∃ n, n ∈ 𝓝 x ∧ (n ⊆ ⋂ i ∈ is, U i) ∧
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is := by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := hnf.toFinset.filter fun i => x ∈ U i
    let js := hnf.toFinset.filter fun j => x ∉ U j
    refine
      ⟨is, (n ∩ ⋂ j ∈ js, (mulTSupport (f j))ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
    · exact (biInter_finset_mem js).mpr fun j hj => IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
        (Set.not_mem_subset (hso j) (Finset.mem_filter.mp hj).2)
    · exact (biInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (Finset.mem_filter.mp hi).2
    · have hzn : z ∈ n := by
        rw [inter_assoc] at hz
        exact mem_of_mem_inter_left hz
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
      simp only [js, Finset.mem_filter, Finite.mem_toFinset, mem_setOf_eq, mem_iInter,
        and_imp] at hz
      suffices (mulSupport fun i => f i z) ⊆ hnf.toFinset by
        refine hnf.toFinset.subset_coe_filter_of_subset_forall _ this fun i hi => ?_
        specialize hz i ⟨z, ⟨hi, hzn⟩⟩
        contrapose hz
        simp [hz, subset_mulTSupport (f i) hi]
      intro i hi
      simp only [Finite.coe_toFinset, mem_setOf_eq]
      exact ⟨z, ⟨hi, hzn⟩⟩
#align locally_finite.exists_finset_nhd_mul_support_subset LocallyFinite.exists_finset_nhd_mulSupport_subset
#align locally_finite.exists_finset_nhd_support_subset LocallyFinite.exists_finset_nhd_support_subset

@[to_additive]
theorem locallyFinite_mulSupport_iff [CommMonoid M] {f : ι → X → M} :
    (LocallyFinite fun i ↦ mulSupport <| f i) ↔ LocallyFinite fun i ↦ mulTSupport <| f i :=
  ⟨LocallyFinite.closure, fun H ↦ H.subset fun _ ↦ subset_closure⟩

theorem LocallyFinite.smul_left [Zero R] [Zero M] [SMulWithZero R M]
    {s : ι → X → R} (h : LocallyFinite fun i ↦ support <| s i) (f : ι → X → M) :
    LocallyFinite fun i ↦ support <| s i • f i :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, zero_smul]

theorem LocallyFinite.smul_right [Zero M] [SMulZeroClass R M]
    {f : ι → X → M} (h : LocallyFinite fun i ↦ support <| f i) (s : ι → X → R) :
    LocallyFinite fun i ↦ support <| s i • f i :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, smul_zero]

end LocallyFinite
