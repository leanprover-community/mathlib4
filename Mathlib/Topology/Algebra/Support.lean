/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `tsupport f`, as the closure of
the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `mulTSupport` & `tsupport`
* `HasCompactMulSupport` & `HasCompactSupport`

## TODO

The definitions have been put in the root namespace following many other topological definitions,
like `Embedding`. Since then, `Embedding` was renamed to `Topology.IsEmbedding`, so it might be
worth reconsidering namespacing the definitions here.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open Function Set Filter Topology

variable {X α α' β γ δ M R : Type*}

section One

variable [One α] [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
set of all elements where the function is not equal to 1. -/
@[to_additive /-- The topological support of a function is the closure of its support. i.e. the
closure of the set of all elements where the function is nonzero. -/]
def mulTSupport (f : X → α) : Set X := closure (mulSupport f)

@[to_additive]
theorem subset_mulTSupport (f : X → α) : mulSupport f ⊆ mulTSupport f :=
  subset_closure

@[to_additive]
theorem isClosed_mulTSupport (f : X → α) : IsClosed (mulTSupport f) :=
  isClosed_closure

@[to_additive]
theorem mulTSupport_eq_empty_iff {f : X → α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport, closure_empty_iff, mulSupport_eq_empty_iff]

@[to_additive (attr := simp)]
theorem mulTSupport_fun_one : mulTSupport (fun _ ↦ 1 : X → α) = ∅ := by
  rw [mulTSupport, mulSupport_fun_one, closure_empty]

@[to_additive (attr := simp)]
theorem mulTSupport_one : mulTSupport (1 : X → α) = ∅ := by
  rw [mulTSupport, mulSupport_one, closure_empty]

@[to_additive]
theorem mulTSupport_binop_subset [One β] [One γ] (op : α → β → γ)
    (op1 : op 1 1 = 1) (f : X → α) (g : X → β) :
    mulTSupport (fun x ↦ op (f x) (g x)) ⊆ mulTSupport f ∪ mulTSupport g :=
  closure_mono (mulSupport_binop_subset op op1 f g) |>.trans closure_union.subset

@[to_additive]
lemma mulTSupport_comp_subset [One β] {g : α → β} (hg : g 1 = 1) (f : X → α) :
    mulTSupport (g ∘ f) ⊆ mulTSupport f :=
  closure_mono (mulSupport_comp_subset hg f)

@[to_additive]
lemma mulTSupport_subset_comp [One β] {g : α → β} (hg : ∀ {x}, g x = 1 → x = 1) (f : X → α) :
    mulTSupport f ⊆ mulTSupport (g ∘ f) :=
  closure_mono (mulSupport_subset_comp hg f)

@[to_additive]
lemma mulTSupport_comp_eq [One β] {g : α → β} (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : X → α) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq g hg]

@[to_additive]
lemma mulTSupport_comp_eq_of_range_subset [One β] {g : α → β} {f : X → α}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_of_range_subset hg]

@[to_additive]
lemma mulTSupport_comp_subset_preimage {Y : Type*} [TopologicalSpace Y] (g : Y → α) {f : X → Y}
    (hf : Continuous f) :
    mulTSupport (g ∘ f) ⊆ f ⁻¹' mulTSupport g := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_preimage]
  exact hf.closure_preimage_subset _

@[to_additive]
lemma mulTSupport_comp_eq_preimage {Y : Type*} [TopologicalSpace Y] (g : Y → α) (f : X ≃ₜ Y) :
    mulTSupport (g ∘ f) = f ⁻¹' mulTSupport g := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_preimage, Homeomorph.preimage_closure]

@[to_additive]
theorem image_eq_one_of_notMem_mulTSupport {f : X → α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx

@[to_additive]
theorem range_subset_insert_image_mulTSupport (f : X → α) :
    range f ⊆ insert 1 (f '' mulTSupport f) := by
  grw [← subset_mulTSupport f]; exact range_subset_insert_image_mulSupport f

@[to_additive]
theorem range_eq_image_mulTSupport_or (f : X → α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)

theorem tsupport_mul_subset_left {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)

theorem tsupport_mul_subset_right {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)

end One

section Operations

variable [TopologicalSpace X]

@[to_additive (attr := simp)]
theorem mulTSupport_mul [MulOneClass α] (f g : X → α) :
    (mulTSupport fun x ↦ f x * g x) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· * ·) (by simp) f g

@[to_additive]
theorem mulTSupport_pow [Monoid α] (f : X → α) (n : ℕ) :
    (mulTSupport fun x => f x ^ n) ⊆ mulTSupport f :=
  closure_mono <| mulSupport_pow f n

@[to_additive (attr := simp)]
theorem mulTSupport_fun_inv [DivisionMonoid α] (f : X → α) :
    (mulTSupport fun x => (f x)⁻¹) = mulTSupport f :=
  congrArg closure <| mulSupport_fun_inv f

@[to_additive (attr := simp)]
theorem mulTSupport_inv [DivisionMonoid α] (f : X → α) :
    mulTSupport f⁻¹ = mulTSupport f :=
  mulTSupport_fun_inv f

@[to_additive]
theorem mulTSupport_mul_inv [DivisionMonoid α] (f g : X → α) :
    (mulTSupport fun x => f x * (g x)⁻¹) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· * ·⁻¹) (by simp) f g

@[to_additive]
theorem mulTSupport_div [DivisionMonoid α] (f g : X → α) :
    (mulTSupport fun x => f x / g x) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· / ·) one_div_one f g

theorem tsupport_smul_subset_left {M α} [Zero M] [Zero α] [SMulWithZero M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g

theorem tsupport_smul_subset_right {M α} [Zero α] [SMulZeroClass M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport g :=
  closure_mono <| support_smul_subset_right f g

end Operations

section

variable [TopologicalSpace α]
variable [One β]
variable {f : α → β} {x : α}

@[to_additive]
theorem notMem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]

@[to_additive]
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α → β}
    (hf : ∀ x ∈ mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (notMem_mulTSupport_iff_eventuallyEq.mp hx).symm

@[to_additive]
lemma ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α → β}
    {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f ⊆ s) :
    Continuous f :=
  continuous_of_mulTSupport fun _ hx ↦ h's.continuousOn_iff.mp hs <| h''s hx

end

/-! ## Functions with compact support -/
section CompactSupport

variable [TopologicalSpace α] [TopologicalSpace α'] [One β] [One γ] [One δ]
  {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ}

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive /-- A function `f` *has compact support* or is *compactly supported* if the closure of
the support of `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a
compact set. -/]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)

@[to_additive]
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl

@[to_additive]
theorem exists_compact_iff_hasCompactMulSupport [R1Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ x, x ∉ K → f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← notMem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]

namespace HasCompactMulSupport

variable {K : Set α}

@[to_additive]
theorem intro [R1Space α] (hK : IsCompact K) (hfK : ∀ x, x ∉ K → f x = 1) :
    HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩

@[to_additive]
theorem intro' (hK : IsCompact K) (h'K : IsClosed K) (hfK : ∀ x, x ∉ K → f x = 1) :
    HasCompactMulSupport f := by
  have : mulTSupport f ⊆ K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK (isClosed_mulTSupport f) this

@[to_additive]
theorem of_mulSupport_subset_isCompact [R1Space α] (hK : IsCompact K) (h : mulSupport f ⊆ K) :
    HasCompactMulSupport f :=
  hK.closure_of_subset h

@[to_additive]
theorem isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) := hf

@[to_additive]
theorem _root_.hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  mem_coclosedCompact_iff.symm

@[to_additive]
theorem _root_.isCompact_range_of_mulSupport_subset_isCompact [TopologicalSpace β]
    (hf : Continuous f) (hk : IsCompact K) (h'f : mulSupport f ⊆ K) :
    IsCompact (range f) := by
  rcases range_eq_image_or_of_mulSupport_subset h'f with h2 | h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]
theorem isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)

@[to_additive]
theorem mono' {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulTSupport f) :
    HasCompactMulSupport f' :=
  IsCompact.of_isClosed_subset hf isClosed_closure <| closure_minimal hff' isClosed_closure

@[to_additive]
theorem mono {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulSupport f) :
    HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure

@[to_additive]
theorem comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mulSupport_comp_subset hg f

@[to_additive]
theorem _root_.hasCompactMulSupport_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]

@[to_additive]
theorem comp_isClosedEmbedding (hf : HasCompactMulSupport f) {g : α' → α}
    (hg : IsClosedEmbedding g) : HasCompactMulSupport (f ∘ g) := by
  rw [hasCompactMulSupport_def, Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.isEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]
theorem comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] with x hx hx₂
  simp_rw [hx, hx₂, Pi.one_apply, hm]

@[to_additive]
lemma isCompact_preimage [TopologicalSpace β] {K : Set β}
    (h'f : HasCompactMulSupport f) (hf : Continuous f) (hk : IsClosed K) (h'k : 1 ∉ K) :
    IsCompact (f ⁻¹' K) := by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx ↦ ?_)
  apply subset_mulTSupport
  aesop

variable [T2Space α']

section

variable (hf : HasCompactMulSupport f) {g : α → α'} (cont : Continuous g)
include hf cont

@[to_additive]
theorem mulTSupport_extend_one_subset :
    mulTSupport (g.extend f 1) ⊆ g '' mulTSupport f :=
  (hf.image cont).isClosed.closure_subset_iff.mpr <|
    mulSupport_extend_one_subset.trans (image_mono subset_closure)

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

end

@[to_additive]
theorem continuous_extend_one [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f : U → β}
    (cont : Continuous f) (supp : HasCompactMulSupport f) :
    Continuous (Subtype.val.extend f 1) :=
  continuous_of_mulTSupport fun x h ↦ by
    rw [show x = ↑(⟨x, Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl,
      ← (hU.isOpenEmbedding_subtypeVal).continuousAt_iff, extend_comp Subtype.val_injective]
    exact cont.continuousAt

/-- If `f` has compact multiplicative support, then `f` tends to 1 at infinity. -/
@[to_additive /-- If `f` has compact support, then `f` tends to zero at infinity. -/]
theorem is_one_at_infty {f : α → γ} [TopologicalSpace γ]
    (h : HasCompactMulSupport f) : Tendsto f (cocompact α) (𝓝 1) := by
  intro N hN
  rw [mem_map, mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage, image_eq_one_of_notMem_mulTSupport hv]
  exact mem_of_mem_nhds hN

end HasCompactMulSupport

section Compact

variable [CompactSpace α]

/-- In a compact space `α`, any function has compact support. -/
@[to_additive]
theorem HasCompactMulSupport.of_compactSpace (f : α → γ) :
    HasCompactMulSupport f :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_mulTSupport f)
    (Set.subset_univ (mulTSupport f))

end Compact

end CompactSupport

/-! ## Functions with compact support: algebraic operations -/
section CompactSupport2
section Monoid

variable [TopologicalSpace α] [MulOneClass β]
variable {f f' : α → β}

@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := hf.comp₂_left hf' (mul_one 1)

@[to_additive, simp]
protected lemma HasCompactMulSupport.one {α β : Type*} [TopologicalSpace α] [One β] :
    HasCompactMulSupport (1 : α → β) := by
  simp [HasCompactMulSupport]

variable (α β) in
/-- The submonoid of functions `α → β` with compact multiplicative support. -/
@[to_additive /-- The additive submonoid of functions `α → β` with compact support. -/]
def HasCompactMulSupport.submonoid : Submonoid (α → β) where
  carrier := {f | HasCompactMulSupport f}
  one_mem' := .one
  mul_mem' := .mul

@[to_additive (attr := simp)]
theorem HasCompactMulSupport.mem_submonoid_iff {f : α → β} :
    f ∈ HasCompactMulSupport.submonoid α β ↔ HasCompactMulSupport f :=
  Iff.rfl

@[to_additive]
theorem HasCompactMulSupport.list_prod {α β : Type*} [TopologicalSpace α] [Monoid β]
    {l : List (α → β)} (hl : ∀ f ∈ l, HasCompactMulSupport f) :
    HasCompactMulSupport l.prod :=
  list_prod_mem (S := HasCompactMulSupport.submonoid α β) hl

end Monoid

section CommMonoid

variable [TopologicalSpace α] [CommMonoid β]

@[to_additive]
theorem HasCompactMulSupport.multiset_prod
    (m : Multiset (α → β)) (hm : ∀ f ∈ m, HasCompactMulSupport f) :
    HasCompactMulSupport m.prod :=
  multiset_prod_mem (S := HasCompactMulSupport.submonoid α β) m hm

@[to_additive]
theorem HasCompactMulSupport.finset_prod {ι : Type*}
    {s : Finset ι} {f : ι → α → β} (hf : ∀ i ∈ s, HasCompactMulSupport (f i)) :
    HasCompactMulSupport (∏ i ∈ s, f i) :=
  prod_mem (S := HasCompactMulSupport.submonoid α β) hf

end CommMonoid

section DivisionMonoid

@[to_additive]
protected lemma HasCompactMulSupport.inv {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f : α → β} (hf : HasCompactMulSupport f) :
    HasCompactMulSupport (f⁻¹) := by
  simpa only [HasCompactMulSupport, mulTSupport, mulSupport_inv] using hf

@[to_additive]
theorem HasCompactSupport.div {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f f' : α → β} (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f / f') :=
  div_eq_mul_inv f f' ▸ hf.mul hf'.inv

end DivisionMonoid

section SMulZeroClass

variable [TopologicalSpace α] [Zero M] [SMulZeroClass R M]
variable {f : α → R} {f' : α → M}

theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

end SMulZeroClass

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]
variable {f : α → R} {f' : α → M}

theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]
variable {f f' : α → β}

theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]

theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

end MulZeroClass

section OrderedAddGroup

variable [TopologicalSpace α] [AddGroup β] [Lattice β] [AddLeftMono β]

protected theorem HasCompactSupport.abs {f : α → β} (hf : HasCompactSupport f) :
    HasCompactSupport |f| :=
  hf.comp_left (g := abs) abs_zero

end OrderedAddGroup

end CompactSupport2

section LocallyFinite

variable {ι : Type*} [TopologicalSpace X]

-- TODO: reformulate for any locally finite family of sets
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive /-- If a family of functions `f` has locally-finite support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are non-zero. -/]
theorem LocallyFinite.exists_finset_nhds_mulSupport_subset {U : ι → Set X} [One R] {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι), ∃ n, n ∈ 𝓝 x ∧ (n ⊆ ⋂ i ∈ is, U i) ∧
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is := by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i ∈ hnf.toFinset | x ∈ U i}
    let js := {j ∈ hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n ∩ ⋂ j ∈ js, (mulTSupport (f j))ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
    · exact (biInter_finset_mem js).mpr fun j hj => IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
        (Set.notMem_subset (hso j) (Finset.mem_filter.mp hj).2)
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

@[to_additive]
theorem locallyFinite_mulSupport_iff [One M] {f : ι → X → M} :
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

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[to_additive]
theorem HasCompactMulSupport.comp_homeomorph {M} [One M] {f : Y → M}
    (hf : HasCompactMulSupport f) (φ : X ≃ₜ Y) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_isClosedEmbedding φ.isClosedEmbedding

end Homeomorph
