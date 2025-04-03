/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `DirSupInacc` - a set `u` is said to be inaccessible by directed joins if, when the least upper
  bound of a directed set `d` lies in `u` then `d` has non-empty intersection with `u`.
- `DirSupClosed` - a set `s` is said to be closed under directed joins if, whenever a directed set
  `d` has a least upper bound `a` and is a subset of `s` then `a` also lies in `s`.
- `Topology.scott` - the Scott topology is defined as the join of the topology of upper sets and the
  Scott-Hausdorff topology (the topological space where a set `u` is open if, when the least upper
  bound of a directed set `d` lies in `u` then there is a tail of `d` which is a subset of `u`).

## Main statements

- `Topology.IsScott.isUpperSet_of_isOpen`: Scott open sets are upper.
- `Topology.IsScott.isLowerSet_of_isClosed`: Scott closed sets are lower.
- `Topology.IsScott.monotone_of_continuous`: Functions continuous wrt the Scott topology are
  monotone.
- `Topology.IsScott.scottContinuous_iff_continuous` - a function is Scott continuous (preserves
  least upper bounds of directed sets) if and only if it is continuous wrt the Scott topology.
- `Topology.IsScott.instT0Space` - the Scott topology on a partial order is T₀.

## Implementation notes

A type synonym `WithScott` is introduced and for a preorder `α`, `WithScott α` is made an instance
of `TopologicalSpace` by the `scott` topology.

We define a mixin class `IsScott` for the class of types which are both a preorder and a
topology and where the topology is the `scott` topology. It is shown that `WithScott α` is an
instance of `IsScott`.

A class `Scott` is defined in `Topology/OmegaCompletePartialOrder` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains (`OmegaCompletePartialOrder.Continuous'`).
A Scott continuous function between `OmegaCompletePartialOrder`s is always
`OmegaCompletePartialOrder.Continuous'` (`OmegaCompletePartialOrder.ScottContinuous.continuous'`).
The converse is true in some special cases, but not in general
([Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994]).

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Karner, *Continuous monoids and semirings*][Karner2004]

## Tags

Scott topology, preorder
-/

open Set

variable {α β : Type*}

/-! ### Prerequisite order properties -/

section Preorder
variable [Preorder α] {s t : Set α}

/-- A set `s` is said to be inaccessible by directed joins if, when the least upper bound of a
directed set `d` lies in `s` then `d` has non-empty intersection with `s`. -/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/--
A set `s` is said to be closed under directed joins if, whenever a directed set `d` has a least
upper bound `a` and is a subset of `s` then `a` also lies in `s`.
-/
def DirSupClosed (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → d ⊆ s → a ∈ s

@[simp] lemma dirSupInacc_compl : DirSupInacc sᶜ ↔ DirSupClosed s := by
  simp [DirSupInacc, DirSupClosed, ← not_disjoint_iff_nonempty_inter, not_imp_not,
    disjoint_compl_right_iff]

@[simp] lemma dirSupClosed_compl : DirSupClosed sᶜ ↔ DirSupInacc s := by
  rw [← dirSupInacc_compl, compl_compl]

alias ⟨DirSupInacc.of_compl, DirSupClosed.compl⟩ := dirSupInacc_compl
alias ⟨DirSupClosed.of_compl, DirSupInacc.compl⟩ := dirSupClosed_compl

lemma DirSupClosed.inter (hs : DirSupClosed s) (ht : DirSupClosed t) : DirSupClosed (s ∩ t) :=
  fun _d hd hd' _a ha hds ↦ ⟨hs hd hd' ha <| hds.trans inter_subset_left,
    ht hd hd' ha <| hds.trans inter_subset_right⟩

lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  rw [← dirSupClosed_compl, compl_union]; exact hs.compl.inter ht.compl

lemma IsUpperSet.dirSupClosed (hs : IsUpperSet s) : DirSupClosed s :=
  fun _d ⟨_b, hb⟩ _ _a ha hds ↦ hs (ha.1 hb) <| hds hb

lemma IsLowerSet.dirSupInacc (hs : IsLowerSet s) : DirSupInacc s := hs.compl.dirSupClosed.of_compl

lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) := fun _d _ _ _a ha ↦ (isLUB_le_iff ha).2

end Preorder

section CompleteLattice
variable [CompleteLattice α] {s t : Set α}

lemma dirSupInacc_iff_forall_sSup :
    DirSupInacc s ↔ ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ s → (d ∩ s).Nonempty := by
  simp [DirSupInacc, isLUB_iff_sSup_eq]

lemma dirSupClosed_iff_forall_sSup :
    DirSupClosed s ↔ ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → d ⊆ s → sSup d ∈ s := by
  simp [DirSupClosed, isLUB_iff_sSup_eq]

end CompleteLattice

namespace Topology

/-! ### Scott-Hausdorff topology -/

section ScottHausdorff
variable [Preorder α] {s : Set α}

/-- The Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`. -/
def scottHausdorff (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen u := ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
    a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u
  isOpen_univ := fun d ⟨b, hb⟩ _ _ _ _ ↦ ⟨b, hb, (Ici b ∩ d).subset_univ⟩
  isOpen_inter s t hs ht d hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ ↦ ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ ↦ by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

variable (α) [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`. -/
class IsScottHausdorff : Prop where
  topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff α

instance : @IsScottHausdorff α _ (scottHausdorff α) :=
  @IsScottHausdorff.mk _ _ (scottHausdorff α) rfl

namespace IsScottHausdorff
variable [IsScottHausdorff α] {s : Set α}

lemma topology_eq : ‹_› = scottHausdorff α := topology_eq_scottHausdorff

variable {α}

lemma isOpen_iff :
    IsOpen s ↔ ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
      a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by erw [topology_eq_scottHausdorff (α := α)]; rfl

lemma isOpen_of_isLowerSet (h : IsLowerSet s) : IsOpen s :=
  isOpen_iff.2 fun _d ⟨b, hb⟩ _ _ hda ha ↦ ⟨b, hb, fun _ hc ↦ h (mem_upperBounds.1 hda.1 _ hc.2) ha⟩

lemma isClosed_of_isUpperSet (h : IsUpperSet s) : IsClosed s :=
  isOpen_compl_iff.1 <| isOpen_of_isLowerSet h.compl

lemma dirSupInacc_of_isOpen (h : IsOpen s) : DirSupInacc s :=
  fun d hd₁ hd₂ a hda hd₃ ↦ by
    obtain ⟨b, hbd, hb⟩ := isOpen_iff.1 h hd₁ hd₂ hda hd₃; exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

lemma dirSupClosed_of_isClosed (h : IsClosed s) : DirSupClosed s :=
  (dirSupInacc_of_isOpen h.isOpen_compl).of_compl

end IsScottHausdorff
end ScottHausdorff

/-! ### Scott topology -/

section Scott
section Preorder
variable [Preorder α]

/-- The Scott topology.

It is defined as the join of the topology of upper sets and the Scott-Hausdorff topology. -/
def scott (α : Type*) [Preorder α] : TopologicalSpace α := upperSet α ⊔ scottHausdorff α

lemma upperSet_le_scott : upperSet α ≤ scott α := le_sup_left

lemma scottHausdorff_le_scott : scottHausdorff α ≤ scott α := le_sup_right

variable (α) [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Scott topology.

The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology. -/
class IsScott : Prop where
  topology_eq_scott : ‹TopologicalSpace α› = scott α

end Preorder

namespace IsScott
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsScott α]

lemma topology_eq : ‹_› = scott α := topology_eq_scott

variable {α} {s : Set α} {a : α}

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open :
    IsOpen s ↔ IsUpperSet s ∧ IsOpen[scottHausdorff α] s := by erw [topology_eq α]; rfl

lemma isOpen_iff_isUpperSet_and_dirSupInacc : IsOpen s ↔ IsUpperSet s ∧ DirSupInacc s := by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open]
  refine and_congr_right fun h ↦
    ⟨@IsScottHausdorff.dirSupInacc_of_isOpen _ _ (scottHausdorff α) _ _,
      fun h' d d₁ d₂ _ d₃ ha ↦ ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩

lemma isClosed_iff_isLowerSet_and_dirSupClosed : IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet_and_dirSupInacc, isUpperSet_compl,
    dirSupInacc_compl]

lemma isUpperSet_of_isOpen : IsOpen s → IsUpperSet s := fun h ↦
  (isOpen_iff_isUpperSet_and_scottHausdorff_open.mp h).left

lemma isLowerSet_of_isClosed : IsClosed s → IsLowerSet s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left

lemma lowerClosure_subset_closure : ↑(lowerClosure s) ⊆ closure s := by
  convert closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α

lemma isClosed_Iic : IsClosed (Iic a) :=
  isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
`(-∞,a]`.
-/
@[simp] lemma closure_singleton : closure {a} = Iic a := le_antisymm
  (closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) <| by
    rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_subset_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β] {f : α → β}

lemma monotone_of_continuous (hf : Continuous f) : Monotone f := fun _ b hab ↦ by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h

@[simp] lemma scottContinuous_iff_continuous : ScottContinuous f ↔ Continuous f := by
  refine ⟨fun h ↦ continuous_def.2 fun u hu ↦ ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInacc]
    exact ⟨(isUpperSet_of_isOpen hu).preimage h.monotone, fun _ hd₁ hd₂ _ hd₃ ha ↦
      image_inter_nonempty_iff.mp <| (isOpen_iff_isUpperSet_and_dirSupInacc.mp hu).2 (hd₁.image f)
        (directedOn_image.mpr (hd₂.mono @(h.monotone))) (h hd₁ hd₂ hd₃) ha⟩
  · refine fun hf _ d₁ d₂ _ d₃ ↦ ⟨(monotone_of_continuous hf).mem_upperBounds_image d₃.1,
      fun b hb ↦ ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := (isOpen_compl_iff.2 isClosed_Iic).preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInacc] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 d₁ d₂ d₃ h
    simp [upperBounds] at hb
    exact hfcb <| hb _ hcd

end Preorder

section PartialOrder
variable [PartialOrder α] [TopologicalSpace α] [IsScott α]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90) : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h ↦ Iic_injective <| by
    simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end PartialOrder
end IsScott

/--
Type synonym for a preorder equipped with the Scott topology
-/
def WithScott (α : Type*) := α

namespace WithScott

/-- `toScott` is the identity function to the `WithScott` of a type. -/
@[match_pattern] def toScott : α ≃ WithScott α := Equiv.refl _

/-- `ofScott` is the identity function from the `WithScott` of a type. -/
@[match_pattern] def ofScott : WithScott α ≃ α := Equiv.refl _

@[simp] lemma toScott_symm_eq : (@toScott α).symm = ofScott := rfl
@[simp] lemma ofScott_symm_eq : (@ofScott α).symm = toScott := rfl
@[simp] lemma toScott_ofScott (a : WithScott α) : toScott (ofScott a) = a := rfl
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl

@[simp, nolint simpNF]
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl

@[simp, nolint simpNF]
lemma ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b := Iff.rfl

/-- A recursor for `WithScott`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithScott α → Sort _}
    (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a ↦ h (ofScott a)

instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithScott α) := ‹Preorder α›
instance : TopologicalSpace (WithScott α) := scott α
instance : IsScott (WithScott α) := ⟨rfl⟩

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} :
    IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ (scottHausdorff α).IsOpen u := Iff.rfl

end WithScott
end Scott

variable [Preorder α]

lemma scottHausdorff_le_lower : scottHausdorff α ≤ lower α :=
  fun s h => @IsScottHausdorff.isOpen_of_isLowerSet  _ _ (scottHausdorff α) _ _
      <| (@IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _  _ s h)

variable [TopologicalSpace α]

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScott α`.
-/
def IsScott.withScottHomeomorph [IsScott α] : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfInducing ⟨by erw [IsScott.topology_eq α, induced_id]; rfl⟩

lemma IsScott.scottHausdorff_le [IsScott α] : scottHausdorff α ≤ ‹TopologicalSpace α› := by
  rw [IsScott.topology_eq α, scott]; exact le_sup_right

lemma IsLower.scottHausdorff_le [IsLower α] : scottHausdorff α ≤ ‹TopologicalSpace α› :=
  fun _ h ↦
    @IsScottHausdorff.isOpen_of_isLowerSet _ _ (scottHausdorff α) _ _
      <| IsLower.isLowerSet_of_isOpen h

end Topology
