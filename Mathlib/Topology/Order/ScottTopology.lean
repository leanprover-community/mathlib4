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

section Preorder
variable [Preorder α] {s t : Set α}

lemma IsUpperSet.upperBounds_subset (hs : IsUpperSet s) : s.Nonempty → upperBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

lemma IsLowerSet.lowerBounds_subset (hs : IsLowerSet s) : s.Nonempty → lowerBounds s ⊆ s :=
  fun ⟨_a, ha⟩ _b hb ↦ hs (hb ha) ha

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
  fun _d hd hd' _a ha hds ↦ ⟨hs hd hd' ha $ hds.trans $ inter_subset_left _ _,
    ht hd hd' ha $ hds.trans $ inter_subset_right _ _⟩

lemma DirSupInacc.union (hs : DirSupInacc s) (ht : DirSupInacc t) : DirSupInacc (s ∪ t) := by
  rw [← dirSupClosed_compl, compl_union]; exact hs.compl.inter ht.compl

lemma dirSupClosed_Iic (a : α) : DirSupClosed (Iic a) := fun _d _ _ _a ha ↦ (isLUB_le_iff ha).2

end Preorder
#exit

namespace Topology
variable [Preorder α] {s : Set α}

/--
The Scott-Hausdorff topology is defined as the topological space where a set `u` is open if, when
the least upper bound of a directed set `d` lies in `u` then there is a tail of `d` which is a
subset of `u`.
-/
def scottHausdorff : TopologicalSpace α where
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

/-- Predicate for an ordered topological space to be equipped with the Scott-Hausdorff topology. -/
class IsScottHausdorff (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff

namespace IsScottHausdorff
variable (α) [TopologicalSpace α] [Preorder α] [IsScottHausdorff α] {s : Set α}

lemma topology_eq : ‹_› = scottHausdorff := topology_eq_scottHausdorff

variable {α}

lemma isOpen_iff :
    IsOpen s ↔ ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
      a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by erw [topology_eq_scottHausdorff (α := α)]; rfl

lemma isOpen_of_isLowerSet (h : IsLowerSet s) : IsOpen s :=
  isOpen_iff.2 fun _d ⟨b, hb⟩ _ _ hda ha ↦ ⟨b, hb, fun _ hc ↦ h (mem_upperBounds.1 hda.1 _ hc.2) ha⟩

lemma dirSupInacc_of_isOpen (h : IsOpen s) : DirSupInacc s :=
  fun d hd₁ hd₂ a hda hd₃ ↦ by
    obtain ⟨b, hbd, hb⟩ := isOpen_iff.1 h hd₁ hd₂ hda hd₃; exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

lemma dirSupClosed_of_isClosed (h : IsClosed s) : DirSupClosed s :=
  (dirSupInacc_of_isOpen h.isOpen_compl).of_compl

end IsScottHausdorff

/--
The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology.
-/
def scott : TopologicalSpace α := upperSet α ⊔ scottHausdorff

lemma upperSet_le_scott : upperSet α ≤ scott := le_sup_left

lemma scottHausdorff_le_scott : @scottHausdorff α ≤ @scott α := le_sup_right
/--
The Scott topology is defined as the join of the topology of upper sets and the topological space
where a set `u` is open if, when the least upper bound of a directed set `d` lies in `u` then there
is a tail of `d` which is a subset of `u`.
-/
class IsScott (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_scott : ‹TopologicalSpace α› = scott

namespace IsScott
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsScott α]

lemma topology_eq : ‹_› = scott := topology_eq_scott

variable {α} {s : Set α} {a : α}

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open :
    IsOpen s ↔ IsUpperSet s ∧ scottHausdorff.IsOpen s := by erw [topology_eq α]; rfl

lemma isOpen_iff_isUpperSet_and_dirSupInacc : IsOpen s ↔ IsUpperSet s ∧ DirSupInacc s := by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open]
  constructor
  · refine' And.imp_right _
    convert @IsScottHausdorff.dirSupInacc_of_isOpen _ _
    exact ⟨rfl⟩
  · intros h
    constructor
    · exact h.1
    · intros d d₁ d₂ _ d₃ ha
      obtain ⟨b, hbd, hbu⟩ := h.2 d₁ d₂ d₃ ha
      exact ⟨b, hbd, Subset.trans (inter_subset_left (Ici b) d) (h.1.Ici_subset hbu)⟩

lemma isClosed_iff_isLowerSet_and_dirSupClosed : IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet_and_dirSupInacc, isUpperSet_compl,
    dirSupInacc_compl]

lemma isUpperSet_of_isOpen : IsOpen s → IsUpperSet s := fun h ↦
  (isOpen_iff_isUpperSet_and_scottHausdorff_open.mp h).left

lemma isLowerSet_of_isClosed : IsClosed s → IsLowerSet s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left

lemma lowerClosure_subset_closure : ↑(lowerClosure s) ⊆ closure s := by
  convert closure.mono (@upperSet_le_scott α _)
  rw [@Topology.IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
  · exact instIsUpperSetUpperSet
  · exact topology_eq α

lemma isClosed_Iic : IsClosed (Iic a) :=
  isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic a, _⟩

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
`(-∞,a]`.
-/
@[simp] lemma closure_singleton : closure {a} = Iic a := le_antisymm
  (closure_minimal (by rw [singleton_subset_iff, mem_Iic])
    (isClosed_iff_isLowerSet_and_dirSupClosed.mpr
      ⟨isLowerSet_Iic a, fun _ _ _ _ d₃ d₄ ↦ (isLUB_le_iff d₃).mpr d₄⟩)) $ by
    rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_subset_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β]

lemma monotone_of_continuous {f : α → β} (hf : Continuous f) : Monotone f := fun _ b hab ↦ by
  let u := (Iic (f b))ᶜ
  by_contra h
  have s1 : IsOpen u
  · rw [isOpen_compl_iff, ← closure_singleton]
    exact isClosed_closure }
  have u3 : b ∈ f⁻¹' u := isUpperSet_of_isOpen (IsOpen.preimage hf s1) hab h
  have c1 : f b ∈ (Iic (f b))ᶜ := by
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1

@[simp] lemma scottContinuous_iff_continuous {f : α → β} : ScottContinuous f ↔ Continuous f := by
  refine ⟨fun h \map ⟩
  · intro h
    rw [continuous_def]
    intros u hu
    rw [isOpen_iff_isUpperSet_and_dirSupInacc]
    exact ⟨IsUpperSet.preimage (isUpperSet_of_isOpen hu) h.monotone,
      fun _ hd₁ hd₂ _ hd₃ ha ↦ image_inter_nonempty_iff.mp
        $ (isOpen_iff_isUpperSet_and_dirSupInacc.mp hu).2 (hd₁.image f)
        (directedOn_image.mpr (hd₂.mono (by simp only [Order.Preimage]; apply h.monotone)))
        (h hd₁ hd₂ hd₃) ha⟩
  · exact fun hf _ d₁ d₂ _ d₃ ↦ ⟨
      Monotone.mem_upperBounds_image (monotone_of_continuous hf) ((isLUB_le_iff d₃).mp le_rfl),
      by
        rw [lowerBounds, mem_setOf_eq]
        intros b hb
        let u := (Iic b)ᶜ
        by_contra h
        have s1 : IsOpen u := by
          rw [isOpen_compl_iff, ← closure_singleton]
          exact isClosed_closure
        have s2 : IsOpen (f⁻¹' u) := IsOpen.preimage hf s1
        rw [isOpen_iff_isUpperSet_and_dirSupInacc] at s2
        obtain ⟨c, hcd, hfcb⟩ := s2.2 d₁ d₂ d₃ h
        simp at hfcb
        simp [upperBounds] at hb
        have c1: f c ≤ b := hb _ hcd
        contradiction⟩

end Preorder

section PartialOrder
variable [PartialOrder α] [TopologicalSpace α] [IsScott α]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90): T0Space α :=
    (t0Space_iff_inseparable α).2 $ fun x y h ↦ Iic_injective $
  by simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end PartialOrder
end IsScott

/--
Type synonym for a preorder equipped with the Scott topology
-/
def WithScott := α

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

/-- A recursor for `WithScott`. Use as `induction x using WithScott.rec`. -/
protected def rec {β : WithScott α → Sort _}
    (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a ↦ h (ofScott a)

instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithScott α) := ‹Preorder α›
instance : TopologicalSpace (WithScott α) := scott
instance : IsScott (WithScott α) := ⟨rfl⟩

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} :
    IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ scottHausdorff.IsOpen u := Iff.rfl

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScott α`.
-/
def withScottHomeomorph : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

end WithScott
end Topology

section complete_lattice

variable [CompleteLattice α] [TopologicalSpace α] [Topology.IsScott α]

lemma isOpen_iff_isUpperSet_and_sup_mem_implies_tail_subset {u : Set α} :
    IsOpen u ↔ IsUpperSet u ∧ ∀ ⦃d : Set α⦄,
    d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ ↦ h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d hd₁ hd₂ a hd₃ ha ↦ h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)⟩

lemma isOpen_iff_upper_and_sup_mem_implies_inter_nonempty :
    IsOpen u ↔ IsUpperSet u ∧ ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u →
    (d ∩u).Nonempty := by
  rw [Topology.IsScott.isOpen_iff_isUpperSet_and_dirSupInacc]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ ↦ h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d hd₁ hd₂ a hd₃ ha ↦ h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)⟩

lemma isClosed_iff_lower_and_closed_under_Directed_Sup : IsClosed s
    ↔ IsLowerSet s ∧
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → d ⊆ s → sSup d ∈ s := by
  rw [Topology.IsScott.isClosed_iff_isLowerSet_and_dirSupClosed]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ ↦ h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d a h₁ h₂ h₃ ha ↦ Set.mem_of_eq_of_mem (IsLUB.sSup_eq h₃).symm (h h₁ h₂ ha)⟩

end complete_lattice

variable [Preorder α]

namespace Topology

lemma IsScott.scottHausdorff_le [TopologicalSpace α] [IsScott α] :
    scottHausdorff ≤ ‹TopologicalSpace α› := by
  rw [IsScott.topology_eq α, scott]
  apply le_sup_right

lemma IsLower.scottHausdorff_le [TopologicalSpace α] [IsLower α] :
    scottHausdorff ≤ ‹TopologicalSpace α› :=
  fun _ h ↦ ScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen h)

end Topology
