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
- `Scott` - the Scott topology is defined as the join of the topology of upper sets and the
  Scott-Hausdorff topology (the topological space where a set `u` is open if, when the least upper
  bound of a directed set `d` lies in `u` then there is a tail of `d` which is a subset of `u`).

## Main statements

- `IsScott.isUpperSet_of_isOpen`: Scott open sets are upper.
- `IsScott.isLowerSet_of_isClosed`: Scott closed sets are lower.
- `IsScott.monotone_of_continuous`: Functions continuous wrt the Scott topology are monotone.
- `IsScott.scottContinuous_iff_continuous` - a function is Scott continuous (preserves least upper
  bounds of directed sets) if and only if it is continuous wrt the Scott topology.
- `IsScott.instT0Space` - the Scott topology on a partial order is T₀.

## Implementation notes

A type synonym `WithScott` is introduced and for a preorder `α`, `WithScott α` is made an instance
of `TopologicalSpace` by the `Scott` topology.

We define a mixin class `IsScott` for the class of types which are both a preorder and a
topology and where the topology is the `Scott` topology. It is shown that `WithScott α` is an
instance of `IsScott`.

A class `Scott` is defined in `Topology.OmegaCompletePartialOrder` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains (`OmegaCompletePartialOrder.Continuous'`).
A Scott continuous function between `OmegaCompletePartialOrder`s is always
`OmegaCompletePartialOrder.Continuous'` (`ScottContinuous.continuous'`). The converse is true in
some special cases, but not in general ([Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994]).

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

Scott topology, preorder
-/

variable (α β : Type*)

open Set

section preorder

variable {α β}

variable [Preorder α] [Preorder β]

/--
A set `u` is said to be inaccessible by directed joins if, when the least upper bound of a directed
set `d` lies in `u` then `d` has non-empty intersection with `u`.
-/
def DirSupInacc (u : Set α) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a → a ∈ u → (d ∩ u).Nonempty

namespace Topology
/--
The Scott-Hausdorff topology is defined as the topological space where a set `u` is open if, when
the least upper bound of a directed set `d` lies in `u` then there is a tail of `d` which is a
subset of `u`.
-/
def scottHausdorff : TopologicalSpace α where
  IsOpen u := ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
    a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u
  isOpen_univ := fun d ⟨b, hb⟩ _ _ _ _ => ⟨b, hb, (Ici b ∩ d).subset_univ⟩
  isOpen_inter s t hs ht d hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    refine ⟨c, hcd, ?_⟩
    · calc
        Ici c ∩ d ⊆ Ici b₁ ∩ Ici b₂ ∩ d := by
        { apply inter_subset_inter_left d
          apply subset_inter (Ici_subset_Ici.mpr hc.1) (Ici_subset_Ici.mpr hc.2) }
        _ = (Ici b₁ ∩ d) ∩ (Ici b₂ ∩ d) := by rw [inter_inter_distrib_right]
        _ ⊆ s ∩ t := inter_subset_inter hb₁ds hb₂dt
  isOpen_sUnion := fun s h d hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ => by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

lemma ScottHausdorff.isOpen_of_isLowerSet {s : Set α} (h : IsLowerSet s) :
    scottHausdorff.IsOpen s := fun d ⟨b, hb⟩ _ _ hda ha =>
      ⟨b, hb,Subset.trans (inter_subset_right (Ici b) d)
      (fun _ hc => h (mem_upperBounds.mp hda.1 _ hc) ha)⟩

/--
The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology.
-/
def Scott : TopologicalSpace α := upperSet α ⊔ scottHausdorff

lemma upperSet_le_Scott : upperSet α ≤ Scott := le_sup_left

lemma scottHausdorff_le_Scott : @scottHausdorff α ≤ @Scott α := le_sup_right

end Topology

end preorder

namespace Topology
/--
Type synonym for a preorder equipped with the Scott topology
-/
def WithScott := α

variable {α β}

namespace WithScott

/-- `toScott` is the identity function to the `WithScott` of a type.  -/
@[match_pattern] def toScott : α ≃ WithScott α := Equiv.refl _

/-- `ofScott` is the identity function from the `WithScott` of a type.  -/
@[match_pattern] def ofScott : WithScott α ≃ α := Equiv.refl _

@[simp] lemma toScott_symm_eq : (@toScott α).symm = ofScott := rfl
@[simp] lemma ofScott_symm_eq : (@ofScott α).symm = toScott := rfl
@[simp] lemma toScott_ofScott (a : WithScott α) : toScott (ofScott a) = a := rfl
@[simp] lemma ofScott_toScott (a : α) : ofScott (toScott a) = a := rfl
-- porting note: removed @[simp] to make linter happy
lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl
-- porting note: removed @[simp] to make linter happy
lemma ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b := Iff.rfl

/-- A recursor for `WithScott`. Use as `induction x using WithScott.rec`. -/
protected def rec {β : WithScott α → Sort _}
  (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a => h (ofScott a)

instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithScott α) := ‹Preorder α›

instance : TopologicalSpace (WithScott α) := Scott

end WithScott

/--
The Scott topology is defined as the join of the topology of upper sets and the topological space
where a set `u` is open if, when the least upper bound of a directed set `d` lies in `u` then there
is a tail of `d` which is a subset of `u`.
-/
class IsScott (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_ScottTopology : t = Scott

attribute [nolint docBlame]
  IsScott.topology_eq_ScottTopology

instance [Preorder α] : IsScott (WithScott α) :=
  ⟨rfl⟩

namespace IsScott

section preorder

variable [Preorder α]

lemma isOpen_iff_upper_and_Scott_Hausdorff_Open' {u : Set α} :
  IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ scottHausdorff.IsOpen u := Iff.rfl

variable [TopologicalSpace α] [IsScott α]

variable (α)

lemma topology_eq : ‹_› = Scott := topology_eq_ScottTopology

variable {α}

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScott α`.
-/
def WithScottHomeomorph : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

end preorder

section morphisms

variable [Preorder α] [Preorder β]

open TopologicalSpace

lemma UpperSetTopology_Monotone_coinduced_LE' {t₁ : TopologicalSpace α} [Topology.IsUpperSet α]
  {f : α → β}  (hf : Monotone f) : coinduced f t₁ ≤ @Scott β _ := by
  apply le_sup_of_le_left
  rwa [← continuous_iff_coinduced_le,
    ← @IsUpperSet.monotone_iff_continuous α β _ _ t₁ (upperSet β) _ _ ]

lemma UpperSetTopology_Monotone_coinduced_LE {t₁ : TopologicalSpace α} [Topology.IsUpperSet α]
    {t₂ : TopologicalSpace β} [IsScott β] {f : α → β} (hf : Monotone f) :
    coinduced f t₁ ≤ t₂ := by
  rw [IsScott.topology_eq β]
  apply UpperSetTopology_Monotone_coinduced_LE' hf

lemma Monotone_From_UpperSetTopology_Continuous {t₁ : TopologicalSpace α} [Topology.IsUpperSet α]
    {t₂ : TopologicalSpace β} [IsScott β] {f : α → β} (hf : Monotone f)  : Continuous f := by
  rw [continuous_iff_coinduced_le]
  apply UpperSetTopology_Monotone_coinduced_LE hf

end morphisms

section preorder

variable [Preorder α] [TopologicalSpace α] [IsScott α] {u : Set α}

lemma isOpen_iff_upper_and_Scott_Hausdorff_Open :
    IsOpen u ↔ IsUpperSet u ∧ scottHausdorff.IsOpen u := by erw [topology_eq α]; rfl

lemma isOpen_iff_upper_and_DirSupInacc {u : Set α} :
    IsOpen u ↔ IsUpperSet u ∧ DirSupInacc u := by
  rw [isOpen_iff_upper_and_Scott_Hausdorff_Open]
  constructor
  · refine' And.imp_right _
    intros h d d₁ d₂ a d₃ ha
    obtain ⟨b, hbd, hbdu⟩ := h d₁ d₂ d₃ ha
    exact ⟨b, hbd, mem_of_subset_of_mem hbdu ⟨left_mem_Ici, hbd⟩⟩
  · intros h
    constructor
    · exact h.1
    · intros d d₁ d₂ a d₃ ha
      obtain ⟨b, hbd, hbu⟩ := h.2 d₁ d₂ d₃ ha
      exact ⟨b, hbd, Subset.trans (inter_subset_left (Ici b) d) (h.1.Ici_subset hbu)⟩

lemma isClosed_iff_lower_and_subset_implies_LUB_mem {s : Set α} : IsClosed s
    ↔ (IsLowerSet s ∧
    ∀ ⦃d : Set α⦄ ⦃a : α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d a → d ⊆ s → a ∈ s ) := by
  rw [← isOpen_compl_iff, isOpen_iff_upper_and_DirSupInacc,
    isLowerSet_compl.symm, compl_compl]
  apply and_congr_right'
  constructor
  · intros h d a d₁ d₂ d₃ d₄
    by_contra h'
    have c1: (d ∩ sᶜ).Nonempty := h d₁ d₂ d₃ h'
    have c2: d ∩ sᶜ =  ∅ := by
      rw [← subset_empty_iff, ← inter_compl_self s]
      exact inter_subset_inter_left _ d₄
    rw [c2] at c1
    simp only [Set.not_nonempty_empty] at c1
  · intros h d d₁ d₂ a d₃ d₄
    rw [inter_compl_nonempty_iff]
    by_contra h'
    have c1: a ∈ s := h d₁ d₂ d₃ h'
    contradiction

lemma isUpperSet_of_isOpen {s : Set α} : IsOpen s → IsUpperSet s := fun h =>
  (isOpen_iff_upper_and_Scott_Hausdorff_Open.mp h).left

lemma isLowerSet_of_isClosed {s : Set α} : IsClosed s → IsLowerSet s := fun h =>
  (isClosed_iff_lower_and_subset_implies_LUB_mem.mp h).left

lemma lowerClosure_le_closure {s : Set α} : lowerClosure s ≤ closure s := by
  convert closure.mono (@upperSet_le_Scott α _)
  rw [@Topology.IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
  · exact instIsUpperSetUpperSet
  · exact topology_eq α

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [le_antisymm_iff]
  constructor
  · apply closure_minimal
    · rw [singleton_subset_iff, mem_Iic]
    · rw [isClosed_iff_lower_and_subset_implies_LUB_mem]
      exact ⟨isLowerSet_Iic a, fun _ _ _ _ d₃ d₄ => (isLUB_le_iff d₃).mpr d₄⟩
  · rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_le_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β]

lemma monotone_of_continuous {f : α → β} (hf : Continuous f) : Monotone f := by
  rw [Monotone]
  intros a b hab
  let u := (Iic (f b))ᶜ
  by_contra h
  have s1 : IsOpen u
  { rw [isOpen_compl_iff, ← closure_singleton]
    exact isClosed_closure }
  have u3 : b ∈ f⁻¹'  u := isUpperSet_of_isOpen (IsOpen.preimage hf s1) hab h
  have c1 : f b ∈ (Iic (f b))ᶜ := by
    simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1

@[simp] lemma scottContinuous_iff_continuous {f : α → β} : ScottContinuous f ↔ Continuous f := by
  constructor
  · intro h
    rw [continuous_def]
    intros u hu
    rw [isOpen_iff_upper_and_DirSupInacc]
    exact ⟨IsUpperSet.preimage (isUpperSet_of_isOpen hu) h.monotone,
      fun _ hd₁ hd₂ _ hd₃ ha => image_inter_nonempty_iff.mp
        $ (isOpen_iff_upper_and_DirSupInacc.mp hu).2 (hd₁.image f)
        (directedOn_image.mpr (hd₂.mono (by simp only [Order.Preimage]; apply h.monotone)))
        (h hd₁ hd₂ hd₃) ha⟩
  · intros hf d d₁ d₂ a d₃
    rw [IsLUB]
    constructor
    · apply Monotone.mem_upperBounds_image (monotone_of_continuous hf) ((isLUB_le_iff d₃).mp le_rfl)
    · rw [lowerBounds, mem_setOf_eq]
      intros b hb
      let u := (Iic b)ᶜ
      by_contra h
      have s1 : IsOpen u := by
        rw [isOpen_compl_iff, ← closure_singleton]
        exact isClosed_closure
      have s2 : IsOpen (f⁻¹'  u) := IsOpen.preimage hf s1
      rw [isOpen_iff_upper_and_DirSupInacc] at s2
      obtain ⟨c, hcd, hfcb⟩ := s2.2 d₁ d₂ d₃ h
      simp at hfcb
      rw [upperBounds] at hb
      simp at hb
      have c1: f c ≤ b := hb _ hcd
      contradiction

end preorder

section partial_order
variable [PartialOrder α] [TopologicalSpace α] [IsScott α]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90): T0Space α :=
    (t0Space_iff_inseparable α).2 $ fun x y h => Iic_injective $
  by simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end partial_order

end IsScott

end Topology

section complete_lattice

variable [CompleteLattice α] [TopologicalSpace α] [Topology.IsScott α]

lemma isOpen_iff_isUpperSet_and_sup_mem_implies_tail_subset {u : Set α} :
    IsOpen u ↔ IsUpperSet u ∧ ∀ ⦃d : Set α⦄,
    d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u := by
  rw [Topology.IsScott.isOpen_iff_upper_and_Scott_Hausdorff_Open]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d hd₁ hd₂ a hd₃ ha => h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)⟩

lemma isOpen_iff_upper_and_sup_mem_implies_inter_nonempty
    {u : Set α} : IsOpen u ↔
    IsUpperSet u ∧  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ u →
    (d∩u).Nonempty := by
  rw [Topology.IsScott.isOpen_iff_upper_and_DirSupInacc]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d hd₁ hd₂ a hd₃ ha => h hd₁ hd₂ (Set.mem_of_eq_of_mem (IsLUB.sSup_eq hd₃) ha)⟩

lemma isClosed_iff_lower_and_closed_under_Directed_Sup {s : Set α} : IsClosed s
    ↔ IsLowerSet s ∧
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → d ⊆ s → sSup d ∈ s := by
  rw [Topology.IsScott.isClosed_iff_lower_and_subset_implies_LUB_mem]
  apply and_congr_right'
  exact ⟨fun h d hd₁ hd₂ hd₃ => h hd₁ hd₂ (isLUB_sSup d) hd₃,
    fun h d a h₁ h₂ h₃ ha => Set.mem_of_eq_of_mem (IsLUB.sSup_eq h₃).symm (h h₁ h₂ ha)⟩

end complete_lattice

variable [Preorder α]

lemma scottHausdorffTopology_le_of_scottTopology [TopologicalSpace α] [Topology.IsScott α] :
    Topology.scottHausdorff ≤ ‹TopologicalSpace α› := by
  rw [Topology.IsScott.topology_eq α, Topology.Scott]
  apply le_sup_right

lemma scottHausdorffTopology_le_Lower [TopologicalSpace α] [Topology.IsLower α] :
    Topology.scottHausdorff ≤ ‹TopologicalSpace α› :=
  fun _ h => Topology.ScottHausdorff.isOpen_of_isLowerSet (Topology.IsLower.isLowerSet_of_isOpen h)
