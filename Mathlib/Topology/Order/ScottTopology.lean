/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.ScottContinuity
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

/-- A set `s` is said to be inaccessible by directed joins on `D` if, when the least upper bound of
a directed set `d` in `D` lies in `s` then `d` has non-empty intersection with `s`. -/
def DirSupInaccOn (D : Set (Set α)) (s : Set α) : Prop :=
  ∀ ⦃d⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

/-- A set `s` is said to be inaccessible by directed joins if, when the least upper bound of a
directed set `d` lies in `s` then `d` has non-empty intersection with `s`. -/
def DirSupInacc (s : Set α) : Prop :=
  ∀ ⦃d⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → a ∈ s → (d ∩ s).Nonempty

@[simp] lemma dirSupInaccOn_univ : DirSupInaccOn univ s ↔ DirSupInacc s := by
  simp [DirSupInaccOn, DirSupInacc]

@[simp] lemma DirSupInacc.dirSupInaccOn {D : Set (Set α)} :
    DirSupInacc s → DirSupInaccOn D s := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

lemma DirSupInaccOn.mono {D₁ D₂ : Set (Set α)} (hD : D₁ ⊆ D₂) (hf : DirSupInaccOn D₂ s) :
    DirSupInaccOn D₁ s := fun ⦃_⦄ a ↦ hf (hD a)

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
variable [CompleteLattice α] {s : Set α}

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

/-- The Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`. -/
def scottHausdorff (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α where
  IsOpen u := ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
    a ∈ u → ∃ b ∈ d, Ici b ∩ d ⊆ u
  isOpen_univ := fun d _ ⟨b, hb⟩ _ _ _ _ ↦ ⟨b, hb, (Ici b ∩ d).subset_univ⟩
  isOpen_inter s t hs ht d hd₀ hd₁ hd₂ a hd₃ ha := by
    obtain ⟨b₁, hb₁d, hb₁ds⟩ := hs hd₀ hd₁ hd₂ hd₃ ha.1
    obtain ⟨b₂, hb₂d, hb₂dt⟩ := ht hd₀ hd₁ hd₂ hd₃ ha.2
    obtain ⟨c, hcd, hc⟩ := hd₂ b₁ hb₁d b₂ hb₂d
    exact ⟨c, hcd, fun e ⟨hce, hed⟩ ↦ ⟨hb₁ds ⟨hc.1.trans hce, hed⟩, hb₂dt ⟨hc.2.trans hce, hed⟩⟩⟩
  isOpen_sUnion := fun s h d hd₀ hd₁ hd₂ a hd₃ ⟨s₀, hs₀s, has₀⟩ ↦ by
    obtain ⟨b, hbd, hbds₀⟩ := h s₀ hs₀s hd₀ hd₁ hd₂ hd₃ has₀
    exact ⟨b, hbd, Set.subset_sUnion_of_subset s s₀ hbds₀ hs₀s⟩

variable (α) (D : Set (Set α)) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Scott-Hausdorff topology.

A set `u` is open in the Scott-Hausdorff topology iff when the least upper bound of a directed set
`d` lies in `u` then there is a tail of `d` which is a subset of `u`. -/
class IsScottHausdorff : Prop where
  topology_eq_scottHausdorff : ‹TopologicalSpace α› = scottHausdorff α D

instance : @IsScottHausdorff α D _ (scottHausdorff α D) :=
  @IsScottHausdorff.mk _ _ _ (scottHausdorff α D) rfl

namespace IsScottHausdorff
variable {s : Set α}

lemma topology_eq [IsScottHausdorff α D] : ‹_› = scottHausdorff α D := topology_eq_scottHausdorff

variable {α D}

lemma isOpen_iff [IsScottHausdorff α D] :
    IsOpen s ↔ ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a : α⦄, IsLUB d a →
      a ∈ s → ∃ b ∈ d, Ici b ∩ d ⊆ s := by
  simp [topology_eq_scottHausdorff (α := α) (D := D), IsOpen, scottHausdorff]

lemma dirSupInaccOn_of_isOpen [IsScottHausdorff α D] (h : IsOpen s) : DirSupInaccOn D s :=
  fun d hd₀ hd₁ hd₂ a hda hd₃ ↦ by
    obtain ⟨b, hbd, hb⟩ := isOpen_iff.mp h hd₀ hd₁ hd₂ hda hd₃; exact ⟨b, hbd, hb ⟨le_rfl, hbd⟩⟩

lemma dirSupClosed_of_isClosed [IsScottHausdorff α univ] (h : IsClosed s) : DirSupClosed s := by
  apply DirSupInacc.of_compl
  rw [← dirSupInaccOn_univ]
  exact (dirSupInaccOn_of_isOpen h.isOpen_compl)

end IsScottHausdorff
end ScottHausdorff

section ScottHausdorff
namespace IsScottHausdorff

variable {s : Set α} [Preorder α] {t : TopologicalSpace α} [IsScottHausdorff α univ]

lemma isOpen_of_isLowerSet (h : IsLowerSet s) : IsOpen s :=
  (isOpen_iff (D := univ)).2 fun _d _ ⟨b, hb⟩ _ _ hda ha ↦
    ⟨b, hb, fun _ hc ↦ h (mem_upperBounds.1 hda.1 _ hc.2) ha⟩

lemma isClosed_of_isUpperSet (h : IsUpperSet s) : IsClosed s :=
  isOpen_compl_iff.1 <| isOpen_of_isLowerSet h.compl

end IsScottHausdorff
end ScottHausdorff

/-! ### Scott topology -/

section Scott
section Preorder

/-- The Scott topology.

It is defined as the join of the topology of upper sets and the Scott-Hausdorff topology. -/
def scott (α : Type*) (D : Set (Set α)) [Preorder α] : TopologicalSpace α :=
  upperSet α ⊔ scottHausdorff α D

lemma upperSet_le_scott [Preorder α] : upperSet α ≤ scott α univ := le_sup_left

lemma scottHausdorff_le_scott [Preorder α] : scottHausdorff α univ ≤ scott α univ:= le_sup_right

variable (α) (D) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Scott topology.

The Scott topology is defined as the join of the topology of upper sets and the Scott Hausdorff
topology. -/
class IsScott : Prop where
  topology_eq_scott : ‹TopologicalSpace α› = scott α D

end Preorder

namespace IsScott
section Preorder
variable (α) (D) [Preorder α] [TopologicalSpace α]

lemma topology_eq [IsScott α D] : ‹_› = scott α D := topology_eq_scott

variable {α} {D} {s : Set α} {a : α}

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ IsOpen[scottHausdorff α D] s := by rw [topology_eq α D]; rfl

lemma isOpen_iff_isUpperSet_and_dirSupInaccOn [IsScott α D] :
    IsOpen s ↔ IsUpperSet s ∧ DirSupInaccOn D s := by
  rw [isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D)]
  refine and_congr_right fun h ↦
    ⟨@IsScottHausdorff.dirSupInaccOn_of_isOpen _ _ _ (scottHausdorff α D) _ _,
      fun h' d d₀ d₁ d₂ _ d₃ ha ↦ ?_⟩
  obtain ⟨b, hbd, hbu⟩ := h' d₀ d₁ d₂ d₃ ha
  exact ⟨b, hbd, Subset.trans inter_subset_left (h.Ici_subset hbu)⟩

lemma isClosed_iff_isLowerSet_and_dirSupClosed [IsScott α univ] :
    IsClosed s ↔ IsLowerSet s ∧ DirSupClosed s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ), isUpperSet_compl,
    dirSupInaccOn_univ, dirSupInacc_compl]

lemma isUpperSet_of_isOpen [IsScott α D] : IsOpen s → IsUpperSet s := fun h ↦
  (isOpen_iff_isUpperSet_and_scottHausdorff_open (D := D).mp h).left

lemma isLowerSet_of_isClosed [IsScott α univ] : IsClosed s → IsLowerSet s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).left

lemma dirSupClosed_of_isClosed [IsScott α univ] : IsClosed s → DirSupClosed s := fun h ↦
  (isClosed_iff_isLowerSet_and_dirSupClosed.mp h).right

lemma lowerClosure_subset_closure [IsScott α univ] : ↑(lowerClosure s) ⊆ closure s := by
  convert closure.mono (@upperSet_le_scott α _)
  · rw [@IsUpperSet.closure_eq_lowerClosure α _ (upperSet α) ?_ s]
    infer_instance
  · exact topology_eq α univ

lemma isClosed_Iic [IsScott α univ] : IsClosed (Iic a) :=
  isClosed_iff_isLowerSet_and_dirSupClosed.2 ⟨isLowerSet_Iic _, dirSupClosed_Iic _⟩

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
`(-∞,a]`.
-/
@[simp] lemma closure_singleton [IsScott α univ] : closure {a} = Iic a := le_antisymm
  (closure_minimal (by rw [singleton_subset_iff, mem_Iic]) isClosed_Iic) <| by
    rw [← LowerSet.coe_Iic, ← lowerClosure_singleton]
    apply lowerClosure_subset_closure

variable [Preorder β] [TopologicalSpace β] [IsScott β univ] {f : α → β}

lemma monotone_of_continuous [IsScott α D] (hf : Continuous f) : Monotone f := fun _ b hab ↦ by
  by_contra h
  simpa only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true]
    using isUpperSet_of_isOpen (D := D) ((isOpen_compl_iff.2 isClosed_Iic).preimage hf) hab h

@[simp] lemma scottContinuous_iff_continuous {D : Set (Set α)} [Topology.IsScott α D]
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) : ScottContinuousOn D f ↔ Continuous f := by
  refine ⟨fun h ↦ continuous_def.2 fun u hu ↦ ?_, ?_⟩
  · rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)]
    exact ⟨(isUpperSet_of_isOpen (D := univ) hu).preimage (h.monotone D hD),
      fun t h₀ hd₁ hd₂ a hd₃ ha ↦ image_inter_nonempty_iff.mp <|
        (isOpen_iff_isUpperSet_and_dirSupInaccOn (D := univ).mp hu).2 trivial (Nonempty.image f hd₁)
        (directedOn_image.mpr (hd₂.mono @(h.monotone D hD))) (h h₀ hd₁ hd₂ hd₃) ha⟩
  · refine fun hf t h₀ d₁ d₂ a d₃ ↦
      ⟨(monotone_of_continuous (D := D) hf).mem_upperBounds_image d₃.1,
      fun b hb ↦ ?_⟩
    by_contra h
    let u := (Iic b)ᶜ
    have hu : IsOpen (f ⁻¹' u) := (isOpen_compl_iff.2 Topology.IsScott.isClosed_Iic).preimage hf
    rw [isOpen_iff_isUpperSet_and_dirSupInaccOn (D := D)] at hu
    obtain ⟨c, hcd, hfcb⟩ := hu.2 h₀ d₁ d₂ d₃ h
    simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      mem_setOf] at hb
    exact hfcb <| hb _ hcd

end Preorder

section PartialOrder
variable [PartialOrder α] [TopologicalSpace α] [IsScott α univ]

/--
The Scott topology on a partial order is T₀.
-/
-- see Note [lower instance priority]
instance (priority := 90) : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h ↦ Iic_injective <| by
    simpa only [inseparable_iff_closure_eq, IsScott.closure_singleton] using h

end PartialOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α]

lemma isOpen_iff_Iic_compl_or_univ [TopologicalSpace α] [Topology.IsScott α univ] (U : Set α) :
    IsOpen U ↔ U = univ ∨ ∃ a, (Iic a)ᶜ = U := by
  constructor
  · intro hU
    rcases eq_empty_or_nonempty Uᶜ with eUc | neUc
    · exact Or.inl (compl_empty_iff.mp eUc)
    · apply Or.inr
      use sSup Uᶜ
      rw [compl_eq_comm, le_antisymm_iff]
      exact ⟨fun _ ha ↦ le_sSup ha, (isLowerSet_of_isClosed hU.isClosed_compl).Iic_subset
        (dirSupClosed_iff_forall_sSup.mp (dirSupClosed_of_isClosed hU.isClosed_compl)
        neUc (isChain_of_trichotomous Uᶜ).directedOn le_rfl)⟩
  · rintro (rfl | ⟨a, rfl⟩)
    · exact isOpen_univ
    · exact isClosed_Iic.isOpen_compl

-- N.B. A number of conditions equivalent to `scott α = upper α` are given in Gierz _et al_,
-- Chapter III, Exercise 3.23.
lemma scott_eq_upper_of_completeLinearOrder : scott α univ = upper α := by
  letI := upper α
  ext U
  rw [@Topology.IsUpper.isTopologicalSpace_basis _ _ (upper α)
    ({ topology_eq_upperTopology := rfl }) U]
  letI := scott α univ
  rw [@isOpen_iff_Iic_compl_or_univ _ _ (scott α univ) ({ topology_eq_scott := rfl }) U]

/- The upper topology on a complete linear order is the Scott topology -/
instance [TopologicalSpace α] [IsUpper α] : IsScott α univ where
  topology_eq_scott := by
    rw [scott_eq_upper_of_completeLinearOrder]
    exact IsUpper.topology_eq α

end CompleteLinearOrder

lemma isOpen_iff_scottContinuous_mem [Preorder α] {s : Set α} [TopologicalSpace α]
    [IsScott α univ] : IsOpen s ↔ ScottContinuous fun x ↦ x ∈ s := by
  rw [← scottContinuousOn_univ, scottContinuous_iff_continuous (fun _ _ _ ↦ by trivial)]
  exact isOpen_iff_continuous_mem

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

lemma toScott_inj {a b : α} : toScott a = toScott b ↔ a = b := Iff.rfl

lemma ofScott_inj {a b : WithScott α} : ofScott a = ofScott b ↔ a = b := Iff.rfl
/-- A recursor for `WithScott`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithScott α → Sort _}
    (h : ∀ a, β (toScott a)) : ∀ a, β a := fun a ↦ h (ofScott a)

instance [Nonempty α] : Nonempty (WithScott α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithScott α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithScott α) := ‹Preorder α›
instance : TopologicalSpace (WithScott α) := scott α univ
instance : IsScott (WithScott α) univ := ⟨rfl⟩

lemma isOpen_iff_isUpperSet_and_scottHausdorff_open' {u : Set α} :
    IsOpen (WithScott.ofScott ⁻¹' u) ↔ IsUpperSet u ∧ (scottHausdorff α univ).IsOpen u := Iff.rfl

end WithScott
end Scott

variable [Preorder α]

lemma scottHausdorff_le_lower : scottHausdorff α univ ≤ lower α :=
  fun s h => IsScottHausdorff.isOpen_of_isLowerSet (t := scottHausdorff α univ)
      <| (@IsLower.isLowerSet_of_isOpen (Topology.WithLower α) _ _ _ s h)

variable [TopologicalSpace α]

/-- If `α` is equipped with the Scott topology, then it is homeomorphic to `WithScott α`.
-/
def IsScott.withScottHomeomorph [IsScott α univ] : WithScott α ≃ₜ α :=
  WithScott.ofScott.toHomeomorphOfIsInducing ⟨IsScott.topology_eq α univ ▸ induced_id.symm⟩

lemma IsScott.scottHausdorff_le [IsScott α univ] :
    scottHausdorff α univ ≤ ‹TopologicalSpace α› := by
  rw [IsScott.topology_eq α univ, scott]; exact le_sup_right

lemma IsLower.scottHausdorff_le [IsLower α] : scottHausdorff α univ ≤ ‹TopologicalSpace α› :=
  fun _ h ↦
    IsScottHausdorff.isOpen_of_isLowerSet (t := scottHausdorff α univ)
      <| IsLower.isLowerSet_of_isOpen h

end Topology
