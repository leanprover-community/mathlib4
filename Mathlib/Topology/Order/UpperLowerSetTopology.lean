/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Logic.Lemmas
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.LowerUpperTopology

/-!
# Upper and lower sets topologies

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets and the lower set topology on a preorder as the topology where the open sets are
the lower sets.

In general the upper set topology does not coincide with the upper topology and the lower set
topology does not coincide with the lower topology.

## Main statements

- `Topology.IsUpperSet.toAlexandrovDiscrete`: The upper set topology is Alexandrov-discrete.
- `Topology.IsUpperSet.isClosed_iff_isLower` - a set is closed if and only if it is a Lower set
- `Topology.IsUpperSet.closure_eq_lowerClosure` - topological closure coincides with lower closure
- `Topology.IsUpperSet.monotone_iff_continuous` - the continuous functions are the monotone
  functions
- `IsUpperSet.monotone_to_upperTopology_continuous`: A monotone map from a preorder with the upper
  set topology to a preorder with the upper topology is continuous.

We provide the upper set topology in three ways (and similarly for the lower set topology):
* `Topology.upperSet`: The upper set topology as a `TopologicalSpace α`
* `Topology.IsUpperSet`: Prop-valued mixin typeclass stating that an existing topology is the upper
  set topology.
* `Topology.WithUpperSet`: Type synonym equipping a preorder with its upper set topology.

## Motivation

An Alexandrov topology is a topology where the intersection of any collection of open sets is open.
The upper set topology is an Alexandrov topology and, given any Alexandrov topological space, we can
equip it with a preorder (namely the specialization preorder) whose upper set topology coincides
with the original topology. See `Topology.Specialization`.

## Tags

upper set topology, lower set topology, preorder, Alexandrov
-/

@[expose] public section

open Set TopologicalSpace Filter

variable {α β γ : Type*}

namespace Topology

/-- Topology whose open sets are upper sets.

Note: In general the upper set topology does not coincide with the upper topology. -/
def upperSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion

/-- Topology whose open sets are lower sets.

Note: In general the lower set topology does not coincide with the lower topology. -/
def lowerSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion

/-- Type synonym for a preorder equipped with the upper set topology. -/
def WithUpperSet (α : Type*) := α

namespace WithUpperSet

/-- `toUpperSet` is the identity function to the `WithUpperSet` of a type. -/
@[match_pattern] def toUpperSet : α ≃ WithUpperSet α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `WithUpperSet` of a type. -/
@[match_pattern] def ofUpperSet : WithUpperSet α ≃ α := Equiv.refl _

@[simp] lemma toUpperSet_symm : (@toUpperSet α).symm = ofUpperSet := rfl
@[simp] lemma ofUpperSet_symm : (@ofUpperSet α).symm = toUpperSet := rfl
@[simp] lemma toUpperSet_ofUpperSet (a : WithUpperSet α) : toUpperSet (ofUpperSet a) = a := rfl
@[simp] lemma ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl
lemma toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl
lemma ofUpperSet_inj {a b : WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithUpperSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithUpperSet α → Sort*} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
  fun a => h (ofUpperSet a)

instance [Nonempty α] : Nonempty (WithUpperSet α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithUpperSet α) := ‹Inhabited α›

variable [Preorder α] [Preorder β]

instance : Preorder (WithUpperSet α) := ‹Preorder α›
instance : TopologicalSpace (WithUpperSet α) := upperSet α

lemma ofUpperSet_le_iff {a b : WithUpperSet α} : ofUpperSet a ≤ ofUpperSet b ↔ a ≤ b := Iff.rfl
lemma toUpperSet_le_iff {a b : α} : toUpperSet a ≤ toUpperSet b ↔ a ≤ b := Iff.rfl

/-- `ofUpperSet` as an `OrderIso` -/
def ofUpperSetOrderIso : WithUpperSet α ≃o α where
  toEquiv := ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff

/-- `toUpperSet` as an `OrderIso` -/
def toUpperSetOrderIso : α ≃o WithUpperSet α where
  toEquiv := toUpperSet
  map_rel_iff' := toUpperSet_le_iff

end WithUpperSet

/-- Type synonym for a preorder equipped with the lower set topology. -/
def WithLowerSet (α : Type*) := α

namespace WithLowerSet

/-- `toLowerSet` is the identity function to the `WithLowerSet` of a type. -/
@[match_pattern] def toLowerSet : α ≃ WithLowerSet α := Equiv.refl _

/-- `ofLowerSet` is the identity function from the `WithLowerSet` of a type. -/
@[match_pattern] def ofLowerSet : WithLowerSet α ≃ α := Equiv.refl _

@[simp] lemma toLowerSet_symm : (@toLowerSet α).symm = ofLowerSet := rfl
@[simp] lemma ofLowerSet_symm : (@ofLowerSet α).symm = toLowerSet := rfl
@[simp] lemma toLowerSet_ofLowerSet (a : WithLowerSet α) : toLowerSet (ofLowerSet a) = a := rfl
@[simp] lemma ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl
lemma toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl
lemma ofLowerSet_inj {a b : WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithLowerSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : WithLowerSet α → Sort*} (h : ∀ a, β (toLowerSet a)) : ∀ a, β a :=
  fun a => h (ofLowerSet a)

instance [Nonempty α] : Nonempty (WithLowerSet α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLowerSet α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLowerSet α) := ‹Preorder α›
instance : TopologicalSpace (WithLowerSet α) := lowerSet α

lemma ofLowerSet_le_iff {a b : WithLowerSet α} : ofLowerSet a ≤ ofLowerSet b ↔ a ≤ b := Iff.rfl
lemma toLowerSet_le_iff {a b : α} : toLowerSet a ≤ toLowerSet b ↔ a ≤ b := Iff.rfl

/-- `ofLowerSet` as an `OrderIso` -/
def ofLowerSetOrderIso : WithLowerSet α ≃o α where
  toEquiv := ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff

/-- `toLowerSet` as an `OrderIso` -/
def toLowerSetOrderIso : α ≃o WithLowerSet α where
  toEquiv := toLowerSet
  map_rel_iff' := toLowerSet_le_iff

end WithLowerSet

/--
The Upper Set topology is homeomorphic to the Lower Set topology on the dual order
-/
def WithUpperSet.toDualHomeomorph [Preorder α] : WithUpperSet α ≃ₜ WithLowerSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng


/--
The Lower Set topology is homeomorphic to the Upper Set topology on the dual order
-/
def WithLowerSet.toDualHomeomorph [Preorder α] : WithLowerSet α ≃ₜ WithUpperSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

/-- Prop-valued mixin for an ordered topological space to be
The upper set topology is the topology where the open sets are the upper sets. In general the upper
set topology does not coincide with the upper topology.
-/
protected class IsUpperSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSet α

attribute [nolint docBlame] IsUpperSet.topology_eq_upperSetTopology

instance [Preorder α] : Topology.IsUpperSet (WithUpperSet α) := ⟨rfl⟩

instance [Preorder α] : @Topology.IsUpperSet α (upperSet α) _ := by
  letI := upperSet α
  exact ⟨rfl⟩

/--
The lower set topology is the topology where the open sets are the lower sets. In general the lower
set topology does not coincide with the lower topology.
-/
protected class IsLowerSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = lowerSet α

attribute [nolint docBlame] IsLowerSet.topology_eq_lowerSetTopology

instance [Preorder α] : Topology.IsLowerSet (WithLowerSet α) := ⟨rfl⟩

instance [Preorder α] : @Topology.IsLowerSet α (lowerSet α) _ := by
  letI := lowerSet α
  exact ⟨rfl⟩

namespace IsUpperSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] {s : Set α}

lemma topology_eq : ‹_› = upperSet α := topology_eq_upperSetTopology

variable {α}

instance _root_.OrderDual.instIsLowerSet [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] :
    Topology.IsLowerSet αᵒᵈ where
  topology_eq_lowerSetTopology := by ext; rw [IsUpperSet.topology_eq α]

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSet α`. -/
def WithUpperSetHomeomorph : WithUpperSet α ≃ₜ α :=
  WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

lemma isOpen_iff_isUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl

instance toAlexandrovDiscrete : AlexandrovDiscrete α where
  isOpen_sInter S := by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
lemma isClosed_iff_isLower : IsClosed s ↔ IsLowerSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet,
    isLowerSet_compl.symm, compl_compl]

lemma closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s := by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)

/--
The closure of a singleton `{a}` in the upper set topology is the right-closed left-infinite
interval (-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [closure_eq_lowerClosure, lowerClosure_singleton]
  rfl

lemma specializes_iff_le {a b : α} : a ⤳ b ↔ b ≤ a := by
  simp only [specializes_iff_closure_subset, closure_singleton, Iic_subset_Iic]

lemma nhdsKer_eq_upperClosure (s : Set α) : nhdsKer s = ↑(upperClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Ici a := by
  rw [nhdsKer_eq_upperClosure, upperClosure_singleton, UpperSet.coe_Ici]

lemma nhds_eq_principal_Ici (a : α) : 𝓝 a = 𝓟 (Ici a) := by
  rw [← principal_nhdsKer_singleton, nhdsKer_singleton]

lemma nhdsSet_eq_principal_upperClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(upperClosure s) := by
  rw [← principal_nhdsKer, nhdsKer_eq_upperClosure]

end Preorder

protected lemma _root_.Topology.isUpperSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsUpperSet α ↔ (∀ a : α, 𝓝 a = 𝓟 (Ici a)) where
  mp _ a := nhds_eq_principal_Ici a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Ici]⟩

instance : Topology.IsUpperSet Prop := by
  simp [Topology.isUpperSet_iff_nhds, Prop.forall]

section maps

variable [Preorder α] [Preorder β]

open Topology

protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [Topology.IsUpperSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs ↦ IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic, ← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]

lemma monotone_to_upperTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [IsUpper β] {f : α → β} (hf : Monotone f) : Continuous f := by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf

lemma upperSet_le_upper {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
    [@Topology.IsUpper α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs

end maps

end IsUpperSet

namespace IsLowerSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {s : Set α}

lemma topology_eq : ‹_› = lowerSet α := topology_eq_lowerSetTopology

variable {α}

instance _root_.OrderDual.instIsUpperSet [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] :
    Topology.IsUpperSet αᵒᵈ where
  topology_eq_upperSetTopology := by ext; rw [IsLowerSet.topology_eq α]

/-- If `α` is equipped with the lower set topology, then it is homeomorphic to `WithLowerSet α`. -/
def WithLowerSetHomeomorph : WithLowerSet α ≃ₜ α :=
  WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩

lemma isOpen_iff_isLowerSet : IsOpen s ↔ IsLowerSet s := by rw [topology_eq α]; rfl

instance toAlexandrovDiscrete : AlexandrovDiscrete α := IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)

lemma isClosed_iff_isUpper : IsClosed s ↔ IsUpperSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isLowerSet, isUpperSet_compl.symm, compl_compl]

lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

/--
The closure of a singleton `{a}` in the lower set topology is the right-closed left-infinite
interval (-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Ici a := by
  rw [closure_eq_upperClosure, upperClosure_singleton]
  rfl

lemma specializes_iff_le {a b : α} : a ⤳ b ↔ a ≤ b := by
  simp only [specializes_iff_closure_subset, closure_singleton, Ici_subset_Ici]

lemma nhdsKer_eq_lowerClosure (s : Set α) : nhdsKer s = ↑(lowerClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]

@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Iic a := by
  rw [nhdsKer_eq_lowerClosure, lowerClosure_singleton, LowerSet.coe_Iic]

lemma nhds_eq_principal_Iic (a : α) : 𝓝 a = 𝓟 (Iic a) := by
  rw [← principal_nhdsKer_singleton, nhdsKer_singleton]

lemma nhdsSet_eq_principal_lowerClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(lowerClosure s) := by
  rw [← principal_nhdsKer, nhdsKer_eq_lowerClosure]

end Preorder

protected lemma _root_.Topology.isLowerSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsLowerSet α ↔ (∀ a : α, 𝓝 a = 𝓟 (Iic a)) where
  mp _ a := nhds_eq_principal_Iic a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Iic]⟩

section maps

variable [Preorder α] [Preorder β]

open Topology
open OrderDual

protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [Topology.IsLowerSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))

lemma monotone_to_lowerTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [IsLower β] {f : α → β} (hf : Monotone f) : Continuous f :=
  IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual

lemma lowerSet_le_lower {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
    [@IsLower α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs

end maps

end IsLowerSet

lemma isUpperSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α := by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet

lemma isLowerSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsLowerSet αᵒᵈ ↔ Topology.IsUpperSet α := isUpperSet_orderDual.symm

namespace WithUpperSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the upper set topology. -/
def map (f : α →o β) : C(WithUpperSet α, WithUpperSet β) where
  toFun := toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsUpperSet.preimage hs f.monotone

@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl

@[simp] lemma toUpperSet_specializes_toUpperSet {a b : α} :
    toUpperSet a ⤳ toUpperSet b ↔ b ≤ a := by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]

@[simp] lemma ofUpperSet_le_ofUpperSet {a b : WithUpperSet α} :
    ofUpperSet a ≤ ofUpperSet b ↔ b ⤳ a := toUpperSet_specializes_toUpperSet.symm

@[simp] lemma isUpperSet_toUpperSet_preimage {s : Set (WithUpperSet α)} :
    IsUpperSet (toUpperSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

@[simp] lemma isOpen_ofUpperSet_preimage {s : Set α} :
    IsOpen (ofUpperSet ⁻¹' s) ↔ IsUpperSet s := isUpperSet_toUpperSet_preimage.symm

end WithUpperSet

namespace WithLowerSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the lower set topology. -/
def map (f : α →o β) : C(WithLowerSet α, WithLowerSet β) where
  toFun := toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsLowerSet.preimage hs f.monotone

@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl

@[simp] lemma toLowerSet_specializes_toLowerSet {a b : α} :
    toLowerSet a ⤳ toLowerSet b ↔ a ≤ b := by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]

@[simp] lemma ofLowerSet_le_ofLowerSet {a b : WithLowerSet α} :
    ofLowerSet a ≤ ofLowerSet b ↔ a ⤳ b := toLowerSet_specializes_toLowerSet.symm

@[simp] lemma isLowerSet_toLowerSet_preimage {s : Set (WithLowerSet α)} :
    IsLowerSet (toLowerSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

@[simp] lemma isOpen_ofLowerSet_preimage {s : Set α} :
    IsOpen (ofLowerSet ⁻¹' s) ↔ IsLowerSet s := isLowerSet_toLowerSet_preimage.symm

end WithLowerSet

namespace IsUpperSet
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α]
    [Preorder β] [TopologicalSpace β] [Topology.IsUpperSet β]

open scoped Filter

lemma specializes_bot [OrderBot α] {a : α} : a ⤳ ⊥ := by
  simp [IsUpperSet.specializes_iff_le]

lemma specializes_top [OrderTop α] {a : α} : ⊤ ⤳ a := by
  simp [IsUpperSet.specializes_iff_le]

@[simps]
instance [OrderBot α] : OrderBot (WithUpperSet α) where
  bot := WithUpperSet.toUpperSet ⊥
  bot_le a := by cases a; simp [WithUpperSet.toUpperSet_le_iff]

@[simps]
instance [OrderTop α] : OrderTop (WithUpperSet α) where
  top := WithUpperSet.toUpperSet ⊤
  le_top a := by cases a; simp [WithUpperSet.toUpperSet_le_iff]

lemma WithBot.continuous_coe :
    Continuous (Y := WithUpperSet <| WithBot α) (WithUpperSet.toUpperSet ∘ WithBot.some) := by
  rw [← IsUpperSet.monotone_iff_continuous]
  exact WithBot.coe_mono

lemma WithTop.continuous_coe :
    Continuous (Y := WithUpperSet <| WithTop α) (WithUpperSet.toUpperSet ∘ WithTop.some) := by
  rw [← IsUpperSet.monotone_iff_continuous]
  exact WithTop.coe_mono

lemma WithBot.isOpenEmbedding_coe :
    IsOpenEmbedding (Y := WithUpperSet <| WithBot α) (WithUpperSet.toUpperSet ∘ WithBot.some) :=
  have inj : (WithUpperSet.toUpperSet ∘ WithBot.some).Injective := Option.some_injective _
{ eq_induced := by
    ext s
    simp_rw [isOpen_induced_iff]
    constructor
    · intro hs; use WithUpperSet.toUpperSet ∘ WithBot.some '' s; split_ands
      · rw [IsUpperSet.isOpen_iff_isUpperSet, IsUpperSet]
        intro a b; cases a with | _ a => cases b with | _ b =>
        cases a using WithBot.recBotCoe <;> cases b using WithBot.recBotCoe
        rotate_right
        · simp_rw [WithUpperSet.toUpperSet_le_iff, WithBot.coe_le_coe,
           ← IsUpperSet.specializes_iff_le]; intro h
          simp_rw [← Function.comp_apply (f := WithUpperSet.toUpperSet), inj.mem_set_image]
          exact h.mem_open hs
        all_goals simp [WithBot.some, WithUpperSet, WithUpperSet.toUpperSet, WithBot.le_bot_iff]
      · rw [inj.preimage_image]
    · rintro ⟨t, tO, rfl⟩
      exact tO.preimage WithBot.continuous_coe
  injective := inj
  isOpen_range := by
    rw [← isClosed_compl_iff]
    convert_to IsClosed {(⊥ : WithUpperSet (WithBot α))}
    · ext x
      cases x using WithBot.recBotCoe <;> simp [WithUpperSet, WithUpperSet.toUpperSet]
    · rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
      rintro a b h ⟨⟩; simpa [WithUpperSet, WithBot.le_bot_iff] using h }

lemma nhds_bot [OrderBot α] : 𝓝 (⊥ : α) = ⊤ := by
  rw [eq_top_iff, le_nhds_iff]
  intro s hs sO
  rw [Filter.mem_top, eq_univ_iff_forall]
  intro x; exact specializes_bot.mem_open sO hs

omit [TopologicalSpace α] in
lemma WithBot.isClosed_singleton_bot : IsClosed {(⊥ : WithUpperSet <| WithBot α)} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro x y h ⟨⟩; cases y
  simp [WithUpperSet.toUpperSet_le_iff, WithBot.le_bot_iff] at h; simp [h]

omit [TopologicalSpace α] in
@[simp]
lemma WithBot.le_bot_iff {a : WithUpperSet (WithBot α)} :
    a ≤ WithUpperSet.toUpperSet (⊥ : WithBot α) ↔ a = WithUpperSet.toUpperSet (⊥ : WithBot α) :=
  _root_.WithBot.le_bot_iff

def WithBot.lift {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)] (Uo : IsOpen U)
    (f : C(U, α)) : C(X, WithUpperSet (WithBot α)) where
  toFun x := if h : x ∈ U then (WithUpperSet.toUpperSet ∘ WithBot.some) (f ⟨x, h⟩) else ⊥
  continuous_toFun := by
    constructor; intro s hs
    by_cases hb : ⊥ ∈ s
    · have : s = univ := by
        rw [eq_univ_iff_forall]; intro x; exact IsUpperSet.specializes_bot.mem_open hs hb
      simp [this]
    · simp only [preimage_dif, hb, exists_false, setOf_false, union_empty]
      rw [Uo.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen, preimage_setOf_eq]
      · simpa [← mem_preimage, setOf_mem_eq] using
          hs.preimage WithBot.continuous_coe |>.preimage <| map_continuous f
      · intro x; simp +contextual

@[simp]
lemma WithBot.lift_coe {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)] (Uo : IsOpen U)
    (f : C(U, α)) (x : U) :
    WithBot.lift Uo f (x : X) = (WithUpperSet.toUpperSet ∘ WithBot.some) (f x) := by
  simp [WithBot.lift]

@[simp]
lemma WithBot.lift_of_mem {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) {x : X} (hx : x ∈ U) :
    WithBot.lift Uo f x = (WithUpperSet.toUpperSet ∘ WithBot.some) (f ⟨x, hx⟩) := by
  simp [WithBot.lift, hx]

@[simp]
lemma WithBot.lift_of_notMem {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) {x : X} (hx : x ∉ U) : WithBot.lift Uo f x = ⊥ := by
  simp [WithBot.lift, hx]

@[simp]
lemma WithBot.lift_restrict {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) :
    (WithBot.lift Uo f).restrict U =
      .comp ⟨WithUpperSet.toUpperSet ∘ WithBot.some, continuous_coe⟩ f := by
  ext x; simp [WithBot.lift]

@[simp]
lemma WithBot.lift_restrict_compl {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) :
    (WithBot.lift Uo f).restrict Uᶜ = .const _ ⊥ := by
  ext x; simpa [WithBot.lift, -Subtype.coe_prop] using x.2

end IsUpperSet

namespace IsLowerSet

variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α]
    [Preorder β] [TopologicalSpace β] [Topology.IsLowerSet β]

lemma specializes_bot [OrderBot α] {a : α} : ⊥ ⤳ a := by
  simp [IsLowerSet.specializes_iff_le]

lemma specializes_top [OrderTop α] {a : α} : a ⤳ ⊤ := by
  simp [IsLowerSet.specializes_iff_le]

@[simps]
instance [OrderBot α] : OrderBot (WithLowerSet α) where
  bot := WithLowerSet.toLowerSet ⊥
  bot_le a := by cases a; simp [WithLowerSet.toLowerSet_le_iff]

@[simps]
instance [OrderTop α] : OrderTop (WithLowerSet α) where
  top := WithLowerSet.toLowerSet ⊤
  le_top a := by cases a; simp [WithLowerSet.toLowerSet_le_iff]

lemma WithTop.continuous_coe :
    Continuous (Y := WithLowerSet <| WithTop α) (WithLowerSet.toLowerSet ∘ WithTop.some) := by
  rw [← IsLowerSet.monotone_iff_continuous]
  exact WithTop.coe_mono

lemma WithBot.continuous_coe :
    Continuous (Y := WithLowerSet <| WithBot α) (WithLowerSet.toLowerSet ∘ WithBot.some) := by
  rw [← IsLowerSet.monotone_iff_continuous]
  exact WithBot.coe_mono

open OrderDual in
lemma isOpenEmbedding_iff_orderDual {f : α → β} :
    IsOpenEmbedding f ↔ IsOpenEmbedding (toDual ∘ f ∘ ofDual) := by
  let η₁ : α ≃ₜ αᵒᵈ :=
    IsLowerSet.WithLowerSetHomeomorph.symm.trans <|
      WithLowerSet.toDualHomeomorph.trans IsUpperSet.WithUpperSetHomeomorph
  let η₂ : β ≃ₜ βᵒᵈ :=
    IsLowerSet.WithLowerSetHomeomorph.symm.trans <|
      WithLowerSet.toDualHomeomorph.trans IsUpperSet.WithUpperSetHomeomorph
  have h_of : IsOpenEmbedding (@ofDual α) := η₁.symm.isOpenEmbedding
  have h_to : IsOpenEmbedding (@toDual β) := η₂.isOpenEmbedding
  refine (fun (mp : {f : _} → IsOpenEmbedding f →  IsOpenEmbedding (⇑toDual ∘ f ∘ ⇑ofDual)) ↦
    ⟨mp, ?mpr⟩) ?mp
  case mp => intro f h; exact h_to.comp (h.comp h_of)
  case mpr => intro h; simpa using mp h

lemma WithTop.isOpenEmbedding_coe :
    IsOpenEmbedding (Y := WithLowerSet <| WithTop α) (WithLowerSet.toLowerSet ∘ WithTop.some) := by
  rw [isOpenEmbedding_iff_orderDual]
  exact IsUpperSet.WithBot.isOpenEmbedding_coe

lemma nhds_top [OrderTop α] : 𝓝 (⊤ : α) = ⊤ := by
  rw [eq_top_iff, le_nhds_iff]
  intro s hs sO
  rw [Filter.mem_top, eq_univ_iff_forall]
  intro x; exact specializes_top.mem_open sO hs

omit [TopologicalSpace α] in
lemma WithTop.isClosed_singleton_top : IsClosed {(⊤ : WithLowerSet <| WithTop α)} := by
  rw [IsLowerSet.isClosed_iff_isUpper, IsUpperSet]
  rintro x y h ⟨⟩; cases y
  simp [WithLowerSet.toLowerSet_le_iff] at h; simp [h]

omit [TopologicalSpace α] in
@[simp]
lemma WithTop.top_le_iff {a : WithLowerSet (WithTop α)} :
    WithLowerSet.toLowerSet (⊤ : WithTop α) ≤ a ↔ a = WithLowerSet.toLowerSet (⊤ : WithTop α) :=
  _root_.WithTop.top_le_iff

def WithTop.lift {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)] (Uo : IsOpen U)
    (f : C(U, α)) : C(X, WithLowerSet (WithTop α)) where
  toFun x := if h : x ∈ U then (WithLowerSet.toLowerSet ∘ WithTop.some) (f ⟨x, h⟩) else ⊤
  continuous_toFun := by
    constructor; intro s hs
    by_cases hb : ⊤ ∈ s
    · have : s = univ := by
        rw [eq_univ_iff_forall]; intro x; exact IsLowerSet.specializes_top.mem_open hs hb
      simp [this]
    · simp only [preimage_dif, hb, exists_false, setOf_false, union_empty]
      rw [Uo.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen, preimage_setOf_eq]
      · simpa [← mem_preimage, setOf_mem_eq] using
          hs.preimage WithTop.continuous_coe |>.preimage <| map_continuous f
      · intro x; simp +contextual

@[simp]
lemma WithTop.lift_coe {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)] (Uo : IsOpen U)
    (f : C(U, α)) (x : U) :
    WithTop.lift Uo f (x : X) = (WithLowerSet.toLowerSet ∘ WithTop.some) (f x) := by
  simp [WithTop.lift]

@[simp]
lemma WithTop.lift_of_mem {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) {x : X} (hx : x ∈ U) :
    WithTop.lift Uo f x = (WithLowerSet.toLowerSet ∘ WithTop.some) (f ⟨x, hx⟩) := by
  simp [WithTop.lift, hx]

@[simp]
lemma WithTop.lift_of_notMem {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) {x : X} (hx : x ∉ U) : WithTop.lift Uo f x = ⊤ := by
  simp [WithTop.lift, hx]

@[simp]
lemma WithTop.lift_restrict {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) :
    (WithTop.lift Uo f).restrict U =
      .comp ⟨WithLowerSet.toLowerSet ∘ WithTop.some, continuous_coe⟩ f := by
  ext x; simp [WithTop.lift]

@[simp]
lemma WithTop.lift_restrict_compl {X} [TopologicalSpace X] {U : Set X} [DecidablePred (· ∈ U)]
    (Uo : IsOpen U) (f : C(U, α)) :
    (WithTop.lift Uo f).restrict Uᶜ = .const _ ⊤ := by
  ext x; simpa [WithTop.lift, -Subtype.coe_prop] using x.2

end IsLowerSet
end Topology
