/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.AlexandrovDiscrete
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Order.LowerUpperTopology

/-!
# UpperSet and LowerSet topologies

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
- `Topology.IsUpperSet.monotone_to_upperTopology_continuous` - a `Monotone` map from a `Preorder`
  with the `Topology.IsUpperSet` to `Preorder` with the `UpperTopology` is `Continuous`

## Implementation notes

A type synonym `Topology.WithUpperSet` is introduced and for a preorder `α`,
`Topology.WithUpperSet α` is made an instance of `TopologicalSpace` by the topology where the upper
sets are the open sets.

We define a mixin class `Topology.IsUpperSet` for the class of types which are both a preorder and a
topology and where the open sets are the upper sets. It is shown that `Topology.WithUpperSet α` is
an instance of `Topology.IsUpperSet`.

Similarly for the lower set topology.

## Motivation

An Alexandrov topology is a topology where the intersection of any collection of open sets is open.
The `Topology.IsUpperSet` is an Alexandrov topology, and, given any Alexandrov topology, a
`Preorder` may be defined on the underlying set such that the `Topology.IsUpperSet` of the
`Preorder` coincides with the original topology.

Furthermore, the `Topology.IsUpperSet` is used in the construction of the Scott Topology.

## Tags

upper set topology, lower set topology, preorder, Alexandrov
-/

variable {α β γ : Type*}

section preorder

variable (α) [Preorder α]

/--
The set of upper sets forms a topology. In general the upper set topology does not coincide with the
upper topology.
-/
def Topology.upperSet : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_sUnion := fun _ h => isUpperSet_sUnion h, }

/--
The set of lower sets forms a topology. In general the lower set topology does not coincide with the
lower topology.
-/
def Topology.lowerSet : TopologicalSpace α :=
{ IsOpen := IsLowerSet,
  isOpen_univ := isLowerSet_univ,
  isOpen_inter := fun _ _ => IsLowerSet.inter,
  isOpen_sUnion := fun _ h => isLowerSet_sUnion h, }

end preorder

open Set TopologicalSpace

/-- Type synonym for a preorder equipped with the upper set topology. -/
def Topology.WithUpperSet (α : Type*) := α

/-- Type synonym for a preorder equipped with the lower set topology. -/
def Topology.WithLowerSet (α : Type*) := α

namespace Topology.WithUpperSet

/-- `toUpperSet` is the identity function to the `Topology.WithUpperSet` of a type.  -/
@[match_pattern]
def toUpperSet : α ≃ Topology.WithUpperSet α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `Topology.WithUpperSet` of a type.  -/
@[match_pattern]
def ofUpperSet : Topology.WithUpperSet α ≃ α := Equiv.refl _

@[simp]
theorem to_Topology.WithUpperSet_symm_eq : (@toUpperSet α).symm = ofUpperSet := rfl

@[simp]
theorem of_Topology.WithUpperSet_symm_eq : (@ofUpperSet α).symm = toUpperSet := rfl

@[simp]
theorem toUpperSet_ofUpperSet (a : Topology.WithUpperSet α) : toUpperSet (ofUpperSet a) = a := rfl

@[simp]
theorem ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl

theorem toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl

theorem ofUpperSet_inj {a b : Topology.WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `Topology.WithUpperSet`. Use as `induction x using Topology.WithUpperSet.rec`. -/
protected def rec {β : Topology.WithUpperSet α → Sort*} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
  fun a => h (ofUpperSet a)

instance [Nonempty α] : Nonempty (Topology.WithUpperSet α) := ‹Nonempty α›

instance [Inhabited α] : Inhabited (Topology.WithUpperSet α) := ‹Inhabited α›

variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]

instance : Preorder (Topology.WithUpperSet α) := ‹Preorder α›

instance : TopologicalSpace (Topology.WithUpperSet α) := Topology.upperSet α

theorem ofUpperSet_le_iff {a b : Topology.WithUpperSet α} : ofUpperSet a ≤ ofUpperSet b ↔ a ≤ b :=
  Iff.rfl

theorem toUpperSet_le_iff {a b : α} : toUpperSet a ≤ toUpperSet b ↔ a ≤ b := Iff.rfl

/-- `ofUpper` as an `OrderIso` -/
def ofUpperSetOrderIso : OrderIso (Topology.WithUpperSet α) α :=
{ ofUpperSet with
  map_rel_iff' := ofUpperSet_le_iff }

/-- `toUpper` as an `OrderIso` -/
def toUpperSetOrderIso : OrderIso α (Topology.WithUpperSet α) :=
{ toUpperSet with
  map_rel_iff' := toUpperSet_le_iff }

end Topology.WithUpperSet

namespace Topology.WithLowerSet

/-- `toLowerSet` is the identity function to the `Topology.WithLowerSet` of a type.  -/
@[match_pattern]
def toLowerSet : α ≃ Topology.WithLowerSet α := Equiv.refl _

/-- `ofLowerSet` is the identity function from the `Topology.WithLowerSet` of a type.  -/
@[match_pattern]
def ofLowerSet : Topology.WithLowerSet α ≃ α := Equiv.refl _

@[simp]
theorem to_Topology.WithLowerSet_symm_eq : (@toLowerSet α).symm = ofLowerSet := rfl

@[simp]
theorem of_Topology.WithLowerSet_symm_eq : (@ofLowerSet α).symm = toLowerSet := rfl

@[simp]
theorem toLowerSet_ofLowerSet (a : Topology.WithLowerSet α) : toLowerSet (ofLowerSet a) = a := rfl

@[simp]
theorem ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl

theorem toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl

theorem ofLowerSet_inj {a b : Topology.WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `Topology.WithLowerSet`. Use as `induction x using Topology.WithLowerSet.rec`. -/
protected def rec {β : Topology.WithLowerSet α → Sort*} (h : ∀ a, β (toLowerSet a)) : ∀ a, β a :=
  fun a => h (ofLowerSet a)

instance [Nonempty α] : Nonempty (Topology.WithLowerSet α) := ‹Nonempty α›

instance [Inhabited α] : Inhabited (Topology.WithLowerSet α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (Topology.WithLowerSet α) := ‹Preorder α›

instance : TopologicalSpace (Topology.WithLowerSet α) := Topology.lowerSet α

theorem ofLowerSet_le_iff {a b : Topology.WithLowerSet α} : ofLowerSet a ≤ ofLowerSet b ↔ a ≤ b :=
  Iff.rfl

theorem toLowerSet_le_iff {a b : α} : toLowerSet a ≤ toLowerSet b ↔ a ≤ b := Iff.rfl

/-- `ofLower` as an `OrderIso` -/
def ofLowerSetOrderIso : OrderIso (Topology.WithLowerSet α) α :=
{ ofLowerSet with
  map_rel_iff' := ofLowerSet_le_iff }

/-- `toLower` as an `OrderIso` -/
def toLowerSetOrderIso : OrderIso α (Topology.WithLowerSet α) :=
{ toLowerSet with
  map_rel_iff' := toLowerSet_le_iff }

end Topology.WithLowerSet

/--
The Upper Set topology is homeomorphic to the Lower Set topology on the dual order
-/
def Topology.WithUpperSet.toDualHomeomorph [Preorder α] :
    Topology.WithUpperSet α ≃ₜ Topology.WithLowerSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

/--
The upper set topology is the topology where the open sets are the upper sets. In general the upper
set topology does not coincide with the upper topology.
-/
class Topology.IsUpperSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = Topology.upperSet α

instance [Preorder α] : Topology.IsUpperSet (Topology.WithUpperSet α) := ⟨rfl⟩

instance [Preorder α] : @Topology.IsUpperSet (Topology.WithUpperSet α) (Topology.upperSet α) _ :=
  ⟨rfl⟩

instance [Preorder α] : @Topology.IsUpperSet α (Topology.upperSet α) _ := by
  letI := Topology.upperSet α
  exact ⟨rfl⟩

/--
The lower set topology is the topology where the open sets are the lower sets. In general the lower
set topology does not coincide with the lower topology.
-/
class Topology.IsLowerSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = Topology.lowerSet α

instance [Preorder α] : Topology.IsLowerSet (Topology.WithLowerSet α) := ⟨rfl⟩

instance [Preorder α] : @Topology.IsLowerSet (Topology.WithLowerSet α) (Topology.lowerSet α) _ :=
  ⟨rfl⟩

instance [Preorder α] : @Topology.IsLowerSet α (Topology.lowerSet α) _ := by
  letI := Topology.lowerSet α
  exact ⟨rfl⟩

namespace Topology.IsUpperSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] {s : Set α}

lemma topology_eq : ‹_› = Topology.upperSet α := topology_eq_upperSetTopology

variable {α}

instance instTopology.IsLowerSetDual [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] :
    Topology.IsLowerSet (αᵒᵈ) where
  topology_eq_lowerSetTopology := by
    ext
    rw [(Topology.IsUpperSet.topology_eq (α))]

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`Topology.WithUpperSet α`.
-/
def Topology.WithUpperSetHomeomorph : Topology.WithUpperSet α ≃ₜ α :=
  Topology.WithUpperSet.ofUpperSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma isOpen_iff_isUpperSet : IsOpen s ↔ _root_.IsUpperSet s := by
  rw [topology_eq α]
  rfl

instance toAlexandrovDiscrete : AlexandrovDiscrete α where
  isOpen_sInter S := by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
lemma isClosed_iff_isLower {s : Set α} : IsClosed s ↔ (_root_.IsLowerSet s) := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet,
    isLowerSet_compl.symm, compl_compl]

lemma isClosed_isLower {s : Set α} : IsClosed s → _root_.IsLowerSet s := fun h =>
  (isClosed_iff_isLower.mp h)

lemma closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s := by
  rw [subset_antisymm_iff]
  constructor
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)
  · apply lowerClosure_min subset_closure (isClosed_isLower isClosed_closure)

/--
The closure of a singleton `{a}` in the upper set topology is the right-closed left-infinite
interval (-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [closure_eq_lowerClosure, lowerClosure_singleton]
  rfl

end Preorder

section maps

variable [Preorder α] [Preorder β]

open Topology

protected lemma monotone_iff_continuous [TopologicalSpace α] [Topology.IsUpperSet α]
    [TopologicalSpace β] [Topology.IsUpperSet β] {f : α → β} :
    Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs ↦ IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic, ← closure_singleton] at hab ⊢
    apply (Continuous.closure_preimage_subset hf {f b})
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]

lemma monotone_to_upperTopology_continuous [TopologicalSpace α]
    [Topology.IsUpperSet α] [TopologicalSpace β] [Topology.IsUpper β] {f : α → β}
    (hf : Monotone f) : Continuous f := by
  rw [continuous_def]
  intro s hs
  rw [isOpen_iff_isUpperSet]
  apply IsUpperSet.preimage _ hf
  apply Topology.IsUpper.isUpperSet_of_isOpen hs

lemma upperSet_LE_upper {t₁ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
    {t₂ : TopologicalSpace α} [@Topology.IsUpper α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact Topology.IsUpper.isUpperSet_of_isOpen hs

end maps

end Topology.IsUpperSet

namespace Topology.IsLowerSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {s : Set α}

lemma topology_eq : ‹_› = Topology.lowerSet α := topology_eq_lowerSetTopology

variable {α}

instance instTopology.IsUpperSetDual [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] :
    Topology.IsUpperSet (αᵒᵈ) where
  topology_eq_upperSetTopology := by
    ext
    rw [(Topology.IsLowerSet.topology_eq (α))]

/-- If `α` is equipped with the lower set topology, then it is homeomorphic to
`Topology.WithLowerSet α`.
-/
def Topology.WithLowerSetHomeomorph : Topology.WithLowerSet α ≃ₜ α :=
  Topology.WithLowerSet.ofLowerSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma isOpen_iff_isLowerSet : IsOpen s ↔ _root_.IsLowerSet s := by
  rw [topology_eq α]
  rfl

instance toAlexandrovDiscrete : AlexandrovDiscrete α :=
Topology.IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)

lemma isClosed_iff_isUpper {s : Set α} : IsClosed s ↔ (_root_.IsUpperSet s) := by
  rw [← isOpen_compl_iff, isOpen_iff_isLowerSet, isUpperSet_compl.symm, compl_compl]

lemma isClosed_isUpper {s : Set α} : IsClosed s → _root_.IsUpperSet s := fun h =>
  (isClosed_iff_isUpper.mp h)

lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  Topology.IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

/--
The closure of a singleton `{a}` in the lower set topology is the right-closed left-infinite
interval (-∞,a].
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Ici a := by
  rw [closure_eq_upperClosure, upperClosure_singleton]
  rfl

end Preorder

section maps

variable [Preorder α] [Preorder β]

open Topology
open OrderDual

protected lemma monotone_iff_continuous [TopologicalSpace α] [Topology.IsLowerSet α]
    [TopologicalSpace β] [Topology.IsLowerSet β] {f : α → β} :
    Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact Topology.IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f:= (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))

lemma monotone_to_lowerTopology_continuous [TopologicalSpace α]
    [Topology.IsLowerSet α] [TopologicalSpace β] [Topology.IsLower β] {f : α → β}
    (hf : Monotone f) : Continuous f := by
  apply Topology.IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f:= (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))
  exact Monotone.dual hf

lemma lowerSet_LE_lower {t₁ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
    {t₂ : TopologicalSpace α} [@Topology.IsLower α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact Topology.IsLower.isLowerSet_of_isOpen hs

end maps

end Topology.IsLowerSet

lemma upperSet_dual_iff_lowerSet [Preorder α] [TopologicalSpace α] :
    Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α := by
  constructor
  · apply Topology.IsUpperSet.instTopology.IsLowerSetDual
  · apply Topology.IsLowerSet.instTopology.IsUpperSetDual

lemma lowerSet_dual_iff_upperSet [Preorder α] [TopologicalSpace α] :
    Topology.IsLowerSet αᵒᵈ ↔ Topology.IsUpperSet α := by
  constructor
  · apply Topology.IsLowerSet.instTopology.IsUpperSetDual
  · apply Topology.IsUpperSet.instTopology.IsLowerSetDual

namespace Topology.WithUpperSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the upper set topology. -/
def map (f : α →o β) : C(Topology.WithUpperSet α, Topology.WithUpperSet β) where
  toFun := toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 λ _s hs ↦ IsUpperSet.preimage hs f.monotone

@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β): map (g.comp f) = (map g).comp (map f) := rfl

@[simp] lemma toUpperSet_specializes_toUpperSet {a b : α} :
    toUpperSet a ⤳ toUpperSet b ↔ b ≤ a := by
  simp_rw [specializes_iff_closure_subset, Topology.IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]

@[simp] lemma ofUpperSet_le_ofUpperSet {a b : Topology.WithUpperSet α} :
    ofUpperSet a ≤ ofUpperSet b ↔ b ⤳ a := toUpperSet_specializes_toUpperSet.symm

@[simp] lemma isUpperSet_toUpperSet_preimage {s : Set (Topology.WithUpperSet α)} :
    _root_.IsUpperSet (toUpperSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

@[simp] lemma isOpen_ofUpperSet_preimage {s : Set α} : IsOpen (ofUpperSet ⁻¹' s) ↔
  _root_.IsUpperSet s := isUpperSet_toUpperSet_preimage.symm

end Topology.WithUpperSet

namespace Topology.WithLowerSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the lower set topology. -/
def map (f : α →o β) : C(Topology.WithLowerSet α, Topology.WithLowerSet β) where
  toFun := toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 λ _s hs ↦ IsLowerSet.preimage hs f.monotone

@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
@[simp] lemma map_comp (g : β →o γ) (f : α →o β): map (g.comp f) = (map g).comp (map f) := rfl

@[simp] lemma toLowerSet_specializes_toLowerSet {a b : α} :
  toLowerSet a ⤳ toLowerSet b ↔ a ≤ b := by
  simp_rw [specializes_iff_closure_subset, Topology.IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]

@[simp] lemma ofLowerSet_le_ofLowerSet {a b : Topology.WithLowerSet α} :
    ofLowerSet a ≤ ofLowerSet b ↔ a ⤳ b := toLowerSet_specializes_toLowerSet.symm

@[simp] lemma isLowerSet_toLowerSet_preimage {s : Set (Topology.WithLowerSet α)} :
    _root_.IsLowerSet (toLowerSet ⁻¹' s) ↔ IsOpen s := Iff.rfl

@[simp] lemma isOpen_ofLowerSet_preimage {s : Set α} : IsOpen (ofLowerSet ⁻¹' s) ↔
  _root_.IsLowerSet s := isLowerSet_toLowerSet_preimage.symm

end Topology.WithLowerSet
