/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Order.Basic

/-!
# UpperSet and LowerSet topologies

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets and the lower set topology on a preorder as the topology where the open sets are
the lower sets.

In general the upper set topology does not coincide with the upper topology and the lower set
topology does not coincide with the lower topology.

## Main statements

- `UpperSetTopology.IsOpen_sInter` - the intersection of any set of open sets is open
- `UpperSetTopology.IsOpen_iInter` - the intersection of any indexed collection of open sets is open
- `UpperSetTopology.isClosed_iff_isLower` - a set is closed if and only if it is a Lower set
- `UpperSetTopology.closure_eq_lowerClosure` - topological closure coincides with lower closure
- `UpperSetTopology.Monotone_tfae` - the continuous functions are characterised as the monotone
  functions
- `UpperSetTopology.Monotone_to_UpperTopology_Continuous` - a `Monotone` map from a `Preorder`
  with the `UpperSetTopology` to `Preorder` with the `UpperTopology` is `Continuous`

## Implementation notes

A type synonym `WithUpperSetTopology` is introduced and for a preorder `α`, `WithUpperSetTopology α`
is made an instance of `TopologicalSpace` by the topology where the upper sets are the open sets.

We define a mixin class `UpperSetTopology` for the class of types which are both a preorder and a
topology and where the open sets are the upper sets. It is shown that `WithUpperSetTopology α` is an
instance of `UpperSetTopology`.

Similarly for the lower set topology.

## Motivation

An Alexandrov topology is a topology where the intersection of any collection of open sets is open.
The `UpperSetTopology` is an Alexandrov topology, and, given any Alexandrov topology, a `Preorder`
may be defined on the underlying set such that the `UpperSetTopology` of the `Preorder` coincides
with the original topology.

Furthermore, the `UpperSetTopology` is used in the construction of the Scott Topology.

## Tags

upper set topology, lower set topology, preorder, Alexandrov
-/

set_option autoImplicit true


variable (α β : Type*)

section preorder

variable [Preorder α]

/--
The set of upper sets forms a topology. In general the upper set topology does not coincide with the
upper topology.
-/
def upperSetTopology' : TopologicalSpace α :=
{ IsOpen := IsUpperSet,
  isOpen_univ := isUpperSet_univ,
  isOpen_inter := fun _ _ => IsUpperSet.inter,
  isOpen_sUnion := fun _ h => isUpperSet_sUnion h, }

/--
The set of lower sets forms a topology. In general the lower set topology does not coincide with the
lower topology.
-/
def lowerSetTopology' : TopologicalSpace α :=
{ IsOpen := IsLowerSet,
  isOpen_univ := isLowerSet_univ,
  isOpen_inter := fun _ _ => IsLowerSet.inter,
  isOpen_sUnion := fun _ h => isLowerSet_sUnion h, }

end preorder

open Set TopologicalSpace

/-- Type synonym for a preorder equipped with the upper set topology. -/
def WithUpperSetTopology := α

/-- Type synonym for a preorder equipped with the lower set topology. -/
def WithLowerSetTopology := α

variable {α β}

namespace WithUpperSetTopology

/-- `toUpperSet` is the identity function to the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def toUpperSet : α ≃ WithUpperSetTopology α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `WithUpperSetTopology` of a type.  -/
@[match_pattern]
def ofUpperSet : WithUpperSetTopology α ≃ α := Equiv.refl _

@[simp]
theorem to_withUpperSetTopology_symm_eq : (@toUpperSet α).symm = ofUpperSet := rfl

@[simp]
theorem of_withUpperSetTopology_symm_eq : (@ofUpperSet α).symm = toUpperSet := rfl

@[simp]
theorem toUpperSet_ofUpperSet (a : WithUpperSetTopology α) : toUpperSet (ofUpperSet a) = a := rfl

@[simp]
theorem ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl

theorem toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl

theorem ofUpperSet_inj {a b : WithUpperSetTopology α} : ofUpperSet a = ofUpperSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithUpperSetTopology`. Use as `induction x using WithUpperSetTopology.rec`. -/
protected def rec {β : WithUpperSetTopology α → Sort*} (h : ∀ a, β (toUpperSet a)) : ∀ a, β a :=
  fun a => h (ofUpperSet a)

instance [Nonempty α] : Nonempty (WithUpperSetTopology α) := ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithUpperSetTopology α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithUpperSetTopology α) := ‹Preorder α›

instance : TopologicalSpace (WithUpperSetTopology α) := upperSetTopology' α

theorem ofUpperSet_le_iff {a b : WithUpperSetTopology α} : ofUpperSet a ≤ ofUpperSet b ↔ a ≤ b :=
  Iff.rfl

theorem toUpperSet_le_iff {a b : α} : toUpperSet a ≤ toUpperSet b ↔ a ≤ b := Iff.rfl

/-- `ofUpper` as an `OrderIso` -/
def ofUpperSetOrderIso : OrderIso (WithUpperSetTopology α) α :=
{ ofUpperSet with
  map_rel_iff' := ofUpperSet_le_iff }

/-- `toUpper` as an `OrderIso` -/
def toUpperSetOrderIso : OrderIso α (WithUpperSetTopology α) :=
{ toUpperSet with
  map_rel_iff' := toUpperSet_le_iff }

end WithUpperSetTopology

namespace WithLowerSetTopology

/-- `toLowerSet` is the identity function to the `WithLowerSetTopology` of a type.  -/
@[match_pattern]
def toLowerSet : α ≃ WithLowerSetTopology α := Equiv.refl _

/-- `ofLowerSet` is the identity function from the `WithLowerSetTopology` of a type.  -/
@[match_pattern]
def ofLowerSet : WithLowerSetTopology α ≃ α := Equiv.refl _

@[simp]
theorem to_withLowerSetTopology_symm_eq : (@toLowerSet α).symm = ofLowerSet := rfl

@[simp]
theorem of_withLowerSetTopology_symm_eq : (@ofLowerSet α).symm = toLowerSet := rfl

@[simp]
theorem toLowerSet_ofLowerSet (a : WithLowerSetTopology α) : toLowerSet (ofLowerSet a) = a := rfl

@[simp]
theorem ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl

theorem toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl

theorem ofLowerSet_inj {a b : WithLowerSetTopology α} : ofLowerSet a = ofLowerSet b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithLowerSetTopology`. Use as `induction x using WithLowerSetTopology.rec`. -/
protected def rec {β : WithLowerSetTopology α → Sort*} (h : ∀ a, β (toLowerSet a)) : ∀ a, β a :=
  fun a => h (ofLowerSet a)

instance [Nonempty α] : Nonempty (WithLowerSetTopology α) := ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithLowerSetTopology α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLowerSetTopology α) := ‹Preorder α›

instance : TopologicalSpace (WithLowerSetTopology α) := lowerSetTopology' α

theorem ofLowerSet_le_iff {a b : WithLowerSetTopology α} : ofLowerSet a ≤ ofLowerSet b ↔ a ≤ b :=
  Iff.rfl

theorem toLowerSet_le_iff {a b : α} : toLowerSet a ≤ toLowerSet b ↔ a ≤ b := Iff.rfl

/-- `ofLower` as an `OrderIso` -/
def ofLowerSetOrderIso : OrderIso (WithLowerSetTopology α) α :=
{ ofLowerSet with
  map_rel_iff' := ofLowerSet_le_iff }

/-- `toLower` as an `OrderIso` -/
def toLowerSetOrderIso : OrderIso α (WithLowerSetTopology α) :=
{ toLowerSet with
  map_rel_iff' := toLowerSet_le_iff }

end WithLowerSetTopology

def UpperLowerSet_toOrderDualHomeomorph [Preorder α] :
    WithUpperSetTopology α ≃ₜ WithLowerSetTopology αᵒᵈ where
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
class UpperSetTopology (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSetTopology' α

instance [Preorder α] : UpperSetTopology (WithUpperSetTopology α) := ⟨rfl⟩

instance [Preorder α] : @UpperSetTopology (WithUpperSetTopology α) (upperSetTopology' α) _ := ⟨rfl⟩

instance [Preorder α] : @UpperSetTopology α (upperSetTopology' α) _ := by
  letI := upperSetTopology' α
  exact ⟨rfl⟩

/--
The lower set topology is the topology where the open sets are the lower sets. In general the lower
set topology does not coincide with the lower topology.
-/
class LowerSetTopology (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = lowerSetTopology' α

instance [Preorder α] : LowerSetTopology (WithLowerSetTopology α) := ⟨rfl⟩

instance [Preorder α] : @LowerSetTopology (WithLowerSetTopology α) (lowerSetTopology' α) _ := ⟨rfl⟩

instance [Preorder α] : @LowerSetTopology α (lowerSetTopology' α) _ := by
  letI := lowerSetTopology' α
  exact ⟨rfl⟩

namespace UpperSetTopology

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [UpperSetTopology α] {s : Set α}

lemma topology_eq : ‹_› = upperSetTopology' α := topology_eq_upperSetTopology

variable {α}

instance instLowerSetTopologyDual [Preorder α] [TopologicalSpace α] [UpperSetTopology α] :
    LowerSetTopology (αᵒᵈ) where
  topology_eq_lowerSetTopology := by
    ext
    rw [(UpperSetTopology.topology_eq (α))]

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSetTopology α`.
-/
def withUpperSetTopologyHomeomorph : WithUpperSetTopology α ≃ₜ α :=
  WithUpperSetTopology.ofUpperSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma IsOpen_iff_IsUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl

-- Alexandrov property, set formulation
theorem IsOpen_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsOpen s) : IsOpen (⋂₀ S) := by
  simp_rw [IsOpen_iff_IsUpperSet] at *
  apply isUpperSet_sInter
  intros s hs
  exact hf _ hs

-- Alexandrov property, index formulation
theorem isOpen_iInter {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) := by
  simp_rw [IsOpen_iff_IsUpperSet] at *
  apply isUpperSet_iInter
  intros i
  exact hf i

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
lemma isClosed_iff_isLower {s : Set α} : IsClosed s ↔ (IsLowerSet s) := by
  rw [← isOpen_compl_iff, IsOpen_iff_IsUpperSet,
    isLowerSet_compl.symm, compl_compl]

lemma isClosed_isLower {s : Set α} : IsClosed s → IsLowerSet s := fun h =>
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

protected lemma monotone_iff_continuous [TopologicalSpace α] [UpperSetTopology α]
    [TopologicalSpace β] [UpperSetTopology β] {f : α → β} :
    Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, IsOpen_iff_IsUpperSet]
    exact fun _ hs ↦ IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic, ← closure_singleton] at hab ⊢
    apply (Continuous.closure_preimage_subset hf {f b})
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]

lemma Monotone_to_UpperTopology_Continuous [TopologicalSpace α]
    [UpperSetTopology α] [TopologicalSpace β] [UpperTopology β] {f : α → β} (hf : Monotone f) :
    Continuous f := by
  rw [continuous_def]
  intro s hs
  rw [IsOpen_iff_IsUpperSet]
  apply IsUpperSet.preimage _ hf
  apply UpperTopology.isUpperSet_of_isOpen hs

lemma UpperSetLEUpper {t₁ : TopologicalSpace α} [@UpperSetTopology α t₁ _]
    {t₂ : TopologicalSpace α} [@UpperTopology α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@IsOpen_iff_IsUpperSet α _ t₁]
  exact UpperTopology.isUpperSet_of_isOpen hs

end maps

end UpperSetTopology

namespace LowerSetTopology

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [LowerSetTopology α] {s : Set α}

lemma topology_eq : ‹_› = lowerSetTopology' α := topology_eq_lowerSetTopology

variable {α}

instance instUpperSetTopologyDual [Preorder α] [TopologicalSpace α] [LowerSetTopology α] :
    UpperSetTopology (αᵒᵈ) where
  topology_eq_upperSetTopology := by
    ext
    rw [(LowerSetTopology.topology_eq (α))]

/-- If `α` is equipped with the lower set topology, then it is homeomorphic to
`WithLowerSetTopology α`.
-/
def withLowerSetTopologyHomeomorph : WithLowerSetTopology α ≃ₜ α :=
  WithLowerSetTopology.ofLowerSet.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

lemma IsOpen_iff_IsLowerSet : IsOpen s ↔ IsLowerSet s := by
  rw [topology_eq α]
  rfl

-- Alexandrov property, set formulation
theorem IsOpen_sInter {S : Set (Set α)} (hf : ∀ s ∈ S, IsOpen s) : IsOpen (⋂₀ S) :=
  UpperSetTopology.IsOpen_sInter (α := αᵒᵈ) (fun s a ↦ hf s a)

-- Alexandrov property, index formulation
theorem isOpen_iInter {f : ι → Set α} (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
  UpperSetTopology.isOpen_iInter (α := αᵒᵈ) hf

lemma isClosed_iff_isUpper {s : Set α} : IsClosed s ↔ (IsUpperSet s) := by
  rw [← isOpen_compl_iff, IsOpen_iff_IsLowerSet, isUpperSet_compl.symm, compl_compl]

lemma isClosed_isUpper {s : Set α} : IsClosed s → IsUpperSet s := fun h =>
  (isClosed_iff_isUpper.mp h)

lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  UpperSetTopology.closure_eq_lowerClosure (α := αᵒᵈ)

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

protected lemma monotone_iff_continuous [TopologicalSpace α] [LowerSetTopology α]
    [TopologicalSpace β] [LowerSetTopology β] {f : α → β} :
    Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact UpperSetTopology.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f:= (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))

lemma Monotone_to_LowerTopology_Continuous [TopologicalSpace α]
    [LowerSetTopology α] [TopologicalSpace β] [LowerTopology β] {f : α → β} (hf : Monotone f) :
    Continuous f := by
  apply UpperSetTopology.Monotone_to_UpperTopology_Continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f:= (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))
  exact Monotone.dual hf

lemma LowerSetLELower {t₁ : TopologicalSpace α} [@LowerSetTopology α t₁ _]
    {t₂ : TopologicalSpace α} [@LowerTopology α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@IsOpen_iff_IsLowerSet α _ t₁]
  exact LowerTopology.isLowerSet_of_isOpen hs

end maps

end LowerSetTopology

lemma UpperSetDual_iff_LowerSet [Preorder α] [TopologicalSpace α] :
    UpperSetTopology αᵒᵈ ↔ LowerSetTopology α := by
  constructor
  · apply UpperSetTopology.instLowerSetTopologyDual
  · apply LowerSetTopology.instUpperSetTopologyDual

lemma LowerSetDual_iff_UpperSet [Preorder α] [TopologicalSpace α] :
    LowerSetTopology αᵒᵈ ↔ UpperSetTopology α := by
  constructor
  · apply LowerSetTopology.instUpperSetTopologyDual
  · apply UpperSetTopology.instLowerSetTopologyDual
