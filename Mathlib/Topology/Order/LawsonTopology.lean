/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Order.ScottTopology

/-!
# Lawson topology

This file introduces the Lawson topology on a preorder.

## Main definitions

- `LawsonTopology'` - the Lawson topology is defined as the meet of the `LowerTopology` and the
  `ScottTopology`.

## Main statements

## Implementation notes

A type synonym `WithLawsonTopology` is introduced and for a preorder `α`, `WithLawsonTopology α`
is made an instance of `topological_space` by the `LawsonTopology'`.

We define a mixin class `LawsonTopology` for the class of types which are both a preorder and a
topology and where the topology is the `LawsonTopology'`.
It is shown that `WithLawsonTopology α` is an instance of `LawsonTopology`.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags
Lawson topology, preorder
-/

open Set

open TopologicalSpace

variable {α β : Type*}

variable [TopologicalSpace α]

--instance : TopologicalSpace (α×α) := by exact instTopologicalSpaceProd


namespace Topology

/-! ### Lawson topology -/

section Lawson
section Preorder

--variable [Preorder α]

/--
The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
def lawson (α : Type*) [Preorder α] : TopologicalSpace α := lower α ⊓ scott α

variable (α) [Preorder α] [TopologicalSpace α]

/-- Predicate for an ordered topological space to be equipped with its Lawson topology.

The Lawson topology is defined as the meet of the `LowerTopology` and the `ScottTopology`.
-/
class IsLawson : Prop where
  topology_eq_lawson : ‹TopologicalSpace α› = lawson α

end Preorder

namespace IsLawson
section Preorder
variable (α) [Preorder α] [TopologicalSpace α] [IsLawson α]

lemma topology_eq : ‹_› = lawson α := topology_eq_lawson

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawsonBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ u : Set α, IsOpen[scott α] u ∧ ∃ t : Set α, t.Finite ∧
    u ∩ (upperClosure t : Set α)ᶜ = s }

open TopologicalSpace

/-- The complements of the upper closures of finite sets intersected with Scott open sets form
a basis for the lawson topology. -/
def lawson_basis := (image2 (fun x x_1 ↦ ⇑WithLower.toLower ⁻¹' x ∩ ⇑WithScott.toScott ⁻¹' x_1)
  (IsLower.lowerBasis (WithLower α)) {U | @IsOpen (WithScott α) _ U})

protected theorem isTopologicalBasis : TopologicalSpace.IsTopologicalBasis (lawson_basis α) := by
  rw [lawson_basis]
  convert IsTopologicalBasis.inf_induced IsLower.isTopologicalBasis
    (TopologicalSpace.isTopologicalBasis_opens (α := WithScott α))
    WithLower.toLower WithScott.toScott
  erw [topology_eq α]
  rw [lawson]
  apply (congrArg₂ Inf.inf _) _
  letI _ := lower α; exact @IsLower.withLowerHomeomorph α ‹_› (lower α) ⟨rfl⟩ |>.inducing.induced
  letI _ := scott α; exact @IsScott.withScottHomeomorph α _ (scott α) ⟨rfl⟩ |>.inducing.induced


variable (s : Set α) (h: IsUpperSet s) (hs: IsOpen[Topology.scottHausdorff α] s)



-- Have the lower open sets are SH by
-- IsScottHausdorff.isOpen_of_isLowerSet (IsLower.isLowerSet_of_isOpen _)
-- Have the Scott open sets are SH by scottHausdorff_le_scott I think)
-- Together these are a subbasis
/-
lemma isOpen_implies_scottHausdorff_open {s : Set α} : IsOpen s → IsOpen[scottHausdorff α] s := by
  erw [topology_eq α];
  intro hs
  sorry
-/

--#check ⟨h, hs⟩

--#check IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩

--variable [IsScott α]

-- Get the statement deliberately wrong for now
/-
lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
  IsOpen s ↔ IsOpen[Topology.scottHausdorff α] s := by
  sorry
-/

/-
  constructor
  · intro hs
    rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr ⟨h, hs⟩]
    convert IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open.mpr _
    rw [IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
    rw [@IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open _ _ _ _ s]

    constructor
    · exact h
    · exact fun d d₁ d₂ d₃ => (@LawsonOpen_implies_ScottHausdorffOpen' _ _ l S _ _ _ _ s)
        hs d d₁ d₂ d₃
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)
-/

end Preorder
end IsLawson

/--
Type synonym for a preorder equipped with the Lawson topology
-/
def WithLawson (α : Type*) := α

namespace WithLawson

/-- `toLawson` is the identity function to the `WithLawson` of a type.  -/
@[match_pattern] def toLawson : α ≃ WithLawson α := Equiv.refl _

/-- `ofLawson` is the identity function from the `WithLawson` of a type.  -/
@[match_pattern] def ofLawson : WithLawson α ≃ α := Equiv.refl _

@[simp] lemma to_Lawson_symm_eq : (@toLawson α).symm = ofLawson := rfl
@[simp] lemma of_Lawson_symm_eq : (@ofLawson α).symm = toLawson := rfl
@[simp] lemma toLawson_ofLawson (a : WithLawson α) : toLawson (ofLawson a) = a := rfl
@[simp] lemma ofLawson_toLawson (a : α) : ofLawson (toLawson a) = a := rfl

@[simp, nolint simpNF]
lemma toLawson_inj {a b : α} : toLawson a = toLawson b ↔ a = b := Iff.rfl

@[simp, nolint simpNF]
lemma ofLawson_inj {a b : WithLawson α} : ofLawson a = ofLawson b ↔ a = b :=
Iff.rfl

/-- A recursor for `WithLawson`. Use as `induction x using WithLawson.rec`. -/
protected def rec {β : WithLawson α → Sort _}
    (h : ∀ a, β (toLawson a)) : ∀ a, β a := fun a => h (ofLawson a)

instance [Nonempty α] : Nonempty (WithLawson α) := ‹Nonempty α›
instance [Inhabited α] : Inhabited (WithLawson α) := ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLawson α) := ‹Preorder α›
instance : TopologicalSpace (WithLawson α) := lawson α
instance : IsLawson (WithLawson α) := ⟨rfl⟩

/-- If `α` is equipped with the Lawson topology, then it is homeomorphic to `WithLawson α`.
-/
def withLawsonTopologyHomeomorph [TopologicalSpace α] [IsLawson α]  : WithLawson α ≃ₜ α :=
  WithLawson.ofLawson.toHomeomorphOfInducing ⟨by erw [IsLawson.topology_eq α, induced_id]; rfl⟩

theorem isOpen_preimage_ofLawson (S : Set α) :
    IsOpen (Topology.WithLawson.ofLawson ⁻¹' S) ↔
      (lawson α).IsOpen S :=
  Iff.rfl

theorem isClosed_preimage_ofLawson (S : Set α) :
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' S) ↔
      @IsClosed (WithLawson α) _ S :=
  Iff.rfl

theorem isOpen_def (T : Set (Topology.WithLawson α)) :
    IsOpen T ↔
      (lawson α).IsOpen (Topology.WithLawson.toLawson ⁻¹' T) :=
  Iff.rfl

end WithLawson
end Lawson


namespace LawsonTopology

section preorder

variable [Preorder α]

variable [TopologicalSpace α] [Topology.IsLawson α]

variable (α)

variable {α}



/-
lemma isOpen_iff_Lower_and_Scott_Open (u : Set α) : (lawson α).IsOpen u
↔ ((lower α).IsOpen u ∧ (scott α).IsOpen u) := by
  sorry
-/


end preorder

end LawsonTopology

section ts

variable [Preorder α]

lemma Lawson_le_Scott' : lawson α ≤ scott α := inf_le_right

lemma Lawson_le_Lower' : lawson α ≤ lower α := inf_le_left

lemma Scott_Hausdorff_le_Lawson' : scottHausdorff α  ≤ lawson α := by
  rw [lawson, le_inf_iff]
  constructor
  · exact @Scott_Hausdorff_le_Lower' α _
  · exact @scottHausdorff_le_scott α _



lemma LawsonOpen_implies_ScottHausdorffOpen''' (s : Set α) :
    IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) → (scottHausdorff α).IsOpen s :=
  Scott_Hausdorff_le_Lawson' _

lemma ScottOpen_implies_LawsonOpen (s : Set α) :
    IsOpen (Topology.WithScott.ofScott ⁻¹' s) → IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) :=
  Lawson_le_Scott' _

lemma ScottClosed_implies_LawsonClosed (s : Set α) :
    IsClosed (Topology.WithScott.ofScott ⁻¹' s) →
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff]
  apply Lawson_le_Scott' _


lemma LowerOpen_implies_LawsonOpen (s : Set α) :
    IsOpen (Topology.WithLower.ofLower ⁻¹' s) → IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) :=
  Lawson_le_Lower' _

lemma LowerClosed_implies_LawsonClosed (s : Set α) :
    IsClosed (Topology.WithLower.ofLower ⁻¹' s) →
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' s) := by
  rw [← isOpen_compl_iff, ← isOpen_compl_iff]
  exact Lawson_le_Lower' _

end ts

section csh

variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [Topology.IsScott α] [Topology.IsLawson β] (e : OrderIso α β) (s : Set α)

/-
lemma Lawson_le_Scott'' [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsScott α] [Topology.IsLawson β] (e : OrderIso α β) :
    Equiv.toHomeomorphOfInducing e  ≤ α := inf_le_right
-/

/-
lemma ScottOpen_implies_LawsonOpen' [Preorder α] [Preorder β] [TopologicalSpace α]
    [TopologicalSpace β] [Topology.IsScott α] [Topology.IsLawson β] (e : OrderIso α β) (s : Set α) :
    IsOpen s → IsOpen (e '' s) := by
  apply   Lawson_le_Scott'

example [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]
  [Topology.IsScott α] [Topology.IsLawson β] (e : OrderIso α β) : Continuous e := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen'
  --apply ScottOpen_implies_LawsonOpen
  --apply Lawson_le_Scott'
-/

lemma ScottLawsonCont' [Preorder α] :
    Continuous (WithScott.toScott ∘ WithLawson.ofLawson : WithLawson α → _) := by
  rw [continuous_def]
  intro s hs
  apply ScottOpen_implies_LawsonOpen _ hs

lemma LawsonOpen_iff_ScottOpen' [Preorder α] (s : Set α) (h : IsUpperSet s) :
    IsOpen (Topology.WithScott.ofScott ⁻¹' s) ↔ IsOpen (Topology.WithLawson.ofLawson ⁻¹' s) := by
  constructor
  · apply ScottOpen_implies_LawsonOpen
  · intro hs
    rw [Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open]
    constructor
    · exact h
    · apply LawsonOpen_implies_ScottHausdorffOpen''' _ hs

variable  (L : TopologicalSpace α) (l : TopologicalSpace α) (S : TopologicalSpace α)

variable [Preorder α]  [@Topology.IsLawson α _ L] [@Topology.IsLower α l _]
  [@Topology.IsScott α _ S]

lemma Scott_le_Lawson : L ≤ S := by
  rw [@Topology.IsScott.topology_eq α _ S _, @Topology.IsLawson.topology_eq α _ L _]
  apply inf_le_right

lemma Scott_Hausdorff_le_Lawson : (scottHausdorff α) ≤ L := by
  rw [@Topology.IsLawson.topology_eq α _ L _,  lawson, le_inf_iff,
    ← @Topology.IsLower.topology_eq α _ l _, ← @Topology.IsScott.topology_eq α _ S _]
  constructor
  · exact @IsLower.scottHausdorff_le  α _ l _
  · convert scottHausdorff_le_scott
    exact IsScott.topology_eq_scott

open Topology

lemma LawsonOpen_implies_ScottHausdorffOpen : IsOpen[L] ≤ IsOpen[scottHausdorff α] := by
  rw [← TopologicalSpace.le_def]
  apply (@Scott_Hausdorff_le_Lawson _ L l _ _ _)

lemma LawsonOpen_implies_ScottHausdorffOpen' (s : Set α) :
    IsOpen[L] s → IsOpen[scottHausdorff α] s := by
  apply (@LawsonOpen_implies_ScottHausdorffOpen _ _ l)

end csh

section Preorder

open Topology

variable [Preorder α]
  (S :TopologicalSpace α) (l : TopologicalSpace α) (L : TopologicalSpace α)
  [@IsScott α _ S]  [@IsLawson α _ L] [@IsLower α l _]

-- Scott open iff UpperSet and STopology open
lemma LawsonOpen_iff_ScottOpen (s : Set α) (h : IsUpperSet s) :
    IsOpen[L] s ↔ IsOpen[S] s := by
  constructor
  · intro hs
    rw [@Topology.IsScott.isOpen_iff_isUpperSet_and_scottHausdorff_open α _ S]
    constructor
    · exact h
    · apply fun d d₁ d₂ _ => (@LawsonOpen_implies_ScottHausdorffOpen' α L l S _ _ _ _ s hs)
      exact α
      exact α
      exact α
      exact α
  · apply TopologicalSpace.le_def.mp (Scott_le_Lawson _ _)

end Preorder

section CompleteLattice

variable [CompleteLattice α] [TopologicalSpace α] [IsLawson α]

theorem isClosed_preimage_ofLawson (S : Set α) :
    IsClosed (Topology.WithLawson.ofLawson ⁻¹' S) ↔
      IsClosed S := by
  rw [← isOpen_compl_iff]
  rw [← preimage_compl]
  rw [Topology.WithLawson.isOpen_preimage_ofLawson]
  rw [← isOpen_compl_iff]
  rw [← IsLawson.topology_eq]
  exact Eq.to_iff rfl

lemma singletonUpperLower (a : α) : ↑(upperClosure {a}) ∩ ↑(lowerClosure {a}) = ({a} : Set α) :=
  Set.OrdConnected.upperClosure_inter_lowerClosure ordConnected_singleton

lemma singletonIsClosed (a : α) : IsClosed ({a} : Set α) := by
  rw [← singletonUpperLower]
  apply IsClosed.inter
  · rw [← isClosed_preimage_ofLawson]
    apply LowerClosed_implies_LawsonClosed
    apply IsLower.isClosed_upperClosure
    exact finite_singleton a
  · rw [← isClosed_preimage_ofLawson]
    apply ScottClosed_implies_LawsonClosed
    simp only [lowerClosure_singleton, LowerSet.coe_Iic]
    exact Topology.IsScott.isClosed_Iic

instance (priority := 90) t0Space : T0Space α where
  t0 := by
    intros a b h
    rw [inseparable_iff_closure_eq, closure_eq_iff_isClosed.mpr (singletonIsClosed a),
      closure_eq_iff_isClosed.mpr (singletonIsClosed b), singleton_eq_singleton_iff] at h
    exact h


/- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`.
def IsCompact (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f
-/
--#check IsCompact

--prefilters (also known as filter bases)
--#check FilterBasis
--filter subbasis - finite intersectio property - any finite collection has non-empty intersection

-- Ultrafilter lemma
--#check Ultrafilter.exists_le

/-
`isCompact_of_finite_subcover` says that if a set satisfies the traditional property of every
open cover having a finite sub-cover then the set is compact in the filter definition
-/
--#check isCompact_of_finite_subcover

/-
theorem isCompact_iff_ultrafilter_le_nhds :
    IsCompact s ↔ ∀ f : Ultrafilter X, ↑f ≤ 𝓟 s → ∃ x ∈ s, ↑f ≤ 𝓝 x
-/
--#check isCompact_iff_ultrafilter_le_nhds

-- {s : Set (Set α)} generateFrom s



/-
instance (priority := 90) compactSpace : CompactSpace α where
  isCompact_univ := by
    sorry
-/

end CompleteLattice

/-
variable {s : Set (Set β)}

#check generateFrom s

universe u

variable {ι : Type u} (U : ι → s)

#check (Set.univ : Set β)

variable (i : ι)

#check (U i : Set β)

#check Classical.choice

variable [t : TopologicalSpace β]
-/

-- Probably not the optimal argument as still requires axiom of choice
/-
theorem isCompact_of_finite_subcover
    (ht : t = generateFrom s) (h : ∀ {ι : Type u} (U : ι → s), (univ  ⊆ ⋃ i, (U i : Set β)) →
      ∃ t : Finset ι, univ ⊆ ⋃ i ∈ t, (U i : Set β)) :
    CompactSpace β  where
  isCompact_univ := by
    rw [isCompact_iff_ultrafilter_le_nhds]
    by_contra nH
    simp at nH
    rcases nH with ⟨F,hF⟩
    have e1 (x : β) : ∃ S ∈ s, x ∈ S ∧ S ∉ F := sorry
    let V : β → s := fun x => by choice
-/
