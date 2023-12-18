/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Topology.Bases
import Mathlib.Order.Filter.CountableInter
/-!
# Lindelöf sets and Lindelöf spaces

## Main definitions

We define the following properties for sets in a topological space:

* `IsLindelof`: a set such that each open cover has a countable subcover. This is defined in Mathlib
  using filters.
* `LindelofSpace`: typeclass stating that the whole space is a Lindëlof set.
* `NonLindelofSpace`: a space that is not a Lindëlof space.

## Main results

* ToBeAdded
-/
open Set Filter Topology TopologicalSpace


universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Lindelof

/-- A set `s` is Lindelöf if every open cover has a countable subcover. This is implemented in
  Mathlib by showing that for every nontrivial filter `f` with the countable intersection
  property that contains `s`, there exists `a ∈ s` such that every set of `f`
  meets every neighborhood of `a`. The equivalence of these two still needs to be proven in Mathlib
  (Work in progress). -/
def IsLindelof (s : Set X) :=
  ∀ ⦃f⦄ [NeBot f] [CountableInterFilter f], f ≤ 𝓟 s → ∃ x ∈ s, ClusterPt x f

/-- Type class for Lindelöf spaces.  -/
class LindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a Lindelöf space, `Set.univ` is a Lindelöf set. -/
  isLindelof_univ : IsLindelof (univ : Set X)

/-- `X` is a non-Lindelöf topological space if it is not a Lindelöf space. -/
class NonLindelofSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a non-Lindelöf space, `Set.univ` is not a Lindelöf set. -/
  nonLindelof_univ : ¬IsLindelof (univ : Set X)

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if it belongs to each filter `𝓝 x ⊓ f`, `x ∈ s`. -/
theorem IsLindelof.compl_mem_sets (hs : IsLindelof s) {f : Filter X} [CountableInterFilter f]
  (hf : ∀ x ∈ s, sᶜ ∈ 𝓝 x ⊓ f) : sᶜ ∈ f := by
  contrapose! hf
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc] at hf ⊢
  apply @hs
  apply inf_le_right

/-- The complement to a Lindelöf set belongs to a filter `f` with the countable intersection
  property if each `x ∈ s` has a neighborhood `t` within `s` such that `tᶜ` belongs to `f`. -/
theorem IsLindelof.compl_mem_sets_of_nhdsWithin (hs : IsLindelof s) {f : Filter X}
  [CountableInterFilter f] (hf : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, tᶜ ∈ f) : sᶜ ∈ f := by
  refine' hs.compl_mem_sets fun x hx => _
  rcases hf x hx with ⟨t, ht, hst⟩
  replace ht := mem_inf_principal.1 ht
  apply mem_inf_of_inter ht hst
  rintro x ⟨h₁, h₂⟩ hs
  exact h₂ (h₁ hs)

/-- If `p : Set X → Prop` is stable under restriction and union, and each point `x`
  of a Lindelöf set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_elim]
theorem IsLindelof.induction_on (hs : IsLindelof s) {p : Set X → Prop} (he : p ∅)
    (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s)
    (hcountable_union : ∀ (S : Set (Set X)), S.Countable → (∀ s ∈ S, p s) → p (⋃ s ∈ S, s))
    (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) : p s := by
  let f : Filter X :=
    { sets := { t | p tᶜ }
      univ_sets := by simpa
      sets_of_superset := fun ht₁ ht => hmono (compl_subset_compl.2 ht) ht₁
      inter_sets := by
        intro ht₁ ht₂
        simp [compl_inter]
        intro p₁ p₂
        let Se : Set (Set X) := {ht₁ᶜ, ht₂ᶜ}
        have hSe : Se.Countable := by simp
        have : ∀ s ∈ Se, p s := by
          intros x hx
          rcases hx with ⟨rfl|_⟩
          · exact p₁
          · have h : x = ht₂ᶜ := by
              assumption
            rw [h]
            exact p₂
        have := hcountable_union Se hSe this
        have : ⋃ s∈ Se, s = ht₁ᶜ ∪ ht₂ᶜ := by simp
        rwa [← this]
        }
  have : CountableInterFilter f := by
    apply CountableInterFilter.mk
    simp [compl_sInter]
    intro S hS hsp
    let f := fun (x : Set X) ↦ xᶜ
    let S' := f '' S
    have hsp : ∀ s ∈ S', p s := by simpa
    have hS' : S'.Countable := by apply Countable.image hS
    have : ⋃ s ∈ S, sᶜ = ⋃ s ∈ S', s := by simp
    rw [this]
    apply hcountable_union S' hS' hsp
  have : sᶜ ∈ f := hs.compl_mem_sets_of_nhdsWithin (by simpa using hnhds)
  rwa [← compl_compl s]

/-- The intersection of a Lindelöf set and a closed set is a Lindelöf set. -/
theorem IsLindelof.inter_right (hs : IsLindelof s) (ht : IsClosed t) : IsLindelof (s ∩ t) := by
  intro f hnf _ hstf
  obtain ⟨x, hsx, hx⟩ : ∃ x ∈ s, ClusterPt x f :=
    hs (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _)))
  have : x ∈ t := ht.mem_of_nhdsWithin_neBot <|
    hx.mono <| le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))
  exact ⟨x, ⟨hsx, this⟩, hx⟩

  /-- The intersection of a closed set and a Lindelöf set is a Lindelöf set. -/
theorem IsLindelof.inter_left (ht : IsLindelof t) (hs : IsClosed s) : IsLindelof (s ∩ t) :=
  inter_comm t s ▸ ht.inter_right hs

  /-- The set difference of a Lindelöf set and an open set is a Lindelöf set. -/
theorem IsLindelof.diff (hs : IsLindelof s) (ht : IsOpen t) : IsLindelof (s \ t) :=
  hs.inter_right (isClosed_compl_iff.mpr ht)

/-- A closed subset of a Lindelöf set is a Lindelöf set. -/
theorem IsLindelof.of_isClosed_subset (hs : IsLindelof s) (ht : IsClosed t) (h : t ⊆ s) :
    IsLindelof t :=
  inter_eq_self_of_subset_right h ▸ hs.inter_right ht

/-- A continuous image of a Lindelöf set is a Lindelöf set within its image. -/
theorem IsLindelof.image_of_continuousOn {f : X → Y} (hs : IsLindelof s) (hf : ContinuousOn f s) :
    IsLindelof (f '' s) := by
  intro l lne _ ls
  have : NeBot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_neBot_of_image_mem lne (le_principal_iff.1 ls)
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, ClusterPt x (l.comap f ⊓ 𝓟 s) := @hs _ this _ inf_le_right
  haveI := hx.neBot
  use f x, mem_image_of_mem f hxs
  have : Tendsto f (𝓝 x ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f x) ⊓ l) := by
    convert (hf x hxs).inf (@tendsto_comap _ _ f l) using 1
    rw [nhdsWithin]
    ac_rfl
  exact this.neBot

/-- A continuous image of a Lindelöf set is a Lindelöf set within the codomain. -/
theorem IsLindelof.image {f : X → Y} (hs : IsLindelof s) (hf : Continuous f)
  : IsLindelof (f '' s) := hs.image_of_continuousOn hf.continuousOn
