/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Order.Minimal
/-!
# Irreducibility in topological spaces

## Main definitions

* `IrreducibleSpace`: a typeclass applying to topological spaces, stating that the space is not the
  union of a nontrivial pair of disjoint opens.
* `IsIrreducible`: for a nonempty set in a topological space, the property that the set is an
  irreducible space in the subspace topology.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.

-/

open Set Classical

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def IsPreirreducible (s : Set X) : Prop :=
  ∀ u v : Set X, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty
#align is_preirreducible IsPreirreducible

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def IsIrreducible (s : Set X) : Prop :=
  s.Nonempty ∧ IsPreirreducible s
#align is_irreducible IsIrreducible

theorem IsIrreducible.nonempty (h : IsIrreducible s) : s.Nonempty :=
  h.1
#align is_irreducible.nonempty IsIrreducible.nonempty

theorem IsIrreducible.isPreirreducible (h : IsIrreducible s) : IsPreirreducible s :=
  h.2
#align is_irreducible.is_preirreducible IsIrreducible.isPreirreducible

theorem isPreirreducible_empty : IsPreirreducible (∅ : Set X) := fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim
#align is_preirreducible_empty isPreirreducible_empty

theorem Set.Subsingleton.isPreirreducible (hs : s.Subsingleton) : IsPreirreducible s :=
  fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩
#align set.subsingleton.is_preirreducible Set.Subsingleton.isPreirreducible

-- Porting note (#10756): new lemma
theorem isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set X) :=
  subsingleton_singleton.isPreirreducible

theorem isIrreducible_singleton {x} : IsIrreducible ({x} : Set X) :=
  ⟨singleton_nonempty x, isPreirreducible_singleton⟩
#align is_irreducible_singleton isIrreducible_singleton

theorem isPreirreducible_iff_closure : IsPreirreducible (closure s) ↔ IsPreirreducible s :=
  forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]
#align is_preirreducible_iff_closure isPreirreducible_iff_closure

theorem isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s :=
  and_congr closure_nonempty_iff isPreirreducible_iff_closure
#align is_irreducible_iff_closure isIrreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure
#align is_preirreducible.closure IsPreirreducible.closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure
#align is_irreducible.closure IsIrreducible.closure

theorem exists_preirreducible (s : Set X) (H : IsPreirreducible s) :
    ∃ t : Set X, IsPreirreducible t ∧ s ⊆ t ∧ ∀ u, IsPreirreducible u → t ⊆ u → u = t :=
  let ⟨m, hm, hsm, hmm⟩ :=
    zorn_subset_nonempty { t : Set X | IsPreirreducible t }
      (fun c hc hcc _ =>
        ⟨⋃₀ c, fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
          let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy
          let ⟨q, hqc, hxq⟩ := mem_sUnion.1 hx
          Or.casesOn (hcc.total hpc hqc)
            (fun hpq : p ⊆ q =>
              let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
              ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
            fun hqp : q ⊆ p =>
            let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
            ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩,
          fun _ hxc => subset_sUnion_of_mem hxc⟩)
      s H
  ⟨m, hm, hsm, fun _u hu hmu => hmm _ hu hmu⟩
#align exists_preirreducible exists_preirreducible

/-- The set of irreducible components of a topological space. -/
def irreducibleComponents (X : Type*) [TopologicalSpace X] : Set (Set X) :=
  maximals (· ≤ ·) { s : Set X | IsIrreducible s }
#align irreducible_components irreducibleComponents

theorem isClosed_of_mem_irreducibleComponents (s) (H : s ∈ irreducibleComponents X) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed, eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)
#align is_closed_of_mem_irreducible_components isClosed_of_mem_irreducibleComponents

theorem irreducibleComponents_eq_maximals_closed (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X = maximals (· ≤ ·) { s : Set X | IsClosed s ∧ IsIrreducible s } := by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x ≤ s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this
#align irreducible_components_eq_maximals_closed irreducibleComponents_eq_maximals_closed

/-- A maximal irreducible set that contains a given point. -/
def irreducibleComponent (x : X) : Set X :=
  Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)
#align irreducible_component irreducibleComponent

theorem irreducibleComponent_property (x : X) :
    IsPreirreducible (irreducibleComponent x) ∧
      {x} ⊆ irreducibleComponent x ∧
        ∀ u, IsPreirreducible u → irreducibleComponent x ⊆ u → u = irreducibleComponent x :=
  Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)
#align irreducible_component_property irreducibleComponent_property

theorem mem_irreducibleComponent {x : X} : x ∈ irreducibleComponent x :=
  singleton_subset_iff.1 (irreducibleComponent_property x).2.1
#align mem_irreducible_component mem_irreducibleComponent

theorem isIrreducible_irreducibleComponent {x : X} : IsIrreducible (irreducibleComponent x) :=
  ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩
#align is_irreducible_irreducible_component isIrreducible_irreducibleComponent

theorem eq_irreducibleComponent {x : X} :
    IsPreirreducible s → irreducibleComponent x ⊆ s → s = irreducibleComponent x :=
  (irreducibleComponent_property x).2.2 _
#align eq_irreducible_component eq_irreducibleComponent

theorem irreducibleComponent_mem_irreducibleComponents (x : X) :
    irreducibleComponent x ∈ irreducibleComponents X :=
  ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩
#align irreducible_component_mem_irreducible_components irreducibleComponent_mem_irreducibleComponents

theorem isClosed_irreducibleComponent {x : X} : IsClosed (irreducibleComponent x) :=
  isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)
#align is_closed_irreducible_component isClosed_irreducibleComponent

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class PreirreducibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a preirreducible space, `Set.univ` is a preirreducible set. -/
  isPreirreducible_univ : IsPreirreducible (univ : Set X)
#align preirreducible_space PreirreducibleSpace

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class IrreducibleSpace (X : Type*) [TopologicalSpace X] extends PreirreducibleSpace X : Prop where
  toNonempty : Nonempty X
#align irreducible_space IrreducibleSpace

-- see Note [lower instance priority]
attribute [instance 50] IrreducibleSpace.toNonempty

theorem IrreducibleSpace.isIrreducible_univ (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] :
    IsIrreducible (univ : Set X) :=
  ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩
#align irreducible_space.is_irreducible_univ IrreducibleSpace.isIrreducible_univ

theorem irreducibleSpace_def (X : Type*) [TopologicalSpace X] :
    IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
  ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩
#align irreducible_space_def irreducibleSpace_def

theorem nonempty_preirreducible_inter [PreirreducibleSpace X] :
    IsOpen s → IsOpen t → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t
#align nonempty_preirreducible_inter nonempty_preirreducible_inter

/-- In a (pre)irreducible space, a nonempty open set is dense. -/
protected theorem IsOpen.dense [PreirreducibleSpace X] (ho : IsOpen s) (hne : s.Nonempty) :
    Dense s :=
  dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne
#align is_open.dense IsOpen.dense

theorem IsPreirreducible.image (H : IsPreirreducible s) (f : X → Y) (hf : ContinuousOn f s) :
    IsPreirreducible (f '' s) := by
  rintro u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩
  rw [← mem_preimage] at hxu hyv
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  have := H u' v' hu' hv'
  rw [inter_comm s u', ← u'_eq] at this
  rw [inter_comm s v', ← v'_eq] at this
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨x, hxs, hxu', hxv'⟩
  refine ⟨f x, mem_image_of_mem f hxs, ?_, ?_⟩
  all_goals
    rw [← mem_preimage]
    apply mem_of_mem_inter_left
    show x ∈ _ ∩ s
    simp [*]
#align is_preirreducible.image IsPreirreducible.image

theorem IsIrreducible.image (H : IsIrreducible s) (f : X → Y) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩
#align is_irreducible.image IsIrreducible.image

theorem Subtype.preirreducibleSpace (h : IsPreirreducible s) : PreirreducibleSpace s where
  isPreirreducible_univ := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩
#align subtype.preirreducible_space Subtype.preirreducibleSpace

theorem Subtype.irreducibleSpace (h : IsIrreducible s) : IrreducibleSpace s where
  isPreirreducible_univ :=
    (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype
#align subtype.irreducible_space Subtype.irreducibleSpace

/-- An infinite type with cofinite topology is an irreducible topological space. -/
instance (priority := 100) {X} [Infinite X] : IrreducibleSpace (CofiniteTopology X) where
  isPreirreducible_univ u v := by
    haveI : Infinite (CofiniteTopology X) := ‹_›
    simp only [CofiniteTopology.isOpen_iff, univ_inter]
    intro hu hv hu' hv'
    simpa only [compl_union, compl_compl] using ((hu hu').union (hv hv')).infinite_compl.nonempty
  toNonempty := (inferInstance : Nonempty X)

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
theorem isIrreducible_iff_sInter :
    IsIrreducible s ↔
      ∀ (U : Finset (Set X)), (∀ u ∈ U, IsOpen u) → (∀ u ∈ U, (s ∩ u).Nonempty) →
        (s ∩ ⋂₀ ↑U).Nonempty := by
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | @insert u U _ IH =>
      rw [Finset.coe_insert, sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}
#align is_irreducible_iff_sInter isIrreducible_iff_sInter

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
theorem isPreirreducible_iff_closed_union_closed :
    IsPreirreducible s ↔
      ∀ z₁ z₂ : Set X, IsClosed z₁ → IsClosed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := by
  refine compl_surjective.forall.trans <| forall_congr' fun z₁ => compl_surjective.forall.trans <|
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp, ← not_or, not_imp_not]
#align is_preirreducible_iff_closed_union_closed isPreirreducible_iff_closed_union_closed

/-- A set is irreducible if and only if for every cover by a finite collection of closed sets, it is
contained in one of the members of the collection. -/
theorem isIrreducible_iff_sUnion_closed :
    IsIrreducible s ↔
      ∀ t : Finset (Set X), (∀ z ∈ t, IsClosed z) → (s ⊆ ⋃₀ ↑t) → ∃ z ∈ t, s ⊆ z := by
  simp only [isIrreducible_iff_sInter]
  refine ((@compl_involutive (Set X) _).toPerm _).finsetCongr.forall_congr fun {t} => ?_
  simp_rw [Equiv.finsetCongr_apply, Finset.forall_mem_map, Finset.mem_map, Finset.coe_map,
    sUnion_image, Equiv.coe_toEmbedding, Function.Involutive.coe_toPerm, isClosed_compl_iff,
    exists_exists_and_eq_and]
  refine forall_congr' fun _ => Iff.trans ?_ not_imp_not
  simp only [not_exists, not_and, ← compl_iInter₂, ← sInter_eq_biInter,
    subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter]
#align is_irreducible_iff_sUnion_closed isIrreducible_iff_sUnion_closed

/-- A nonempty open subset of a preirreducible subspace is dense in the subspace. -/
theorem subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S)
    (hU : IsOpen U) (h : (S ∩ U).Nonempty) : S ⊆ closure (S ∩ U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S ∩ U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)
#align subset_closure_inter_of_is_preirreducible_of_is_open subset_closure_inter_of_isPreirreducible_of_isOpen

/-- If `∅ ≠ U ⊆ S ⊆ t` such that `U` is open and `t` is preirreducible, then `S` is irreducible. -/
theorem IsPreirreducible.subset_irreducible {S U : Set X} (ht : IsPreirreducible t)
    (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U ⊆ S) (h₂ : S ⊆ t) : IsIrreducible S := by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t ∩ ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x ∈ U ∧ x ∈ u ∧ x ∈ v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩
#align is_preirreducible.subset_irreducible IsPreirreducible.subset_irreducible

theorem IsPreirreducible.open_subset {U : Set X} (ht : IsPreirreducible t) (hU : IsOpen U)
    (hU' : U ⊆ t) : IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2
#align is_preirreducible.open_subset IsPreirreducible.open_subset

theorem IsPreirreducible.interior (ht : IsPreirreducible t) : IsPreirreducible (interior t) :=
  ht.open_subset isOpen_interior interior_subset
#align is_preirreducible.interior IsPreirreducible.interior

theorem IsPreirreducible.preimage (ht : IsPreirreducible t) {f : Y → X}
    (hf : OpenEmbedding f) : IsPreirreducible (f ⁻¹' t) := by
  rintro U V hU hV ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨_, h₁, ⟨y, h₂, rfl⟩, ⟨y', h₃, h₄⟩⟩ :=
    ht _ _ (hf.isOpenMap _ hU) (hf.isOpenMap _ hV) ⟨f x, hx, Set.mem_image_of_mem f hx'⟩
      ⟨f y, hy, Set.mem_image_of_mem f hy'⟩
  cases hf.inj h₄
  exact ⟨y, h₁, h₂, h₃⟩
#align is_preirreducible.preimage IsPreirreducible.preimage

end Preirreducible
