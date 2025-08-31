/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Order.Minimal
import Mathlib.Order.Zorn
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.StacksAttribute

/-!
# Irreducibility in topological spaces

## Main definitions

* `IrreducibleSpace`: a typeclass applying to topological spaces, stating that the space
  is nonempty and does not admit a nontrivial pair of disjoint opens.
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

open Set Topology

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def IsPreirreducible (s : Set X) : Prop :=
  ∀ u v : Set X, IsOpen u → IsOpen v → (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
@[stacks 004V "(1) as predicate on subsets of a space"]
def IsIrreducible (s : Set X) : Prop :=
  s.Nonempty ∧ IsPreirreducible s

theorem IsIrreducible.nonempty (h : IsIrreducible s) : s.Nonempty :=
  h.1

theorem IsIrreducible.isPreirreducible (h : IsIrreducible s) : IsPreirreducible s :=
  h.2

theorem isPreirreducible_empty : IsPreirreducible (∅ : Set X) := fun _ _ _ _ _ ⟨_, h1, _⟩ =>
  h1.elim

theorem Set.Subsingleton.isPreirreducible (hs : s.Subsingleton) : IsPreirreducible s :=
  fun _u _v _ _ ⟨_x, hxs, hxu⟩ ⟨y, hys, hyv⟩ => ⟨y, hys, hs hxs hys ▸ hxu, hyv⟩

theorem isPreirreducible_singleton {x} : IsPreirreducible ({x} : Set X) :=
  subsingleton_singleton.isPreirreducible

theorem isIrreducible_singleton {x} : IsIrreducible ({x} : Set X) :=
  ⟨singleton_nonempty x, isPreirreducible_singleton⟩

theorem isPreirreducible_iff_closure : IsPreirreducible (closure s) ↔ IsPreirreducible s :=
  forall₄_congr fun u v hu hv => by
    iterate 3 rw [closure_inter_open_nonempty_iff]
    exacts [hu.inter hv, hv, hu]

@[stacks 004W "(1)"]
theorem isIrreducible_iff_closure : IsIrreducible (closure s) ↔ IsIrreducible s :=
  and_congr closure_nonempty_iff isPreirreducible_iff_closure

protected alias ⟨_, IsPreirreducible.closure⟩ := isPreirreducible_iff_closure

protected alias ⟨_, IsIrreducible.closure⟩ := isIrreducible_iff_closure

theorem exists_preirreducible (s : Set X) (H : IsPreirreducible s) :
    ∃ t : Set X, IsPreirreducible t ∧ s ⊆ t ∧ ∀ u, IsPreirreducible u → t ⊆ u → u = t :=
  let ⟨m, hsm, hm⟩ :=
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
  ⟨m, hm.prop, hsm, fun _u hu hmu => (hm.eq_of_subset hu hmu).symm⟩

/-- The set of irreducible components of a topological space. -/
@[stacks 004V "(2)"]
def irreducibleComponents (X : Type*) [TopologicalSpace X] : Set (Set X) :=
  {s | Maximal IsIrreducible s}

@[stacks 004W "(2)"]
theorem isClosed_of_mem_irreducibleComponents (s) (H : s ∈ irreducibleComponents X) :
    IsClosed s := by
  rw [← closure_eq_iff_isClosed, eq_comm]
  exact subset_closure.antisymm (H.2 H.1.closure subset_closure)

theorem irreducibleComponents_eq_maximals_closed (X : Type*) [TopologicalSpace X] :
    irreducibleComponents X = { s | Maximal (fun x ↦ IsClosed x ∧ IsIrreducible x) s} := by
  ext s
  constructor
  · intro H
    exact ⟨⟨isClosed_of_mem_irreducibleComponents _ H, H.1⟩, fun x h e => H.2 h.2 e⟩
  · intro H
    refine ⟨H.1.2, fun x h e => ?_⟩
    have : closure x ≤ s := H.2 ⟨isClosed_closure, h.closure⟩ (e.trans subset_closure)
    exact le_trans subset_closure this

@[stacks 004W "(3)"]
lemma exists_mem_irreducibleComponents_subset_of_isIrreducible (s : Set X) (hs : IsIrreducible s) :
    ∃ u ∈ irreducibleComponents X, s ⊆ u := by
  obtain ⟨u,hu⟩ := exists_preirreducible s hs.isPreirreducible
  use u, ⟨⟨hs.left.mono hu.right.left,hu.left⟩,fun _ h hl => (hu.right.right _ h.right hl).le⟩
  exact hu.right.left

/-- A maximal irreducible set that contains a given point. -/
@[stacks 004W "(4)"]
def irreducibleComponent (x : X) : Set X :=
  Classical.choose (exists_preirreducible {x} isPreirreducible_singleton)

theorem irreducibleComponent_property (x : X) :
    IsPreirreducible (irreducibleComponent x) ∧
      {x} ⊆ irreducibleComponent x ∧
        ∀ u, IsPreirreducible u → irreducibleComponent x ⊆ u → u = irreducibleComponent x :=
  Classical.choose_spec (exists_preirreducible {x} isPreirreducible_singleton)

@[stacks 004W "(4)"]
theorem mem_irreducibleComponent {x : X} : x ∈ irreducibleComponent x :=
  singleton_subset_iff.1 (irreducibleComponent_property x).2.1

theorem isIrreducible_irreducibleComponent {x : X} : IsIrreducible (irreducibleComponent x) :=
  ⟨⟨x, mem_irreducibleComponent⟩, (irreducibleComponent_property x).1⟩

theorem eq_irreducibleComponent {x : X} :
    IsPreirreducible s → irreducibleComponent x ⊆ s → s = irreducibleComponent x :=
  (irreducibleComponent_property x).2.2 _

theorem irreducibleComponent_mem_irreducibleComponents (x : X) :
    irreducibleComponent x ∈ irreducibleComponents X :=
  ⟨isIrreducible_irreducibleComponent, fun _ h₁ h₂ => (eq_irreducibleComponent h₁.2 h₂).le⟩

theorem isClosed_irreducibleComponent {x : X} : IsClosed (irreducibleComponent x) :=
  isClosed_of_mem_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class PreirreducibleSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a preirreducible space, `Set.univ` is a preirreducible set. -/
  isPreirreducible_univ : IsPreirreducible (univ : Set X)

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
@[stacks 004V "(1) as predicate on a space"]
class IrreducibleSpace (X : Type*) [TopologicalSpace X] : Prop extends PreirreducibleSpace X where
  toNonempty : Nonempty X

-- see Note [lower instance priority]
attribute [instance 50] IrreducibleSpace.toNonempty

theorem IrreducibleSpace.isIrreducible_univ (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] :
    IsIrreducible (univ : Set X) :=
  ⟨univ_nonempty, PreirreducibleSpace.isPreirreducible_univ⟩

theorem irreducibleSpace_def (X : Type*) [TopologicalSpace X] :
    IrreducibleSpace X ↔ IsIrreducible (⊤ : Set X) :=
  ⟨@IrreducibleSpace.isIrreducible_univ X _, fun h =>
    haveI : PreirreducibleSpace X := ⟨h.2⟩
    ⟨⟨h.1.some⟩⟩⟩

theorem nonempty_preirreducible_inter [PreirreducibleSpace X] :
    IsOpen s → IsOpen t → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using
    @PreirreducibleSpace.isPreirreducible_univ X _ _ s t

/-- In a (pre)irreducible space, a nonempty open set is dense. -/
protected theorem IsOpen.dense [PreirreducibleSpace X] (ho : IsOpen s) (hne : s.Nonempty) :
    Dense s :=
  dense_iff_inter_open.2 fun _t hto htne => nonempty_preirreducible_inter hto ho htne hne

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

@[stacks 0379]
theorem IsIrreducible.image (H : IsIrreducible s) (f : X → Y) (hf : ContinuousOn f s) :
    IsIrreducible (f '' s) :=
  ⟨H.nonempty.image _, H.isPreirreducible.image f hf⟩

theorem Subtype.preirreducibleSpace (h : IsPreirreducible s) : PreirreducibleSpace s where
  isPreirreducible_univ := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨x, hxs⟩, -, hxu⟩ ⟨⟨y, hys⟩, -, hyv⟩
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨x, hxs, ⟨hxu, hxv⟩⟩
    exact ⟨⟨x, hxs⟩, ⟨Set.mem_univ _, ⟨hxu, hxv⟩⟩⟩

theorem Subtype.irreducibleSpace (h : IsIrreducible s) : IrreducibleSpace s where
  isPreirreducible_univ :=
    (Subtype.preirreducibleSpace h.isPreirreducible).isPreirreducible_univ
  toNonempty := h.nonempty.to_subtype

instance (priority := low) [Subsingleton X] : PreirreducibleSpace X :=
  ⟨(Set.subsingleton_univ_iff.mpr ‹_›).isPreirreducible⟩

/-- An infinite type with cofinite topology is an irreducible topological space. -/
instance (priority := 100) {X} [Infinite X] : IrreducibleSpace (CofiniteTopology X) where
  isPreirreducible_univ u v := by
    haveI : Infinite (CofiniteTopology X) := ‹_›
    simp only [CofiniteTopology.isOpen_iff, univ_inter]
    intro hu hv hu' hv'
    simpa only [compl_union, compl_compl] using ((hu hu').union (hv hv')).infinite_compl.nonempty
  toNonempty := (inferInstance : Nonempty X)

theorem irreducibleComponents_eq_singleton [IrreducibleSpace X] :
    irreducibleComponents X = {univ} :=
  Set.ext fun _ ↦ IsGreatest.maximal_iff (s := IsIrreducible (X := X))
    ⟨IrreducibleSpace.isIrreducible_univ X, fun _ _ ↦ Set.subset_univ _⟩

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
theorem isIrreducible_iff_sInter :
    IsIrreducible s ↔
      ∀ (U : Finset (Set X)), (∀ u ∈ U, IsOpen u) → (∀ u ∈ U, (s ∩ u).Nonempty) →
        (s ∩ ⋂₀ ↑U).Nonempty := by
  classical
  refine ⟨fun h U hu hU => ?_, fun h => ⟨?_, ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => simpa using h.nonempty
    | insert u U _ IH =>
      rw [Finset.coe_insert, sInter_insert]
      rw [Finset.forall_mem_insert] at hu hU
      exact h.2 _ _ hu.1 (U.finite_toSet.isOpen_sInter hu.2) hU.1 (IH hu.2 hU.2)
  · simpa using h ∅
  · intro u v hu hv hu' hv'
    simpa [*] using h {u, v}

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
theorem isPreirreducible_iff_isClosed_union_isClosed :
    IsPreirreducible s ↔
      ∀ z₁ z₂ : Set X, IsClosed z₁ → IsClosed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ := by
  refine compl_surjective.forall.trans <| forall_congr' fun z₁ => compl_surjective.forall.trans <|
    forall_congr' fun z₂ => ?_
  simp only [isOpen_compl_iff, ← compl_union, inter_compl_nonempty_iff]
  refine forall₂_congr fun _ _ => ?_
  rw [← and_imp, ← not_or, not_imp_not]
@[deprecated (since := "2024-11-19")] alias
isPreirreducible_iff_closed_union_closed := isPreirreducible_iff_isClosed_union_isClosed

/-- A set is irreducible if and only if for every cover by a finite collection of closed sets, it is
contained in one of the members of the collection. -/
theorem isIrreducible_iff_sUnion_isClosed :
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

@[deprecated (since := "2024-11-19")] alias
isIrreducible_iff_sUnion_closed := isIrreducible_iff_sUnion_isClosed

/-- A nonempty open subset of a preirreducible subspace is dense in the subspace. -/
theorem subset_closure_inter_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S)
    (hU : IsOpen U) (h : (S ∩ U).Nonempty) : S ⊆ closure (S ∩ U) := by
  by_contra h'
  obtain ⟨x, h₁, h₂, h₃⟩ :=
    hS _ (closure (S ∩ U))ᶜ hU isClosed_closure.isOpen_compl h (inter_compl_nonempty_iff.mpr h')
  exact h₃ (subset_closure ⟨h₁, h₂⟩)

/-- If `∅ ≠ U ⊆ S ⊆ t` such that `U` is open and `t` is preirreducible, then `S` is irreducible. -/
theorem IsPreirreducible.subset_irreducible {S U : Set X} (ht : IsPreirreducible t)
    (hU : U.Nonempty) (hU' : IsOpen U) (h₁ : U ⊆ S) (h₂ : S ⊆ t) : IsIrreducible S := by
  obtain ⟨z, hz⟩ := hU
  replace ht : IsIrreducible t := ⟨⟨z, h₂ (h₁ hz)⟩, ht⟩
  refine ⟨⟨z, h₁ hz⟩, ?_⟩
  rintro u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  classical
  obtain ⟨x, -, hx'⟩ : Set.Nonempty (t ∩ ⋂₀ ↑({U, u, v} : Finset (Set X))) := by
    refine isIrreducible_iff_sInter.mp ht {U, u, v} ?_ ?_
    · simp [*]
    · intro U H
      simp only [Finset.mem_insert, Finset.mem_singleton] at H
      rcases H with (rfl | rfl | rfl)
      exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩]
  replace hx' : x ∈ U ∧ x ∈ u ∧ x ∈ v := by simpa using hx'
  exact ⟨x, h₁ hx'.1, hx'.2⟩

theorem IsPreirreducible.open_subset {U : Set X} (ht : IsPreirreducible t) (hU : IsOpen U)
    (hU' : U ⊆ t) : IsPreirreducible U :=
  U.eq_empty_or_nonempty.elim (fun h => h.symm ▸ isPreirreducible_empty) fun h =>
    (ht.subset_irreducible h hU (fun _ => id) hU').2

theorem IsPreirreducible.interior (ht : IsPreirreducible t) : IsPreirreducible (interior t) :=
  ht.open_subset isOpen_interior interior_subset

theorem IsPreirreducible.preimage (ht : IsPreirreducible t) {f : Y → X}
    (hf : IsOpenEmbedding f) : IsPreirreducible (f ⁻¹' t) := by
  rintro U V hU hV ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
  obtain ⟨_, h₁, ⟨y, h₂, rfl⟩, ⟨y', h₃, h₄⟩⟩ :=
    ht _ _ (hf.isOpenMap _ hU) (hf.isOpenMap _ hV) ⟨f x, hx, Set.mem_image_of_mem f hx'⟩
      ⟨f y, hy, Set.mem_image_of_mem f hy'⟩
  cases hf.injective h₄
  exact ⟨y, h₁, h₂, h₃⟩

section

open Set.Notation

@[stacks 004Z]
lemma IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V) (f : X → Y) (hf' : IsOpenMap f)
    (hf'' : V ⊆ closure (V ∩ { x | IsPreirreducible (f ⁻¹' {x}) })) :
    IsPreirreducible (f ⁻¹' V) := by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hzV, hz⟩ :=
    mem_closure_iff.mp (hf'' hzV) _ ((hf' _ hU₁).inter (hf' _ hU₂)) ⟨hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ ∈ _ from (show f z₃ = z from hz₃) ▸ hzV, hz₃'⟩

lemma IsPreirreducible.preimage_of_isPreirreducible_fiber
    {V : Set Y} (hV : IsPreirreducible V)
    (f : X → Y) (hf' : IsOpenMap f) (hf'' : ∀ x, IsPreirreducible (f ⁻¹' {x})) :
    IsPreirreducible (f ⁻¹' V) := by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'', subset_closure]

variable (f : X → Y) (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
variable (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x})) (hf₄ : Function.Surjective f)

include hf₁ hf₂ hf₃ hf₄

lemma preimage_mem_irreducibleComponents_of_isPreirreducible_fiber
    {V : Set Y} (hV : V ∈ irreducibleComponents Y) :
    f ⁻¹' V ∈ irreducibleComponents X := by
  obtain ⟨Z, hZ, hWZ, H⟩ :=
    exists_preirreducible _ (hV.1.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃)
  have hZ' : IsIrreducible Z := by
    obtain ⟨x, hx⟩ := hV.1.1
    obtain ⟨x, rfl⟩ := hf₄ x
    exact ⟨⟨_, hWZ hx⟩, hZ⟩
  have hWZ' : f ⁻¹' V = Z := by
    refine hWZ.antisymm (Set.image_subset_iff.mp ?_)
    exact hV.2 (IsIrreducible.image hZ' f hf₁.continuousOn)
      ((Set.image_preimage_eq V hf₄).symm.trans_le (Set.image_mono hWZ))
  rw [hWZ']
  exact ⟨hZ', fun s hs hs' ↦ (H s hs.2 hs').le⟩

lemma image_mem_irreducibleComponents_of_isPreirreducible_fiber
    {V : Set X} (hV : V ∈ irreducibleComponents X) :
    f '' V ∈ irreducibleComponents Y :=
  ⟨hV.1.image _ hf₁.continuousOn, fun Z hZ hWZ ↦ by
    have := hV.2 ⟨(by obtain ⟨x, hx⟩ := hV.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

/-- If `f : X → Y` is continuous, open, and has irreducible fibers, then it induces an
bijection between irreducible components -/
@[stacks 037A]
def irreducibleComponentsEquivOfIsPreirreducibleFiber :
    irreducibleComponents Y ≃o irreducibleComponents X where
  invFun W := ⟨f '' W.1,
    image_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1,
    preimage_mem_irreducibleComponents_of_isPreirreducible_fiber f hf₁ hf₂ hf₃ hf₄ W.2⟩
  right_inv W := Subtype.ext <| by
    refine (Set.subset_preimage_image _ _).antisymm' (W.2.2 ?_ (Set.subset_preimage_image _ _))
    refine ⟨?_, (W.2.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
    obtain ⟨x, hx⟩ := W.2.1.1
    exact ⟨_, x, hx, rfl⟩
  left_inv _ := Subtype.ext <| Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H ↦ ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using Set.image_mono (f := f) H

end

end Preirreducible
