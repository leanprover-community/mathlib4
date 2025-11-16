/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.Defs.Filter

/-!
# Openness and closedness of a set

This file provides lemmas relating to the predicates `IsOpen` and `IsClosed` of a set endowed with
a topology.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space
-/

open Set Filter Topology

universe u v

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.ofClosed {X : Type u} (T : Set (Set X)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ A, A ⊆ T → ⋂₀ A ∈ T)
    (union_mem : ∀ A, A ∈ T → ∀ B, B ∈ T → A ∪ B ∈ T) : TopologicalSpace X where
  IsOpen X := Xᶜ ∈ T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy

section TopologicalSpace

variable {X : Type u} {ι : Sort v} {α : Type*} {x : X} {s s₁ s₂ t : Set X} {p p₁ p₂ : X → Prop}

lemma isOpen_mk {p h₁ h₂ h₃} : IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s := Iff.rfl

@[ext (iff := false)]
protected theorem TopologicalSpace.ext :
    ∀ {f g : TopologicalSpace X}, IsOpen[f] = IsOpen[g] → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h _ => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

theorem isOpen_fold {t : TopologicalSpace X} : t.IsOpen s = IsOpen[t] s :=
  rfl

variable [TopologicalSpace X]

theorem isOpen_iUnion {f : ι → Set X} (h : ∀ i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  isOpen_sUnion (forall_mem_range.2 h)

theorem isOpen_biUnion {s : Set α} {f : α → Set X} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋃ i ∈ s, f i) :=
  isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi

theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)

lemma isOpen_iff_of_cover {f : α → Set X} (ho : ∀ i, IsOpen (f i)) (hU : (⋃ i, f i) = univ) :
    IsOpen s ↔ ∀ i, IsOpen (f i ∩ s) := by
  refine ⟨fun h i ↦ (ho i).inter h, fun h ↦ ?_⟩
  rw [← s.inter_univ, inter_comm, ← hU, iUnion_inter]
  exact isOpen_iUnion fun i ↦ h i

@[simp] theorem isOpen_empty : IsOpen (∅ : Set X) := by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim

theorem Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) (h : ∀ t ∈ s, IsOpen t) :
    IsOpen (⋂₀ s) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => rw [sInter_empty]; exact isOpen_univ
  | insert _ _ ih =>
    simp only [sInter_insert, forall_mem_insert] at h ⊢
    exact h.1.inter (ih h.2)

theorem Set.Finite.isOpen_biInter {s : Set α} {f : α → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  sInter_image f s ▸ (hs.image _).isOpen_sInter (forall_mem_image.2 h)

theorem isOpen_iInter_of_finite [Finite ι] {s : ι → Set X} (h : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  (finite_range _).isOpen_sInter (forall_mem_range.2 h)

theorem isOpen_biInter_finset {s : Finset α} {f : α → Set X} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isOpen_biInter h

@[simp]
theorem isOpen_const {p : Prop} : IsOpen { _x : X | p } := by by_cases p <;> simp [*]

theorem IsOpen.and : IsOpen { x | p₁ x } → IsOpen { x | p₂ x } → IsOpen { x | p₁ x ∧ p₂ x } :=
  IsOpen.inter

@[simp] theorem isOpen_compl_iff : IsOpen sᶜ ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩

theorem TopologicalSpace.ext_iff_isClosed {X} {t₁ t₂ : TopologicalSpace X} :
    t₁ = t₂ ↔ ∀ s, IsClosed[t₁] s ↔ IsClosed[t₂] s := by
  rw [TopologicalSpace.ext_iff, compl_surjective.forall]
  simp only [@isOpen_compl_iff _ _ t₁, @isOpen_compl_iff _ _ t₂]

alias ⟨_, TopologicalSpace.ext_isClosed⟩ := TopologicalSpace.ext_iff_isClosed

theorem isClosed_const {p : Prop} : IsClosed { _x : X | p } := ⟨isOpen_const (p := ¬p)⟩

@[simp] theorem isClosed_empty : IsClosed (∅ : Set X) := isClosed_const

@[simp] theorem isClosed_univ : IsClosed (univ : Set X) := isClosed_const

lemma IsOpen.isLocallyClosed (hs : IsOpen s) : IsLocallyClosed s :=
  ⟨_, _, hs, isClosed_univ, (inter_univ _).symm⟩

lemma IsClosed.isLocallyClosed (hs : IsClosed s) : IsLocallyClosed s :=
  ⟨_, _, isOpen_univ, hs, (univ_inter _).symm⟩

theorem IsClosed.union : IsClosed s₁ → IsClosed s₂ → IsClosed (s₁ ∪ s₂) := by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter

theorem isClosed_sInter {s : Set (Set X)} : (∀ t ∈ s, IsClosed t) → IsClosed (⋂₀ s) := by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion

theorem isClosed_iInter {f : ι → Set X} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
  isClosed_sInter <| forall_mem_range.2 h

theorem isClosed_biInter {s : Set α} {f : α → Set X} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋂ i ∈ s, f i) :=
  isClosed_iInter fun i => isClosed_iInter <| h i

@[simp]
theorem isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpen s := by
  rw [← isOpen_compl_iff, compl_compl]

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff

theorem IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ h₂.isOpen_compl

theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ∩ s₂) := by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂

theorem IsClosed.sdiff (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)

theorem Set.Finite.isClosed_biUnion {s : Set α} {f : α → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋃ i ∈ s, f i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact hs.isOpen_biInter h

lemma isClosed_biUnion_finset {s : Finset α} {f : α → Set X} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋃ i ∈ s, f i) :=
  s.finite_toSet.isClosed_biUnion h

theorem isClosed_iUnion_of_finite [Finite ι] {s : ι → Set X} (h : ∀ i, IsClosed (s i)) :
    IsClosed (⋃ i, s i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter_of_finite h

theorem isClosed_imp {p q : X → Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x → q x } := by
  simpa only [imp_iff_not_or] using hp.isClosed_compl.union hq

theorem IsClosed.not : IsClosed { a | p a } → IsOpen { a | ¬p a } :=
  isOpen_compl_iff.mpr

theorem IsClosed.and :
    IsClosed { x | p₁ x } → IsClosed { x | p₂ x } → IsClosed { x | p₁ x ∧ p₂ x } :=
  IsClosed.inter

/-!
### Limits of filters in topological spaces

In this section we define functions that return a limit of a filter (or of a function along a
filter), if it exists, and a random point otherwise. These functions are rarely used in Mathlib,
most of the theorems are written using `Filter.Tendsto`. One of the reasons is that
`Filter.limUnder f g = x` is not equivalent to `Filter.Tendsto g f (𝓝 x)` unless the codomain is a
Hausdorff space and `g` has a limit along `f`.
-/

section lim

/-- If a filter `f` is majorated by some `𝓝 x`, then it is majorated by `𝓝 (Filter.lim f)`. We
formulate this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it useful for
types without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem le_nhds_lim {f : Filter X} (h : ∃ x, f ≤ 𝓝 x) : f ≤ 𝓝 (@lim _ _ h.nonempty f) :=
  Classical.epsilon_spec h

/-- If `g` tends to some `𝓝 x` along `f`, then it tends to `𝓝 (Filter.limUnder f g)`. We formulate
this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it useful for types
without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Lean will unify this
instance with any other instance. -/
theorem tendsto_nhds_limUnder {f : Filter α} {g : α → X} (h : ∃ x, Tendsto g f (𝓝 x)) :
    Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty f g)) :=
  le_nhds_lim h

theorem limUnder_of_not_tendsto [hX : Nonempty X] {f : Filter α} {g : α → X}
    (h : ¬ ∃ x, Tendsto g f (𝓝 x)) :
    limUnder f g = Classical.choice hX := by
  simp_rw [Tendsto] at h
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h]

end lim

end TopologicalSpace
