/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Topology.Defs.Filter

/-!
# Basic theory of topological spaces

The main definition is the typeclass `TopologicalSpace X` which endows a type `X` with a topology.
Then `Set X` gets predicates `IsOpen`, `IsClosed` and functions `interior`, `closure` and
`frontier`.

## Notation

The following notation is introduced elsewhere and it is heavily used in this file.

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`.

## Implementation notes

Topology in mathlib heavily uses filters (even more than in Bourbaki). See explanations in
<https://leanprover-community.github.io/theories/topology.html>.

## References

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

## Tags

topological space, interior, closure, frontier
-/

open Set Filter

universe u v w x

/-! ### Topological spaces -/

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

variable {X : Type u} {Y : Type v} {ι : Sort w} {α β : Type*}
  {x : X} {s s₁ s₂ t : Set X} {p p₁ p₂ : X → Prop}

open Topology

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

/-! ### Interior of a set -/

theorem mem_interior : x ∈ interior s ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_setOf_eq, and_assoc, and_left_comm]

@[simp]
theorem isOpen_interior : IsOpen (interior s) :=
  isOpen_sUnion fun _ => And.left

theorem interior_subset : interior s ⊆ s :=
  sUnion_subset fun _ => And.right

theorem interior_maximal (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩

theorem IsOpen.interior_eq (h : IsOpen s) : interior s = s :=
  interior_subset.antisymm (interior_maximal (Subset.refl s) h)

theorem interior_eq_iff_isOpen : interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩

theorem subset_interior_iff_isOpen : s ⊆ interior s ↔ IsOpen s := by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]

theorem IsOpen.subset_interior_iff (h₁ : IsOpen s) : s ⊆ interior t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩

theorem subset_interior_iff : t ⊆ interior s ↔ ∃ U, IsOpen U ∧ t ⊆ U ∧ U ⊆ s :=
  ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩

lemma interior_subset_iff : interior s ⊆ t ↔ ∀ U, IsOpen U → U ⊆ s → U ⊆ t := by
  simp [interior]

@[mono, gcongr]
theorem interior_mono (h : s ⊆ t) : interior s ⊆ interior t :=
  interior_maximal (Subset.trans interior_subset h) isOpen_interior

@[simp]
theorem interior_empty : interior (∅ : Set X) = ∅ :=
  isOpen_empty.interior_eq

@[simp]
theorem interior_univ : interior (univ : Set X) = univ :=
  isOpen_univ.interior_eq

@[simp]
theorem interior_eq_univ : interior s = univ ↔ s = univ :=
  ⟨fun h => univ_subset_iff.mp <| h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩

@[simp]
theorem interior_interior : interior (interior s) = interior s :=
  isOpen_interior.interior_eq

@[simp]
theorem interior_inter : interior (s ∩ t) = interior s ∩ interior t :=
  (Monotone.map_inf_le (fun _ _ ↦ interior_mono) s t).antisymm <|
    interior_maximal (inter_subset_inter interior_subset interior_subset) <|
      isOpen_interior.inter isOpen_interior

theorem Set.Finite.interior_biInter {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set X) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ _ => simp [*]

theorem Set.Finite.interior_sInter {S : Set (Set X)} (hS : S.Finite) :
    interior (⋂₀ S) = ⋂ s ∈ S, interior s := by
  rw [sInter_eq_biInter, hS.interior_biInter]

@[simp]
theorem Finset.interior_iInter {ι : Type*} (s : Finset ι) (f : ι → Set X) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) :=
  s.finite_toSet.interior_biInter f

@[simp]
theorem interior_iInter_of_finite [Finite ι] (f : ι → Set X) :
    interior (⋂ i, f i) = ⋂ i, interior (f i) := by
  rw [← sInter_range, (finite_range f).interior_sInter, biInter_range]

@[simp]
theorem interior_iInter₂_lt_nat {n : ℕ} (f : ℕ → Set X) :
    interior (⋂ m < n, f m) = ⋂ m < n, interior (f m) :=
  (finite_lt_nat n).interior_biInter f

@[simp]
theorem interior_iInter₂_le_nat {n : ℕ} (f : ℕ → Set X) :
    interior (⋂ m ≤ n, f m) = ⋂ m ≤ n, interior (f m) :=
  (finite_le_nat n).interior_biInter f

theorem interior_union_isClosed_of_interior_empty (h₁ : IsClosed s)
    (h₂ : interior t = ∅) : interior (s ∪ t) = interior s :=
  have : interior (s ∪ t) ⊆ s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s ⊆ t := fun _ ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s ⊆ interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s ⊆ ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono subset_union_left)

theorem isOpen_iff_forall_mem_open : IsOpen s ↔ ∀ x ∈ s, ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]

theorem interior_iInter_subset (s : ι → Set X) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) :=
  subset_iInter fun _ => interior_mono <| iInter_subset _ _

theorem interior_iInter₂_subset (p : ι → Sort*) (s : ∀ i, p i → Set X) :
    interior (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), interior (s i j) :=
  (interior_iInter_subset _).trans <| iInter_mono fun _ => interior_iInter_subset _

theorem interior_sInter_subset (S : Set (Set X)) : interior (⋂₀ S) ⊆ ⋂ s ∈ S, interior s :=
  calc
    interior (⋂₀ S) = interior (⋂ s ∈ S, s) := by rw [sInter_eq_biInter]
    _ ⊆ ⋂ s ∈ S, interior s := interior_iInter₂_subset _ _

theorem Filter.HasBasis.lift'_interior {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) : (l.lift' interior).HasBasis p fun i => interior (s i) :=
  h.lift' fun _ _ ↦ interior_mono

theorem Filter.lift'_interior_le (l : Filter X) : l.lift' interior ≤ l := fun _s hs ↦
  mem_of_superset (mem_lift' hs) interior_subset

theorem Filter.HasBasis.lift'_interior_eq_self {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) (ho : ∀ i, p i → IsOpen (s i)) : l.lift' interior = l :=
  le_antisymm l.lift'_interior_le <| h.lift'_interior.ge_iff.2 fun i hi ↦ by
    simpa only [(ho i hi).interior_eq] using h.mem_of_mem hi

/-! ### Closure of a set -/

@[simp]
theorem isClosed_closure : IsClosed (closure s) :=
  isClosed_sInter fun _ => And.left

theorem subset_closure : s ⊆ closure s :=
  subset_sInter fun _ => And.right

theorem not_mem_of_not_mem_closure {P : X} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)

theorem closure_minimal (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  sInter_subset_of_mem ⟨h₂, h₁⟩

theorem Disjoint.closure_left (hd : Disjoint s t) (ht : IsOpen t) :
    Disjoint (closure s) t :=
  disjoint_compl_left.mono_left <| closure_minimal hd.subset_compl_right ht.isClosed_compl

theorem Disjoint.closure_right (hd : Disjoint s t) (hs : IsOpen s) :
    Disjoint s (closure t) :=
  (hd.symm.closure_left hs).symm

@[simp] theorem IsClosed.closure_eq (h : IsClosed s) : closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure

theorem IsClosed.closure_subset (hs : IsClosed s) : closure s ⊆ s :=
  closure_minimal (Subset.refl _) hs

theorem IsClosed.closure_subset_iff (h₁ : IsClosed t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩

theorem IsClosed.mem_iff_closure_subset (hs : IsClosed s) :
    x ∈ s ↔ closure ({x} : Set X) ⊆ s :=
  (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm

@[mono, gcongr]
theorem closure_mono (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_minimal (Subset.trans h subset_closure) isClosed_closure

theorem monotone_closure (X : Type*) [TopologicalSpace X] : Monotone (@closure X _) := fun _ _ =>
  closure_mono

theorem diff_subset_closure_iff : s \ t ⊆ closure t ↔ s ⊆ closure t := by
  rw [diff_subset_iff, union_eq_self_of_subset_left subset_closure]

theorem closure_inter_subset_inter_closure (s t : Set X) :
    closure (s ∩ t) ⊆ closure s ∩ closure t :=
  (monotone_closure X).map_inf_le s t

theorem isClosed_of_closure_subset (h : closure s ⊆ s) : IsClosed s := by
  rw [subset_closure.antisymm h]; exact isClosed_closure

theorem closure_eq_iff_isClosed : closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩

theorem closure_subset_iff_isClosed : closure s ⊆ s ↔ IsClosed s :=
  ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩

theorem closure_empty : closure (∅ : Set X) = ∅ :=
  isClosed_empty.closure_eq

@[simp]
theorem closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]
theorem closure_nonempty_iff : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff

theorem closure_univ : closure (univ : Set X) = univ :=
  isClosed_univ.closure_eq

theorem closure_closure : closure (closure s) = closure s :=
  isClosed_closure.closure_eq

theorem closure_eq_compl_interior_compl : closure s = (interior sᶜ)ᶜ := by
  rw [interior, closure, compl_sUnion, compl_image_set_of]
  simp only [compl_subset_compl, isOpen_compl_iff]

@[simp]
theorem closure_union : closure (s ∪ t) = closure s ∪ closure t := by
  simp [closure_eq_compl_interior_compl, compl_inter]

theorem Set.Finite.closure_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → Set X) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  simp [closure_eq_compl_interior_compl, hs.interior_biInter]

theorem Set.Finite.closure_sUnion {S : Set (Set X)} (hS : S.Finite) :
    closure (⋃₀ S) = ⋃ s ∈ S, closure s := by
  rw [sUnion_eq_biUnion, hS.closure_biUnion]

@[simp]
theorem Finset.closure_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set X) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) :=
  s.finite_toSet.closure_biUnion f

@[simp]
theorem closure_iUnion_of_finite [Finite ι] (f : ι → Set X) :
    closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  rw [← sUnion_range, (finite_range _).closure_sUnion, biUnion_range]

@[simp]
theorem closure_iUnion₂_lt_nat {n : ℕ} (f : ℕ → Set X) :
    closure (⋃ m < n, f m) = ⋃ m < n, closure (f m) :=
  (finite_lt_nat n).closure_biUnion f

@[simp]
theorem closure_iUnion₂_le_nat {n : ℕ} (f : ℕ → Set X) :
    closure (⋃ m ≤ n, f m) = ⋃ m ≤ n, closure (f m) :=
  (finite_le_nat n).closure_biUnion f

theorem interior_subset_closure : interior s ⊆ closure s :=
  Subset.trans interior_subset subset_closure

@[simp]
theorem interior_compl : interior sᶜ = (closure s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

@[simp]
theorem closure_compl : closure sᶜ = (interior s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

theorem mem_closure_iff :
    x ∈ closure s ↔ ∀ o, IsOpen o → x ∈ o → (o ∩ s).Nonempty :=
  ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s ⊆ oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩

theorem closure_inter_open_nonempty_iff (h : IsOpen t) :
    (closure s ∩ t).Nonempty ↔ (s ∩ t).Nonempty :=
  ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
    h.mono <| inf_le_inf_right t subset_closure⟩

theorem Filter.le_lift'_closure (l : Filter X) : l ≤ l.lift' closure :=
  le_lift'.2 fun _ h => mem_of_superset h subset_closure

theorem Filter.HasBasis.lift'_closure {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) : (l.lift' closure).HasBasis p fun i => closure (s i) :=
  h.lift' (monotone_closure X)

theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter X} {p : ι → Prop} {s : ι → Set X}
    (h : l.HasBasis p s) (hc : ∀ i, p i → IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure

@[simp]
theorem Filter.lift'_closure_eq_bot {l : Filter X} : l.lift' closure = ⊥ ↔ l = ⊥ :=
  ⟨fun h => bot_unique <| h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩

theorem dense_iff_closure_eq : Dense s ↔ closure s = univ :=
  eq_univ_iff_forall.symm

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq

theorem interior_eq_empty_iff_dense_compl : interior s = ∅ ↔ Dense sᶜ := by
  rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]

theorem Dense.interior_compl (h : Dense s) : interior sᶜ = ∅ :=
  interior_eq_empty_iff_dense_compl.2 <| by rwa [compl_compl]

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
theorem dense_closure : Dense (closure s) ↔ Dense s := by
  rw [Dense, Dense, closure_closure]

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure

@[simp]
theorem dense_univ : Dense (univ : Set X) := fun _ => subset_closure trivial

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open

theorem Dense.exists_mem_open (hs : Dense s) {U : Set X} (ho : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩

theorem Dense.nonempty_iff (hs : Dense s) : s.Nonempty ↔ Nonempty X :=
  ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩

theorem Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h

@[mono]
theorem Dense.mono (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
  closure_mono h (hd x)

/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
theorem dense_compl_singleton_iff_not_open :
    Dense ({x}ᶜ : Set X) ↔ ¬IsOpen ({x} : Set X) := by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => ?_
    obtain rfl : U = {x} := eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU

/-- If a closed property holds for a dense subset, it holds for the whole space. -/
@[elab_as_elim]
lemma Dense.induction (hs : Dense s) {P : X → Prop}
    (mem : ∀ x ∈ s, P x) (isClosed : IsClosed { x | P x }) (x : X) : P x :=
  hs.closure_eq.symm.subset.trans (isClosed.closure_subset_iff.mpr mem) (Set.mem_univ _)

theorem IsOpen.subset_interior_closure {s : Set X} (s_open : IsOpen s) :
    s ⊆ interior (closure s) := s_open.subset_interior_iff.mpr subset_closure

theorem IsClosed.closure_interior_subset {s : Set X} (s_closed : IsClosed s) :
    closure (interior s) ⊆ s := s_closed.closure_subset_iff.mpr interior_subset

/-! ### Frontier of a set -/

@[simp]
theorem closure_diff_interior (s : Set X) : closure s \ interior s = frontier s :=
  rfl

/-- Interior and frontier are disjoint. -/
lemma disjoint_interior_frontier : Disjoint (interior s) (frontier s) := by
  rw [disjoint_iff_inter_eq_empty, ← closure_diff_interior, diff_eq,
    ← inter_assoc, inter_comm, ← inter_assoc, compl_inter_self, empty_inter]

@[simp]
theorem closure_diff_frontier (s : Set X) : closure s \ frontier s = interior s := by
  rw [frontier, diff_diff_right_self, inter_eq_self_of_subset_right interior_subset_closure]

@[simp]
theorem self_diff_frontier (s : Set X) : s \ frontier s = interior s := by
  rw [frontier, diff_diff_right, diff_eq_empty.2 subset_closure,
    inter_eq_self_of_subset_right interior_subset, empty_union]

theorem frontier_eq_closure_inter_closure : frontier s = closure s ∩ closure sᶜ := by
  rw [closure_compl, frontier, diff_eq]

theorem frontier_subset_closure : frontier s ⊆ closure s :=
  diff_subset

theorem frontier_subset_iff_isClosed : frontier s ⊆ s ↔ IsClosed s := by
  rw [frontier, diff_subset_iff, union_eq_right.mpr interior_subset, closure_subset_iff_isClosed]

alias ⟨_, IsClosed.frontier_subset⟩ := frontier_subset_iff_isClosed

theorem frontier_closure_subset : frontier (closure s) ⊆ frontier s :=
  diff_subset_diff closure_closure.subset <| interior_mono subset_closure

theorem frontier_interior_subset : frontier (interior s) ⊆ frontier s :=
  diff_subset_diff (closure_mono interior_subset) interior_interior.symm.subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp]
theorem frontier_compl (s : Set X) : frontier sᶜ = frontier s := by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]

@[simp]
theorem frontier_univ : frontier (univ : Set X) = ∅ := by simp [frontier]

@[simp]
theorem frontier_empty : frontier (∅ : Set X) = ∅ := by simp [frontier]

theorem frontier_inter_subset (s t : Set X) :
    frontier (s ∩ t) ⊆ frontier s ∩ closure t ∪ closure s ∩ frontier t := by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq ?_
  simp only [inter_union_distrib_left, union_inter_distrib_right, inter_assoc,
    inter_comm (closure t)]

theorem frontier_union_subset (s t : Set X) :
    frontier (s ∪ t) ⊆ frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t := by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ

theorem IsClosed.frontier_eq (hs : IsClosed s) : frontier s = s \ interior s := by
  rw [frontier, hs.closure_eq]

theorem IsOpen.frontier_eq (hs : IsOpen s) : frontier s = closure s \ s := by
  rw [frontier, hs.interior_eq]

theorem IsOpen.inter_frontier_eq (hs : IsOpen s) : s ∩ frontier s = ∅ := by
  rw [hs.frontier_eq, inter_diff_self]

theorem disjoint_frontier_iff_isOpen : Disjoint (frontier s) s ↔ IsOpen s := by
  rw [← isClosed_compl_iff, ← frontier_subset_iff_isClosed,
    frontier_compl, subset_compl_iff_disjoint_right]

/-- The frontier of a set is closed. -/
theorem isClosed_frontier : IsClosed (frontier s) := by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure

/-- The frontier of a closed set has no interior point. -/
theorem interior_frontier (h : IsClosed s) : interior (frontier s) = ∅ := by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) ⊆ interior s := by rw [A]; exact interior_mono diff_subset
  have C : interior (frontier s) ⊆ frontier s := interior_subset
  have : interior (frontier s) ⊆ interior s ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_diff_self, subset_empty_iff] at this

theorem closure_eq_interior_union_frontier (s : Set X) : closure s = interior s ∪ frontier s :=
  (union_diff_cancel interior_subset_closure).symm

theorem closure_eq_self_union_frontier (s : Set X) : closure s = s ∪ frontier s :=
  (union_diff_cancel' interior_subset subset_closure).symm

theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (frontier s) t :=
  subset_compl_iff_disjoint_right.1 <|
    frontier_subset_closure.trans <| closure_minimal (disjoint_left.1 hd) <| isClosed_compl_iff.2 ht

theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (frontier t) :=
  (hd.symm.frontier_left hs).symm

theorem frontier_eq_inter_compl_interior : frontier s = (interior s)ᶜ ∩ (interior sᶜ)ᶜ := by
  rw [← frontier_compl, ← closure_compl, ← diff_eq, closure_diff_interior]

theorem compl_frontier_eq_union_interior : (frontier s)ᶜ = interior s ∪ interior sᶜ := by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

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
theorem le_nhds_lim {f : Filter X} (h : ∃ x, f ≤ 𝓝 x) : f ≤ 𝓝 (@lim _ _ (nonempty_of_exists h) f) :=
  Classical.epsilon_spec h

/-- If `g` tends to some `𝓝 x` along `f`, then it tends to `𝓝 (Filter.limUnder f g)`. We formulate
this lemma with a `[Nonempty X]` argument of `lim` derived from `h` to make it useful for types
without a `[Nonempty X]` instance. Because of the built-in proof irrelevance, Lean will unify this
instance with any other instance. -/
theorem tendsto_nhds_limUnder {f : Filter α} {g : α → X} (h : ∃ x, Tendsto g f (𝓝 x)) :
    Tendsto g f (𝓝 (@limUnder _ _ _ (nonempty_of_exists h) f g)) :=
  le_nhds_lim h

theorem limUnder_of_not_tendsto [hX : Nonempty X] {f : Filter α} {g : α → X}
    (h : ¬ ∃ x, Tendsto g f (𝓝 x)) :
    limUnder f g = Classical.choice hX := by
  simp_rw [limUnder, lim, Classical.epsilon, Classical.strongIndefiniteDescription]
  rw [dif_neg]
  exact h

end lim

end TopologicalSpace
