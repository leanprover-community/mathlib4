/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Order.Filter.Lift
import Mathlib.Topology.Defs.Filter

/-!
# Basic theory of topological spaces.

The main definition is the type class `TopologicalSpace X` which endows a type `X` with a topology.
Then `Set X` gets predicates `IsOpen`, `IsClosed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `X` gets a neighborhood filter `𝓝 x`. A filter `F` on `X` has
`x` as a cluster point if `ClusterPt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : α → X` clusters at `x`
along `F : Filter α` if `MapClusterPt x F f : ClusterPt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `MapClusterPt x atTop u`.

For topological spaces `X` and `Y`, a function `f : X → Y` and a point `x : X`,
`ContinuousAt f x` means `f` is continuous at `x`, and global continuity is
`Continuous f`. There is also a version of continuity `PContinuous` for
partially defined functions.

## Notation

The following notation is introduced elsewhere and it heavily used in this file.

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

topological space, interior, closure, frontier, neighborhood, continuity, continuous function
-/

noncomputable section

open Set Filter

universe u v w x

/-!
### Topological spaces
-/

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

section

variable [TopologicalSpace X]

end

protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by ext; exact h _⟩

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

theorem Set.Finite.isOpen_sInter {s : Set (Set X)} (hs : s.Finite) :
    (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
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

@[simp] -- Porting note: added `simp`
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

/-!
### Interior of a set
-/

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
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) :=
  hs.induction_on (by simp) <| by intros; simp [*]

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
      have : u \ s ⊆ t := fun x ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
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

/-!
### Closure of a set
-/

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

theorem IsClosed.closure_eq (h : IsClosed s) : closure s = s :=
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

@[simp]
theorem closure_empty : closure (∅ : Set X) = ∅ :=
  isClosed_empty.closure_eq

@[simp]
theorem closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩

@[simp]
theorem closure_nonempty_iff : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne, closure_empty_iff]

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff

@[simp]
theorem closure_univ : closure (univ : Set X) = univ :=
  isClosed_univ.closure_eq

@[simp]
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

theorem IsOpen.subset_interior_closure {s : Set X} (s_open : IsOpen s) :
    s ⊆ interior (closure s) := s_open.subset_interior_iff.mpr subset_closure

theorem IsClosed.closure_interior_subset {s : Set X} (s_closed : IsClosed s) :
    closure (interior s) ⊆ s := s_closed.closure_subset_iff.mpr interior_subset

/-!
### Frontier of a set
-/

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

theorem frontier_eq_inter_compl_interior :
    frontier s = (interior s)ᶜ ∩ (interior sᶜ)ᶜ := by
  rw [← frontier_compl, ← closure_compl, ← diff_eq, closure_diff_interior]

theorem compl_frontier_eq_union_interior :
    (frontier s)ᶜ = interior s ∪ interior sᶜ := by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]

/-!
### Neighborhoods
-/

theorem nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_setOf_eq, @and_comm (x ∈ _), iInf_and]

/-- The open sets containing `x` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

theorem nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl :=
  ⟨fun t => (nhds_basis_opens x).mem_iff.trans <|
    compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]
theorem lift'_nhds_interior (x : X) : (𝓝 x).lift' interior = 𝓝 x :=
  (nhds_basis_opens x).lift'_interior_eq_self fun _ ↦ And.right

theorem Filter.HasBasis.nhds_interior {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p (interior <| s ·) :=
  lift'_nhds_interior x ▸ h.lift'_interior

/-- A filter lies below the neighborhood filter at `x` iff it contains every open set around `x`. -/
theorem le_nhds_iff {f} : f ≤ 𝓝 x ↔ ∀ s : Set X, x ∈ s → IsOpen s → s ∈ f := by simp [nhds_def]

/-- To show a filter is above the neighborhood filter at `x`, it suffices to show that it is above
the principal filter of some open set `s` containing `x`. -/
theorem nhds_le_of_le {f} (h : x ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 x ≤ f := by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

/-- A predicate is true in a neighborhood of `x` iff it is true for all the points in an open set
containing `x`. -/
theorem eventually_nhds_iff {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ t : Set X, (∀ y ∈ t, p y) ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff.trans <| by simp only [subset_def, exists_prop, mem_setOf_eq]

theorem frequently_nhds_iff {p : X → Prop} :
    (∃ᶠ y in 𝓝 x, p y) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ y ∈ U, p y :=
  (nhds_basis_opens x).frequently_iff.trans <| by simp

theorem mem_interior_iff_mem_nhds : x ∈ interior s ↔ s ∈ 𝓝 x :=
  mem_interior.trans mem_nhds_iff.symm

theorem map_nhds {f : X → α} :
    map f (𝓝 x) = ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 (f '' s) :=
  ((nhds_basis_opens x).map f).eq_biInf

theorem mem_of_mem_nhds : s ∈ 𝓝 x → x ∈ s := fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs

/-- If a predicate is true in a neighborhood of `x`, then it is true for `x`. -/
theorem Filter.Eventually.self_of_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) : p x :=
  mem_of_mem_nhds h

theorem IsOpen.mem_nhds (hs : IsOpen s) (hx : x ∈ s) : s ∈ 𝓝 x :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩

protected theorem IsOpen.mem_nhds_iff (hs : IsOpen s) : s ∈ 𝓝 x ↔ x ∈ s :=
  ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩

theorem IsClosed.compl_mem_nhds (hs : IsClosed s) (hx : x ∉ s) : sᶜ ∈ 𝓝 x :=
  hs.isOpen_compl.mem_nhds (mem_compl hx)

theorem IsOpen.eventually_mem (hs : IsOpen s) (hx : x ∈ s) :
    ∀ᶠ x in 𝓝 x, x ∈ s :=
  IsOpen.mem_nhds hs hx

/-- The open neighborhoods of `x` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `x` instead. -/
theorem nhds_basis_opens' (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsOpen s) fun x => x := by
  convert nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds {U : Set X} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 <| h x hx, isOpen_interior, interior_subset⟩

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds' {U : Set X} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds (by simpa using h)

/-- If a predicate is true in a neighbourhood of `x`, then for `y` sufficiently close
to `x` this predicate is true in a neighbourhood of `y`. -/
theorem Filter.Eventually.eventually_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]
theorem eventually_eventually_nhds {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 x, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]
theorem frequently_frequently_nhds {p : X → Prop} :
    (∃ᶠ x' in 𝓝 x, ∃ᶠ x'' in 𝓝 x', p x'') ↔ ∃ᶠ x in 𝓝 x, p x := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]
theorem eventually_mem_nhds : (∀ᶠ x' in 𝓝 x, s ∈ 𝓝 x') ↔ s ∈ 𝓝 x :=
  eventually_eventually_nhds

@[simp]
theorem nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x :=
  Filter.ext fun _ => eventually_eventually_nhds

@[simp]
theorem eventually_eventuallyEq_nhds {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

theorem Filter.EventuallyEq.eq_of_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) : f x = g x :=
  h.self_of_nhds

@[simp]
theorem eventually_eventuallyLE_nhds [LE α] {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `x`, then for `y` sufficiently close
to `x` these functions are equal in a neighbourhood of `y`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds

/-- If `f x ≤ g x` in a neighbourhood of `x`, then for `y` sufficiently close to `x` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem Filter.EventuallyLE.eventuallyLE_nhds [LE α] {f g : X → α} (h : f ≤ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds

theorem all_mem_nhds (x : X) (P : Set X → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀ s ∈ 𝓝 x, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by simp only [@and_comm (x ∈ _), and_imp]

theorem all_mem_nhds_filter (x : X) (f : Set X → Set α) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : Filter α) : (∀ s ∈ 𝓝 x, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

theorem tendsto_nhds {f : α → X} {l : Filter α} :
    Tendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _

theorem tendsto_atTop_nhds [Nonempty α] [SemilatticeSup α] {f : α → X} :
    Tendsto f atTop (𝓝 x) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (atTop_basis.tendsto_iff (nhds_basis_opens x)).trans <| by
    simp only [and_imp, exists_prop, true_and_iff, mem_Ici]

theorem tendsto_const_nhds {f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha

theorem tendsto_atTop_of_eventually_const {ι : Type*} [SemilatticeSup ι] [Nonempty ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atTop.mpr ⟨i₀, h⟩)) tendsto_const_nhds

theorem tendsto_atBot_of_eventually_const {ι : Type*} [SemilatticeInf ι] [Nonempty ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atBot.mpr ⟨i₀, h⟩)) tendsto_const_nhds

theorem pure_le_nhds : pure ≤ (𝓝 : X → Filter X) := fun _ _ hs => mem_pure.2 <| mem_of_mem_nhds hs

theorem tendsto_pure_nhds (f : α → X) (a : α) : Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

theorem OrderTop.tendsto_atTop_nhds [PartialOrder α] [OrderTop α] (f : α → X) :
    Tendsto f atTop (𝓝 (f ⊤)) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]
instance nhds_neBot : NeBot (𝓝 x) :=
  neBot_of_le (pure_le_nhds x)

theorem tendsto_nhds_of_eventually_eq {l : Filter α} {f : α → X} (h : ∀ᶠ x' in l, f x' = x) :
    Tendsto f l (𝓝 x) :=
  tendsto_const_nhds.congr' (.symm h)

theorem Filter.EventuallyEq.tendsto {l : Filter α} {f : α → X} (hf : f =ᶠ[l] fun _ ↦ x) :
    Tendsto f l (𝓝 x) :=
  tendsto_nhds_of_eventually_eq hf

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/


theorem ClusterPt.neBot {F : Filter X} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h

theorem Filter.HasBasis.clusterPt_iff {ιX ιF} {pX : ιX → Prop} {sX : ιX → Set X} {pF : ιF → Prop}
    {sF : ιF → Set X} {F : Filter X} (hX : (𝓝 x).HasBasis pX sX) (hF : F.HasBasis pF sF) :
    ClusterPt x F ↔ ∀ ⦃i⦄, pX i → ∀ ⦃j⦄, pF j → (sX i ∩ sF j).Nonempty :=
  hX.inf_basis_neBot_iff hF

theorem Filter.HasBasis.clusterPt_iff_frequently {ι} {p : ι → Prop} {s : ι → Set X} {F : Filter X}
    (hx : (𝓝 x).HasBasis p s) : ClusterPt x F ↔ ∀ i, p i → ∃ᶠ x in F, x ∈ s i := by
  simp only [hx.clusterPt_iff F.basis_sets, Filter.frequently_iff, inter_comm (s _),
    Set.Nonempty, id, mem_inter_iff]

theorem clusterPt_iff {F : Filter X} :
    ClusterPt x F ↔ ∀ ⦃U : Set X⦄, U ∈ 𝓝 x → ∀ ⦃V⦄, V ∈ F → (U ∩ V).Nonempty :=
  inf_neBot_iff

theorem clusterPt_iff_not_disjoint {F : Filter X} :
    ClusterPt x F ↔ ¬Disjoint (𝓝 x) F := by
  rw [disjoint_iff, ClusterPt, neBot_iff]

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_clusterPt`. -/
theorem clusterPt_principal_iff :
    ClusterPt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty :=
  inf_principal_neBot_iff

theorem clusterPt_principal_iff_frequently :
    ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, exists_prop, mem_inter_iff]

theorem ClusterPt.of_le_nhds {f : Filter X} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]

theorem ClusterPt.of_le_nhds' {f : Filter X} (H : f ≤ 𝓝 x) (_hf : NeBot f) :
    ClusterPt x f :=
  ClusterPt.of_le_nhds H

theorem ClusterPt.of_nhds_le {f : Filter X} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]

theorem ClusterPt.mono {f g : Filter X} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  NeBot.mono H <| inf_le_inf_left _ h

theorem ClusterPt.of_inf_left {f g : Filter X} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left

theorem ClusterPt.of_inf_right {f g : Filter X} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right

theorem Ultrafilter.clusterPt_iff {f : Ultrafilter X} : ClusterPt x f ↔ ↑f ≤ 𝓝 x :=
  ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩

theorem clusterPt_iff_ultrafilter {f : Filter X} : ClusterPt x f ↔
    ∃ u : Ultrafilter X, u ≤ f ∧ u ≤ 𝓝 x := by
  simp_rw [ClusterPt, ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

section MapClusterPt

variable {F : Filter α} {u : α → X} {x : X}

theorem mapClusterPt_def : MapClusterPt x F u ↔ ClusterPt x (map u F) := Iff.rfl
alias ⟨MapClusterPt.clusterPt, _⟩ := mapClusterPt_def

theorem MapClusterPt.mono {G : Filter α} (h : MapClusterPt x F u) (hle : F ≤ G) :
    MapClusterPt x G u :=
  h.clusterPt.mono (map_mono hle)

theorem MapClusterPt.tendsto_comp' [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x ⊓ map u F) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  (tendsto_inf.2 ⟨hf, tendsto_map.mono_left inf_le_right⟩).neBot (hx := hu)

theorem MapClusterPt.tendsto_comp [TopologicalSpace Y] {f : X → Y} {y : Y}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hu : MapClusterPt x F u) : MapClusterPt y F (f ∘ u) :=
  hu.tendsto_comp' (hf.mono_left inf_le_left)

theorem MapClusterPt.continuousAt_comp [TopologicalSpace Y] {f : X → Y} (hf : ContinuousAt f x)
    (hu : MapClusterPt x F u) : MapClusterPt (f x) F (f ∘ u) :=
  hu.tendsto_comp hf

theorem Filter.HasBasis.mapClusterPt_iff_frequently {ι : Sort*} {p : ι → Prop} {s : ι → Set X}
    (hx : (𝓝 x).HasBasis p s) : MapClusterPt x F u ↔ ∀ i, p i → ∃ᶠ a in F, u a ∈ s i := by
  simp_rw [MapClusterPt, hx.clusterPt_iff_frequently, frequently_map]

theorem mapClusterPt_iff : MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s :=
  (𝓝 x).basis_sets.mapClusterPt_iff_frequently

theorem mapClusterPt_iff_ultrafilter :
    MapClusterPt x F u ↔ ∃ U : Ultrafilter α, U ≤ F ∧ Tendsto u U (𝓝 x) := by
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, tendsto_iff_comap,
    ← le_inf_iff, exists_ultrafilter_iff, inf_comm]

theorem mapClusterPt_comp {φ : α → β} {u : β → X} :
    MapClusterPt x F (u ∘ φ) ↔ MapClusterPt x (map φ F) u := Iff.rfl

theorem Filter.Tendsto.mapClusterPt [NeBot F] (h : Tendsto u F (𝓝 x)) : MapClusterPt x F u :=
  .of_le_nhds h

theorem MapClusterPt.of_comp {φ : β → α} {p : Filter β} (h : Tendsto φ p F)
    (H : MapClusterPt x p (u ∘ φ)) : MapClusterPt x F u :=
  H.clusterPt.mono <| map_mono h

@[deprecated MapClusterPt.of_comp (since := "2024-09-07")]
theorem mapClusterPt_of_comp {φ : β → α} {p : Filter β} [NeBot p]
    (h : Tendsto φ p F) (H : Tendsto (u ∘ φ) p (𝓝 x)) : MapClusterPt x F u :=
  .of_comp h H.mapClusterPt

end MapClusterPt

theorem accPt_sup (x : X) (F G : Filter X) :
    AccPt x (F ⊔ G) ↔ AccPt x F ∨ AccPt x G := by
  simp only [AccPt, inf_sup_left, sup_neBot]

theorem acc_iff_cluster (x : X) (F : Filter X) : AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F) := by
  rw [AccPt, nhdsWithin, ClusterPt, inf_assoc]

/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`. -/
theorem acc_principal_iff_cluster (x : X) (C : Set X) :
    AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ {x})) := by
  rw [acc_iff_cluster, inf_principal, inter_comm, diff_eq]

/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
theorem accPt_iff_nhds (x : X) (C : Set X) : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff, Set.Nonempty, exists_prop, and_assoc,
    @and_comm (¬_ = x)]

/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`. -/
theorem accPt_iff_frequently (x : X) (C : Set X) : AccPt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff_frequently, and_comm]

/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `G`. -/
theorem AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
  NeBot.mono h (inf_le_inf_left _ hFG)

theorem AccPt.clusterPt (x : X) (F : Filter X) (h : AccPt x F) : ClusterPt x F :=
  ((acc_iff_cluster x F).mp h).mono inf_le_right

/-!
### Interior, closure and frontier in terms of neighborhoods
-/

theorem interior_eq_nhds' : interior s = { x | s ∈ 𝓝 x } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_setOf_eq]

theorem interior_eq_nhds : interior s = { x | 𝓝 x ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by simp only [le_principal_iff]

@[simp]
theorem interior_mem_nhds : interior s ∈ 𝓝 x ↔ s ∈ 𝓝 x :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩

theorem interior_setOf_eq {p : X → Prop} : interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'

theorem isOpen_setOf_eventually_nhds {p : X → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOf_eq, isOpen_interior]

theorem subset_interior_iff_nhds {V : Set X} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x := by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]

theorem isOpen_iff_nhds : IsOpen s ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ interior s := subset_interior_iff_isOpen.symm
    _ ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_setOf]

theorem TopologicalSpace.ext_iff_nhds {X} {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ x, @nhds _ t x = @nhds _ t' x :=
  ⟨fun H x ↦ congrFun (congrArg _ H) _, fun H ↦ by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds

theorem isOpen_iff_mem_nhds : IsOpen s ↔ ∀ x ∈ s, s ∈ 𝓝 x :=
  isOpen_iff_nhds.trans <| forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
theorem isOpen_iff_eventually : IsOpen s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
  isOpen_iff_mem_nhds

theorem isOpen_iff_ultrafilter :
    IsOpen s ↔ ∀ x ∈ s, ∀ (l : Ultrafilter X), ↑l ≤ 𝓝 x → s ∈ l := by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]

theorem isOpen_singleton_iff_nhds_eq_pure (x : X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x := by
  constructor
  · intro h
    apply le_antisymm _ (pure_le_nhds x)
    rw [le_pure_iff]
    exact h.mem_nhds (mem_singleton x)
  · intro h
    simp [isOpen_iff_nhds, h]

theorem isOpen_singleton_iff_punctured_nhds (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[≠] x = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure, nhdsWithin, ← mem_iff_inf_principal_compl, ← le_pure_iff,
    nhds_neBot.le_pure_iff]

theorem mem_closure_iff_frequently : x ∈ closure s ↔ ∃ᶠ x in 𝓝 x, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds,
    closure_eq_compl_interior_compl, mem_compl_iff, compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
theorem isClosed_iff_frequently : IsClosed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s := by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem isClosed_setOf_clusterPt {f : Filter X} : IsClosed { x | ClusterPt x f } := by
  simp only [ClusterPt, inf_neBot_iff_frequently_left, setOf_forall, imp_iff_not_or]
  refine isClosed_iInter fun p => IsClosed.union ?_ ?_ <;> apply isClosed_compl_iff.2
  exacts [isOpen_setOf_eventually_nhds, isOpen_const]

theorem mem_closure_iff_clusterPt : x ∈ closure s ↔ ClusterPt x (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm

theorem mem_closure_iff_nhds_ne_bot : x ∈ closure s ↔ 𝓝 x ⊓ 𝓟 s ≠ ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff

@[deprecated (since := "2024-01-28")]
alias mem_closure_iff_nhds_neBot := mem_closure_iff_nhds_ne_bot

theorem mem_closure_iff_nhdsWithin_neBot : x ∈ closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt

lemma nhdsWithin_neBot : (𝓝[s] x).NeBot ↔ ∀ ⦃t⦄, t ∈ 𝓝 x → (t ∩ s).Nonempty := by
  rw [nhdsWithin, inf_neBot_iff]
  exact forall₂_congr fun U _ ↦
    ⟨fun h ↦ h (mem_principal_self _), fun h u hsu ↦ h.mono <| inter_subset_inter_right _ hsu⟩

@[gcongr]
theorem nhdsWithin_mono (x : X) {s t : Set X} (h : s ⊆ t) : 𝓝[s] x ≤ 𝓝[t] x :=
  inf_le_inf_left _ (principal_mono.mpr h)

lemma not_mem_closure_iff_nhdsWithin_eq_bot : x ∉ closure s ↔ 𝓝[s] x = ⊥ := by
  rw [mem_closure_iff_nhdsWithin_neBot, not_neBot]

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
theorem dense_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set X) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
-- Porting note (#10618): was a `@[simp]` lemma but `simp` can prove it
theorem closure_compl_singleton (x : X) [NeBot (𝓝[≠] x)] : closure {x}ᶜ = (univ : Set X) :=
  (dense_compl_singleton x).closure_eq

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
theorem interior_singleton (x : X) [NeBot (𝓝[≠] x)] : interior {x} = (∅ : Set X) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)

theorem not_isOpen_singleton (x : X) [NeBot (𝓝[≠] x)] : ¬IsOpen ({x} : Set X) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)

theorem closure_eq_cluster_pts : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun _ => mem_closure_iff_clusterPt

theorem mem_closure_iff_nhds : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, (t ∩ s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff

theorem mem_closure_iff_nhds' : x ∈ closure s ↔ ∀ t ∈ 𝓝 x, ∃ y : s, ↑y ∈ t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]

theorem mem_closure_iff_comap_neBot :
    x ∈ closure s ↔ NeBot (comap ((↑) : s → X) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]

theorem mem_closure_iff_nhds_basis' {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_clusterPt.trans <|
    (h.clusterPt_iff (hasBasis_principal _)).trans <| by simp only [exists_prop, forall_const]

theorem mem_closure_iff_nhds_basis {p : ι → Prop} {s : ι → Set X} (h : (𝓝 x).HasBasis p s) :
    x ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [Set.Nonempty, mem_inter_iff, exists_prop, and_comm]

theorem clusterPt_iff_forall_mem_closure {F : Filter X} :
    ClusterPt x F ↔ ∀ s ∈ F, x ∈ closure s := by
  simp_rw [ClusterPt, inf_neBot_iff, mem_closure_iff_nhds]
  rw [forall₂_swap]

theorem clusterPt_iff_lift'_closure {F : Filter X} :
    ClusterPt x F ↔ pure x ≤ (F.lift' closure) := by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

theorem clusterPt_iff_lift'_closure' {F : Filter X} :
    ClusterPt x F ↔ (F.lift' closure ⊓ pure x).NeBot := by
  rw [clusterPt_iff_lift'_closure, ← Ultrafilter.coe_pure, inf_comm, Ultrafilter.inf_neBot_iff]

@[simp]
theorem clusterPt_lift'_closure_iff {F : Filter X} :
    ClusterPt x (F.lift' closure) ↔ ClusterPt x F := by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure X) (monotone_closure X)]

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
theorem mem_closure_iff_ultrafilter :
    x ∈ closure s ↔ ∃ u : Ultrafilter X, s ∈ u ∧ ↑u ≤ 𝓝 x := by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]

theorem isClosed_iff_clusterPt : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ closure s ⊆ s := closure_subset_iff_isClosed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by simp only [subset_def, mem_closure_iff_clusterPt]

theorem isClosed_iff_ultrafilter : IsClosed s ↔
    ∀ x, ∀ u : Ultrafilter X, ↑u ≤ 𝓝 x → s ∈ u → x ∈ s := by
  simp [isClosed_iff_clusterPt, ClusterPt, ← exists_ultrafilter_iff]

theorem isClosed_iff_nhds :
    IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).Nonempty) → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]

lemma isClosed_iff_forall_filter :
    IsClosed s ↔ ∀ x, ∀ F : Filter X, F.NeBot → F ≤ 𝓟 s → F ≤ 𝓝 x → x ∈ s := by
  simp_rw [isClosed_iff_clusterPt]
  exact ⟨fun hs x F F_ne FS Fx ↦ hs _ <| NeBot.mono F_ne (le_inf Fx FS),
         fun hs x hx ↦ hs x (𝓝 x ⊓ 𝓟 s) hx inf_le_right inf_le_left⟩

theorem IsClosed.interior_union_left (_ : IsClosed s) :
    interior (s ∪ t) ⊆ s ∪ interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a ∈ s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u ∩ sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩

theorem IsClosed.interior_union_right (h : IsClosed t) :
    interior (s ∪ t) ⊆ interior s ∪ t := by
  simpa only [union_comm _ t] using h.interior_union_left

theorem IsOpen.inter_closure (h : IsOpen s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  compl_subset_compl.mp <| by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl

theorem IsOpen.closure_inter (h : IsOpen t) : closure s ∩ t ⊆ closure (s ∩ t) := by
  simpa only [inter_comm t] using h.inter_closure

theorem Dense.open_subset_closure_inter (hs : Dense s) (ht : IsOpen t) :
    t ⊆ closure (t ∩ s) :=
  calc
    t = t ∩ closure s := by rw [hs.closure_eq, inter_univ]
    _ ⊆ closure (t ∩ s) := ht.inter_closure

theorem mem_closure_of_mem_closure_union (h : x ∈ closure (s₁ ∪ s₂))
    (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ := by
  rw [mem_closure_iff_nhds_ne_bot] at *
  rwa [← sup_principal, inf_sup_left, inf_principal_eq_bot.mpr h₁, bot_sup_eq] at h

/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem Dense.inter_of_isOpen_left (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s ∩ t) := fun x =>
  closure_minimal hso.inter_closure isClosed_closure <| by simp [hs.closure_eq, ht.closure_eq]

/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem Dense.inter_of_isOpen_right (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_isOpen_left hs hto

theorem Dense.inter_nhds_nonempty (hs : Dense s) (ht : t ∈ 𝓝 x) :
    (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩

theorem closure_diff : closure s \ closure t ⊆ closure (s \ t) :=
  calc
    closure s \ closure t = (closure t)ᶜ ∩ closure s := by simp only [diff_eq, inter_comm]
    _ ⊆ closure ((closure t)ᶜ ∩ s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [diff_eq, inter_comm]
    _ ⊆ closure (s \ t) := closure_mono <| diff_subset_diff (Subset.refl s) subset_closure

theorem Filter.Frequently.mem_of_closed (h : ∃ᶠ x in 𝓝 x, x ∈ s)
    (hs : IsClosed s) : x ∈ s :=
  hs.closure_subset h.mem_closure

theorem IsClosed.mem_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (hs : IsClosed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ s :=
  (hf.frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs

theorem IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s :=
  hs.mem_of_frequently_of_tendsto h.frequently hf

theorem mem_closure_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ closure s :=
  (hf.frequently h).mem_closure

theorem mem_closure_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ closure s :=
  mem_closure_of_frequently_of_tendsto h.frequently hf

/-- Suppose that `f` sends the complement to `s` to a single point `x`, and `l` is some filter.
Then `f` tends to `x` along `l` restricted to `s` if and only if it tends to `x` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : α → X} {l : Filter α} {s : Set α}
    (h : ∀ a ∉ s, f a = x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) ↔ Tendsto f l (𝓝 x) := by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff]
    at this
  exact this.1

/-!
### Limits of filters in topological spaces

In this section we define functions that return a limit of a filter (or of a function along a
filter), if it exists, and a random point otherwise. These functions are rarely used in Mathlib,
most of the theorems are written using `Filter.Tendsto`. One of the reasons is that
`Filter.limUnder f g = x` is not equivalent to `Filter.Tendsto g f (𝓝 x)` unless the codomain is a
Hausdorff space and `g` has a limit along `f`.
-/

section lim

-- "Lim"

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

end lim

end TopologicalSpace

open Topology

/-!
### Continuity
-/

section Continuous

variable {X Y Z : Type*}

open TopologicalSpace

-- The curly braces are intentional, so this definition works well with simp
-- when topologies are not those provided by instances.
theorem continuous_def {_ : TopologicalSpace X} {_ : TopologicalSpace Y} {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {s : Set X} {x : X} {y : Y}

theorem IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : IsOpen t) :
    IsOpen (f ⁻¹' t) :=
  hf.isOpen_preimage t h

theorem continuous_congr {g : X → Y} (h : ∀ x, f x = g x) :
    Continuous f ↔ Continuous g :=
  .of_eq <| congrArg _ <| funext h

theorem Continuous.congr {g : X → Y} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g :=
  continuous_congr h' |>.mp h

theorem ContinuousAt.tendsto (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h

theorem continuousAt_def : ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl

theorem continuousAt_congr {g : X → Y} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]

theorem ContinuousAt.congr {g : X → Y} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf

theorem ContinuousAt.preimage_mem_nhds {t : Set Y} (h : ContinuousAt f x)
    (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
  h ht

/-- If `f x ∈ s ∈ 𝓝 (f x)` for continuous `f`, then `f y ∈ s` near `x`.

This is essentially `Filter.Tendsto.eventually_mem`, but infers in more cases when applied. -/
theorem ContinuousAt.eventually_mem {f : X → Y} {x : X} (hf : ContinuousAt f x) {s : Set Y}
    (hs : s ∈ 𝓝 (f x)) : ∀ᶠ y in 𝓝 x, f y ∈ s :=
  hf hs

/-- If a function ``f` tends to somewhere other than `𝓝 (f x)` at `x`,
then `f` is not continuous at `x`
-/
lemma not_continuousAt_of_tendsto {f : X → Y} {l₁ : Filter X} {l₂ : Filter Y} {x : X}
    (hf : Tendsto f l₁ l₂) [l₁.NeBot] (hl₁ : l₁ ≤ 𝓝 x) (hl₂ : Disjoint (𝓝 (f x)) l₂) :
    ¬ ContinuousAt f x := fun cont ↦
  (cont.mono_left hl₁).not_tendsto hl₂ hf

/-- Deprecated, please use `not_mem_tsupport_iff_eventuallyEq` instead. -/
@[deprecated (since := "2024-01-15")]
theorem eventuallyEq_zero_nhds {M₀} [Zero M₀] {f : X → M₀} :
    f =ᶠ[𝓝 x] 0 ↔ x ∉ closure (Function.support f) := by
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds, Function.compl_support,
    EventuallyEq, eventually_iff]
  simp only [Pi.zero_apply]

theorem ClusterPt.map {lx : Filter X} {ly : Filter Y} (H : ClusterPt x lx)
    (hfc : ContinuousAt f x) (hf : Tendsto f lx ly) : ClusterPt (f x) ly :=
  (NeBot.map H f).mono <| hfc.tendsto.inf hf

/-- See also `interior_preimage_subset_preimage_interior`. -/
theorem preimage_interior_subset_interior_preimage {t : Set Y} (hf : Continuous f) :
    f ⁻¹' interior t ⊆ interior (f ⁻¹' t) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)

@[continuity]
theorem continuous_id : Continuous (id : X → X) :=
  continuous_def.2 fun _ => id

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
theorem continuous_id' : Continuous (fun (x : X) => x) := continuous_id

theorem Continuous.comp {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  continuous_def.2 fun _ h => (h.preimage hg).preimage hf

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity, fun_prop]
theorem Continuous.comp' {g : Y → Z} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) := hg.comp hf

theorem Continuous.iterate {f : X → X} (h : Continuous f) (n : ℕ) : Continuous f^[n] :=
  Nat.recOn n continuous_id fun _ ihn => ihn.comp h

nonrec theorem ContinuousAt.comp {g : Y → Z} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

@[fun_prop]
theorem ContinuousAt.comp' {g : Y → Z} {x : X} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x := ContinuousAt.comp hg hf

/-- See note [comp_of_eq lemmas] -/
theorem ContinuousAt.comp_of_eq {g : Y → Z} (hg : ContinuousAt g y)
    (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x := by subst hy; exact hg.comp hf

theorem Continuous.tendsto (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩

/-- A version of `Continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
theorem Continuous.tendsto' (hf : Continuous f) (x : X) (y : Y) (h : f x = y) :
    Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.tendsto x

@[fun_prop]
theorem Continuous.continuousAt (h : Continuous f) : ContinuousAt f x :=
  h.tendsto x

theorem continuous_iff_continuousAt : Continuous f ↔ ∀ x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
    hf x <| hU.mem_nhds hx⟩

@[fun_prop]
theorem continuousAt_const : ContinuousAt (fun _ : X => y) x :=
  tendsto_const_nhds

@[continuity, fun_prop]
theorem continuous_const : Continuous fun _ : X => y :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_const

theorem Filter.EventuallyEq.continuousAt (h : f =ᶠ[𝓝 x] fun _ => y) :
    ContinuousAt f x :=
  (continuousAt_congr h).2 tendsto_const_nhds

theorem continuous_of_const (h : ∀ x y, f x = f y) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    Filter.EventuallyEq.continuousAt <| Eventually.of_forall fun y => h y x

theorem continuousAt_id : ContinuousAt id x :=
  continuous_id.continuousAt

@[fun_prop]
theorem continuousAt_id' (y) : ContinuousAt (fun x : X => x) y := continuousAt_id

theorem ContinuousAt.iterate {f : X → X} (hf : ContinuousAt f x) (hx : f x = x) (n : ℕ) :
    ContinuousAt f^[n] x :=
  Nat.recOn n continuousAt_id fun _n ihn ↦ ihn.comp_of_eq hf hx

theorem continuous_iff_isClosed : Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  continuous_def.trans <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]

theorem IsClosed.preimage (hf : Continuous f) {t : Set Y} (h : IsClosed t) :
    IsClosed (f ⁻¹' t) :=
  continuous_iff_isClosed.mp hf t h

theorem mem_closure_image (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf

theorem continuousAt_iff_ultrafilter :
    ContinuousAt f x ↔ ∀ g : Ultrafilter X, ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))

theorem continuous_iff_ultrafilter :
    Continuous f ↔ ∀ (x) (g : Ultrafilter X), ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]

theorem Continuous.closure_preimage_subset (hf : Continuous f) (t : Set Y) :
    closure (f ⁻¹' t) ⊆ f ⁻¹' closure t := by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)

theorem Continuous.frontier_preimage_subset (hf : Continuous f) (t : Set Y) :
    frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t :=
  diff_subset_diff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
protected theorem Set.MapsTo.closure {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) : MapsTo f (closure s) (closure t) := by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)

/-- See also `IsClosedMap.closure_image_eq_of_continuous`. -/
theorem image_closure_subset_closure_image (h : Continuous f) :
    f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure h).image_subset

theorem closure_image_closure (h : Continuous f) :
    closure (f '' closure s) = closure (f '' s) :=
  Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_subset _ subset_closure)

theorem closure_subset_preimage_closure_image (h : Continuous f) :
    closure s ⊆ f ⁻¹' closure (f '' s) :=
  (mapsTo_image _ _).closure h

theorem map_mem_closure {t : Set Y} (hf : Continuous f)
    (hx : x ∈ closure s) (ht : MapsTo f s t) : f x ∈ closure t :=
  ht.closure hf hx

/-- If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` to `t`. -/
theorem Set.MapsTo.closure_left {t : Set Y} (h : MapsTo f s t)
    (hc : Continuous f) (ht : IsClosed t) : MapsTo f (closure s) t :=
  ht.closure_eq ▸ h.closure hc

theorem Filter.Tendsto.lift'_closure (hf : Continuous f) {l l'} (h : Tendsto f l l') :
    Tendsto f (l.lift' closure) (l'.lift' closure) :=
  tendsto_lift'.2 fun s hs ↦ by
    filter_upwards [mem_lift' (h hs)] using (mapsTo_preimage _ _).closure hf

theorem tendsto_lift'_closure_nhds (hf : Continuous f) (x : X) :
    Tendsto f ((𝓝 x).lift' closure) ((𝓝 (f x)).lift' closure) :=
  (hf.tendsto x).lift'_closure hf

/-!
### Function with dense range
-/

section DenseRange

variable {α ι : Type*} (f : α → X) (g : X → Y)
variable {f : α → X} {s : Set X}

/-- A surjective map has dense range. -/
theorem Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [hf.range_eq]

theorem denseRange_id : DenseRange (id : X → X) :=
  Function.Surjective.denseRange Function.surjective_id

theorem denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ :=
  dense_iff_closure_eq

theorem DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ :=
  h.closure_eq

@[simp]
lemma denseRange_subtype_val {p : X → Prop} : DenseRange (@Subtype.val _ p) ↔ Dense {x | p x} := by
  simp [DenseRange]

theorem Dense.denseRange_val (h : Dense s) : DenseRange ((↑) : s → X) :=
  denseRange_subtype_val.2 h

theorem Continuous.range_subset_closure_image_dense {f : X → Y} (hf : Continuous f)
    (hs : Dense s) : range f ⊆ closure (f '' s) := by
  rw [← image_univ, ← hs.closure_eq]
  exact image_closure_subset_closure_image hf

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
theorem DenseRange.dense_image {f : X → Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) : Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure

/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
theorem DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) (hs : IsOpen s) :
    s ⊆ closure (f '' (f ⁻¹' s)) := by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
theorem DenseRange.dense_of_mapsTo {f : X → Y} (hf' : DenseRange f) (hf : Continuous f)
    (hs : Dense s) {t : Set Y} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
theorem DenseRange.comp {g : Y → Z} {f : α → Y} (hg : DenseRange g) (hf : DenseRange f)
    (cg : Continuous g) : DenseRange (g ∘ f) := by
  rw [DenseRange, range_comp]
  exact hg.dense_image cg hf

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty α ↔ Nonempty X :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff

theorem DenseRange.nonempty [h : Nonempty X] (hf : DenseRange f) : Nonempty α :=
  hf.nonempty_iff.mpr h

/-- Given a function `f : X → Y` with dense range and `y : Y`, returns some `x : X`. -/
def DenseRange.some (hf : DenseRange f) (x : X) : α :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨x⟩

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) (ho : IsOpen s) (hs : s.Nonempty) :
    ∃ a, f a ∈ s :=
  exists_range_iff.1 <| hf.exists_mem_open ho hs

theorem DenseRange.mem_nhds (h : DenseRange f) (hs : s ∈ 𝓝 x) :
    ∃ a, f a ∈ s :=
  let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨x, mem_interior_iff_mem_nhds.2 hs⟩
  ⟨a, interior_subset ha⟩

end DenseRange

end Continuous

library_note "continuity lemma statement"/--
The library contains many lemmas stating that functions/operations are continuous. There are many
ways to formulate the continuity of operations. Some are more convenient than others.
Note: for the most part this note also applies to other properties
(`Measurable`, `Differentiable`, `ContinuousOn`, ...).

### The traditional way
As an example, let's look at addition `(+) : M → M → M`. We can state that this is continuous
in different definitionally equal ways (omitting some typing information)
* `Continuous (fun p ↦ p.1 + p.2)`;
* `Continuous (Function.uncurry (+))`;
* `Continuous ↿(+)`. (`↿` is notation for recursively uncurrying a function)

However, lemmas with this conclusion are not nice to use in practice because
1. They confuse the elaborator. The following two examples fail, because of limitations in the
  elaboration process.
  ```
  variable {M : Type*} [Add M] [TopologicalSpace M] [ContinuousAdd M]
  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp _

  example : Continuous (fun x : M ↦ x + x) :=
    continuous_add.comp (continuous_id.prod_mk continuous_id)
  ```
  The second is a valid proof, which is accepted if you write it as
  `continuous_add.comp (continuous_id.prod_mk continuous_id : _)`

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way

A much more convenient way to write continuity lemmas is like `Continuous.add`:
```
Continuous.add {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
  Continuous (fun x ↦ f x + g x)
```
The conclusion can be `Continuous (f + g)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `Continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.

As an example for a unary operation, we have `Continuous.neg`.
```
Continuous.neg {f : X → G} (hf : Continuous f) : Continuous (fun x ↦ -f x)
```
For unary functions, the elaborator is not confused when applying the traditional lemma
(like `continuous_neg`), but it's still convenient to have the short version available (compare
`hf.neg.neg.neg` with `continuous_neg.comp <| continuous_neg.comp <| continuous_neg.comp hf`).

As a harder example, consider an operation of the following type:
```
def strans {x : F} (γ γ' : Path x x) (t₀ : I) : Path x x
```
The precise definition is not important, only its type.
The correct continuity principle for this operation is something like this:
```
{f : X → F} {γ γ' : ∀ x, Path (f x) (f x)} {t₀ s : X → I}
  (hγ : Continuous ↿γ) (hγ' : Continuous ↿γ')
  (ht : Continuous t₀) (hs : Continuous s) :
  Continuous (fun x ↦ strans (γ x) (γ' x) (t x) (s x))
```
Note that *all* arguments of `strans` are indexed over `X`, even the basepoint `x`, and the last
argument `s` that arises since `Path x x` has a coercion to `I → F`. The paths `γ` and `γ'` (which
are unary functions from `I`) become binary functions in the continuity lemma.

### Summary
* Make sure that your continuity lemmas are stated in the most general way, and in a convenient
  form. That means that:
  - The conclusion has a variable `X` as domain (not something like `Y × Z`);
  - Wherever possible, all point arguments `c : Y` are replaced by functions `c : X → Y`;
  - All `n`-ary function arguments are replaced by `n+1`-ary functions
    (`f : Y → Z` becomes `f : X → Y → Z`);
  - All (relevant) arguments have continuity assumptions, and perhaps there are additional
    assumptions needed to make the operation continuous;
  - The function in the conclusion is fully applied.
* These remarks are mostly about the format of the *conclusion* of a continuity lemma.
  In assumptions it's fine to state that a function with more than 1 argument is continuous using
  `↿` or `Function.uncurry`.

### Functions with discontinuities

In some cases, you want to work with discontinuous functions, and in certain expressions they are
still continuous. For example, consider the fractional part of a number, `Int.fract : ℝ → ℝ`.
In this case, you want to add conditions to when a function involving `fract` is continuous, so you
get something like this: (assumption `hf` could be weakened, but the important thing is the shape
of the conclusion)
```
lemma ContinuousOn.comp_fract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ → Y} {g : X → ℝ} (hf : Continuous ↿f) (hg : Continuous g) (h : ∀ s, f s 0 = f s 1) :
    Continuous (fun x ↦ f x (fract (g x)))
```
With `ContinuousAt` you can be even more precise about what to prove in case of discontinuities,
see e.g. `ContinuousAt.comp_div_cases`.
-/

library_note "comp_of_eq lemmas"/--
Lean's elaborator has trouble elaborating applications of lemmas that state that the composition of
two functions satisfy some property at a point, like `ContinuousAt.comp` / `ContDiffAt.comp` and
`ContMDiffWithinAt.comp`. The reason is that a lemma like this looks like
`ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f) x`.
Since Lean's elaborator elaborates the arguments from left-to-right, when you write `hg.comp hf`,
the elaborator will try to figure out *both* `f` and `g` from the type of `hg`. It tries to figure
out `f` just from the point where `g` is continuous. For example, if `hg : ContinuousAt g (a, x)`
then the elaborator will assign `f` to the function `Prod.mk a`, since in that case `f x = (a, x)`.
This is undesirable in most cases where `f` is not a variable. There are some ways to work around
this, for example by giving `f` explicitly, or to force Lean to elaborate `hf` before elaborating
`hg`, but this is annoying.
Another better solution is to reformulate composition lemmas to have the following shape
`ContinuousAt g y → ContinuousAt f x → f x = y → ContinuousAt (g ∘ f) x`.
This is even useful if the proof of `f x = y` is `rfl`.
The reason that this works better is because the type of `hg` doesn't mention `f`.
Only after elaborating the two `ContinuousAt` arguments, Lean will try to unify `f x` with `y`,
which is often easy after having chosen the correct functions for `f` and `g`.
Here is an example that shows the difference:
```
example [TopologicalSpace X] [TopologicalSpace Y] {x₀ : X} (f : X → X → Y)
    (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
    ContinuousAt (fun x ↦ f x x) x₀ :=
  -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/

set_option linter.style.longFile 1900
