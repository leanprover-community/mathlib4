/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Algebra.Support
import Mathlib.Order.Filter.Lift
import Mathlib.Tactic.Continuity

#align_import topology.basic from "leanprover-community/mathlib"@"e354e865255654389cc46e6032160238df2e0f40"

/-!
# Basic theory of topological spaces.

The main definition is the type class `TopologicalSpace α` which endows a type `α` with a topology.
Then `Set α` gets predicates `IsOpen`, `IsClosed` and functions `interior`, `closure` and
`frontier`. Each point `x` of `α` gets a neighborhood filter `𝓝 x`. A filter `F` on `α` has
`x` as a cluster point if `ClusterPt x F : 𝓝 x ⊓ F ≠ ⊥`. A map `f : ι → α` clusters at `x`
along `F : Filter ι` if `MapClusterPt x F f : ClusterPt x (map f F)`. In particular
the notion of cluster point of a sequence `u` is `MapClusterPt x atTop u`.

For topological spaces `α` and `β`, a function `f : α → β` and a point `a : α`,
`ContinuousAt f a` means `f` is continuous at `a`, and global continuity is
`Continuous f`. There is also a version of continuity `PContinuous` for
partially defined functions.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≤] x`: the filter `nhdsWithin x (Set.Iic x)` of left-neighborhoods of `x`;
* `𝓝[≥] x`: the filter `nhdsWithin x (Set.Ici x)` of right-neighborhoods of `x`;
* `𝓝[<] x`: the filter `nhdsWithin x (Set.Iio x)` of punctured left-neighborhoods of `x`;
* `𝓝[>] x`: the filter `nhdsWithin x (Set.Ioi x)` of punctured right-neighborhoods of `x`;
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

set_option autoImplicit true


noncomputable section

open Set Filter

universe u v w

/-!
### Topological spaces
-/


/-- A topology on `α`. -/
class TopologicalSpace (α : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set α → Prop
  /-- The set representing the whole space is an open set. Use `isOpen_univ` in the root namespace
  instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set. Use `isOpen_sUnion` in the root namespace
  instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
#align topological_space TopologicalSpace

/-- A constructor for topologies by specifying the closed sets,
and showing that they satisfy the appropriate conditions. -/
def TopologicalSpace.ofClosed {α : Type u} (T : Set (Set α)) (empty_mem : ∅ ∈ T)
    (sInter_mem : ∀ A, A ⊆ T → ⋂₀ A ∈ T)
    (union_mem : ∀ A, A ∈ T → ∀ B, B ∈ T → A ∪ B ∈ T) : TopologicalSpace α where
  IsOpen X := Xᶜ ∈ T
  isOpen_univ := by simp [empty_mem]
  isOpen_inter s t hs ht := by simpa only [compl_inter] using union_mem sᶜ hs tᶜ ht
  isOpen_sUnion s hs := by
    simp only [Set.compl_sUnion]
    exact sInter_mem (compl '' s) fun z ⟨y, hy, hz⟩ => hz ▸ hs y hy
#align topological_space.of_closed TopologicalSpace.ofClosed

section TopologicalSpace

variable {α : Type u} {β : Type v} {ι : Sort w} {a : α} {s s₁ s₂ t : Set α} {p p₁ p₂ : α → Prop}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `α` -/
def IsOpen [TopologicalSpace α] : Set α → Prop := TopologicalSpace.IsOpen
#align is_open IsOpen

set_option quotPrecheck false in
/-- Notation for `IsOpen` with respect to a non-standard topology. -/
scoped[Topology] notation (name := IsOpen_of) "IsOpen[" t "]" => @IsOpen _ t

open Topology

lemma isOpen_mk {p h₁ h₂ h₃} {s : Set α} : IsOpen[⟨p, h₁, h₂, h₃⟩] s ↔ p s := Iff.rfl
#align is_open_mk isOpen_mk

@[ext]
protected theorem TopologicalSpace.ext :
    ∀ {f g : TopologicalSpace α}, IsOpen[f] = IsOpen[g] → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
#align topological_space_eq TopologicalSpace.ext

section

variable [TopologicalSpace α]

@[simp] theorem isOpen_univ : IsOpen (univ : Set α) := TopologicalSpace.isOpen_univ
#align is_open_univ isOpen_univ

theorem IsOpen.inter (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∩ s₂) :=
  TopologicalSpace.isOpen_inter s₁ s₂ h₁ h₂
#align is_open.inter IsOpen.inter

theorem isOpen_sUnion {s : Set (Set α)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h
#align is_open_sUnion isOpen_sUnion

end

protected theorem TopologicalSpace.ext_iff {t t' : TopologicalSpace α} :
    t = t' ↔ ∀ s, IsOpen[t] s ↔ IsOpen[t'] s :=
  ⟨fun h s => h ▸ Iff.rfl, fun h => by ext; exact h _⟩
#align topological_space_eq_iff TopologicalSpace.ext_iff

theorem isOpen_fold {s : Set α} {t : TopologicalSpace α} : t.IsOpen s = IsOpen[t] s :=
  rfl
#align is_open_fold isOpen_fold

variable [TopologicalSpace α]

theorem isOpen_iUnion {f : ι → Set α} (h : ∀ i, IsOpen (f i)) : IsOpen (⋃ i, f i) :=
  isOpen_sUnion (forall_range_iff.2 h)
#align is_open_Union isOpen_iUnion

theorem isOpen_biUnion {s : Set β} {f : β → Set α} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋃ i ∈ s, f i) :=
  isOpen_iUnion fun i => isOpen_iUnion fun hi => h i hi
#align is_open_bUnion isOpen_biUnion

theorem IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s₁ ∪ s₂) := by
  rw [union_eq_iUnion]; exact isOpen_iUnion (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align is_open.union IsOpen.union

@[simp] theorem isOpen_empty : IsOpen (∅ : Set α) := by
  rw [← sUnion_empty]; exact isOpen_sUnion fun a => False.elim
#align is_open_empty isOpen_empty

theorem isOpen_sInter {s : Set (Set α)} (hs : s.Finite) : (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s) :=
  Finite.induction_on hs (fun _ => by rw [sInter_empty]; exact isOpen_univ) fun _ _ ih h => by
    simp only [sInter_insert, ball_insert_iff] at h ⊢
    exact h.1.inter (ih h.2)
#align is_open_sInter isOpen_sInter

theorem isOpen_biInter {s : Set β} {f : β → Set α} (hs : s.Finite) (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  sInter_image f s ▸ isOpen_sInter (hs.image _) (ball_image_iff.2 h)
#align is_open_bInter isOpen_biInter

theorem isOpen_iInter [Finite ι] {s : ι → Set α} (h : ∀ i, IsOpen (s i)) : IsOpen (⋂ i, s i) :=
  isOpen_sInter (finite_range _) (forall_range_iff.2 h)
#align is_open_Inter isOpen_iInter

theorem isOpen_biInter_finset {s : Finset β} {f : β → Set α} (h : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (⋂ i ∈ s, f i) :=
  isOpen_biInter s.finite_toSet h
#align is_open_bInter_finset isOpen_biInter_finset

@[simp] -- porting note: added `simp`
theorem isOpen_const {p : Prop} : IsOpen { _a : α | p } := by by_cases p <;> simp [*]
#align is_open_const isOpen_const

theorem IsOpen.and : IsOpen { a | p₁ a } → IsOpen { a | p₂ a } → IsOpen { a | p₁ a ∧ p₂ a } :=
  IsOpen.inter
#align is_open.and IsOpen.and

/-- A set is closed if its complement is open -/
class IsClosed (s : Set α) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ
#align is_closed IsClosed

set_option quotPrecheck false in
/-- Notation for `IsClosed` with respect to a non-standard topology. -/
scoped[Topology] notation (name := IsClosed_of) "IsClosed[" t "]" => @IsClosed _ t

@[simp] theorem isOpen_compl_iff {s : Set α} : IsOpen sᶜ ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩
#align is_open_compl_iff isOpen_compl_iff

-- porting note: todo: redefine as `IsClosed s ∧ IsOpen s`
/-- A set is clopen if it is both open and closed. -/
def IsClopen (s : Set α) : Prop :=
  IsOpen s ∧ IsClosed s
#align is_clopen IsClopen

protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.1
#align is_clopen.is_open IsClopen.isOpen

protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.2
#align is_clopen.is_closed IsClopen.isClosed

-- porting note: new lemma
theorem isClosed_const {p : Prop} : IsClosed { _a : α | p } := ⟨isOpen_const (p := ¬p)⟩

@[simp] theorem isClosed_empty : IsClosed (∅ : Set α) := isClosed_const
#align is_closed_empty isClosed_empty

@[simp] theorem isClosed_univ : IsClosed (univ : Set α) := isClosed_const
#align is_closed_univ isClosed_univ

theorem IsClosed.union : IsClosed s₁ → IsClosed s₂ → IsClosed (s₁ ∪ s₂) := by
  simpa only [← isOpen_compl_iff, compl_union] using IsOpen.inter
#align is_closed.union IsClosed.union

theorem isClosed_sInter {s : Set (Set α)} : (∀ t ∈ s, IsClosed t) → IsClosed (⋂₀ s) := by
  simpa only [← isOpen_compl_iff, compl_sInter, sUnion_image] using isOpen_biUnion
#align is_closed_sInter isClosed_sInter

theorem isClosed_iInter {f : ι → Set α} (h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i) :=
  isClosed_sInter <| forall_range_iff.2 h
#align is_closed_Inter isClosed_iInter

theorem isClosed_biInter {s : Set β} {f : β → Set α} (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋂ i ∈ s, f i) :=
  isClosed_iInter fun i => isClosed_iInter <| h i
#align is_closed_bInter isClosed_biInter

@[simp]
theorem isClosed_compl_iff {s : Set α} : IsClosed sᶜ ↔ IsOpen s := by
  rw [← isOpen_compl_iff, compl_compl]
#align is_closed_compl_iff isClosed_compl_iff

alias ⟨_, IsOpen.isClosed_compl⟩ := isClosed_compl_iff
#align is_open.is_closed_compl IsOpen.isClosed_compl

theorem IsOpen.sdiff {s t : Set α} (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s \ t) :=
  IsOpen.inter h₁ h₂.isOpen_compl
#align is_open.sdiff IsOpen.sdiff

theorem IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (s₁ ∩ s₂) := by
  rw [← isOpen_compl_iff] at *
  rw [compl_inter]
  exact IsOpen.union h₁ h₂
#align is_closed.inter IsClosed.inter

theorem IsClosed.sdiff {s t : Set α} (h₁ : IsClosed s) (h₂ : IsOpen t) : IsClosed (s \ t) :=
  IsClosed.inter h₁ (isClosed_compl_iff.mpr h₂)
#align is_closed.sdiff IsClosed.sdiff

theorem isClosed_biUnion {s : Set β} {f : β → Set α} (hs : s.Finite) (h : ∀ i ∈ s, IsClosed (f i)) :
    IsClosed (⋃ i ∈ s, f i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_biInter hs h
#align is_closed_bUnion isClosed_biUnion

theorem isClosed_iUnion [Finite ι] {s : ι → Set α} (h : ∀ i, IsClosed (s i)) :
    IsClosed (⋃ i, s i) := by
  simp only [← isOpen_compl_iff, compl_iUnion] at *
  exact isOpen_iInter h
#align is_closed_Union isClosed_iUnion

theorem isClosed_imp {p q : α → Prop} (hp : IsOpen { x | p x }) (hq : IsClosed { x | q x }) :
    IsClosed { x | p x → q x } := by
  simpa only [imp_iff_not_or] using hp.isClosed_compl.union hq
#align is_closed_imp isClosed_imp

theorem IsClosed.not : IsClosed { a | p a } → IsOpen { a | ¬p a } :=
  isOpen_compl_iff.mpr
#align is_closed.not IsClosed.not

/-!
### Interior of a set
-/

/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set α) : Set α :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
#align interior interior

-- porting note: use `∃ t, t ⊆ s ∧ _` instead of `∃ t ⊆ s, _`
theorem mem_interior {s : Set α} {x : α} : x ∈ interior s ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_setOf_eq, and_assoc, and_left_comm]
#align mem_interior mem_interiorₓ

@[simp]
theorem isOpen_interior {s : Set α} : IsOpen (interior s) :=
  isOpen_sUnion fun _ => And.left
#align is_open_interior isOpen_interior

theorem interior_subset {s : Set α} : interior s ⊆ s :=
  sUnion_subset fun _ => And.right
#align interior_subset interior_subset

theorem interior_maximal {s t : Set α} (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩
#align interior_maximal interior_maximal

theorem IsOpen.interior_eq {s : Set α} (h : IsOpen s) : interior s = s :=
  interior_subset.antisymm (interior_maximal (Subset.refl s) h)
#align is_open.interior_eq IsOpen.interior_eq

theorem interior_eq_iff_isOpen {s : Set α} : interior s = s ↔ IsOpen s :=
  ⟨fun h => h ▸ isOpen_interior, IsOpen.interior_eq⟩
#align interior_eq_iff_is_open interior_eq_iff_isOpen

theorem subset_interior_iff_isOpen {s : Set α} : s ⊆ interior s ↔ IsOpen s := by
  simp only [interior_eq_iff_isOpen.symm, Subset.antisymm_iff, interior_subset, true_and]
#align subset_interior_iff_is_open subset_interior_iff_isOpen

theorem IsOpen.subset_interior_iff {s t : Set α} (h₁ : IsOpen s) : s ⊆ interior t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h interior_subset, fun h₂ => interior_maximal h₂ h₁⟩
#align is_open.subset_interior_iff IsOpen.subset_interior_iff

theorem subset_interior_iff {s t : Set α} : t ⊆ interior s ↔ ∃ U, IsOpen U ∧ t ⊆ U ∧ U ⊆ s :=
  ⟨fun h => ⟨interior s, isOpen_interior, h, interior_subset⟩, fun ⟨_U, hU, htU, hUs⟩ =>
    htU.trans (interior_maximal hUs hU)⟩
#align subset_interior_iff subset_interior_iff

@[mono]
theorem interior_mono {s t : Set α} (h : s ⊆ t) : interior s ⊆ interior t :=
  interior_maximal (Subset.trans interior_subset h) isOpen_interior
#align interior_mono interior_mono

@[simp]
theorem interior_empty : interior (∅ : Set α) = ∅ :=
  isOpen_empty.interior_eq
#align interior_empty interior_empty

@[simp]
theorem interior_univ : interior (univ : Set α) = univ :=
  isOpen_univ.interior_eq
#align interior_univ interior_univ

@[simp]
theorem interior_eq_univ {s : Set α} : interior s = univ ↔ s = univ :=
  ⟨fun h => univ_subset_iff.mp <| h.symm.trans_le interior_subset, fun h => h.symm ▸ interior_univ⟩
#align interior_eq_univ interior_eq_univ

@[simp]
theorem interior_interior {s : Set α} : interior (interior s) = interior s :=
  isOpen_interior.interior_eq
#align interior_interior interior_interior

@[simp]
theorem interior_inter {s t : Set α} : interior (s ∩ t) = interior s ∩ interior t :=
  Subset.antisymm
    (subset_inter (interior_mono <| inter_subset_left s t)
      (interior_mono <| inter_subset_right s t))
    (interior_maximal (inter_subset_inter interior_subset interior_subset) <|
      IsOpen.inter isOpen_interior isOpen_interior)
#align interior_inter interior_inter

@[simp]
theorem Finset.interior_iInter {ι : Type*} (s : Finset ι) (f : ι → Set α) :
    interior (⋂ i ∈ s, f i) = ⋂ i ∈ s, interior (f i) := by
  classical
    refine' s.induction_on (by simp) _
    intro i s _ h₂
    simp [h₂]
#align finset.interior_Inter Finset.interior_iInter

-- todo: generalize to `ι : Sort*`
@[simp]
theorem interior_iInter {ι : Type*} [Finite ι] (f : ι → Set α) :
    interior (⋂ i, f i) = ⋂ i, interior (f i) := by
  cases nonempty_fintype ι
  convert Finset.univ.interior_iInter f <;> simp
#align interior_Inter interior_iInter

theorem interior_union_isClosed_of_interior_empty {s t : Set α} (h₁ : IsClosed s)
    (h₂ : interior t = ∅) : interior (s ∪ t) = interior s :=
  have : interior (s ∪ t) ⊆ s := fun x ⟨u, ⟨(hu₁ : IsOpen u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩ =>
    by_contradiction fun hx₂ : x ∉ s =>
      have : u \ s ⊆ t := fun x ⟨h₁, h₂⟩ => Or.resolve_left (hu₂ h₁) h₂
      have : u \ s ⊆ interior t := by rwa [(IsOpen.sdiff hu₁ h₁).subset_interior_iff]
      have : u \ s ⊆ ∅ := by rwa [h₂] at this
      this ⟨hx₁, hx₂⟩
  Subset.antisymm (interior_maximal this isOpen_interior) (interior_mono <| subset_union_left _ _)
#align interior_union_is_closed_of_interior_empty interior_union_isClosed_of_interior_empty

theorem isOpen_iff_forall_mem_open : IsOpen s ↔ ∀ x ∈ s, ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t := by
  rw [← subset_interior_iff_isOpen]
  simp only [subset_def, mem_interior]
#align is_open_iff_forall_mem_open isOpen_iff_forall_mem_open

theorem interior_iInter_subset (s : ι → Set α) : interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) :=
  subset_iInter fun _ => interior_mono <| iInter_subset _ _
#align interior_Inter_subset interior_iInter_subset

theorem interior_Inter₂_subset (p : ι → Sort*) (s : ∀ i, p i → Set α) :
    interior (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), interior (s i j) :=
  (interior_iInter_subset _).trans <| iInter_mono fun _ => interior_iInter_subset _
#align interior_Inter₂_subset interior_Inter₂_subset

theorem interior_sInter_subset (S : Set (Set α)) : interior (⋂₀ S) ⊆ ⋂ s ∈ S, interior s :=
  calc
    interior (⋂₀ S) = interior (⋂ s ∈ S, s) := by rw [sInter_eq_biInter]
    _ ⊆ ⋂ s ∈ S, interior s := interior_Inter₂_subset _ _
#align interior_sInter_subset interior_sInter_subset

/-!
### Closure of a set
-/


/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set α) : Set α :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
#align closure closure

set_option quotPrecheck false in
/-- Notation for `closure` with respect to a non-standard topology. -/
scoped[Topology] notation (name := closure_of) "closure[" t "]" => @closure _ t

@[simp]
theorem isClosed_closure {s : Set α} : IsClosed (closure s) :=
  isClosed_sInter fun _ => And.left
#align is_closed_closure isClosed_closure

theorem subset_closure {s : Set α} : s ⊆ closure s :=
  subset_sInter fun _ => And.right
#align subset_closure subset_closure

theorem not_mem_of_not_mem_closure {s : Set α} {P : α} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align not_mem_of_not_mem_closure not_mem_of_not_mem_closure

theorem closure_minimal {s t : Set α} (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t :=
  sInter_subset_of_mem ⟨h₂, h₁⟩
#align closure_minimal closure_minimal

theorem Disjoint.closure_left {s t : Set α} (hd : Disjoint s t) (ht : IsOpen t) :
    Disjoint (closure s) t :=
  disjoint_compl_left.mono_left <| closure_minimal hd.subset_compl_right ht.isClosed_compl
#align disjoint.closure_left Disjoint.closure_left

theorem Disjoint.closure_right {s t : Set α} (hd : Disjoint s t) (hs : IsOpen s) :
    Disjoint s (closure t) :=
  (hd.symm.closure_left hs).symm
#align disjoint.closure_right Disjoint.closure_right

theorem IsClosed.closure_eq {s : Set α} (h : IsClosed s) : closure s = s :=
  Subset.antisymm (closure_minimal (Subset.refl s) h) subset_closure
#align is_closed.closure_eq IsClosed.closure_eq

theorem IsClosed.closure_subset {s : Set α} (hs : IsClosed s) : closure s ⊆ s :=
  closure_minimal (Subset.refl _) hs
#align is_closed.closure_subset IsClosed.closure_subset

theorem IsClosed.closure_subset_iff {s t : Set α} (h₁ : IsClosed t) : closure s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans subset_closure, fun h => closure_minimal h h₁⟩
#align is_closed.closure_subset_iff IsClosed.closure_subset_iff

theorem IsClosed.mem_iff_closure_subset {s : Set α} (hs : IsClosed s) {x : α} :
    x ∈ s ↔ closure ({x} : Set α) ⊆ s :=
  (hs.closure_subset_iff.trans Set.singleton_subset_iff).symm
#align is_closed.mem_iff_closure_subset IsClosed.mem_iff_closure_subset

@[mono]
theorem closure_mono {s t : Set α} (h : s ⊆ t) : closure s ⊆ closure t :=
  closure_minimal (Subset.trans h subset_closure) isClosed_closure
#align closure_mono closure_mono

theorem monotone_closure (α : Type*) [TopologicalSpace α] : Monotone (@closure α _) := fun _ _ =>
  closure_mono
#align monotone_closure monotone_closure

theorem diff_subset_closure_iff {s t : Set α} : s \ t ⊆ closure t ↔ s ⊆ closure t := by
  rw [diff_subset_iff, union_eq_self_of_subset_left subset_closure]
#align diff_subset_closure_iff diff_subset_closure_iff

theorem closure_inter_subset_inter_closure (s t : Set α) :
    closure (s ∩ t) ⊆ closure s ∩ closure t :=
  (monotone_closure α).map_inf_le s t
#align closure_inter_subset_inter_closure closure_inter_subset_inter_closure

theorem isClosed_of_closure_subset {s : Set α} (h : closure s ⊆ s) : IsClosed s := by
  rw [subset_closure.antisymm h]; exact isClosed_closure
#align is_closed_of_closure_subset isClosed_of_closure_subset

theorem closure_eq_iff_isClosed {s : Set α} : closure s = s ↔ IsClosed s :=
  ⟨fun h => h ▸ isClosed_closure, IsClosed.closure_eq⟩
#align closure_eq_iff_is_closed closure_eq_iff_isClosed

theorem closure_subset_iff_isClosed {s : Set α} : closure s ⊆ s ↔ IsClosed s :=
  ⟨isClosed_of_closure_subset, IsClosed.closure_subset⟩
#align closure_subset_iff_is_closed closure_subset_iff_isClosed

@[simp]
theorem closure_empty : closure (∅ : Set α) = ∅ :=
  isClosed_empty.closure_eq
#align closure_empty closure_empty

@[simp]
theorem closure_empty_iff (s : Set α) : closure s = ∅ ↔ s = ∅ :=
  ⟨subset_eq_empty subset_closure, fun h => h.symm ▸ closure_empty⟩
#align closure_empty_iff closure_empty_iff

@[simp]
theorem closure_nonempty_iff {s : Set α} : (closure s).Nonempty ↔ s.Nonempty := by
  simp only [nonempty_iff_ne_empty, Ne.def, closure_empty_iff]
#align closure_nonempty_iff closure_nonempty_iff

alias ⟨Set.Nonempty.of_closure, Set.Nonempty.closure⟩ := closure_nonempty_iff
#align set.nonempty.of_closure Set.Nonempty.of_closure
#align set.nonempty.closure Set.Nonempty.closure

@[simp]
theorem closure_univ : closure (univ : Set α) = univ :=
  isClosed_univ.closure_eq
#align closure_univ closure_univ

@[simp]
theorem closure_closure {s : Set α} : closure (closure s) = closure s :=
  isClosed_closure.closure_eq
#align closure_closure closure_closure

@[simp]
theorem closure_union {s t : Set α} : closure (s ∪ t) = closure s ∪ closure t :=
  Subset.antisymm
    (closure_minimal (union_subset_union subset_closure subset_closure) <|
      IsClosed.union isClosed_closure isClosed_closure)
    ((monotone_closure α).le_map_sup s t)
#align closure_union closure_union

@[simp]
theorem Finset.closure_biUnion {ι : Type*} (s : Finset ι) (f : ι → Set α) :
    closure (⋃ i ∈ s, f i) = ⋃ i ∈ s, closure (f i) := by
  classical
    refine' s.induction_on (by simp) _
    intro i s _ h₂
    simp [h₂]
#align finset.closure_bUnion Finset.closure_biUnion

@[simp]
theorem closure_iUnion {ι : Type*} [Finite ι] (f : ι → Set α) :
    closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  cases nonempty_fintype ι
  convert Finset.univ.closure_biUnion f <;> simp
#align closure_Union closure_iUnion

theorem interior_subset_closure {s : Set α} : interior s ⊆ closure s :=
  Subset.trans interior_subset subset_closure
#align interior_subset_closure interior_subset_closure

theorem closure_eq_compl_interior_compl {s : Set α} : closure s = (interior sᶜ)ᶜ := by
  rw [interior, closure, compl_sUnion, compl_image_set_of]
  simp only [compl_subset_compl, isOpen_compl_iff]
#align closure_eq_compl_interior_compl closure_eq_compl_interior_compl

@[simp]
theorem interior_compl {s : Set α} : interior sᶜ = (closure s)ᶜ := by
  simp [closure_eq_compl_interior_compl]
#align interior_compl interior_compl

@[simp]
theorem closure_compl {s : Set α} : closure sᶜ = (interior s)ᶜ := by
  simp [closure_eq_compl_interior_compl]
#align closure_compl closure_compl

theorem mem_closure_iff {s : Set α} {a : α} :
    a ∈ closure s ↔ ∀ o, IsOpen o → a ∈ o → (o ∩ s).Nonempty :=
  ⟨fun h o oo ao =>
    by_contradiction fun os =>
      have : s ⊆ oᶜ := fun x xs xo => os ⟨x, xo, xs⟩
      closure_minimal this (isClosed_compl_iff.2 oo) h ao,
    fun H _ ⟨h₁, h₂⟩ =>
    by_contradiction fun nc =>
      let ⟨_, hc, hs⟩ := H _ h₁.isOpen_compl nc
      hc (h₂ hs)⟩
#align mem_closure_iff mem_closure_iff

theorem closure_inter_open_nonempty_iff {s t : Set α} (h : IsOpen t) :
    (closure s ∩ t).Nonempty ↔ (s ∩ t).Nonempty :=
  ⟨fun ⟨_x, hxcs, hxt⟩ => inter_comm t s ▸ mem_closure_iff.1 hxcs t h hxt, fun h =>
    h.mono <| inf_le_inf_right t subset_closure⟩
#align closure_inter_open_nonempty_iff closure_inter_open_nonempty_iff

theorem Filter.le_lift'_closure (l : Filter α) : l ≤ l.lift' closure :=
  le_lift'.2 fun _ h => mem_of_superset h subset_closure
#align filter.le_lift'_closure Filter.le_lift'_closure

theorem Filter.HasBasis.lift'_closure {l : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) : (l.lift' closure).HasBasis p fun i => closure (s i) :=
  h.lift' (monotone_closure α)
#align filter.has_basis.lift'_closure Filter.HasBasis.lift'_closure

theorem Filter.HasBasis.lift'_closure_eq_self {l : Filter α} {p : ι → Prop} {s : ι → Set α}
    (h : l.HasBasis p s) (hc : ∀ i, p i → IsClosed (s i)) : l.lift' closure = l :=
  le_antisymm (h.ge_iff.2 fun i hi => (hc i hi).closure_eq ▸ mem_lift' (h.mem_of_mem hi))
    l.le_lift'_closure
#align filter.has_basis.lift'_closure_eq_self Filter.HasBasis.lift'_closure_eq_self

@[simp]
theorem Filter.lift'_closure_eq_bot {l : Filter α} : l.lift' closure = ⊥ ↔ l = ⊥ :=
  ⟨fun h => bot_unique <| h ▸ l.le_lift'_closure, fun h =>
    h.symm ▸ by rw [lift'_bot (monotone_closure _), closure_empty, principal_empty]⟩
#align filter.lift'_closure_eq_bot Filter.lift'_closure_eq_bot

/-- A set is dense in a topological space if every point belongs to its closure. -/
def Dense (s : Set α) : Prop :=
  ∀ x, x ∈ closure s
#align dense Dense

theorem dense_iff_closure_eq {s : Set α} : Dense s ↔ closure s = univ :=
  eq_univ_iff_forall.symm
#align dense_iff_closure_eq dense_iff_closure_eq

alias ⟨Dense.closure_eq, _⟩ := dense_iff_closure_eq
#align dense.closure_eq Dense.closure_eq

theorem interior_eq_empty_iff_dense_compl {s : Set α} : interior s = ∅ ↔ Dense sᶜ := by
  rw [dense_iff_closure_eq, closure_compl, compl_univ_iff]
#align interior_eq_empty_iff_dense_compl interior_eq_empty_iff_dense_compl

theorem Dense.interior_compl {s : Set α} (h : Dense s) : interior sᶜ = ∅ :=
  interior_eq_empty_iff_dense_compl.2 <| by rwa [compl_compl]
#align dense.interior_compl Dense.interior_compl

/-- The closure of a set `s` is dense if and only if `s` is dense. -/
@[simp]
theorem dense_closure {s : Set α} : Dense (closure s) ↔ Dense s := by
  rw [Dense, Dense, closure_closure]
#align dense_closure dense_closure

protected alias ⟨_, Dense.closure⟩ := dense_closure
alias ⟨Dense.of_closure, _⟩ := dense_closure
#align dense.of_closure Dense.of_closure
#align dense.closure Dense.closure

@[simp]
theorem dense_univ : Dense (univ : Set α) := fun _ => subset_closure trivial
#align dense_univ dense_univ

/-- A set is dense if and only if it has a nonempty intersection with each nonempty open set. -/
theorem dense_iff_inter_open {s : Set α} :
    Dense s ↔ ∀ U, IsOpen U → U.Nonempty → (U ∩ s).Nonempty := by
  constructor <;> intro h
  · rintro U U_op ⟨x, x_in⟩
    exact mem_closure_iff.1 (h _) U U_op x_in
  · intro x
    rw [mem_closure_iff]
    intro U U_op x_in
    exact h U U_op ⟨_, x_in⟩
#align dense_iff_inter_open dense_iff_inter_open

alias ⟨Dense.inter_open_nonempty, _⟩ := dense_iff_inter_open
#align dense.inter_open_nonempty Dense.inter_open_nonempty

theorem Dense.exists_mem_open {s : Set α} (hs : Dense s) {U : Set α} (ho : IsOpen U)
    (hne : U.Nonempty) : ∃ x ∈ s, x ∈ U :=
  let ⟨x, hx⟩ := hs.inter_open_nonempty U ho hne
  ⟨x, hx.2, hx.1⟩
#align dense.exists_mem_open Dense.exists_mem_open

theorem Dense.nonempty_iff {s : Set α} (hs : Dense s) : s.Nonempty ↔ Nonempty α :=
  ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ =>
    let ⟨y, hy⟩ := hs.inter_open_nonempty _ isOpen_univ ⟨x, trivial⟩
    ⟨y, hy.2⟩⟩
#align dense.nonempty_iff Dense.nonempty_iff

theorem Dense.nonempty [h : Nonempty α] {s : Set α} (hs : Dense s) : s.Nonempty :=
  hs.nonempty_iff.2 h
#align dense.nonempty Dense.nonempty

@[mono]
theorem Dense.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) (hd : Dense s₁) : Dense s₂ := fun x =>
  closure_mono h (hd x)
#align dense.mono Dense.mono

/-- Complement to a singleton is dense if and only if the singleton is not an open set. -/
theorem dense_compl_singleton_iff_not_open {x : α} :
    Dense ({x}ᶜ : Set α) ↔ ¬IsOpen ({x} : Set α) := by
  constructor
  · intro hd ho
    exact (hd.inter_open_nonempty _ ho (singleton_nonempty _)).ne_empty (inter_compl_self _)
  · refine' fun ho => dense_iff_inter_open.2 fun U hU hne => inter_compl_nonempty_iff.2 fun hUx => _
    obtain rfl : U = {x}
    exact eq_singleton_iff_nonempty_unique_mem.2 ⟨hne, hUx⟩
    exact ho hU
#align dense_compl_singleton_iff_not_open dense_compl_singleton_iff_not_open

/-!
### Frontier of a set
-/

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : Set α) : Set α :=
  closure s \ interior s
#align frontier frontier

@[simp]
theorem closure_diff_interior (s : Set α) : closure s \ interior s = frontier s :=
  rfl
#align closure_diff_interior closure_diff_interior

@[simp]
theorem closure_diff_frontier (s : Set α) : closure s \ frontier s = interior s := by
  rw [frontier, diff_diff_right_self, inter_eq_self_of_subset_right interior_subset_closure]
#align closure_diff_frontier closure_diff_frontier

@[simp]
theorem self_diff_frontier (s : Set α) : s \ frontier s = interior s := by
  rw [frontier, diff_diff_right, diff_eq_empty.2 subset_closure,
    inter_eq_self_of_subset_right interior_subset, empty_union]
#align self_diff_frontier self_diff_frontier

theorem frontier_eq_closure_inter_closure {s : Set α} : frontier s = closure s ∩ closure sᶜ := by
  rw [closure_compl, frontier, diff_eq]
#align frontier_eq_closure_inter_closure frontier_eq_closure_inter_closure

theorem frontier_subset_closure {s : Set α} : frontier s ⊆ closure s :=
  diff_subset _ _
#align frontier_subset_closure frontier_subset_closure

theorem IsClosed.frontier_subset (hs : IsClosed s) : frontier s ⊆ s :=
  frontier_subset_closure.trans hs.closure_eq.subset
#align is_closed.frontier_subset IsClosed.frontier_subset

theorem frontier_closure_subset {s : Set α} : frontier (closure s) ⊆ frontier s :=
  diff_subset_diff closure_closure.subset <| interior_mono subset_closure
#align frontier_closure_subset frontier_closure_subset

theorem frontier_interior_subset {s : Set α} : frontier (interior s) ⊆ frontier s :=
  diff_subset_diff (closure_mono interior_subset) interior_interior.symm.subset
#align frontier_interior_subset frontier_interior_subset

/-- The complement of a set has the same frontier as the original set. -/
@[simp]
theorem frontier_compl (s : Set α) : frontier sᶜ = frontier s := by
  simp only [frontier_eq_closure_inter_closure, compl_compl, inter_comm]
#align frontier_compl frontier_compl

@[simp]
theorem frontier_univ : frontier (univ : Set α) = ∅ := by simp [frontier]
#align frontier_univ frontier_univ

@[simp]
theorem frontier_empty : frontier (∅ : Set α) = ∅ := by simp [frontier]
#align frontier_empty frontier_empty

theorem frontier_inter_subset (s t : Set α) :
    frontier (s ∩ t) ⊆ frontier s ∩ closure t ∪ closure s ∩ frontier t := by
  simp only [frontier_eq_closure_inter_closure, compl_inter, closure_union]
  refine' (inter_subset_inter_left _ (closure_inter_subset_inter_closure s t)).trans_eq _
  simp only [inter_distrib_left, inter_distrib_right, inter_assoc, inter_comm (closure t)]
#align frontier_inter_subset frontier_inter_subset

theorem frontier_union_subset (s t : Set α) :
    frontier (s ∪ t) ⊆ frontier s ∩ closure tᶜ ∪ closure sᶜ ∩ frontier t := by
  simpa only [frontier_compl, ← compl_union] using frontier_inter_subset sᶜ tᶜ
#align frontier_union_subset frontier_union_subset

theorem IsClosed.frontier_eq {s : Set α} (hs : IsClosed s) : frontier s = s \ interior s := by
  rw [frontier, hs.closure_eq]
#align is_closed.frontier_eq IsClosed.frontier_eq

theorem IsOpen.frontier_eq {s : Set α} (hs : IsOpen s) : frontier s = closure s \ s := by
  rw [frontier, hs.interior_eq]
#align is_open.frontier_eq IsOpen.frontier_eq

theorem IsOpen.inter_frontier_eq {s : Set α} (hs : IsOpen s) : s ∩ frontier s = ∅ := by
  rw [hs.frontier_eq, inter_diff_self]
#align is_open.inter_frontier_eq IsOpen.inter_frontier_eq

/-- The frontier of a set is closed. -/
theorem isClosed_frontier {s : Set α} : IsClosed (frontier s) := by
  rw [frontier_eq_closure_inter_closure]; exact IsClosed.inter isClosed_closure isClosed_closure
#align is_closed_frontier isClosed_frontier

/-- The frontier of a closed set has no interior point. -/
theorem interior_frontier {s : Set α} (h : IsClosed s) : interior (frontier s) = ∅ := by
  have A : frontier s = s \ interior s := h.frontier_eq
  have B : interior (frontier s) ⊆ interior s := by rw [A]; exact interior_mono (diff_subset _ _)
  have C : interior (frontier s) ⊆ frontier s := interior_subset
  have : interior (frontier s) ⊆ interior s ∩ (s \ interior s) :=
    subset_inter B (by simpa [A] using C)
  rwa [inter_diff_self, subset_empty_iff] at this
#align interior_frontier interior_frontier

theorem closure_eq_interior_union_frontier (s : Set α) : closure s = interior s ∪ frontier s :=
  (union_diff_cancel interior_subset_closure).symm
#align closure_eq_interior_union_frontier closure_eq_interior_union_frontier

theorem closure_eq_self_union_frontier (s : Set α) : closure s = s ∪ frontier s :=
  (union_diff_cancel' interior_subset subset_closure).symm
#align closure_eq_self_union_frontier closure_eq_self_union_frontier

theorem Disjoint.frontier_left (ht : IsOpen t) (hd : Disjoint s t) : Disjoint (frontier s) t :=
  subset_compl_iff_disjoint_right.1 <|
    frontier_subset_closure.trans <| closure_minimal (disjoint_left.1 hd) <| isClosed_compl_iff.2 ht
#align disjoint.frontier_left Disjoint.frontier_left

theorem Disjoint.frontier_right (hs : IsOpen s) (hd : Disjoint s t) : Disjoint s (frontier t) :=
  (hd.symm.frontier_left hs).symm
#align disjoint.frontier_right Disjoint.frontier_right

theorem frontier_eq_inter_compl_interior {s : Set α} :
    frontier s = (interior s)ᶜ ∩ (interior sᶜ)ᶜ := by
  rw [← frontier_compl, ← closure_compl]; rfl
#align frontier_eq_inter_compl_interior frontier_eq_inter_compl_interior

theorem compl_frontier_eq_union_interior {s : Set α} :
    (frontier s)ᶜ = interior s ∪ interior sᶜ := by
  rw [frontier_eq_inter_compl_interior]
  simp only [compl_inter, compl_compl]
#align compl_frontier_eq_union_interior compl_frontier_eq_union_interior

/-!
### Neighborhoods
-/

/-- A set is called a neighborhood of `a` if it contains an open set around `a`. The set of all
neighborhoods of `a` forms a filter, the neighborhood filter at `a`, is here defined as the
infimum over the principal filters of all open sets containing `a`. -/
irreducible_def nhds (a : α) : Filter α :=
  ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 s
#align nhds nhds
#align nhds_def nhds_def

/-- The "neighborhood within" filter. Elements of `𝓝[s] a` are sets containing the
intersection of `s` and a neighborhood of `a`. -/
def nhdsWithin (a : α) (s : Set α) : Filter α :=
  nhds a ⊓ 𝓟 s
#align nhds_within nhdsWithin

section

@[inherit_doc]
scoped[Topology] notation "𝓝" => nhds

@[inherit_doc]
scoped[Topology] notation "𝓝[" s "] " x:100 => nhdsWithin x s

/-- Notation for the filter of punctured neighborhoods of a point. -/
scoped[Topology] notation "𝓝[≠] " x:100 => nhdsWithin x {x}ᶜ

/-- Notation for the filter of right neighborhoods of a point. -/
scoped[Topology] notation "𝓝[≥] " x:100 => nhdsWithin x (Set.Ici x)

/-- Notation for the filter of left neighborhoods of a point. -/
scoped[Topology] notation "𝓝[≤] " x:100 => nhdsWithin x (Set.Iic x)

/-- Notation for the filter of punctured right neighborhoods of a point. -/
scoped[Topology] notation "𝓝[>] " x:100 => nhdsWithin x (Set.Ioi x)

/-- Notation for the filter of punctured left neighborhoods of a point. -/
scoped[Topology] notation "𝓝[<] " x:100 => nhdsWithin x (Set.Iio x)

end

theorem nhds_def' (a : α) : 𝓝 a = ⨅ (s : Set α) (_ : IsOpen s) (_ : a ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_setOf_eq, @and_comm (a ∈ _), iInf_and]
#align nhds_def' nhds_def'

/-- The open sets containing `a` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens (a : α) :
    (𝓝 a).HasBasis (fun s : Set α => a ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩)
    ⟨univ, ⟨mem_univ a, isOpen_univ⟩⟩
#align nhds_basis_opens nhds_basis_opens

theorem nhds_basis_closeds (a : α) : (𝓝 a).HasBasis (fun s : Set α => a ∉ s ∧ IsClosed s) compl :=
  ⟨fun t => (nhds_basis_opens a).mem_iff.trans <|
    compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩
#align nhds_basis_closeds nhds_basis_closeds

/-- A filter lies below the neighborhood filter at `a` iff it contains every open set around `a`. -/
theorem le_nhds_iff {f a} : f ≤ 𝓝 a ↔ ∀ s : Set α, a ∈ s → IsOpen s → s ∈ f := by simp [nhds_def]
#align le_nhds_iff le_nhds_iff

/-- To show a filter is above the neighborhood filter at `a`, it suffices to show that it is above
the principal filter of some open set `s` containing `a`. -/
theorem nhds_le_of_le {f a} {s : Set α} (h : a ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 a ≤ f := by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf
#align nhds_le_of_le nhds_le_of_le

-- porting note: use `∃ t, t ⊆ s ∧ _` instead of `∃ t ⊆ s, _`
theorem mem_nhds_iff {a : α} {s : Set α} : s ∈ 𝓝 a ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ a ∈ t :=
  (nhds_basis_opens a).mem_iff.trans <| exists_congr <| fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩
#align mem_nhds_iff mem_nhds_iffₓ

/-- A predicate is true in a neighborhood of `a` iff it is true for all the points in an open set
containing `a`. -/
theorem eventually_nhds_iff {a : α} {p : α → Prop} :
    (∀ᶠ x in 𝓝 a, p x) ↔ ∃ t : Set α, (∀ x ∈ t, p x) ∧ IsOpen t ∧ a ∈ t :=
  mem_nhds_iff.trans <| by simp only [subset_def, exists_prop, mem_setOf_eq]
#align eventually_nhds_iff eventually_nhds_iff

theorem mem_interior_iff_mem_nhds {s : Set α} {a : α} : a ∈ interior s ↔ s ∈ 𝓝 a :=
  mem_interior.trans mem_nhds_iff.symm
#align mem_interior_iff_mem_nhds mem_interior_iff_mem_nhds

theorem map_nhds {a : α} {f : α → β} :
    map f (𝓝 a) = ⨅ s ∈ { s : Set α | a ∈ s ∧ IsOpen s }, 𝓟 (image f s) :=
  ((nhds_basis_opens a).map f).eq_biInf
#align map_nhds map_nhds

theorem mem_of_mem_nhds {a : α} {s : Set α} : s ∈ 𝓝 a → a ∈ s := fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs
#align mem_of_mem_nhds mem_of_mem_nhds

/-- If a predicate is true in a neighborhood of `a`, then it is true for `a`. -/
theorem Filter.Eventually.self_of_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) : p a :=
  mem_of_mem_nhds h
#align filter.eventually.self_of_nhds Filter.Eventually.self_of_nhds

theorem IsOpen.mem_nhds {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) : s ∈ 𝓝 a :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, ha⟩
#align is_open.mem_nhds IsOpen.mem_nhds

protected theorem IsOpen.mem_nhds_iff {a : α} {s : Set α} (hs : IsOpen s) : s ∈ 𝓝 a ↔ a ∈ s :=
  ⟨mem_of_mem_nhds, fun ha => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, ha⟩⟩
#align is_open.mem_nhds_iff IsOpen.mem_nhds_iff

theorem IsClosed.compl_mem_nhds {a : α} {s : Set α} (hs : IsClosed s) (ha : a ∉ s) : sᶜ ∈ 𝓝 a :=
  hs.isOpen_compl.mem_nhds (mem_compl ha)
#align is_closed.compl_mem_nhds IsClosed.compl_mem_nhds

theorem IsOpen.eventually_mem {a : α} {s : Set α} (hs : IsOpen s) (ha : a ∈ s) :
    ∀ᶠ x in 𝓝 a, x ∈ s :=
  IsOpen.mem_nhds hs ha
#align is_open.eventually_mem IsOpen.eventually_mem

/-- The open neighborhoods of `a` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `a` instead. -/
theorem nhds_basis_opens' (a : α) :
    (𝓝 a).HasBasis (fun s : Set α => s ∈ 𝓝 a ∧ IsOpen s) fun x => x := by
  convert nhds_basis_opens a using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff
#align nhds_basis_opens' nhds_basis_opens'

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds {s U : Set α} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
    ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 <| h x hx, isOpen_interior, interior_subset⟩
#align exists_open_set_nhds exists_open_set_nhds

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds' {s U : Set α} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
    ∃ V : Set α, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds (by simpa using h)
#align exists_open_set_nhds' exists_open_set_nhds'

/-- If a predicate is true in a neighbourhood of `a`, then for `y` sufficiently close
to `a` this predicate is true in a neighbourhood of `y`. -/
theorem Filter.Eventually.eventually_nhds {p : α → Prop} {a : α} (h : ∀ᶠ y in 𝓝 a, p y) :
    ∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩
#align filter.eventually.eventually_nhds Filter.Eventually.eventually_nhds

@[simp]
theorem eventually_eventually_nhds {p : α → Prop} {a : α} :
    (∀ᶠ y in 𝓝 a, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 a, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩
#align eventually_eventually_nhds eventually_eventually_nhds

@[simp]
theorem frequently_frequently_nhds {p : α → Prop} {a : α} :
    (∃ᶠ y in 𝓝 a, ∃ᶠ x in 𝓝 y, p x) ↔ ∃ᶠ x in 𝓝 a, p x := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]
#align frequently_frequently_nhds frequently_frequently_nhds

@[simp]
theorem eventually_mem_nhds {s : Set α} {a : α} : (∀ᶠ x in 𝓝 a, s ∈ 𝓝 x) ↔ s ∈ 𝓝 a :=
  eventually_eventually_nhds
#align eventually_mem_nhds eventually_mem_nhds

@[simp]
theorem nhds_bind_nhds : (𝓝 a).bind 𝓝 = 𝓝 a :=
  Filter.ext fun _ => eventually_eventually_nhds
#align nhds_bind_nhds nhds_bind_nhds

@[simp]
theorem eventually_eventuallyEq_nhds {f g : α → β} {a : α} :
    (∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 a] g :=
  eventually_eventually_nhds
#align eventually_eventually_eq_nhds eventually_eventuallyEq_nhds

theorem Filter.EventuallyEq.eq_of_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) : f a = g a :=
  h.self_of_nhds
#align filter.eventually_eq.eq_of_nhds Filter.EventuallyEq.eq_of_nhds

@[simp]
theorem eventually_eventuallyLE_nhds [LE β] {f g : α → β} {a : α} :
    (∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 a] g :=
  eventually_eventually_nhds
#align eventually_eventually_le_nhds eventually_eventuallyLE_nhds

/-- If two functions are equal in a neighbourhood of `a`, then for `y` sufficiently close
to `a` these functions are equal in a neighbourhood of `y`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : α → β} {a : α} (h : f =ᶠ[𝓝 a] g) :
    ∀ᶠ y in 𝓝 a, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds
#align filter.eventually_eq.eventually_eq_nhds Filter.EventuallyEq.eventuallyEq_nhds

/-- If `f x ≤ g x` in a neighbourhood of `a`, then for `y` sufficiently close to `a` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem Filter.EventuallyLE.eventuallyLE_nhds [LE β] {f g : α → β} {a : α} (h : f ≤ᶠ[𝓝 a] g) :
    ∀ᶠ y in 𝓝 a, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds
#align filter.eventually_le.eventually_le_nhds Filter.EventuallyLE.eventuallyLE_nhds

theorem all_mem_nhds (x : α) (P : Set α → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀ s ∈ 𝓝 x, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by simp only [@and_comm (x ∈ _), and_imp]
#align all_mem_nhds all_mem_nhds

theorem all_mem_nhds_filter (x : α) (f : Set α → Set β) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : Filter β) : (∀ s ∈ 𝓝 x, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)
#align all_mem_nhds_filter all_mem_nhds_filter

theorem tendsto_nhds {f : β → α} {l : Filter β} {a : α} :
    Tendsto f l (𝓝 a) ↔ ∀ s, IsOpen s → a ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _
#align tendsto_nhds tendsto_nhds

theorem tendsto_atTop_nhds [Nonempty β] [SemilatticeSup β] {f : β → α} {a : α} :
    Tendsto f atTop (𝓝 a) ↔ ∀ U : Set α, a ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (atTop_basis.tendsto_iff (nhds_basis_opens a)).trans <| by
    simp only [and_imp, exists_prop, true_and_iff, mem_Ici, ge_iff_le]
#align tendsto_at_top_nhds tendsto_atTop_nhds

theorem tendsto_const_nhds {a : α} {f : Filter β} : Tendsto (fun _ : β => a) f (𝓝 a) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha
#align tendsto_const_nhds tendsto_const_nhds

theorem tendsto_atTop_of_eventually_const {ι : Type*} [SemilatticeSup ι] [Nonempty ι] {x : α}
    {u : ι → α} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atTop.mpr ⟨i₀, h⟩)) tendsto_const_nhds
#align tendsto_at_top_of_eventually_const tendsto_atTop_of_eventually_const

theorem tendsto_atBot_of_eventually_const {ι : Type*} [SemilatticeInf ι] [Nonempty ι] {x : α}
    {u : ι → α} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm (eventually_atBot.mpr ⟨i₀, h⟩)) tendsto_const_nhds
#align tendsto_at_bot_of_eventually_const tendsto_atBot_of_eventually_const

theorem pure_le_nhds : pure ≤ (𝓝 : α → Filter α) := fun _ _ hs => mem_pure.2 <| mem_of_mem_nhds hs
#align pure_le_nhds pure_le_nhds

theorem tendsto_pure_nhds {α : Type*} [TopologicalSpace β] (f : α → β) (a : α) :
    Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)
#align tendsto_pure_nhds tendsto_pure_nhds

theorem OrderTop.tendsto_atTop_nhds {α : Type*} [PartialOrder α] [OrderTop α] [TopologicalSpace β]
    (f : α → β) : Tendsto f atTop (𝓝 (f ⊤)) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)
#align order_top.tendsto_at_top_nhds OrderTop.tendsto_atTop_nhds

@[simp]
instance nhds_neBot {a : α} : NeBot (𝓝 a) :=
  neBot_of_le (pure_le_nhds a)
#align nhds_ne_bot nhds_neBot

theorem tendsto_nhds_of_eventually_eq {f : β → α} {a : α} (h : ∀ᶠ x in l, f x = a) :
    Tendsto f l (𝓝 a) :=
  tendsto_const_nhds.congr' (.symm h)

/-!
### Cluster points

In this section we define [cluster points](https://en.wikipedia.org/wiki/Limit_point)
(also known as limit points and accumulation points) of a filter and of a sequence.
-/


/-- A point `x` is a cluster point of a filter `F` if `𝓝 x ⊓ F ≠ ⊥`. Also known as
an accumulation point or a limit point, but beware that terminology varies. This
is *not* the same as asking `𝓝[≠] x ⊓ F ≠ ⊥`. See `mem_closure_iff_clusterPt` in particular. -/
def ClusterPt (x : α) (F : Filter α) : Prop :=
  NeBot (𝓝 x ⊓ F)
#align cluster_pt ClusterPt

theorem ClusterPt.neBot {x : α} {F : Filter α} (h : ClusterPt x F) : NeBot (𝓝 x ⊓ F) :=
  h
#align cluster_pt.ne_bot ClusterPt.neBot

theorem Filter.HasBasis.clusterPt_iff {ιa ιF} {pa : ιa → Prop} {sa : ιa → Set α} {pF : ιF → Prop}
    {sF : ιF → Set α} {F : Filter α} (ha : (𝓝 a).HasBasis pa sa) (hF : F.HasBasis pF sF) :
    ClusterPt a F ↔ ∀ ⦃i⦄, pa i → ∀ ⦃j⦄, pF j → (sa i ∩ sF j).Nonempty :=
  ha.inf_basis_neBot_iff hF
#align filter.has_basis.cluster_pt_iff Filter.HasBasis.clusterPt_iff

theorem clusterPt_iff {x : α} {F : Filter α} :
    ClusterPt x F ↔ ∀ ⦃U : Set α⦄, U ∈ 𝓝 x → ∀ ⦃V⦄, V ∈ F → (U ∩ V).Nonempty :=
  inf_neBot_iff
#align cluster_pt_iff clusterPt_iff

theorem clusterPt_iff_not_disjoint {x : α} {F : Filter α} :
    ClusterPt x F ↔ ¬Disjoint (𝓝 x) F := by
  rw [disjoint_iff, ClusterPt, neBot_iff]

/-- `x` is a cluster point of a set `s` if every neighbourhood of `x` meets `s` on a nonempty
set. See also `mem_closure_iff_clusterPt`. -/
theorem clusterPt_principal_iff {x : α} {s : Set α} :
    ClusterPt x (𝓟 s) ↔ ∀ U ∈ 𝓝 x, (U ∩ s).Nonempty :=
  inf_principal_neBot_iff
#align cluster_pt_principal_iff clusterPt_principal_iff

theorem clusterPt_principal_iff_frequently {x : α} {s : Set α} :
    ClusterPt x (𝓟 s) ↔ ∃ᶠ y in 𝓝 x, y ∈ s := by
  simp only [clusterPt_principal_iff, frequently_iff, Set.Nonempty, exists_prop, mem_inter_iff]
#align cluster_pt_principal_iff_frequently clusterPt_principal_iff_frequently

theorem ClusterPt.of_le_nhds {x : α} {f : Filter α} (H : f ≤ 𝓝 x) [NeBot f] : ClusterPt x f := by
  rwa [ClusterPt, inf_eq_right.mpr H]
#align cluster_pt.of_le_nhds ClusterPt.of_le_nhds

theorem ClusterPt.of_le_nhds' {x : α} {f : Filter α} (H : f ≤ 𝓝 x) (_hf : NeBot f) :
    ClusterPt x f :=
  ClusterPt.of_le_nhds H
#align cluster_pt.of_le_nhds' ClusterPt.of_le_nhds'

theorem ClusterPt.of_nhds_le {x : α} {f : Filter α} (H : 𝓝 x ≤ f) : ClusterPt x f := by
  simp only [ClusterPt, inf_eq_left.mpr H, nhds_neBot]
#align cluster_pt.of_nhds_le ClusterPt.of_nhds_le

theorem ClusterPt.mono {x : α} {f g : Filter α} (H : ClusterPt x f) (h : f ≤ g) : ClusterPt x g :=
  NeBot.mono H <| inf_le_inf_left _ h
#align cluster_pt.mono ClusterPt.mono

theorem ClusterPt.of_inf_left {x : α} {f g : Filter α} (H : ClusterPt x <| f ⊓ g) : ClusterPt x f :=
  H.mono inf_le_left
#align cluster_pt.of_inf_left ClusterPt.of_inf_left

theorem ClusterPt.of_inf_right {x : α} {f g : Filter α} (H : ClusterPt x <| f ⊓ g) :
    ClusterPt x g :=
  H.mono inf_le_right
#align cluster_pt.of_inf_right ClusterPt.of_inf_right

theorem Ultrafilter.clusterPt_iff {x : α} {f : Ultrafilter α} : ClusterPt x f ↔ ↑f ≤ 𝓝 x :=
  ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩
#align ultrafilter.cluster_pt_iff Ultrafilter.clusterPt_iff

/-- A point `x` is a cluster point of a sequence `u` along a filter `F` if it is a cluster point
of `map u F`. -/
def MapClusterPt {ι : Type*} (x : α) (F : Filter ι) (u : ι → α) : Prop :=
  ClusterPt x (map u F)
#align map_cluster_pt MapClusterPt

theorem mapClusterPt_iff {ι : Type*} (x : α) (F : Filter ι) (u : ι → α) :
    MapClusterPt x F u ↔ ∀ s ∈ 𝓝 x, ∃ᶠ a in F, u a ∈ s := by
  simp_rw [MapClusterPt, ClusterPt, inf_neBot_iff_frequently_left, frequently_map]
  rfl
#align map_cluster_pt_iff mapClusterPt_iff

theorem mapClusterPt_of_comp {ι δ : Type*} {F : Filter ι} {φ : δ → ι} {p : Filter δ} {x : α}
    {u : ι → α} [NeBot p] (h : Tendsto φ p F) (H : Tendsto (u ∘ φ) p (𝓝 x)) :
    MapClusterPt x F u := by
  have :=
    calc
      map (u ∘ φ) p = map u (map φ p) := map_map
      _ ≤ map u F := map_mono h
  have : map (u ∘ φ) p ≤ 𝓝 x ⊓ map u F := le_inf H this
  exact neBot_of_le this
#align map_cluster_pt_of_comp mapClusterPt_of_comp

/-- A point `x` is an accumulation point of a filter `F` if `𝓝[≠] x ⊓ F ≠ ⊥`.-/
def AccPt (x : α) (F : Filter α) : Prop :=
  NeBot (𝓝[≠] x ⊓ F)
#align acc_pt AccPt

theorem acc_iff_cluster (x : α) (F : Filter α) : AccPt x F ↔ ClusterPt x (𝓟 {x}ᶜ ⊓ F) := by
  rw [AccPt, nhdsWithin, ClusterPt, inf_assoc]
#align acc_iff_cluster acc_iff_cluster

/-- `x` is an accumulation point of a set `C` iff it is a cluster point of `C ∖ {x}`.-/
theorem acc_principal_iff_cluster (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ {x})) :=
  by rw [acc_iff_cluster, inf_principal, inter_comm]; rfl
#align acc_principal_iff_cluster acc_principal_iff_cluster

/-- `x` is an accumulation point of a set `C` iff every neighborhood
of `x` contains a point of `C` other than `x`. -/
theorem accPt_iff_nhds (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff, Set.Nonempty, exists_prop, and_assoc,
    @and_comm (¬_ = x)]
#align acc_pt_iff_nhds accPt_iff_nhds

/-- `x` is an accumulation point of a set `C` iff
there are points near `x` in `C` and different from `x`.-/
theorem accPt_iff_frequently (x : α) (C : Set α) : AccPt x (𝓟 C) ↔ ∃ᶠ y in 𝓝 x, y ≠ x ∧ y ∈ C := by
  simp [acc_principal_iff_cluster, clusterPt_principal_iff_frequently, and_comm]
#align acc_pt_iff_frequently accPt_iff_frequently

/-- If `x` is an accumulation point of `F` and `F ≤ G`, then
`x` is an accumulation point of `D`. -/
theorem AccPt.mono {x : α} {F G : Filter α} (h : AccPt x F) (hFG : F ≤ G) : AccPt x G :=
  NeBot.mono h (inf_le_inf_left _ hFG)
#align acc_pt.mono AccPt.mono

/-!
### Interior, closure and frontier in terms of neighborhoods
-/

theorem interior_eq_nhds' {s : Set α} : interior s = { a | s ∈ 𝓝 a } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_setOf_eq]
#align interior_eq_nhds' interior_eq_nhds'

theorem interior_eq_nhds {s : Set α} : interior s = { a | 𝓝 a ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by simp only [le_principal_iff]
#align interior_eq_nhds interior_eq_nhds

@[simp]
theorem interior_mem_nhds {s : Set α} {a : α} : interior s ∈ 𝓝 a ↔ s ∈ 𝓝 a :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩
#align interior_mem_nhds interior_mem_nhds

theorem interior_setOf_eq {p : α → Prop} : interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'
#align interior_set_of_eq interior_setOf_eq

theorem isOpen_setOf_eventually_nhds {p : α → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOf_eq, isOpen_interior]
#align is_open_set_of_eventually_nhds isOpen_setOf_eventually_nhds

theorem subset_interior_iff_nhds {s V : Set α} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x := by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]
#align subset_interior_iff_nhds subset_interior_iff_nhds

theorem isOpen_iff_nhds {s : Set α} : IsOpen s ↔ ∀ a ∈ s, 𝓝 a ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ interior s := subset_interior_iff_isOpen.symm
    _ ↔ ∀ a ∈ s, 𝓝 a ≤ 𝓟 s := by rw [interior_eq_nhds]; rfl
#align is_open_iff_nhds isOpen_iff_nhds

theorem isOpen_iff_mem_nhds {s : Set α} : IsOpen s ↔ ∀ a ∈ s, s ∈ 𝓝 a :=
  isOpen_iff_nhds.trans <| forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff
#align is_open_iff_mem_nhds isOpen_iff_mem_nhds

/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
theorem isOpen_iff_eventually {s : Set α} : IsOpen s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
  isOpen_iff_mem_nhds
#align is_open_iff_eventually isOpen_iff_eventually

theorem isOpen_iff_ultrafilter {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∀ (l : Ultrafilter α), ↑l ≤ 𝓝 x → s ∈ l := by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]
#align is_open_iff_ultrafilter isOpen_iff_ultrafilter

theorem isOpen_singleton_iff_nhds_eq_pure (a : α) : IsOpen ({a} : Set α) ↔ 𝓝 a = pure a := by
  constructor
  · intro h
    apply le_antisymm _ (pure_le_nhds a)
    rw [le_pure_iff]
    exact h.mem_nhds (mem_singleton a)
  · intro h
    simp [isOpen_iff_nhds, h]
#align is_open_singleton_iff_nhds_eq_pure isOpen_singleton_iff_nhds_eq_pure

theorem isOpen_singleton_iff_punctured_nhds {α : Type*} [TopologicalSpace α] (a : α) :
    IsOpen ({a} : Set α) ↔ 𝓝[≠] a = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure, nhdsWithin, ← mem_iff_inf_principal_compl, ← le_pure_iff,
    nhds_neBot.le_pure_iff]
#align is_open_singleton_iff_punctured_nhds isOpen_singleton_iff_punctured_nhds

theorem mem_closure_iff_frequently {s : Set α} {a : α} : a ∈ closure s ↔ ∃ᶠ x in 𝓝 a, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds,
      closure_eq_compl_interior_compl]; rfl
#align mem_closure_iff_frequently mem_closure_iff_frequently

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently
#align filter.frequently.mem_closure Filter.Frequently.mem_closure

/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
theorem isClosed_iff_frequently {s : Set α} : IsClosed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s := by
  rw [← closure_subset_iff_isClosed]
  refine' forall_congr' fun x => _
  rw [mem_closure_iff_frequently]
#align is_closed_iff_frequently isClosed_iff_frequently

/-- The set of cluster points of a filter is closed. In particular, the set of limit points
of a sequence is closed. -/
theorem isClosed_setOf_clusterPt {f : Filter α} : IsClosed { x | ClusterPt x f } := by
  simp only [ClusterPt, inf_neBot_iff_frequently_left, setOf_forall, imp_iff_not_or]
  refine' isClosed_iInter fun p => IsClosed.union _ _ <;> apply isClosed_compl_iff.2
  exacts [isOpen_setOf_eventually_nhds, isOpen_const]
#align is_closed_set_of_cluster_pt isClosed_setOf_clusterPt

theorem mem_closure_iff_clusterPt {s : Set α} {a : α} : a ∈ closure s ↔ ClusterPt a (𝓟 s) :=
  mem_closure_iff_frequently.trans clusterPt_principal_iff_frequently.symm
#align mem_closure_iff_cluster_pt mem_closure_iff_clusterPt

theorem mem_closure_iff_nhds_neBot {s : Set α} : a ∈ closure s ↔ 𝓝 a ⊓ 𝓟 s ≠ ⊥ :=
  mem_closure_iff_clusterPt.trans neBot_iff
#align mem_closure_iff_nhds_ne_bot mem_closure_iff_nhds_neBot

theorem mem_closure_iff_nhdsWithin_neBot {s : Set α} {x : α} : x ∈ closure s ↔ NeBot (𝓝[s] x) :=
  mem_closure_iff_clusterPt
#align mem_closure_iff_nhds_within_ne_bot mem_closure_iff_nhdsWithin_neBot

/-- If `x` is not an isolated point of a topological space, then `{x}ᶜ` is dense in the whole
space. -/
theorem dense_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : Dense ({x}ᶜ : Set α) := by
  intro y
  rcases eq_or_ne y x with (rfl | hne)
  · rwa [mem_closure_iff_nhdsWithin_neBot]
  · exact subset_closure hne
#align dense_compl_singleton dense_compl_singleton

/-- If `x` is not an isolated point of a topological space, then the closure of `{x}ᶜ` is the whole
space. -/
-- porting note: was a `@[simp]` lemma but `simp` can prove it
theorem closure_compl_singleton (x : α) [NeBot (𝓝[≠] x)] : closure {x}ᶜ = (univ : Set α) :=
  (dense_compl_singleton x).closure_eq
#align closure_compl_singleton closure_compl_singleton

/-- If `x` is not an isolated point of a topological space, then the interior of `{x}` is empty. -/
@[simp]
theorem interior_singleton (x : α) [NeBot (𝓝[≠] x)] : interior {x} = (∅ : Set α) :=
  interior_eq_empty_iff_dense_compl.2 (dense_compl_singleton x)
#align interior_singleton interior_singleton

theorem not_isOpen_singleton (x : α) [NeBot (𝓝[≠] x)] : ¬IsOpen ({x} : Set α) :=
  dense_compl_singleton_iff_not_open.1 (dense_compl_singleton x)
#align not_is_open_singleton not_isOpen_singleton

theorem closure_eq_cluster_pts {s : Set α} : closure s = { a | ClusterPt a (𝓟 s) } :=
  Set.ext fun _ => mem_closure_iff_clusterPt
#align closure_eq_cluster_pts closure_eq_cluster_pts

theorem mem_closure_iff_nhds {s : Set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ 𝓝 a, (t ∩ s).Nonempty :=
  mem_closure_iff_clusterPt.trans clusterPt_principal_iff
#align mem_closure_iff_nhds mem_closure_iff_nhds

theorem mem_closure_iff_nhds' {s : Set α} {a : α} : a ∈ closure s ↔ ∀ t ∈ 𝓝 a, ∃ y : s, ↑y ∈ t := by
  simp only [mem_closure_iff_nhds, Set.inter_nonempty_iff_exists_right, SetCoe.exists, exists_prop]
#align mem_closure_iff_nhds' mem_closure_iff_nhds'

theorem mem_closure_iff_comap_neBot {A : Set α} {x : α} :
    x ∈ closure A ↔ NeBot (comap ((↑) : A → α) (𝓝 x)) := by
  simp_rw [mem_closure_iff_nhds, comap_neBot_iff, Set.inter_nonempty_iff_exists_right,
    SetCoe.exists, exists_prop]
#align mem_closure_iff_comap_ne_bot mem_closure_iff_comap_neBot

theorem mem_closure_iff_nhds_basis' {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s)
    {t : Set α} : a ∈ closure t ↔ ∀ i, p i → (s i ∩ t).Nonempty :=
  mem_closure_iff_clusterPt.trans <|
    (h.clusterPt_iff (hasBasis_principal _)).trans <| by simp only [exists_prop, forall_const]
#align mem_closure_iff_nhds_basis' mem_closure_iff_nhds_basis'

theorem mem_closure_iff_nhds_basis {a : α} {p : ι → Prop} {s : ι → Set α} (h : (𝓝 a).HasBasis p s)
    {t : Set α} : a ∈ closure t ↔ ∀ i, p i → ∃ y ∈ t, y ∈ s i :=
  (mem_closure_iff_nhds_basis' h).trans <| by
    simp only [Set.Nonempty, mem_inter_iff, exists_prop, and_comm]
#align mem_closure_iff_nhds_basis mem_closure_iff_nhds_basis

theorem clusterPt_iff_forall_mem_closure {F : Filter α} {a : α} :
    ClusterPt a F ↔ ∀ s ∈ F, a ∈ closure s := by
  simp_rw [ClusterPt, inf_neBot_iff, mem_closure_iff_nhds]
  rw [forall₂_swap]

theorem clusterPt_iff_lift'_closure {F : Filter α} {a : α} :
    ClusterPt a F ↔ pure a ≤ (F.lift' closure) := by
  simp_rw [clusterPt_iff_forall_mem_closure,
    (hasBasis_pure _).le_basis_iff F.basis_sets.lift'_closure, id, singleton_subset_iff, true_and,
    exists_const]

theorem clusterPt_iff_lift'_closure' {F : Filter α} {a : α} :
    ClusterPt a F ↔ (F.lift' closure ⊓ pure a).NeBot := by
  rw [clusterPt_iff_lift'_closure, ← Ultrafilter.coe_pure, inf_comm, Ultrafilter.inf_neBot_iff]

@[simp]
theorem clusterPt_lift'_closure_iff {F : Filter α} {a : α} :
    ClusterPt a (F.lift' closure) ↔ ClusterPt a F := by
  simp [clusterPt_iff_lift'_closure, lift'_lift'_assoc (monotone_closure α) (monotone_closure α)]

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
theorem mem_closure_iff_ultrafilter {s : Set α} {x : α} :
    x ∈ closure s ↔ ∃ u : Ultrafilter α, s ∈ u ∧ ↑u ≤ 𝓝 x := by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]
#align mem_closure_iff_ultrafilter mem_closure_iff_ultrafilter

theorem isClosed_iff_clusterPt {s : Set α} : IsClosed s ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s :=
  calc
    IsClosed s ↔ closure s ⊆ s := closure_subset_iff_isClosed.symm
    _ ↔ ∀ a, ClusterPt a (𝓟 s) → a ∈ s := by simp only [subset_def, mem_closure_iff_clusterPt]
#align is_closed_iff_cluster_pt isClosed_iff_clusterPt

theorem isClosed_iff_nhds {s : Set α} : IsClosed s ↔ ∀ x, (∀ U ∈ 𝓝 x, (U ∩ s).Nonempty) → x ∈ s :=
  by simp_rw [isClosed_iff_clusterPt, ClusterPt, inf_principal_neBot_iff]
#align is_closed_iff_nhds isClosed_iff_nhds

theorem IsClosed.interior_union_left {s t : Set α} (_ : IsClosed s) :
    interior (s ∪ t) ⊆ s ∪ interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a ∈ s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u ∩ sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩
#align is_closed.interior_union_left IsClosed.interior_union_left

theorem IsClosed.interior_union_right {s t : Set α} (h : IsClosed t) :
    interior (s ∪ t) ⊆ interior s ∪ t := by
  simpa only [union_comm _ t] using h.interior_union_left
#align is_closed.interior_union_right IsClosed.interior_union_right

theorem IsOpen.inter_closure {s t : Set α} (h : IsOpen s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  compl_subset_compl.mp <| by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl
#align is_open.inter_closure IsOpen.inter_closure

theorem IsOpen.closure_inter {s t : Set α} (h : IsOpen t) : closure s ∩ t ⊆ closure (s ∩ t) := by
  simpa only [inter_comm t] using h.inter_closure
#align is_open.closure_inter IsOpen.closure_inter

theorem Dense.open_subset_closure_inter {s t : Set α} (hs : Dense s) (ht : IsOpen t) :
    t ⊆ closure (t ∩ s) :=
  calc
    t = t ∩ closure s := by rw [hs.closure_eq, inter_univ]
    _ ⊆ closure (t ∩ s) := ht.inter_closure
#align dense.open_subset_closure_inter Dense.open_subset_closure_inter

theorem mem_closure_of_mem_closure_union {s₁ s₂ : Set α} {x : α} (h : x ∈ closure (s₁ ∪ s₂))
    (h₁ : s₁ᶜ ∈ 𝓝 x) : x ∈ closure s₂ := by
  rw [mem_closure_iff_nhds_neBot] at *
  rwa [←
    calc
      𝓝 x ⊓ principal (s₁ ∪ s₂) = 𝓝 x ⊓ (principal s₁ ⊔ principal s₂) := by rw [sup_principal]
      _ = 𝓝 x ⊓ principal s₁ ⊔ 𝓝 x ⊓ principal s₂ := inf_sup_left
      _ = ⊥ ⊔ 𝓝 x ⊓ principal s₂ := by rw [inf_principal_eq_bot.mpr h₁]
      _ = 𝓝 x ⊓ principal s₂ := bot_sup_eq
      ]
#align mem_closure_of_mem_closure_union mem_closure_of_mem_closure_union

/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem Dense.inter_of_open_left {s t : Set α} (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s ∩ t) := fun x =>
  closure_minimal hso.inter_closure isClosed_closure <| by simp [hs.closure_eq, ht.closure_eq]
#align dense.inter_of_open_left Dense.inter_of_open_left

/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem Dense.inter_of_open_right {s t : Set α} (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_open_left hs hto
#align dense.inter_of_open_right Dense.inter_of_open_right

theorem Dense.inter_nhds_nonempty {s t : Set α} (hs : Dense s) {x : α} (ht : t ∈ 𝓝 x) :
    (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩
#align dense.inter_nhds_nonempty Dense.inter_nhds_nonempty

theorem closure_diff {s t : Set α} : closure s \ closure t ⊆ closure (s \ t) :=
  calc
    closure s \ closure t = (closure t)ᶜ ∩ closure s := by simp only [diff_eq, inter_comm]
    _ ⊆ closure ((closure t)ᶜ ∩ s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [diff_eq, inter_comm]
    _ ⊆ closure (s \ t) := closure_mono <| diff_subset_diff (Subset.refl s) subset_closure
#align closure_diff closure_diff

theorem Filter.Frequently.mem_of_closed {a : α} {s : Set α} (h : ∃ᶠ x in 𝓝 a, x ∈ s)
    (hs : IsClosed s) : a ∈ s :=
  hs.closure_subset h.mem_closure
#align filter.frequently.mem_of_closed Filter.Frequently.mem_of_closed

theorem IsClosed.mem_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α}
    (hs : IsClosed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 a)) : a ∈ s :=
  (hf.frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs
#align is_closed.mem_of_frequently_of_tendsto IsClosed.mem_of_frequently_of_tendsto

theorem IsClosed.mem_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ s :=
  hs.mem_of_frequently_of_tendsto h.frequently hf
#align is_closed.mem_of_tendsto IsClosed.mem_of_tendsto

theorem mem_closure_of_frequently_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α}
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 a)) : a ∈ closure s :=
  (hf.frequently h).mem_closure
#align mem_closure_of_frequently_of_tendsto mem_closure_of_frequently_of_tendsto

theorem mem_closure_of_tendsto {f : β → α} {b : Filter β} {a : α} {s : Set α} [NeBot b]
    (hf : Tendsto f b (𝓝 a)) (h : ∀ᶠ x in b, f x ∈ s) : a ∈ closure s :=
  mem_closure_of_frequently_of_tendsto h.frequently hf
#align mem_closure_of_tendsto mem_closure_of_tendsto

/-- Suppose that `f` sends the complement to `s` to a single point `a`, and `l` is some filter.
Then `f` tends to `a` along `l` restricted to `s` if and only if it tends to `a` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : β → α} {l : Filter β} {s : Set β} {a : α}
    (h : ∀ (x) (_ : x ∉ s), f x = a) : Tendsto f (l ⊓ 𝓟 s) (𝓝 a) ↔ Tendsto f l (𝓝 a) := by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 a)
  · rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine' ⟨fun h' => _, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff]
    at this
  exact this.1
#align tendsto_inf_principal_nhds_iff_of_forall_eq tendsto_inf_principal_nhds_iff_of_forall_eq

/-!
### Limits of filters in topological spaces

In this section we define functions that return a limit of a filter (or of a function along a
filter), if it exists, and a random point otherwise. These functions are rarely used in Mathlib,
most of the theorems are written using `Filter.Tendsto`. One of the reasons is that
`Filter.limUnder f g = a` is not equivalent to `Filter.Tendsto g f (𝓝 a)` unless the codomain is a
Hausdorff space and `g` has a limit along `f`.
-/

section lim

-- "Lim"
set_option linter.uppercaseLean3 false

/-- If `f` is a filter, then `Filter.lim f` is a limit of the filter, if it exists. -/
noncomputable def lim [Nonempty α] (f : Filter α) : α :=
  Classical.epsilon fun a => f ≤ 𝓝 a
#align Lim lim

/--
If `F` is an ultrafilter, then `Filter.Ultrafilter.lim F` is a limit of the filter, if it exists.
Note that dot notation `F.lim` can be used for `F : Filter.Ultrafilter α`.
-/
noncomputable nonrec def Ultrafilter.lim (F : Ultrafilter α) : α :=
  @lim α _ (nonempty_of_neBot F) F
#align ultrafilter.Lim Ultrafilter.lim

/-- If `f` is a filter in `β` and `g : β → α` is a function, then `limUnder f g` is a limit of `g`
at `f`, if it exists. -/
noncomputable def limUnder [Nonempty α] (f : Filter β) (g : β → α) : α :=
  lim (f.map g)
#align lim limUnder

/-- If a filter `f` is majorated by some `𝓝 a`, then it is majorated by `𝓝 (Filter.lim f)`. We
formulate this lemma with a `[Nonempty α]` argument of `lim` derived from `h` to make it useful for
types without a `[Nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify
this instance with any other instance. -/
theorem le_nhds_lim {f : Filter α} (h : ∃ a, f ≤ 𝓝 a) : f ≤ 𝓝 (@lim _ _ (nonempty_of_exists h) f) :=
  Classical.epsilon_spec h
#align le_nhds_Lim le_nhds_lim

/-- If `g` tends to some `𝓝 a` along `f`, then it tends to `𝓝 (Filter.limUnder f g)`. We formulate
this lemma with a `[Nonempty α]` argument of `lim` derived from `h` to make it useful for types
without a `[Nonempty α]` instance. Because of the built-in proof irrelevance, Lean will unify this
instance with any other instance. -/
theorem tendsto_nhds_limUnder {f : Filter β} {g : β → α} (h : ∃ a, Tendsto g f (𝓝 a)) :
    Tendsto g f (𝓝 (@limUnder _ _ _ (nonempty_of_exists h) f g)) :=
  le_nhds_lim h
#align tendsto_nhds_lim tendsto_nhds_limUnder

end lim

end TopologicalSpace

open Topology

/-!
### Continuity
-/

section Continuous

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open TopologicalSpace

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
structure Continuous (f : α → β) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
#align continuous Continuous

set_option quotPrecheck false in
/-- Notation for `Continuous` with respect to a non-standard topologies. -/
scoped[Topology] notation (name := Continuous_of) "Continuous[" t₁ ", " t₂ "]" =>
  @Continuous _ _ t₁ t₂

theorem continuous_def {_ : TopologicalSpace α} {_ : TopologicalSpace β} {f : α → β} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  ⟨fun hf => hf.1, fun h => ⟨h⟩⟩
#align continuous_def continuous_def

theorem IsOpen.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsOpen s) :
    IsOpen (f ⁻¹' s) :=
  hf.isOpen_preimage s h
#align is_open.preimage IsOpen.preimage

theorem Continuous.congr {f g : α → β} (h : Continuous f) (h' : ∀ x, f x = g x) : Continuous g := by
  convert h
  ext
  rw [h']
#align continuous.congr Continuous.congr

/-- A function between topological spaces is continuous at a point `x₀`
if `f x` tends to `f x₀` when `x` tends to `x₀`. -/
def ContinuousAt (f : α → β) (x : α) :=
  Tendsto f (𝓝 x) (𝓝 (f x))
#align continuous_at ContinuousAt

theorem ContinuousAt.tendsto {f : α → β} {x : α} (h : ContinuousAt f x) :
    Tendsto f (𝓝 x) (𝓝 (f x)) :=
  h
#align continuous_at.tendsto ContinuousAt.tendsto

theorem continuousAt_def {f : α → β} {x : α} : ContinuousAt f x ↔ ∀ A ∈ 𝓝 (f x), f ⁻¹' A ∈ 𝓝 x :=
  Iff.rfl
#align continuous_at_def continuousAt_def

theorem continuousAt_congr {f g : α → β} {x : α} (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt f x ↔ ContinuousAt g x := by
  simp only [ContinuousAt, tendsto_congr' h, h.eq_of_nhds]
#align continuous_at_congr continuousAt_congr

theorem ContinuousAt.congr {f g : α → β} {x : α} (hf : ContinuousAt f x) (h : f =ᶠ[𝓝 x] g) :
    ContinuousAt g x :=
  (continuousAt_congr h).1 hf
#align continuous_at.congr ContinuousAt.congr

theorem ContinuousAt.preimage_mem_nhds {f : α → β} {x : α} {t : Set β} (h : ContinuousAt f x)
    (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝 x :=
  h ht
#align continuous_at.preimage_mem_nhds ContinuousAt.preimage_mem_nhds

theorem eventuallyEq_zero_nhds {M₀} [Zero M₀] {a : α} {f : α → M₀} :
    f =ᶠ[𝓝 a] 0 ↔ a ∉ closure (Function.support f) := by
  rw [← mem_compl_iff, ← interior_compl, mem_interior_iff_mem_nhds, Function.compl_support]; rfl
#align eventually_eq_zero_nhds eventuallyEq_zero_nhds

theorem ClusterPt.map {x : α} {la : Filter α} {lb : Filter β} (H : ClusterPt x la) {f : α → β}
    (hfc : ContinuousAt f x) (hf : Tendsto f la lb) : ClusterPt (f x) lb :=
  (NeBot.map H f).mono <| hfc.tendsto.inf hf
#align cluster_pt.map ClusterPt.map

/-- See also `interior_preimage_subset_preimage_interior`. -/
theorem preimage_interior_subset_interior_preimage {f : α → β} {s : Set β} (hf : Continuous f) :
    f ⁻¹' interior s ⊆ interior (f ⁻¹' s) :=
  interior_maximal (preimage_mono interior_subset) (isOpen_interior.preimage hf)
#align preimage_interior_subset_interior_preimage preimage_interior_subset_interior_preimage

@[continuity]
theorem continuous_id : Continuous (id : α → α) :=
  continuous_def.2 fun _ => id
#align continuous_id continuous_id

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity]
theorem continuous_id' : Continuous (fun (x : α) => x) := continuous_id

theorem Continuous.comp {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) :=
  continuous_def.2 fun _ h => (h.preimage hg).preimage hf
#align continuous.comp Continuous.comp

-- This is needed due to reducibility issues with the `continuity` tactic.
@[continuity]
theorem Continuous.comp' {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (fun x => g (f x)) := hg.comp hf

theorem Continuous.iterate {f : α → α} (h : Continuous f) (n : ℕ) : Continuous f^[n] :=
  Nat.recOn n continuous_id fun _ ihn => ihn.comp h
#align continuous.iterate Continuous.iterate

nonrec theorem ContinuousAt.comp {g : β → γ} {f : α → β} {x : α} (hg : ContinuousAt g (f x))
    (hf : ContinuousAt f x) : ContinuousAt (g ∘ f) x :=
  hg.comp hf
#align continuous_at.comp ContinuousAt.comp

/-- See note [comp_of_eq lemmas] -/
theorem ContinuousAt.comp_of_eq {g : β → γ} {f : α → β} {x : α} {y : β} (hg : ContinuousAt g y)
    (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x := by subst hy; exact hg.comp hf
#align continuous_at.comp_of_eq ContinuousAt.comp_of_eq

theorem Continuous.tendsto {f : α → β} (hf : Continuous f) (x) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  ((nhds_basis_opens x).tendsto_iff <| nhds_basis_opens <| f x).2 fun t ⟨hxt, ht⟩ =>
    ⟨f ⁻¹' t, ⟨hxt, ht.preimage hf⟩, Subset.rfl⟩
#align continuous.tendsto Continuous.tendsto

/-- A version of `Continuous.tendsto` that allows one to specify a simpler form of the limit.
E.g., one can write `continuous_exp.tendsto' 0 1 exp_zero`. -/
theorem Continuous.tendsto' {f : α → β} (hf : Continuous f) (x : α) (y : β) (h : f x = y) :
    Tendsto f (𝓝 x) (𝓝 y) :=
  h ▸ hf.tendsto x
#align continuous.tendsto' Continuous.tendsto'

theorem Continuous.continuousAt {f : α → β} {x : α} (h : Continuous f) : ContinuousAt f x :=
  h.tendsto x
#align continuous.continuous_at Continuous.continuousAt

theorem continuous_iff_continuousAt {f : α → β} : Continuous f ↔ ∀ x, ContinuousAt f x :=
  ⟨Continuous.tendsto, fun hf => continuous_def.2 fun _U hU => isOpen_iff_mem_nhds.2 fun x hx =>
    hf x <| hU.mem_nhds hx⟩
#align continuous_iff_continuous_at continuous_iff_continuousAt

theorem continuousAt_const {x : α} {b : β} : ContinuousAt (fun _ : α => b) x :=
  tendsto_const_nhds
#align continuous_at_const continuousAt_const

@[continuity]
theorem continuous_const {b : β} : Continuous fun _ : α => b :=
  continuous_iff_continuousAt.mpr fun _ => continuousAt_const
#align continuous_const continuous_const

theorem Filter.EventuallyEq.continuousAt {x : α} {f : α → β} {y : β} (h : f =ᶠ[𝓝 x] fun _ => y) :
    ContinuousAt f x :=
  (continuousAt_congr h).2 tendsto_const_nhds
#align filter.eventually_eq.continuous_at Filter.EventuallyEq.continuousAt

theorem continuous_of_const {f : α → β} (h : ∀ x y, f x = f y) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    Filter.EventuallyEq.continuousAt <| eventually_of_forall fun y => h y x
#align continuous_of_const continuous_of_const

theorem continuousAt_id {x : α} : ContinuousAt id x :=
  continuous_id.continuousAt
#align continuous_at_id continuousAt_id

theorem ContinuousAt.iterate {f : α → α} {x : α} (hf : ContinuousAt f x) (hx : f x = x) (n : ℕ) :
    ContinuousAt f^[n] x :=
  Nat.recOn n continuousAt_id fun n ihn =>
    show ContinuousAt (f^[n] ∘ f) x from ContinuousAt.comp (hx.symm ▸ ihn) hf
#align continuous_at.iterate ContinuousAt.iterate

theorem continuous_iff_isClosed {f : α → β} : Continuous f ↔ ∀ s, IsClosed s → IsClosed (f ⁻¹' s) :=
  continuous_def.trans <| compl_surjective.forall.trans <| by
    simp only [isOpen_compl_iff, preimage_compl]
#align continuous_iff_is_closed continuous_iff_isClosed

theorem IsClosed.preimage {f : α → β} (hf : Continuous f) {s : Set β} (h : IsClosed s) :
    IsClosed (f ⁻¹' s) :=
  continuous_iff_isClosed.mp hf s h
#align is_closed.preimage IsClosed.preimage

theorem mem_closure_image {f : α → β} {x : α} {s : Set α} (hf : ContinuousAt f x)
    (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  mem_closure_of_frequently_of_tendsto
    ((mem_closure_iff_frequently.1 hx).mono fun _ => mem_image_of_mem _) hf
#align mem_closure_image mem_closure_image

theorem continuousAt_iff_ultrafilter {f : α → β} {x} :
    ContinuousAt f x ↔ ∀ g : Ultrafilter α, ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))
#align continuous_at_iff_ultrafilter continuousAt_iff_ultrafilter

theorem continuous_iff_ultrafilter {f : α → β} :
    Continuous f ↔ ∀ (x) (g : Ultrafilter α), ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]
#align continuous_iff_ultrafilter continuous_iff_ultrafilter

theorem Continuous.closure_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    closure (f ⁻¹' t) ⊆ f ⁻¹' closure t := by
  rw [← (isClosed_closure.preimage hf).closure_eq]
  exact closure_mono (preimage_mono subset_closure)
#align continuous.closure_preimage_subset Continuous.closure_preimage_subset

theorem Continuous.frontier_preimage_subset {f : α → β} (hf : Continuous f) (t : Set β) :
    frontier (f ⁻¹' t) ⊆ f ⁻¹' frontier t :=
  diff_subset_diff (hf.closure_preimage_subset t) (preimage_interior_subset_interior_preimage hf)
#align continuous.frontier_preimage_subset Continuous.frontier_preimage_subset

/-- If a continuous map `f` maps `s` to `t`, then it maps `closure s` to `closure t`. -/
protected theorem Set.MapsTo.closure {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t)
    (hc : Continuous f) : MapsTo f (closure s) (closure t) := by
  simp only [MapsTo, mem_closure_iff_clusterPt]
  exact fun x hx => hx.map hc.continuousAt (tendsto_principal_principal.2 h)
#align set.maps_to.closure Set.MapsTo.closure

/-- See also `IsClosedMap.closure_image_eq_of_continuous`. -/
theorem image_closure_subset_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure h).image_subset
#align image_closure_subset_closure_image image_closure_subset_closure_image

-- porting note: new lemma
theorem closure_image_closure {f : α → β} {s : Set α} (h : Continuous f) :
    closure (f '' closure s) = closure (f '' s) :=
  Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image h) isClosed_closure)
    (closure_mono <| image_subset _ subset_closure)

theorem closure_subset_preimage_closure_image {f : α → β} {s : Set α} (h : Continuous f) :
    closure s ⊆ f ⁻¹' closure (f '' s) := by
  rw [← Set.image_subset_iff]
  exact image_closure_subset_closure_image h
#align closure_subset_preimage_closure_image closure_subset_preimage_closure_image

theorem map_mem_closure {s : Set α} {t : Set β} {f : α → β} {a : α} (hf : Continuous f)
    (ha : a ∈ closure s) (ht : MapsTo f s t) : f a ∈ closure t :=
  ht.closure hf ha
#align map_mem_closure map_mem_closure

/-- If a continuous map `f` maps `s` to a closed set `t`, then it maps `closure s` to `t`. -/
theorem Set.MapsTo.closure_left {s : Set α} {t : Set β} {f : α → β} (h : MapsTo f s t)
    (hc : Continuous f) (ht : IsClosed t) : MapsTo f (closure s) t :=
  ht.closure_eq ▸ h.closure hc
#align set.maps_to.closure_left Set.MapsTo.closure_left

/-!
### Function with dense range
-/

section DenseRange

variable {κ ι : Type*} (f : κ → β) (g : β → γ)

/-- `f : ι → β` has dense range if its range (image) is a dense subset of β. -/
def DenseRange := Dense (range f)
#align dense_range DenseRange

variable {f}

/-- A surjective map has dense range. -/
theorem Function.Surjective.denseRange (hf : Function.Surjective f) : DenseRange f := fun x => by
  simp [hf.range_eq]
#align function.surjective.dense_range Function.Surjective.denseRange

theorem denseRange_id : DenseRange (id : α → α) :=
  Function.Surjective.denseRange Function.surjective_id
#align dense_range_id denseRange_id

theorem denseRange_iff_closure_range : DenseRange f ↔ closure (range f) = univ :=
  dense_iff_closure_eq
#align dense_range_iff_closure_range denseRange_iff_closure_range

theorem DenseRange.closure_range (h : DenseRange f) : closure (range f) = univ :=
  h.closure_eq
#align dense_range.closure_range DenseRange.closure_range

theorem Dense.denseRange_val {s : Set α} (h : Dense s) : DenseRange ((↑) : s → α) := by
  simpa only [DenseRange, Subtype.range_coe_subtype]
#align dense.dense_range_coe Dense.denseRange_val

theorem Continuous.range_subset_closure_image_dense {f : α → β} (hf : Continuous f) {s : Set α}
    (hs : Dense s) : range f ⊆ closure (f '' s) := by
  rw [← image_univ, ← hs.closure_eq]
  exact image_closure_subset_closure_image hf
#align continuous.range_subset_closure_image_dense Continuous.range_subset_closure_image_dense

/-- The image of a dense set under a continuous map with dense range is a dense set. -/
theorem DenseRange.dense_image {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α}
    (hs : Dense s) : Dense (f '' s) :=
  (hf'.mono <| hf.range_subset_closure_image_dense hs).of_closure
#align dense_range.dense_image DenseRange.dense_image

/-- If `f` has dense range and `s` is an open set in the codomain of `f`, then the image of the
preimage of `s` under `f` is dense in `s`. -/
theorem DenseRange.subset_closure_image_preimage_of_isOpen (hf : DenseRange f) {s : Set β}
    (hs : IsOpen s) : s ⊆ closure (f '' (f ⁻¹' s)) := by
  rw [image_preimage_eq_inter_range]
  exact hf.open_subset_closure_inter hs
#align dense_range.subset_closure_image_preimage_of_is_open DenseRange.subset_closure_image_preimage_of_isOpen

/-- If a continuous map with dense range maps a dense set to a subset of `t`, then `t` is a dense
set. -/
theorem DenseRange.dense_of_mapsTo {f : α → β} (hf' : DenseRange f) (hf : Continuous f) {s : Set α}
    (hs : Dense s) {t : Set β} (ht : MapsTo f s t) : Dense t :=
  (hf'.dense_image hf hs).mono ht.image_subset
#align dense_range.dense_of_maps_to DenseRange.dense_of_mapsTo

/-- Composition of a continuous map with dense range and a function with dense range has dense
range. -/
theorem DenseRange.comp {g : β → γ} {f : κ → β} (hg : DenseRange g) (hf : DenseRange f)
    (cg : Continuous g) : DenseRange (g ∘ f) := by
  rw [DenseRange, range_comp]
  exact hg.dense_image cg hf
#align dense_range.comp DenseRange.comp

nonrec theorem DenseRange.nonempty_iff (hf : DenseRange f) : Nonempty κ ↔ Nonempty β :=
  range_nonempty_iff_nonempty.symm.trans hf.nonempty_iff
#align dense_range.nonempty_iff DenseRange.nonempty_iff

theorem DenseRange.nonempty [h : Nonempty β] (hf : DenseRange f) : Nonempty κ :=
  hf.nonempty_iff.mpr h
#align dense_range.nonempty DenseRange.nonempty

/-- Given a function `f : α → β` with dense range and `b : β`, returns some `a : α`. -/
def DenseRange.some (hf : DenseRange f) (b : β) : κ :=
  Classical.choice <| hf.nonempty_iff.mpr ⟨b⟩
#align dense_range.some DenseRange.some

nonrec theorem DenseRange.exists_mem_open (hf : DenseRange f) {s : Set β} (ho : IsOpen s)
    (hs : s.Nonempty) : ∃ a, f a ∈ s :=
  exists_range_iff.1 <| hf.exists_mem_open ho hs
#align dense_range.exists_mem_open DenseRange.exists_mem_open

theorem DenseRange.mem_nhds {f : κ → β} (h : DenseRange f) {b : β} {U : Set β} (U_in : U ∈ 𝓝 b) :
    ∃ a, f a ∈ U :=
  let ⟨a, ha⟩ := h.exists_mem_open isOpen_interior ⟨b, mem_interior_iff_mem_nhds.2 U_in⟩
  ⟨a, interior_subset ha⟩
#align dense_range.mem_nhds DenseRange.mem_nhds

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
  variables {M : Type*} [Add M] [TopologicalSpace M] [ContinuousAdd M]
  example : Continuous (λ x : M, x + x) :=
  continuous_add.comp _

  example : Continuous (λ x : M, x + x) :=
  continuous_add.comp (continuous_id.prod_mk continuous_id)
  ```
  The second is a valid proof, which is accepted if you write it as
  `continuous_add.comp (continuous_id.prod_mk continuous_id : _)`

2. If the operation has more than 2 arguments, they are impractical to use, because in your
  application the arguments in the domain might be in a different order or associated differently.

### The convenient way

A much more convenient way to write continuity lemmas is like `Continuous.add`:
```
Continuous.add {f g : X → M} (hf : Continuous f) (hg : Continuous g) : Continuous (λ x, f x + g x)
```
The conclusion can be `Continuous (f + g)`, which is definitionally equal.
This has the following advantages
* It supports projection notation, so is shorter to write.
* `Continuous.add _ _` is recognized correctly by the elaborator and gives useful new goals.
* It works generally, since the domain is a variable.

As an example for a unary operation, we have `Continuous.neg`.
```
Continuous.neg {f : α → G} (hf : Continuous f) : Continuous (fun x ↦ -f x)
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
example [TopologicalSpace α] [TopologicalSpace β] {x₀ : α} (f : α → α → β)
    (hf : ContinuousAt (Function.uncurry f) (x₀, x₀)) :
    ContinuousAt (fun x ↦ f x x) x₀ :=
  -- hf.comp (continuousAt_id.prod continuousAt_id) -- type mismatch
  -- hf.comp_of_eq (continuousAt_id.prod continuousAt_id) rfl -- works
```
-/
