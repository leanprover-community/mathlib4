/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Lift
public import Mathlib.Topology.Basic

/-!
# Interior, closure and frontier of a set

This file provides lemmas relating to the functions `interior`, `closure` and `frontier` of a set
endowed with a topology.

## Notation

* `𝓝 x`: the filter `nhds x` of neighborhoods of a point `x`;
* `𝓟 s`: the principal filter of a set `s`;
* `𝓝[s] x`: the filter `nhdsWithin x s` of neighborhoods of a point `x` within a set `s`;
* `𝓝[≠] x`: the filter `nhdsWithin x {x}ᶜ` of punctured neighborhoods of `x`.

## Tags

interior, closure, frontier
-/

@[expose] public section

open Set

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {x : X} {s s₁ s₂ t : Set X}

section Interior

theorem mem_interior : x ∈ interior s ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := by
  simp only [interior, mem_sUnion, mem_setOf_eq, and_assoc, and_left_comm]

@[simp]
theorem isOpen_interior : IsOpen (interior s) :=
  isOpen_sUnion fun _ => And.left

theorem interior_subset : interior s ⊆ s :=
  sUnion_subset fun _ => And.right

theorem interior_maximal (h₁ : t ⊆ s) (h₂ : IsOpen t) : t ⊆ interior s :=
  subset_sUnion_of_mem ⟨h₂, h₁⟩

@[grind =]
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

theorem subset_interior_union : interior s ∪ interior t ⊆ interior (s ∪ t) :=
  union_subset (interior_mono subset_union_left) (interior_mono subset_union_right)

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

theorem interior_union_inter_interior_compl_left_subset :
    interior (s ∪ t) ∩ interior sᶜ ⊆ interior t :=
  interior_inter.symm.trans_subset <| interior_mono (union_inter_compl_left_subset ..)

theorem interior_union_inter_interior_compl_right_subset :
    interior (s ∪ t) ∩ interior tᶜ ⊆ interior s :=
  interior_inter.symm.trans_subset <| interior_mono (union_inter_compl_right_subset ..)

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

end Interior

section Closure

@[simp]
theorem isClosed_closure : IsClosed (closure s) :=
  isClosed_sInter fun _ => And.left

theorem subset_closure : s ⊆ closure s :=
  subset_sInter fun _ => And.right

theorem notMem_of_notMem_closure {P : X} (hP : P ∉ closure s) : P ∉ s := fun h =>
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

theorem closure_inter_subset : closure (s ∩ t) ⊆ closure s ∩ closure t :=
  subset_inter (closure_mono inter_subset_left) (closure_mono inter_subset_right)

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

theorem subset_closure_inter_union_closure_compl_left :
    closure t ⊆ closure (s ∩ t) ∪ closure sᶜ :=
  (closure_mono <| subset_inter_union_compl_left ..).trans_eq closure_union

theorem subset_closure_inter_union_closure_compl_right :
    closure s ⊆ closure (s ∩ t) ∪ closure tᶜ :=
  (closure_mono <| subset_inter_union_compl_right ..).trans_eq closure_union

theorem interior_subset_closure : interior s ⊆ closure s :=
  Subset.trans interior_subset subset_closure

@[simp]
theorem interior_compl : interior sᶜ = (closure s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

@[simp]
theorem closure_compl : closure sᶜ = (interior s)ᶜ := by
  simp [closure_eq_compl_interior_compl]

theorem interior_eq_compl_closure_compl : interior s = (closure sᶜ)ᶜ := by simp

theorem interior_union_of_disjoint_closure (h : Disjoint (closure s) (closure t)) :
    interior (s ∪ t) = interior s ∪ interior t := by
  have full : interior sᶜ ∪ interior tᶜ = univ := by simpa [disjoint_iff, ← compl_inter] using h
  refine subset_antisymm ?_ subset_interior_union
  rw [← (interior _).inter_univ, ← full, inter_union_distrib_left]
  exact union_subset
    (interior_union_inter_interior_compl_left_subset.trans subset_union_right)
    (interior_union_inter_interior_compl_right_subset.trans subset_union_left)

theorem closure_inter_of_codisjoint_interior (h : Codisjoint (interior s) (interior t)) :
    closure (s ∩ t) = closure s ∩ closure t := by
  rw [← compl_inj_iff]
  simp only [← interior_compl, compl_inter]
  apply interior_union_of_disjoint_closure
  simpa only [closure_compl, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left]

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

lemma DenseRange.of_comp {α β : Type*} {f : α → X} {g : β → α}
    (h : DenseRange (f ∘ g)) : DenseRange f :=
  Dense.mono (range_comp_subset_range g f) h

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

@[simp] theorem closure_interior_idem :
    closure (interior (closure (interior s))) = closure (interior s) :=
  isClosed_closure.closure_interior_subset.antisymm
    (closure_mono isOpen_interior.subset_interior_closure)

@[simp] theorem interior_closure_idem :
    interior (closure (interior (closure s))) = interior (closure s) :=
  (interior_mono isClosed_closure.closure_interior_subset).antisymm
    isOpen_interior.subset_interior_closure

end Closure

section Frontier

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

lemma mem_interior_iff_notMem_frontier {s : Set X} {x : X} (hx : x ∈ s) :
    x ∈ interior s ↔ x ∉ frontier s := by
  simp [← self_diff_frontier, hx]

lemma mem_frontier_iff_notMem_interior {s : Set X} {x : X} (hx : x ∈ s) :
    x ∈ frontier s ↔ x ∉ interior s := by
  simp [← self_diff_frontier, hx]

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
  simp only [inter_union_distrib_left, inter_assoc,
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

end Frontier
