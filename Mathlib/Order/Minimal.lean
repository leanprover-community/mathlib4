/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Peter Nelson
-/
import Mathlib.Order.Antichain

/-!
# Minimality and Maximality

This file proves basic facts about minimality and maximality
of an element with respect to a predicate `P` on an ordered type `α`.

## Implementation Details

This file underwent a refactor from a version where minimality and maximality were defined using
sets rather than predicates, and with an unbundled order relation rather than a `LE` instance.

A side effect is that it has become less straightforward to state that something is minimal
with respect to a relation that is *not* defeq to the default `LE`.
One possible way would be with a type synonym,
and another would be with an ad hoc `LE` instance and `@` notation.
This was not an issue in practice anywhere in mathlib at the time of the refactor,
but it may be worth re-examining this to make it easier in the future; see the TODO below.

## TODO

* In the linearly ordered case, versions of lemmas like `minimal_mem_image` will hold with
  `MonotoneOn`/`AntitoneOn` assumptions rather than the stronger `x ≤ y ↔ f x ≤ f y` assumptions.

* `Set.maximal_iff_forall_insert` and `Set.minimal_iff_forall_diff_singleton` will generalize to
  lemmas about covering in the case of an `IsStronglyAtomic`/`IsStronglyCoatomic` order.

* `Finset` versions of the lemmas about sets.

* API to allow for easily expressing min/maximality with respect to an arbitrary non-`LE` relation.
* API for `MinimalFor`/`MaximalFor`
-/

assert_not_exists CompleteLattice

open Set OrderDual

variable {ι α : Type*}

section LE
variable [LE α] {f : ι → α} {i j : ι}

@[simp] lemma minimalFor_eq_iff : MinimalFor (· = j) f i ↔ i = j := by simp +contextual [MinimalFor]
@[simp] lemma maximalFor_eq_iff : MaximalFor (· = j) f i ↔ i = j := by simp +contextual [MaximalFor]

end LE

variable {P Q : α → Prop} {a x y : α}

section LE
variable [LE α]

@[simp] lemma minimalFor_id : MinimalFor P id x ↔ Minimal P x := .rfl
@[simp] lemma maximalFor_id : MaximalFor P id x ↔ Maximal P x := .rfl

@[simp] theorem minimal_toDual : Minimal (fun x ↦ P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[simp] theorem maximal_toDual : Maximal (fun x ↦ P (ofDual x)) (toDual x) ↔ Minimal P x :=
  Iff.rfl

alias ⟨Maximal.of_dual, Maximal.dual⟩ := maximal_toDual

@[simp] theorem minimal_false : ¬ Minimal (fun _ ↦ False) x := by
  simp [Minimal]

@[simp] theorem maximal_false : ¬ Maximal (fun _ ↦ False) x := by
  simp [Maximal]

@[simp] theorem minimal_true : Minimal (fun _ ↦ True) x ↔ IsMin x := by
  simp [IsMin, Minimal]

@[simp] theorem maximal_true : Maximal (fun _ ↦ True) x ↔ IsMax x :=
  minimal_true (α := αᵒᵈ)

@[simp] theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x ↦ P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[simp] theorem maximal_subtype {x : Subtype Q} :
    Maximal (fun x ↦ P x.1) x ↔ Maximal (P ⊓ Q) x :=
  minimal_subtype (α := αᵒᵈ)

theorem maximal_true_subtype {x : Subtype P} : Maximal (fun _ ↦ True) x ↔ Maximal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Maximal, hx]

theorem minimal_true_subtype {x : Subtype P} : Minimal (fun _ ↦ True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[simp] theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hy hyx ↦ h.le_of_le hy.prop hyx⟩⟩

@[simp] theorem maximal_maximal : Maximal (Maximal P) x ↔ Maximal P x :=
  minimal_minimal (α := αᵒᵈ)

/-- If `P` is down-closed, then minimal elements satisfying `P` are exactly the globally minimal
elements satisfying `P`. -/
theorem minimal_iff_isMin (hP : ∀ ⦃x y⦄, P y → x ≤ y → P x) : Minimal P x ↔ P x ∧ IsMin x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_le (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

/-- If `P` is up-closed, then maximal elements satisfying `P` are exactly the globally maximal
elements satisfying `P`. -/
theorem maximal_iff_isMax (hP : ∀ ⦃x y⦄, P y → y ≤ x → P x) : Maximal P x ↔ P x ∧ IsMax x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_ge (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

theorem Minimal.mono (h : Minimal P x) (hle : Q ≤ P) (hQ : Q x) : Minimal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_le (hle y hQy)⟩

theorem Maximal.mono (h : Maximal P x) (hle : Q ≤ P) (hQ : Q x) : Maximal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_ge (hle y hQy)⟩

theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ P x ∧ Q x) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩

theorem Maximal.and_right (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (P x ∧ Q x)) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

theorem Maximal.and_left (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩

@[simp] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp +contextual [Minimal]

@[simp] theorem maximal_eq_iff : Maximal (· = y) x ↔ x = y := by
  simp +contextual [Maximal]

theorem not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ ∃ y, P y ∧ y ≤ x ∧ ¬ (x ≤ y) := by
  simp [Minimal, hx]

theorem not_maximal_iff (hx : P x) : ¬ Maximal P x ↔ ∃ y, P y ∧ x ≤ y ∧ ¬ (y ≤ x) :=
  not_minimal_iff (α := αᵒᵈ) hx

theorem Minimal.or (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩

theorem Maximal.or (h : Maximal (fun x ↦ P x ∨ Q x) x) : Maximal P x ∨ Maximal Q x :=
  Minimal.or (α := αᵒᵈ) h

theorem minimal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x := by
  simp_rw [and_iff_left_of_imp (fun x ↦ hPQ x), iff_self_and]
  exact fun h ↦ hPQ h.prop

theorem minimal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Minimal P x) := by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

theorem maximal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Maximal (fun x ↦ P x ∧ Q x) x ↔ (Maximal P x) ∧ Q x :=
  minimal_and_iff_right_of_imp (α := αᵒᵈ) hPQ

theorem maximal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Maximal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Maximal P x) :=
  minimal_and_iff_left_of_imp (α := αᵒᵈ) hPQ

end LE

section Preorder

variable [Preorder α]

theorem minimal_iff_forall_lt : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, y < x → ¬ P y := by
  simp [Minimal, lt_iff_le_not_ge, not_imp_not, imp.swap]

theorem maximal_iff_forall_gt : Maximal P x ↔ P x ∧ ∀ ⦃y⦄, x < y → ¬ P y :=
  minimal_iff_forall_lt (α := αᵒᵈ)

theorem Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y :=
  (minimal_iff_forall_lt.1 h).2 hlt

theorem Maximal.not_prop_of_gt (h : Maximal P x) (hlt : x < y) : ¬ P y :=
  (maximal_iff_forall_gt.1 h).2 hlt

theorem Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬ (y < x) :=
  fun hlt ↦ h.not_prop_of_lt hlt hy

theorem Maximal.not_gt (h : Maximal P x) (hy : P y) : ¬ (x < y) :=
  fun hlt ↦ h.not_prop_of_gt hlt hy

@[simp] theorem minimal_le_iff : Minimal (· ≤ y) x ↔ x ≤ y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans h)

@[simp] theorem maximal_ge_iff : Maximal (y ≤ ·) x ↔ y ≤ x ∧ IsMax x :=
  minimal_le_iff (α := αᵒᵈ)

@[simp] theorem minimal_lt_iff : Minimal (· < y) x ↔ x < y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans_lt h)

@[simp] theorem maximal_gt_iff : Maximal (y < ·) x ↔ y < x ∧ IsMax x :=
  minimal_lt_iff (α := αᵒᵈ)

theorem not_minimal_iff_exists_lt (hx : P x) : ¬ Minimal P x ↔ ∃ y, y < x ∧ P y := by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

theorem not_maximal_iff_exists_gt (hx : P x) : ¬ Maximal P x ↔ ∃ y, x < y ∧ P y :=
  not_minimal_iff_exists_lt (α := αᵒᵈ) hx

alias ⟨exists_gt_of_not_maximal, _⟩ := not_maximal_iff_exists_gt

section WellFoundedLT
variable [WellFoundedLT α]

lemma exists_minimalFor_of_wellFoundedLT (P : ι → Prop) (f : ι → α) (hP : ∃ i, P i) :
    ∃ i, MinimalFor P f i := by
  simpa [not_lt_iff_le_imp_ge, InvImage] using (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

lemma exists_minimal_of_wellFoundedLT (P : α → Prop) (hP : ∃ a, P a) : ∃ a, Minimal P a :=
  exists_minimalFor_of_wellFoundedLT P id hP

lemma exists_minimal_le_of_wellFoundedLT (P : α → Prop) (a : α) (ha : P a) :
    ∃ b ≤ a, Minimal P b := by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b ↦ b ≤ a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb ↦ hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

end WellFoundedLT

section WellFoundedGT
variable [WellFoundedGT α]

lemma exists_maximalFor_of_wellFoundedGT (P : ι → Prop) (f : ι → α) (hP : ∃ i, P i) :
    ∃ i, MaximalFor P f i := exists_minimalFor_of_wellFoundedLT (α := αᵒᵈ) P f hP

lemma exists_maximal_of_wellFoundedGT (P : α → Prop) (hP : ∃ a, P a) : ∃ a, Maximal P a :=
  exists_minimal_of_wellFoundedLT (α := αᵒᵈ) P hP

lemma exists_maximal_ge_of_wellFoundedGT (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, a ≤ b ∧ Maximal P b := exists_minimal_le_of_wellFoundedLT (α := αᵒᵈ) P a ha

end WellFoundedGT
end Preorder

section PartialOrder

variable [PartialOrder α]

theorem Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : y ≤ x) : x = y :=
  (hx.2 hy hge).antisymm hge

theorem Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y ≤ x) : y = x :=
  (hx.eq_of_ge hy hle).symm

theorem Maximal.eq_of_le (hx : Maximal P x) (hy : P y) (hle : x ≤ y) : x = y :=
  hle.antisymm <| hx.2 hy hle

theorem Maximal.eq_of_ge (hx : Maximal P x) (hy : P y) (hge : x ≤ y) : y = x :=
  (hx.eq_of_le hy hge).symm

theorem minimal_iff : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x = y :=
  ⟨fun h ↦ ⟨h.1, fun _ ↦ h.eq_of_ge⟩, fun h ↦ ⟨h.1, fun _ hy hle ↦ (h.2 hy hle).le⟩⟩

theorem maximal_iff : Maximal P x ↔ P x ∧ ∀ ⦃y⦄, P y → x ≤ y → x = y :=
  minimal_iff (α := αᵒᵈ)

theorem minimal_mem_iff {s : Set α} : Minimal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → y ≤ x → x = y :=
  minimal_iff

theorem maximal_mem_iff {s : Set α} : Maximal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → x ≤ y → x = y :=
  maximal_iff

/-- If `P y` holds, and everything satisfying `P` is above `y`, then `y` is the unique minimal
element satisfying `P`. -/
theorem minimal_iff_eq (hy : P y) (hP : ∀ ⦃x⦄, P x → y ≤ x) : Minimal P x ↔ x = y :=
  ⟨fun h ↦ h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ ↦ hP hz⟩⟩

/-- If `P y` holds, and everything satisfying `P` is below `y`, then `y` is the unique maximal
element satisfying `P`. -/
theorem maximal_iff_eq (hy : P y) (hP : ∀ ⦃x⦄, P x → x ≤ y) : Maximal P x ↔ x = y :=
  minimal_iff_eq (α := αᵒᵈ) hy hP

@[simp] theorem minimal_ge_iff : Minimal (y ≤ ·) x ↔ x = y :=
  minimal_iff_eq rfl.le fun _ ↦ id

@[simp] theorem maximal_le_iff : Maximal (· ≤ y) x ↔ x = y :=
  maximal_iff_eq rfl.le fun _ ↦ id

theorem minimal_iff_minimal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ Q y) : Minimal P x ↔ Minimal Q x := by
  refine ⟨fun h' ↦ ⟨?_, fun y hy hyx ↦ h'.le_of_le (hPQ hy) hyx⟩,
    fun h' ↦ ⟨hPQ h'.prop, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

theorem maximal_iff_maximal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, x ≤ y ∧ Q y) : Maximal P x ↔ Maximal Q x :=
  minimal_iff_minimal_of_imp_of_forall (α := αᵒᵈ) hPQ h

end PartialOrder

section Subset

variable {P : Set α → Prop} {s t : Set α}

theorem Minimal.eq_of_superset (h : Minimal P s) (ht : P t) (hts : t ⊆ s) : s = t :=
  h.eq_of_ge ht hts

theorem Maximal.eq_of_subset (h : Maximal P s) (ht : P t) (hst : s ⊆ t) : s = t :=
  h.eq_of_le ht hst

theorem Minimal.eq_of_subset (h : Minimal P s) (ht : P t) (hts : t ⊆ s) : t = s :=
  h.eq_of_le ht hts

theorem Maximal.eq_of_superset (h : Maximal P s) (ht : P t) (hst : s ⊆ t) : t = s :=
  h.eq_of_ge ht hst

theorem minimal_subset_iff : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, P t → t ⊆ s → s = t :=
  _root_.minimal_iff

theorem maximal_subset_iff : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, P t → s ⊆ t → s = t :=
  _root_.maximal_iff

theorem minimal_subset_iff' : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, P t → t ⊆ s → s ⊆ t :=
  Iff.rfl

theorem maximal_subset_iff' : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, P t → s ⊆ t → t ⊆ s :=
  Iff.rfl

theorem not_minimal_subset_iff (hs : P s) : ¬ Minimal P s ↔ ∃ t, t ⊂ s ∧ P t :=
  not_minimal_iff_exists_lt hs

theorem not_maximal_subset_iff (hs : P s) : ¬ Maximal P s ↔ ∃ t, s ⊂ t ∧ P t :=
  not_maximal_iff_exists_gt hs

theorem Set.minimal_iff_forall_ssubset : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, t ⊂ s → ¬ P t :=
  minimal_iff_forall_lt

theorem Minimal.not_prop_of_ssubset (h : Minimal P s) (ht : t ⊂ s) : ¬ P t :=
  (minimal_iff_forall_lt.1 h).2 ht

theorem Minimal.not_ssubset (h : Minimal P s) (ht : P t) : ¬ t ⊂ s :=
  h.not_lt ht

theorem Maximal.mem_of_prop_insert (h : Maximal P s) (hx : P (insert x s)) : x ∈ s :=
  h.eq_of_subset hx (subset_insert _ _) ▸ mem_insert ..

theorem Minimal.notMem_of_prop_diff_singleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s :=
  fun hxs ↦ ((h.eq_of_superset hx diff_subset).subset hxs).2 rfl

@[deprecated (since := "2025-05-23")]
alias Minimal.not_mem_of_prop_diff_singleton := Minimal.notMem_of_prop_diff_singleton

theorem Set.minimal_iff_forall_diff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s \ {x}) :=
  ⟨fun h ↦ ⟨h.1, fun _ hx hP ↦ h.notMem_of_prop_diff_singleton hP hx⟩,
    fun h ↦ ⟨h.1, fun _ ht hts x hxs ↦ by_contra fun hxt ↦
      h.2 x hxs (hP ht <| subset_diff_singleton hts hxt)⟩⟩

theorem Set.exists_diff_singleton_of_not_minimal (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) (hs : P s)
    (h : ¬ Minimal P s) : ∃ x ∈ s, P (s \ {x}) := by
  simpa [Set.minimal_iff_forall_diff_singleton hP, hs] using h

theorem Set.maximal_iff_forall_ssuperset : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, s ⊂ t → ¬ P t :=
  maximal_iff_forall_gt

theorem Maximal.not_prop_of_ssuperset (h : Maximal P s) (ht : s ⊂ t) : ¬ P t :=
  (maximal_iff_forall_gt.1 h).2 ht

theorem Maximal.not_ssuperset (h : Maximal P s) (ht : P t) : ¬ s ⊂ t :=
  h.not_gt ht

theorem Set.maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [not_imp_not]
  exact ⟨fun h ↦ ⟨h.1, fun x ↦ h.mem_of_prop_insert⟩,
    fun h ↦ ⟨h.1, fun t ht hst x hxt ↦ h.2 x (hP ht <| insert_subset hxt hst)⟩⟩

theorem Set.exists_insert_of_not_maximal (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) (hs : P s)
    (h : ¬ Maximal P s) : ∃ x ∉ s, P (insert x s) := by
  simpa [Set.maximal_iff_forall_insert hP, hs] using h

/- TODO : generalize `minimal_iff_forall_diff_singleton` and `maximal_iff_forall_insert`
to `IsStronglyCoatomic`/`IsStronglyAtomic` orders. -/

end Subset

section Set

variable {s t : Set α}
section Preorder

variable [Preorder α]

theorem setOf_minimal_subset (s : Set α) : {x | Minimal (· ∈ s) x} ⊆ s :=
  sep_subset ..

theorem setOf_maximal_subset (s : Set α) : {x | Maximal (· ∈ s) x} ⊆ s :=
  sep_subset ..

theorem Set.Subsingleton.maximal_mem_iff (h : s.Subsingleton) : Maximal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

theorem Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

theorem IsLeast.minimal (h : IsLeast s x) : Minimal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

theorem IsGreatest.maximal (h : IsGreatest s x) : Maximal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

theorem IsAntichain.minimal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Minimal (· ∈ s) x ↔ x ∈ s :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hys hyx ↦ (hs.eq hys h hyx).symm.le⟩⟩

theorem IsAntichain.maximal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Maximal (· ∈ s) x ↔ x ∈ s :=
  hs.to_dual.minimal_mem_iff

/-- If `t` is an antichain shadowing and including the set of maximal elements of `s`,
then `t` *is* the set of maximal elements of `s`. -/
theorem IsAntichain.eq_setOf_maximal (ht : IsAntichain (· ≤ ·) t)
    (h : ∀ x, Maximal (· ∈ s) x → x ∈ t) (hs : ∀ a ∈ t, ∃ b, b ≤ a ∧ Maximal (· ∈ s) b) :
    {x | Maximal (· ∈ s) x} = t := by
  refine Set.ext fun x ↦ ⟨h _, fun hx ↦ ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

/-- If `t` is an antichain shadowed by and including the set of minimal elements of `s`,
then `t` *is* the set of minimal elements of `s`. -/
theorem IsAntichain.eq_setOf_minimal (ht : IsAntichain (· ≤ ·) t)
    (h : ∀ x, Minimal (· ∈ s) x → x ∈ t) (hs : ∀ a ∈ t, ∃ b, a ≤ b ∧ Minimal (· ∈ s) b) :
    {x | Minimal (· ∈ s) x} = t :=
  ht.to_dual.eq_setOf_maximal h hs

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem setOf_maximal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Maximal P x} :=
  fun _ hx _ ⟨hy, _⟩ hne hle ↦ hne (hle.antisymm <| hx.2 hy hle)

theorem setOf_minimal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Minimal P x} :=
  (setOf_maximal_antichain (α := αᵒᵈ) P).swap

theorem IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_ge h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.minimal⟩

theorem IsGreatest.maximal_iff (h : IsGreatest s a) : Maximal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_le h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.maximal⟩

end PartialOrder

end Set

section Image

variable [Preorder α] {β : Type*} [Preorder β] {s : Set α} {t : Set β}
section Function

variable {f : α → β}

theorem minimal_mem_image_monotone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) := by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy, hf hy hx.prop]
  exact hx.le_of_le hy

theorem maximal_mem_image_monotone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Maximal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  minimal_mem_image_monotone (α := αᵒᵈ) (β := βᵒᵈ) (s := s) (fun _ _ hx hy ↦ hf hy hx) hx

theorem minimal_mem_image_monotone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a := by
  refine ⟨fun h ↦ ⟨ha, fun y hys ↦ ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys, ← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

theorem maximal_mem_image_monotone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Maximal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  minimal_mem_image_monotone_iff (α := αᵒᵈ) (β := βᵒᵈ) (s := s) ha fun _ _ hx hy ↦ hf hy hx

theorem minimal_mem_image_antitone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x))
    (hx : Minimal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' ↦ hf h' h) hx

theorem maximal_mem_image_antitone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x))
    (hx : Maximal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) :=
  maximal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' ↦ hf h' h) hx

theorem minimal_mem_image_antitone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    Minimal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' ↦ hf h' h)

theorem maximal_mem_image_antitone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    Maximal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a :=
  minimal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' ↦ hf h' h)

theorem image_monotone_setOf_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal P x} = {x | Minimal (∃ x₀, P x₀ ∧ f x₀ = ·) x} := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_setOf_eq ▸ h).prop
  exact mem_image_of_mem _ <| (minimal_mem_image_monotone_iff (s := setOf P) hy hf).1 h

theorem image_monotone_setOf_maximal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Maximal P x} = {x | Maximal (∃ x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOf_minimal (α := αᵒᵈ) (β := βᵒᵈ) (fun _ _ hx hy ↦ hf hy hx)

theorem image_antitone_setOf_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal P x} = {x | Maximal (∃ x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOf_minimal (β := βᵒᵈ) (fun _ _ hx hy ↦ hf hy hx)

theorem image_antitone_setOf_maximal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Maximal P x} = {x | Minimal (∃ x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOf_maximal (β := βᵒᵈ) (fun _ _ hx hy ↦ hf hy hx)

theorem image_monotone_setOf_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  image_monotone_setOf_minimal hf

theorem image_monotone_setOf_maximal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Maximal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  image_monotone_setOf_maximal hf

theorem image_antitone_setOf_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  image_antitone_setOf_minimal hf

theorem image_antitone_setOf_maximal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Maximal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  image_antitone_setOf_maximal hf

end Function

namespace OrderEmbedding

variable {f : α ↪o β} {t : Set β}

theorem minimal_mem_image (f : α ↪o β) (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) :=
  _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

theorem maximal_mem_image (f : α ↪o β) (hx : Maximal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  _root_.maximal_mem_image_monotone (by simp [f.le_iff_le]) hx

theorem minimal_mem_image_iff (ha : a ∈ s) : Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a :=
  _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

theorem maximal_mem_image_iff (ha : a ∈ s) : Maximal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  _root_.maximal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

theorem minimal_apply_mem_inter_range_iff :
    Minimal (· ∈ t ∩ range f) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  refine ⟨fun h ↦ ⟨h.prop.1, fun y hy ↦ ?_⟩, fun h ↦ ⟨⟨h.prop, by simp⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, by simp⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

theorem maximal_apply_mem_inter_range_iff :
    Maximal (· ∈ t ∩ range f) (f x) ↔ Maximal (fun x ↦ f x ∈ t) x :=
  f.dual.minimal_apply_mem_inter_range_iff

theorem minimal_apply_mem_iff (ht : t ⊆ Set.range f) :
    Minimal (· ∈ t) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  rw [← f.minimal_apply_mem_inter_range_iff, inter_eq_self_of_subset_left ht]

theorem maximal_apply_iff (ht : t ⊆ Set.range f) :
    Maximal (· ∈ t) (f x) ↔ Maximal (fun x ↦ f x ∈ t) x :=
  f.dual.minimal_apply_mem_iff ht

@[simp] theorem image_setOf_minimal : f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  _root_.image_monotone_setOf_minimal (by simp [f.le_iff_le])

@[simp] theorem image_setOf_maximal : f '' {x | Maximal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  _root_.image_monotone_setOf_maximal (by simp [f.le_iff_le])

theorem inter_preimage_setOf_minimal_eq_of_subset (hts : t ⊆ f '' s) :
    x ∈ s ∩ f ⁻¹' {y | Minimal (· ∈ t) y} ↔ Minimal (· ∈ s ∩ f ⁻¹' t) x := by
  simp_rw [mem_inter_iff, preimage_setOf_eq, mem_setOf_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx ↦ f.injective.mem_set_image.1 <| hts hx)]

theorem inter_preimage_setOf_maximal_eq_of_subset (hts : t ⊆ f '' s) :
    x ∈ s ∩ f ⁻¹' {y | Maximal (· ∈ t) y} ↔ Maximal (· ∈ s ∩ f ⁻¹' t) x :=
  f.dual.inter_preimage_setOf_minimal_eq_of_subset hts

end OrderEmbedding

namespace OrderIso

theorem image_setOf_minimal (f : α ≃o β) (P : α → Prop) :
    f '' {x | Minimal P x} = {x | Minimal (fun x ↦ P (f.symm x)) x} := by
  convert _root_.image_monotone_setOf_minimal (f := f) (by simp [f.le_iff_le])
  aesop

theorem image_setOf_maximal (f : α ≃o β) (P : α → Prop) :
    f '' {x | Maximal P x} = {x | Maximal (fun x ↦ P (f.symm x)) x} := by
  convert _root_.image_monotone_setOf_maximal (f := f) (by simp [f.le_iff_le])
  aesop

theorem map_minimal_mem (f : s ≃o t) (hx : Minimal (· ∈ s) x) :
    Minimal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype t)) (s := univ) (x := ⟨x, hx.prop⟩)

theorem map_maximal_mem (f : s ≃o t) (hx : Maximal (· ∈ s) x) :
    Maximal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, maximal_true_subtype, hx,
    true_imp_iff, image_univ] using OrderEmbedding.maximal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype t)) (s := univ) (x := ⟨x, hx.prop⟩)

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
def mapSetOfMinimal (f : s ≃o t) : {x | Minimal (· ∈ s) x} ≃o {x | Minimal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
def mapSetOfMaximal (f : s ≃o t) : {x | Maximal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

/-- If two sets are antitonically order isomorphic, their minimals/maximals are too. -/
def setOfMinimalIsoSetOfMaximal (f : s ≃o tᵒᵈ) :
    {x | Minimal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) (ofDual x)} where
      toFun x := ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfMinimal x).2⟩
      __ := (show s ≃o ofDual⁻¹' t from f).mapSetOfMinimal

/-- If two sets are antitonically order isomorphic, their maximals/minimals are too. -/
def setOfMaximalIsoSetOfMinimal (f : s ≃o tᵒᵈ) :
    {x | Maximal (· ∈ s) x} ≃o {x | Minimal (· ∈ t) (ofDual x)} where
  toFun x := ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfMaximal x).2⟩
  invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfMaximal x).2⟩
  __ := (show s ≃o ofDual⁻¹' t from f).mapSetOfMaximal

end OrderIso

end Image
section Interval

variable [PartialOrder α] {a b : α}

theorem minimal_mem_Icc (hab : a ≤ b) : Minimal (· ∈ Icc a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

theorem maximal_mem_Icc (hab : a ≤ b) : Maximal (· ∈ Icc a b) x ↔ x = b :=
  maximal_iff_eq ⟨hab, rfl.le⟩ (fun _ ↦ And.right)

theorem minimal_mem_Ico (hab : a < b) : Minimal (· ∈ Ico a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

theorem maximal_mem_Ioc (hab : a < b) : Maximal (· ∈ Ioc a b) x ↔ x = b :=
  maximal_iff_eq ⟨hab, rfl.le⟩ (fun _ ↦ And.right)

/- Note : The one-sided interval versions of these lemmas are unnecessary,
since `simp` handles them with `maximal_le_iff` and `minimal_ge_iff`. -/

end Interval
