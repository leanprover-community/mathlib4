/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Peter Nelson
-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.WellFounded

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

* `Set.maximal_iff_forall_insert` and `Set.minimal_iff_forall_sdiff_singleton` will generalize to
  lemmas about covering in the case of an `IsStronglyAtomic`/`IsStronglyCoatomic` order.

* `Finset` versions of the lemmas about sets.

* API to allow for easily expressing min/maximality with respect to an arbitrary non-`LE` relation.
* API for `MinimalFor`/`MaximalFor`
-/

@[expose] public section

assert_not_exists CompleteLattice

open Set OrderDual

variable {ι α β : Type*}

section LE
variable [LE α] {P Q : ι → Prop} {f : ι → α} {i j : ι}

@[to_dual (attr := simp)]
lemma minimalFor_eq_iff : MinimalFor (· = j) f i ↔ i = j := by simp +contextual [MinimalFor]

@[to_dual (attr := gcongr)]
theorem MinimalFor.anti (h : MinimalFor P f i) (hle : Q ≤ P) (hQ : Q i) : MinimalFor Q f i :=
  ⟨hQ, (h.le_of_le <| hle · ·)⟩

end LE

variable {P Q : α → Prop} {a x y : α}

section LE
variable [LE α]

@[to_dual (attr := simp)]
lemma minimalFor_id : MinimalFor P id x ↔ Minimal P x := .rfl

@[to_dual (attr := simp)]
theorem minimal_toDual : Minimal (fun x ↦ P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

@[to_dual]
alias ⟨Minimal.of_dual, Minimal.dual⟩ := minimal_toDual

@[to_dual (attr := simp)]
theorem minimal_false : ¬ Minimal (fun _ ↦ False) x := by
  simp [Minimal]

@[to_dual (attr := simp)] theorem minimal_true : Minimal (fun _ ↦ True) x ↔ IsMin x := by
  simp [IsMin, Minimal]

@[to_dual (attr := simp)]
theorem minimal_subtype {x : Subtype Q} :
    Minimal (fun x ↦ P x.1) x ↔ Minimal (P ⊓ Q) x := by
  obtain ⟨x, hx⟩ := x
  simp only [Minimal, Subtype.forall, Subtype.mk_le_mk, Pi.inf_apply, inf_Prop_eq]
  tauto

@[to_dual]
theorem minimal_true_subtype {x : Subtype P} : Minimal (fun _ ↦ True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

@[to_dual (attr := simp)]
theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hy hyx ↦ h.le_of_le hy.prop hyx⟩⟩

/-- If `P` is down-closed, then minimal elements satisfying `P` are exactly the globally minimal
elements satisfying `P`. -/
@[to_dual
/-- If `P` is up-closed, then maximal elements satisfying `P` are exactly the globally maximal
elements satisfying `P`. -/]
theorem minimal_iff_isMin (hP : ∀ ⦃x y⦄, P y → x ≤ y → P x) : Minimal P x ↔ P x ∧ IsMin x :=
  ⟨fun h ↦ ⟨h.prop, fun _ h' ↦ h.le_of_le (hP h.prop h') h'⟩, fun h ↦ ⟨h.1, fun _ _  h' ↦ h.2 h'⟩⟩

@[to_dual]
theorem Minimal.mono (h : Minimal P x) (hle : Q ≤ P) (hQ : Q x) : Minimal Q x :=
  ⟨hQ, fun y hQy ↦ h.le_of_le (hle y hQy)⟩

@[to_dual]
theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ P x ∧ Q x) x :=
  h.mono (fun _ ↦ And.left) ⟨h.prop, hQ⟩

@[to_dual]
theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (Q x ∧ P x)) x :=
  h.mono (fun _ ↦ And.right) ⟨hQ, h.prop⟩

@[to_dual (attr := simp)] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp +contextual [Minimal]

@[to_dual]
theorem not_minimal_iff (hx : P x) : ¬ Minimal P x ↔ ∃ y, P y ∧ y ≤ x ∧ ¬ (x ≤ y) := by
  simp [Minimal, hx]

@[to_dual]
theorem Minimal.or (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨h | h, hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩

@[to_dual]
theorem minimal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x := by
  simp_rw [and_iff_left_of_imp (fun x ↦ hPQ x), iff_self_and]
  exact fun h ↦ hPQ h.prop

@[to_dual]
theorem minimal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Minimal P x) := by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

end LE

section Preorder

variable [Preorder α] [Preorder β] {Q : ι → Prop} {f : ι → α} {g : α → β} {i j : ι}

@[to_dual maximal_iff_forall_gt]
theorem minimal_iff_forall_lt : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, y < x → ¬ P y := by
  simp [Minimal, lt_iff_le_not_ge, imp.swap]

@[to_dual maximalFor_iff_forall_gt]
theorem minimalFor_iff_forall_lt : MinimalFor Q f i ↔ Q i ∧ ∀ ⦃j⦄, f j < f i → ¬ Q j := by
  simp [MinimalFor, lt_iff_le_not_ge, imp.swap]

@[to_dual not_prop_of_gt]
theorem Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y :=
  (minimal_iff_forall_lt.1 h).2 hlt

@[to_dual not_prop_of_gt]
theorem MinimalFor.not_prop_of_lt (h : MinimalFor Q f i) (hlt : f j < f i) : ¬ Q j :=
  (minimalFor_iff_forall_lt.1 h).2 hlt

@[to_dual not_gt]
theorem Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬(y < x) :=
  fun hlt ↦ h.not_prop_of_lt hlt hy

@[to_dual not_gt]
theorem MinimalFor.not_lt (h : MinimalFor Q f i) (hj : Q j) : ¬(f j < f i) :=
  fun hlt ↦ h.not_prop_of_lt hlt hj

@[to_dual (attr := simp) maximal_ge_iff]
theorem minimal_le_iff : Minimal (· ≤ y) x ↔ x ≤ y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans h)

@[to_dual (attr := simp) maximal_gt_iff]
theorem minimal_lt_iff : Minimal (· < y) x ↔ x < y ∧ IsMin x :=
  minimal_iff_isMin (fun _ _ h h' ↦ h'.trans_lt h)

@[to_dual not_maximal_iff_exists_gt]
theorem not_minimal_iff_exists_lt (hx : P x) : ¬ Minimal P x ↔ ∃ y, y < x ∧ P y := by
  simp_rw [not_minimal_iff hx, lt_iff_le_not_ge, and_comm]

@[to_dual exists_gt_of_not_maximal]
alias ⟨exists_lt_of_not_minimal, _⟩ := not_minimal_iff_exists_lt

@[to_dual]
theorem MinimalFor.of_strictMonoOn_comp (hg : StrictMonoOn g (f '' setOf Q))
    (h : MinimalFor Q (g ∘ f) i) : MinimalFor Q f i := by
  refine ⟨h.prop, fun j hj hle ↦ ?_⟩
  by_contra
  exact h.not_lt hj <| hg ⟨j, hj, rfl⟩ ⟨i, h.prop, rfl⟩ <| lt_of_le_not_ge hle this

@[to_dual]
theorem MinimalFor.minimal_of_strictMonoOn (hg : StrictMonoOn g (setOf P)) (h : MinimalFor P g x) :
    Minimal P x :=
  minimalFor_id.mp <| .of_strictMonoOn_comp (Set.image_id _ ▸ hg) h

@[to_dual]
theorem MinimalFor.maximalFor_of_strictAntiOn_comp (hg : StrictAntiOn g (f '' setOf Q))
    (h : MinimalFor Q (g ∘ f) i) : MaximalFor Q f i := by
  refine ⟨h.prop, fun j hj hle ↦ ?_⟩
  by_contra
  exact h.not_lt hj <| hg ⟨i, h.prop, rfl⟩ ⟨j, hj, rfl⟩ <| lt_of_le_not_ge hle this

@[to_dual]
theorem MinimalFor.maximal_of_strictAntiOn (hg : StrictAntiOn g (setOf P)) (h : MinimalFor P g x) :
    Maximal P x :=
  maximalFor_id.mp <| MinimalFor.maximalFor_of_strictAntiOn_comp (Set.image_id _ ▸ hg) h

section WellFoundedLT
variable [WellFoundedLT α]

@[to_dual]
lemma exists_minimalFor_of_wellFoundedLT (P : ι → Prop) (f : ι → α) (hP : ∃ i, P i) :
    ∃ i, MinimalFor P f i := by
  simpa [not_lt_iff_le_imp_ge, InvImage]
    using! (instIsWellFoundedInvImage (· < ·) f).wf.has_min _ hP

@[to_dual]
lemma exists_minimal_of_wellFoundedLT (P : α → Prop) (hP : ∃ a, P a) : ∃ a, Minimal P a :=
  exists_minimalFor_of_wellFoundedLT P id hP

@[to_dual exists_maximal_ge_of_wellFoundedGT]
lemma exists_minimal_le_of_wellFoundedLT (P : α → Prop) (a : α) (ha : P a) :
    ∃ b ≤ a, Minimal P b := by
  obtain ⟨b, ⟨hba, hb⟩, hbmin⟩ :=
    exists_minimal_of_wellFoundedLT (fun b ↦ b ≤ a ∧ P b) ⟨a, le_rfl, ha⟩
  exact ⟨b, hba, hb, fun c hc hcb ↦ hbmin ⟨hcb.trans hba, hc⟩ hcb⟩

end WellFoundedLT
end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual (rename := hge → hle) eq_of_le]
theorem Minimal.eq_of_ge (hx : Minimal P x) (hy : P y) (hge : y ≤ x) : x = y :=
  (hx.2 hy hge).antisymm hge

@[to_dual (rename := hle → hge) eq_of_ge]
theorem Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y ≤ x) : y = x :=
  (hx.eq_of_ge hy hle).symm

@[to_dual]
theorem minimal_iff : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x = y :=
  ⟨fun h ↦ ⟨h.1, fun _ ↦ h.eq_of_ge⟩, fun h ↦ ⟨h.1, fun _ hy hle ↦ (h.2 hy hle).le⟩⟩

@[to_dual]
theorem minimal_mem_iff {s : Set α} : Minimal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → y ≤ x → x = y :=
  minimal_iff

/-- If `P y` holds, and everything satisfying `P` is above `y`, then `y` is the unique minimal
element satisfying `P`. -/
@[to_dual
/-- If `P y` holds, and everything satisfying `P` is below `y`, then `y` is the unique maximal
element satisfying `P`. -/]
theorem minimal_iff_eq (hy : P y) (hP : ∀ ⦃x⦄, P x → y ≤ x) : Minimal P x ↔ x = y :=
  ⟨fun h ↦ h.eq_of_ge hy (hP h.prop), by rintro rfl; exact ⟨hy, fun z hz _ ↦ hP hz⟩⟩

@[to_dual (attr := simp) maximal_le_iff] theorem minimal_ge_iff : Minimal (y ≤ ·) x ↔ x = y :=
  minimal_iff_eq rfl.le fun _ ↦ id

@[to_dual]
theorem minimal_iff_minimal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ Q y) : Minimal P x ↔ Minimal Q x := by
  refine ⟨fun h' ↦ ⟨?_, fun y hy hyx ↦ h'.le_of_le (hPQ hy) hyx⟩,
    fun h' ↦ ⟨hPQ h'.prop, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

end PartialOrder

section LinearOrder

variable [LinearOrder α] {i j : ι} {Q : ι → Prop} {f : ι → α}

@[to_dual]
theorem Minimal.le (h : Minimal P x) (hy : P y) : x ≤ y :=
  le_of_not_gt (h.not_lt hy)

@[to_dual]
theorem MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i ≤ f j :=
  le_of_not_gt (h.not_lt hj)

end LinearOrder

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

theorem Minimal.notMem_of_prop_sdiff_singleton (h : Minimal P s) (hx : P (s \ {x})) : x ∉ s :=
  fun hxs ↦ ((h.eq_of_superset hx sdiff_subset).subset hxs).2 rfl

@[deprecated (since := "2026-06-03")]
alias Minimal.notMem_of_prop_diff_singleton := Minimal.notMem_of_prop_sdiff_singleton

theorem Set.minimal_iff_forall_sdiff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s \ {x}) :=
  ⟨fun h ↦ ⟨h.1, fun _ hx hP ↦ h.notMem_of_prop_sdiff_singleton hP hx⟩,
    fun h ↦ ⟨h.1, fun _ ht hts x hxs ↦ by_contra fun hxt ↦
      h.2 x hxs (hP ht <| subset_sdiff_singleton hts hxt)⟩⟩

@[deprecated (since := "2026-06-03")]
alias Set.minimal_iff_forall_diff_singleton := Set.minimal_iff_forall_sdiff_singleton

theorem Set.exists_sdiff_singleton_of_not_minimal (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) (hs : P s)
    (h : ¬ Minimal P s) : ∃ x ∈ s, P (s \ {x}) := by
  simpa [Set.minimal_iff_forall_sdiff_singleton hP, hs] using h

@[deprecated (since := "2026-06-03")]
alias Set.exists_diff_singleton_of_not_minimal := Set.exists_sdiff_singleton_of_not_minimal

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

/- TODO : generalize `minimal_iff_forall_sdiff_singleton` and `maximal_iff_forall_insert`
to `IsStronglyCoatomic`/`IsStronglyAtomic` orders. -/

end Subset

section Set

variable {s t : Set α}
section Preorder

variable [Preorder α]

@[to_dual]
theorem setOf_minimal_subset (s : Set α) : {x | Minimal (· ∈ s) x} ⊆ s :=
  sep_subset ..

@[to_dual]
theorem Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

@[to_dual]
theorem IsLeast.minimal (h : IsLeast s x) : Minimal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

end Preorder

section PartialOrder

variable [PartialOrder α]

@[to_dual]
theorem IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_ge h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.minimal⟩

end PartialOrder

end Set

section Image

variable [Preorder α] [Preorder β] {s : Set α} {t : Set β}
section Function

variable {f : α → β}

-- TODO: the names in this section are all wrong
@[to_dual (reorder := hf (x y, 3 4))]
theorem minimal_mem_image_monotone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) := by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy, hf hy hx.prop]
  exact hx.le_of_le hy

@[to_dual (reorder := hf (x y, 3 4))]
theorem minimal_mem_image_monotone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a := by
  refine ⟨fun h ↦ ⟨ha, fun y hys ↦ ?_⟩, minimal_mem_image_monotone hf⟩
  rw [← hf ha hys, ← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

@[to_dual (reorder := hf (x y, 3 4))]
theorem minimal_mem_image_antitone (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x))
    (hx : Minimal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  minimal_mem_image_monotone (β := βᵒᵈ) (fun _ _ h h' ↦ hf h' h) hx

@[to_dual (reorder := hf (x y, 3 4))]
theorem minimal_mem_image_antitone_iff (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    Minimal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  maximal_mem_image_monotone_iff (β := βᵒᵈ) ha (fun _ _ h h' ↦ hf h' h)

@[to_dual (reorder := hf (x y, 3 4))]
theorem image_monotone_setOf_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal P x} = {x | Minimal (∃ x₀, P x₀ ∧ f x₀ = ·) x} := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    exact (minimal_mem_image_monotone_iff hx.prop hf).2 hx
  obtain ⟨y, hy, rfl⟩ := (mem_setOf_eq ▸ h).prop
  exact mem_image_of_mem _ <| (minimal_mem_image_monotone_iff (s := setOf P) hy hf).1 h

@[to_dual (reorder := hf (x y, 3 4))]
theorem image_antitone_setOf_minimal (hf : ∀ ⦃x y⦄, P x → P y → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal P x} = {x | Maximal (∃ x₀, P x₀ ∧ f x₀ = ·) x} :=
  image_monotone_setOf_minimal (β := βᵒᵈ) (fun _ _ hx hy ↦ hf hy hx)

@[to_dual (reorder := hf (x y, 3 4))]
theorem image_monotone_setOf_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  image_monotone_setOf_minimal hf

@[to_dual (reorder := hf (x y, 3 4))]
theorem image_antitone_setOf_minimal_mem (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ y ≤ x)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  image_antitone_setOf_minimal hf

end Function

namespace OrderEmbedding

variable {f : α ↪o β} {t : Set β}

@[to_dual]
theorem minimal_mem_image (f : α ↪o β) (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) :=
  _root_.minimal_mem_image_monotone (by simp [f.le_iff_le]) hx

@[to_dual]
theorem minimal_mem_image_iff (ha : a ∈ s) : Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a :=
  _root_.minimal_mem_image_monotone_iff ha (by simp [f.le_iff_le])

@[to_dual]
theorem minimal_apply_mem_inter_range_iff :
    Minimal (· ∈ t ∩ range f) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  refine ⟨fun h ↦ ⟨h.prop.1, fun y hy ↦ ?_⟩, fun h ↦ ⟨⟨h.prop, mem_range_self x⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, mem_range_self y⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

@[to_dual]
theorem minimal_apply_mem_iff (ht : t ⊆ Set.range f) :
    Minimal (· ∈ t) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  rw [← f.minimal_apply_mem_inter_range_iff, inter_eq_self_of_subset_left ht]

@[deprecated (since := "2026-04-07")] alias maximal_apply_iff := maximal_apply_mem_iff

theorem image_setOf_minimal : f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  _root_.image_monotone_setOf_minimal (by simp [f.le_iff_le])

@[to_dual]
theorem inter_preimage_setOf_minimal_eq_of_subset (hts : t ⊆ f '' s) :
    x ∈ s ∩ f ⁻¹' {y | Minimal (· ∈ t) y} ↔ Minimal (· ∈ s ∩ f ⁻¹' t) x := by
  simp_rw [mem_inter_iff, preimage_setOf_eq, mem_setOf_eq, mem_preimage,
    f.minimal_apply_mem_iff (hts.trans (image_subset_range _ _)),
    minimal_and_iff_left_of_imp (fun _ hx ↦ f.injective.mem_set_image.1 <| hts hx)]

end OrderEmbedding

namespace OrderIso

@[to_dual]
theorem image_setOf_minimal (f : α ≃o β) (P : α → Prop) :
    f '' {x | Minimal P x} = {x | Minimal (fun x ↦ P (f.symm x)) x} := by
  convert! _root_.image_monotone_setOf_minimal (f := f) (by simp [f.le_iff_le])
  aesop

@[to_dual]
theorem map_minimal_mem (f : s ≃o t) (hx : Minimal (· ∈ s) x) :
    Minimal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using! OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ t))) (s := univ) (x := ⟨x, hx.prop⟩)

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
def mapSetOfMinimal (f : s ≃o t) : {x | Minimal (· ∈ s) x} ≃o {x | Minimal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_minimal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_minimal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
@[to_dual existing]
def mapSetOfMaximal (f : s ≃o t) : {x | Maximal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_maximal_mem x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_maximal_mem x.2⟩
  left_inv x := Subtype.ext (congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩ :)
  right_inv x := Subtype.ext (congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩ :)
  map_rel_iff' := f.map_rel_iff

/-- If two sets are antitonically order isomorphic, their minimals/maximals are too. -/
@[to_dual /-- If two sets are antitonically order isomorphic, their maximals/minimals are too. -/]
def setOfMinimalIsoSetOfMaximal (f : s ≃o tᵒᵈ) :
    {x | Minimal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) (ofDual x)} where
      toFun x := ⟨(f ⟨x.1, x.2.1⟩).1, ((show s ≃o ofDual ⁻¹' t from f).mapSetOfMinimal x).2⟩
      invFun x := ⟨(f.symm ⟨x.1, x.2.1⟩).1,
        ((show ofDual ⁻¹' t ≃o s from f.symm).mapSetOfMinimal x).2⟩
      __ := (show s ≃o ofDual ⁻¹' t from f).mapSetOfMinimal

end OrderIso

end Image
section Interval

variable [PartialOrder α] {a b : α}

@[to_dual]
theorem minimal_mem_Icc (hab : a ≤ b) : Minimal (· ∈ Icc a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

@[to_dual]
theorem minimal_mem_Ico (hab : a < b) : Minimal (· ∈ Ico a b) x ↔ x = a :=
  minimal_iff_eq ⟨rfl.le, hab⟩ (fun _ ↦ And.left)

/- Note : The one-sided interval versions of these lemmas are unnecessary,
since `simp` handles them with `maximal_le_iff` and `minimal_ge_iff`. -/

end Interval
