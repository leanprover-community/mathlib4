/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Dedup
import Mathlib.Data.List.Infix

/-!
# Preparations for defining operations on `Finset`.

The operations here ignore multiplicities,
and prepare for defining the corresponding operations on `Finset`.
-/


-- Assert that we define `Finset` without the material on the set lattice.
-- Note that we cannot put this in `Data.Finset.Basic` because we proved relevant lemmas there.
assert_not_exists Set.sInter

namespace Multiset

open List

variable {α : Type*} [DecidableEq α] {s : Multiset α}

/-! ### finset insert -/


/-- `ndinsert a s` is the lift of the list `insert` operation. This operation
  does not respect multiplicities, unlike `cons`, but it is suitable as
  an insert operation on `Finset`. -/
def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]
theorem coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α) :=
  rfl

@[simp]
theorem ndinsert_zero (a : α) : ndinsert a 0 = {a} :=
  rfl

@[simp]
theorem ndinsert_of_mem {a : α} {s : Multiset α} : a ∈ s → ndinsert a s = s :=
  Quot.inductionOn s fun _ h => congr_arg ((↑) : List α → Multiset α) <| insert_of_mem h

@[simp]
theorem ndinsert_of_notMem {a : α} {s : Multiset α} : a ∉ s → ndinsert a s = a ::ₘ s :=
  Quot.inductionOn s fun _ h => congr_arg ((↑) : List α → Multiset α) <| insert_of_not_mem h

@[deprecated (since := "2025-05-23")] alias ndinsert_of_not_mem := ndinsert_of_notMem

@[simp]
theorem mem_ndinsert {a b : α} {s : Multiset α} : a ∈ ndinsert b s ↔ a = b ∨ a ∈ s :=
  Quot.inductionOn s fun _ => mem_insert_iff

@[simp]
theorem le_ndinsert_self (a : α) (s : Multiset α) : s ≤ ndinsert a s :=
  Quot.inductionOn s fun _ => (sublist_insert _ _).subperm

theorem mem_ndinsert_self (a : α) (s : Multiset α) : a ∈ ndinsert a s := by simp

theorem mem_ndinsert_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ ndinsert b s :=
  mem_ndinsert.2 (Or.inr h)

theorem length_ndinsert_of_mem {a : α} {s : Multiset α} (h : a ∈ s) :
    card (ndinsert a s) = card s := by simp [h]

theorem length_ndinsert_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) :
    card (ndinsert a s) = card s + 1 := by simp [h]

@[deprecated (since := "2025-05-23")] alias length_ndinsert_of_not_mem := length_ndinsert_of_notMem

theorem dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ s) = ndinsert a (dedup s) := by
  by_cases h : a ∈ s <;> simp [h]

theorem Nodup.ndinsert (a : α) : Nodup s → Nodup (ndinsert a s) :=
  Quot.inductionOn s fun _ => Nodup.insert

theorem ndinsert_le {a : α} {s t : Multiset α} : ndinsert a s ≤ t ↔ s ≤ t ∧ a ∈ t :=
  ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a ∈ s then by simp [h, l]
    else by
      rw [ndinsert_of_notMem h, ← cons_erase m, cons_le_cons_iff, ← le_cons_of_notMem h,
          cons_erase m]
      exact l⟩

theorem attach_ndinsert (a : α) (s : Multiset α) :
    (s.ndinsert a).attach =
      ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
  have eq :
    ∀ h : ∀ p : { x // x ∈ s }, p.1 ∈ s,
      (fun p : { x // x ∈ s } => ⟨p.val, h p⟩ : { x // x ∈ s } → { x // x ∈ s }) = id :=
    fun _ => funext fun _ => Subtype.ext rfl
  have : ∀ (t) (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
      (s.attach.map fun p => ⟨p.1, eq ▸ mem_ndinsert_of_mem p.2⟩) := by
    intro t ht
    by_cases h : a ∈ s
    · rw [ndinsert_of_mem h] at ht
      subst ht
      rw [eq, map_id, ndinsert_of_mem (mem_attach _ _)]
    · rw [ndinsert_of_notMem h] at ht
      subst ht
      simp [attach_cons, h]
  this _ rfl

@[simp]
theorem disjoint_ndinsert_left {a : α} {s t : Multiset α} :
    Disjoint (ndinsert a s) t ↔ a ∉ t ∧ Disjoint s t :=
  Iff.trans (by simp [disjoint_left]) disjoint_cons_left

@[simp]
theorem disjoint_ndinsert_right {a : α} {s t : Multiset α} :
    Disjoint s (ndinsert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm, disjoint_ndinsert_left]; tauto

/-! ### finset union -/


/-- `ndunion s t` is the lift of the list `union` operation. This operation
  does not respect multiplicities, unlike `s ∪ t`, but it is suitable as
  a union operation on `Finset`. (`s ∪ t` would also work as a union operation
  on finset, but this is more efficient.) -/
def ndunion (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.union p₂

@[simp]
theorem coe_ndunion (l₁ l₂ : List α) : @ndunion α _ l₁ l₂ = (l₁ ∪ l₂ : List α) :=
  rfl

-- `simp` can prove this once we have `ndunion_eq_union`.
theorem zero_ndunion (s : Multiset α) : ndunion 0 s = s :=
  Quot.inductionOn s fun _ => rfl

@[simp]
theorem cons_ndunion (s t : Multiset α) (a : α) : ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => rfl

@[simp]
theorem mem_ndunion {s t : Multiset α} {a : α} : a ∈ ndunion s t ↔ a ∈ s ∨ a ∈ t :=
  Quot.induction_on₂ s t fun _ _ => List.mem_union_iff

theorem le_ndunion_right (s t : Multiset α) : t ≤ ndunion s t :=
  Quot.induction_on₂ s t fun _ _ => (suffix_union_right _ _).sublist.subperm

theorem subset_ndunion_right (s t : Multiset α) : t ⊆ ndunion s t :=
  subset_of_le (le_ndunion_right s t)

theorem ndunion_le_add (s t : Multiset α) : ndunion s t ≤ s + t :=
  Quot.induction_on₂ s t fun _ _ => (union_sublist_append _ _).subperm

theorem ndunion_le {s t u : Multiset α} : ndunion s t ≤ u ↔ s ⊆ u ∧ t ≤ u :=
  Multiset.induction_on s (by simp [zero_ndunion])
    (fun _ _ h =>
      by simp only [cons_ndunion, ndinsert_le, and_comm, cons_subset, and_left_comm, h,
        and_assoc])

theorem subset_ndunion_left (s t : Multiset α) : s ⊆ ndunion s t := fun _ h =>
  mem_ndunion.2 <| Or.inl h

theorem le_ndunion_left {s} (t : Multiset α) (d : Nodup s) : s ≤ ndunion s t :=
  (le_iff_subset d).2 <| subset_ndunion_left _ _

theorem ndunion_le_union (s t : Multiset α) : ndunion s t ≤ s ∪ t :=
  ndunion_le.2 ⟨subset_of_le le_union_left, le_union_right⟩

theorem Nodup.ndunion (s : Multiset α) {t : Multiset α} : Nodup t → Nodup (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => List.Nodup.union _

@[simp]
theorem ndunion_eq_union {s t : Multiset α} (d : Nodup s) : ndunion s t = s ∪ t :=
  le_antisymm (ndunion_le_union _ _) <| union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

theorem dedup_add (s t : Multiset α) : dedup (s + t) = ndunion s (dedup t) :=
  Quot.induction_on₂ s t fun _ _ => congr_arg ((↑) : List α → Multiset α) <| dedup_append _ _

theorem Disjoint.ndunion_eq {s t : Multiset α} (h : Disjoint s t) :
    s.ndunion t = s.dedup + t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Disjoint.union_eq <| by simpa using h

theorem Subset.ndunion_eq_right {s t : Multiset α} (h : s ⊆ t) : s.ndunion t = t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Subset.union_eq_right h

/-! ### finset inter -/


/-- `ndinter s t` is the lift of the list `∩` operation. This operation
  does not respect multiplicities, unlike `s ∩ t`, but it is suitable as
  an intersection operation on `Finset`. (`s ∩ t` would also work as an intersection operation
  on finset, but this is more efficient.) -/
def ndinter (s t : Multiset α) : Multiset α :=
  filter (· ∈ t) s

@[simp]
theorem coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ = (l₁ ∩ l₂ : List α) := by
  simp only [ndinter, mem_coe, filter_coe, coe_eq_coe, ← elem_eq_mem]
  apply Perm.refl

@[simp]
theorem zero_ndinter (s : Multiset α) : ndinter 0 s = 0 :=
  rfl

@[simp]
theorem cons_ndinter_of_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∈ t) :
    ndinter (a ::ₘ s) t = a ::ₘ ndinter s t := by simp [ndinter, h]

@[simp]
theorem ndinter_cons_of_notMem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t) :
    ndinter (a ::ₘ s) t = ndinter s t := by simp [ndinter, h]

@[deprecated (since := "2025-05-23")] alias ndinter_cons_of_not_mem := ndinter_cons_of_notMem

@[simp]
theorem mem_ndinter {s t : Multiset α} {a : α} : a ∈ ndinter s t ↔ a ∈ s ∧ a ∈ t := by
  simp [ndinter, mem_filter]

-- simp can prove this once we have `ndinter_eq_inter` and `Nodup.inter` a few lines down.
theorem Nodup.ndinter {s : Multiset α} (t : Multiset α) : Nodup s → Nodup (ndinter s t) :=
  Nodup.filter _

theorem le_ndinter {s t u : Multiset α} : s ≤ ndinter t u ↔ s ≤ t ∧ s ⊆ u := by
  simp [ndinter, le_filter, subset_iff]

theorem ndinter_le_left (s t : Multiset α) : ndinter s t ≤ s :=
  (le_ndinter.1 le_rfl).1

theorem ndinter_subset_left (s t : Multiset α) : ndinter s t ⊆ s :=
  subset_of_le (ndinter_le_left s t)

theorem ndinter_subset_right (s t : Multiset α) : ndinter s t ⊆ t :=
  (le_ndinter.1 le_rfl).2

theorem ndinter_le_right {s} (t : Multiset α) (d : Nodup s) : ndinter s t ≤ t :=
  (le_iff_subset <| d.ndinter _).2 <| ndinter_subset_right _ _

theorem inter_le_ndinter (s t : Multiset α) : s ∩ t ≤ ndinter s t :=
  le_ndinter.2 ⟨inter_le_left, subset_of_le inter_le_right⟩

@[simp]
theorem ndinter_eq_inter {s t : Multiset α} (d : Nodup s) : ndinter s t = s ∩ t :=
  le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

@[simp]
theorem Nodup.inter {s : Multiset α} (t : Multiset α) (d : Nodup s) : Nodup (s ∩ t) := by
  rw [← ndinter_eq_inter d]
  exact d.filter _

theorem ndinter_eq_zero_iff_disjoint {s t : Multiset α} : ndinter s t = 0 ↔ Disjoint s t := by
  rw [← subset_zero]; simp [subset_iff, disjoint_left]

alias ⟨_, Disjoint.ndinter_eq_zero⟩ := ndinter_eq_zero_iff_disjoint

theorem Subset.ndinter_eq_left {s t : Multiset α} (h : s ⊆ t) : s.ndinter t = s := by
  induction s, t using Quot.induction_on₂
  rw [quot_mk_to_coe'', quot_mk_to_coe'', coe_ndinter, List.Subset.inter_eq_left h]

end Multiset
