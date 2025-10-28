/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Count
import Mathlib.Data.List.Count

/-!
# Sum and difference of multisets

This file defines the following operations on multisets:

* `Add (Multiset α)` instance: `s + t` adds the multiplicities of the elements of `s` and `t`
* `Sub (Multiset α)` instance: `s - t` subtracts the multiplicities of the elements of `s` and `t`
* `Multiset.erase`: `s.erase x` reduces the multiplicity of `x` in `s` by one.

## Notation (defined later)

* `s + t`: The multiset for which the number of occurrences of each `a` is the sum of the
  occurrences of `a` in `s` and `t`.
* `s - t`: The multiset for which the number of occurrences of each `a` is the difference of the
  occurrences of `a` in `s` and `t`.

-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### Additive monoid -/

section add
variable {s t u : Multiset α}

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun _ _ _ _ p₁ p₂ =>
    Quot.sound <| p₁.append p₂

instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

@[simp]
theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl

protected lemma add_le_add_iff_left : s + t ≤ s + u ↔ t ≤ u :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_left _

protected lemma add_le_add_iff_right : s + u ≤ t + u ↔ s ≤ t :=
  Quotient.inductionOn₃ s t u fun _ _ _ => subperm_append_right _

protected alias ⟨le_of_add_le_add_left, add_le_add_left⟩ := Multiset.add_le_add_iff_left
protected alias ⟨le_of_add_le_add_right, add_le_add_right⟩ := Multiset.add_le_add_iff_right

protected lemma add_comm (s t : Multiset α) : s + t = t + s :=
  Quotient.inductionOn₂ s t fun _ _ ↦ Quot.sound perm_append_comm

protected lemma add_assoc (s t u : Multiset α) : s + t + u = s + (t + u) :=
  Quotient.inductionOn₃ s t u fun _ _ _ ↦ congr_arg _ <| append_assoc ..

@[simp high]
protected lemma zero_add (s : Multiset α) : 0 + s = s := Quotient.inductionOn s fun _ ↦ rfl

@[simp high]
protected lemma add_zero (s : Multiset α) : s + 0 = s :=
  Quotient.inductionOn s fun l ↦ congr_arg _ <| append_nil l

lemma le_add_right (s t : Multiset α) : s ≤ s + t := by
  simpa using Multiset.add_le_add_left (zero_le t)

lemma le_add_left (s t : Multiset α) : s ≤ t + s := by
  simpa using Multiset.add_le_add_right (zero_le t)

lemma subset_add_left {s t : Multiset α} : s ⊆ s + t := subset_of_le <| le_add_right s t

lemma subset_add_right {s t : Multiset α} : s ⊆ t + s := subset_of_le <| le_add_left s t

theorem le_iff_exists_add {s t : Multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
  ⟨fun h =>
    leInductionOn h fun s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨_u, e⟩ => e.symm ▸ le_add_right _ _⟩

@[simp]
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_assoc]

@[simp]
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [Multiset.add_comm, cons_add, Multiset.add_comm]

@[simp, grind =]
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => mem_append

variable (p : α → Prop) [DecidablePred p]

@[simp]
theorem countP_add (s t) : countP p (s + t) = countP p s + countP p t :=
  Quotient.inductionOn₂ s t fun _ _ => countP_append

variable [DecidableEq α] in
@[simp]
theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
  countP_add _

protected lemma add_left_inj : s + u = t + u ↔ s = t := by classical simp [Multiset.ext]

protected lemma add_right_inj : s + t = s + u ↔ t = u := by classical simp [Multiset.ext]

@[simp]
theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  Quotient.inductionOn₂ s t fun _ _ => length_append

end add

/-! ### Erasing one copy of an element -/

section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the multiplicity of `a`. -/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun _l₁ _l₂ p => Quot.sound (p.erase a)

@[simp]
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a :=
  rfl

@[simp]
theorem erase_zero (a : α) : (0 : Multiset α).erase a = 0 :=
  rfl

@[simp]
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s :=
  Quot.inductionOn s fun l => congr_arg _ <| List.erase_cons_head a l

@[simp]
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a :=
  Quot.inductionOn s fun _ => congr_arg _ <| List.erase_cons_tail (not_beq_of_ne h)

@[simp]
theorem erase_singleton (a : α) : ({a} : Multiset α).erase a = 0 :=
  erase_cons_head a 0

@[simp]
theorem erase_of_notMem {a : α} {s : Multiset α} : a ∉ s → s.erase a = s :=
  Quot.inductionOn s fun _l h => congr_arg _ <| List.erase_of_not_mem h

@[deprecated (since := "2025-05-23")] alias erase_of_not_mem := erase_of_notMem

@[simp]
theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
  Quot.inductionOn s fun _l h => Quot.sound (perm_cons_erase h).symm

theorem erase_cons_tail_of_mem (h : a ∈ s) :
    (b ::ₘ s).erase a = b ::ₘ s.erase a := by
  rcases eq_or_ne a b with rfl | hab
  · simp [cons_erase h]
  · exact s.erase_cons_tail hab.symm

theorem le_cons_erase (s : Multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
  if h : a ∈ s then le_of_eq (cons_erase h).symm
  else by rw [erase_of_notMem h]; apply le_cons_self

theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a ∈ t ∧ s = t.erase a := by
  rw [Multiset.add_comm, singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
  · rintro ⟨h, rfl⟩
    exact cons_erase h

theorem erase_add_left_pos {a : α} {s : Multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_left l₂ h

theorem erase_add_right_pos {a : α} (s) (h : a ∈ t) : (s + t).erase a = s + t.erase a := by
  rw [Multiset.add_comm, erase_add_left_pos s h, Multiset.add_comm]

theorem erase_add_right_neg {a : α} {s : Multiset α} (t) :
    a ∉ s → (s + t).erase a = s + t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ l₂ h => congr_arg _ <| erase_append_right l₂ h

theorem erase_add_left_neg {a : α} (s) (h : a ∉ t) : (s + t).erase a = s.erase a + t := by
  rw [Multiset.add_comm, erase_add_right_neg s h, Multiset.add_comm]

theorem erase_le (a : α) (s : Multiset α) : s.erase a ≤ s :=
  Quot.inductionOn s fun _ => erase_sublist.subperm

@[simp]
theorem erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a ∈ s :=
  ⟨fun h => not_imp_comm.1 erase_of_notMem (ne_of_lt h), fun h => by
    simpa [h] using lt_cons_self (s.erase a) a⟩

theorem erase_subset (a : α) (s : Multiset α) : s.erase a ⊆ s :=
  subset_of_le (erase_le a s)

theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_erase_of_ne ab

theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a ∈ s.erase b → a ∈ s :=
  mem_of_subset (erase_subset _ _)

theorem erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
  Quot.inductionOn s fun l => congr_arg _ <| l.erase_comm a b

instance : RightCommutative erase (α := α) := ⟨erase_comm⟩

@[gcongr]
theorem erase_le_erase {s t : Multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
  leInductionOn h fun h => (h.erase _).subperm

theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
  ⟨fun h => le_trans (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a ∈ s then by rw [← cons_erase m] at h; exact (cons_le_cons_iff _).1 h
    else le_trans (erase_le _ _) ((le_cons_of_notMem m).1 h)⟩

@[simp]
theorem card_erase_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) = pred (card s) :=
  Quot.inductionOn s fun _l => length_erase_of_mem

-- @[simp] -- removed because LHS is not in simp normal form
theorem card_erase_add_one {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) + 1 = card s :=
  Quot.inductionOn s fun _l => length_erase_add_one

theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) < card s :=
  fun h => card_lt_card (erase_lt.mpr h)

theorem card_erase_le {a : α} {s : Multiset α} : card (s.erase a) ≤ card s :=
  card_le_card (erase_le a s)

theorem card_erase_eq_ite {a : α} {s : Multiset α} :
    card (s.erase a) = if a ∈ s then pred (card s) else card s := by
  by_cases h : a ∈ s
  · rwa [card_erase_of_mem h, if_pos]
  · rwa [erase_of_notMem h, if_neg]

@[simp]
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = count a s - 1 :=
  Quotient.inductionOn s fun l => by
    convert List.count_erase_self (a := a) (l := l) <;> rw [← coe_count] <;> simp

@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : Multiset α) :
    count a (erase s b) = count a s :=
  Quotient.inductionOn s fun l => by
    convert List.count_erase_of_ne ab (l := l) <;> rw [← coe_count] <;> simp

end Erase

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`.
(note that it is truncated subtraction, so `count a (s - t) = 0` if `count a s ≤ count a t`). -/
protected def sub (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.diff p₂

instance : Sub (Multiset α) := ⟨.sub⟩

@[simp]
lemma coe_sub (s t : List α) : (s - t : Multiset α) = s.diff t :=
  rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
@[simp high]
protected lemma sub_zero (s : Multiset α) : s - 0 = s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
lemma sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ <| diff_cons _ _ _

protected lemma zero_sub (t : Multiset α) : 0 - t = 0 :=
  Multiset.induction_on t rfl fun a s ih => by simp [ih]

@[simp]
lemma countP_sub {s t : Multiset α} :
    t ≤ s → ∀ (p : α → Prop) [DecidablePred p], countP p (s - t) = countP p s - countP p t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ hl _ _ ↦ List.countP_diff hl _

@[simp]
lemma count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t :=
  Quotient.inductionOn₂ s t <| by simp [List.count_diff]

/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
This is needed to prove `OrderedSub (Multiset α)`. -/
protected lemma sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t := by
  induction t using Multiset.induction_on generalizing s with
  | empty => simp [Multiset.sub_zero]
  | cons a s IH => simp [IH, erase_le_iff_le_cons]

/-- This is a special case of `tsub_le_iff_left`, which should be used instead of this. -/
protected lemma sub_le_iff_le_add' : s - t ≤ u ↔ s ≤ t + u := by
  rw [Multiset.sub_le_iff_le_add, Multiset.add_comm]

protected theorem sub_le_self (s t : Multiset α) : s - t ≤ s := by
  rw [Multiset.sub_le_iff_le_add]
  exact le_add_right _ _

protected lemma add_sub_assoc (hut : u ≤ t) : s + t - u = s + (t - u) := by
  ext a; simp [Nat.add_sub_assoc <| count_le_of_le _ hut]

protected lemma add_sub_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

protected lemma sub_add_cancel (hts : t ≤ s) : s - t + t = s := by
  ext a; simp [Nat.sub_add_cancel <| count_le_of_le _ hts]

protected lemma sub_add_eq_sub_sub : s - (t + u) = s - t - u := by ext; simp [Nat.sub_add_eq]

protected lemma le_sub_add : s ≤ s - t + t := Multiset.sub_le_iff_le_add.1 le_rfl
protected lemma le_add_sub : s ≤ t + (s - t) := Multiset.sub_le_iff_le_add'.1 le_rfl

protected lemma sub_le_sub_right (hst : s ≤ t) : s - u ≤ t - u :=
  Multiset.sub_le_iff_le_add'.mpr <| hst.trans Multiset.le_add_sub

protected lemma add_sub_cancel_right : s + t - t = s := by ext a; simp

protected lemma eq_sub_of_add_eq (hstu : s + t = u) : s = u - t := by
  rw [← hstu, Multiset.add_sub_cancel_right]

lemma cons_sub_of_le (a : α) {s t : Multiset α} (h : t ≤ s) : a ::ₘ s - t = a ::ₘ (s - t) := by
  rw [← singleton_add, ← singleton_add, Multiset.add_sub_assoc h]

@[simp]
lemma card_sub {s t : Multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
  Nat.eq_sub_of_add_eq <| by rw [← card_add, Multiset.sub_add_cancel h]

@[simp] theorem sub_singleton (a : α) (s : Multiset α) : s - {a} = s.erase a := by
  ext
  simp only [count_sub, count_singleton]
  split <;> simp_all

theorem mem_sub {a : α} {s t : Multiset α} :
    a ∈ s - t ↔ t.count a < s.count a := by
  rw [← count_pos, count_sub, Nat.sub_pos_iff_lt]

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
  induction hst with
  | zero => simpa using huv
  | cons hab hst ih => simpa using ih.cons hab

theorem rel_add_left {as₀ as₁} :
    ∀ {bs}, Rel r (as₀ + as₁) bs ↔ ∃ bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  @(Multiset.induction_on as₀ (by simp) fun a s ih bs ↦ by
      simp only [ih, cons_add, rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩)

theorem rel_add_right {as bs₀ bs₁} :
    Rel r as (bs₀ + bs₁) ↔ ∃ as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ := by
  rw [← rel_flip, rel_add_left]; simp [rel_flip]

end Rel

section Nodup

@[simp]
theorem nodup_singleton : ∀ a : α, Nodup ({a} : Multiset α) :=
  List.nodup_singleton

theorem not_nodup_pair : ∀ a : α, ¬Nodup (a ::ₘ a ::ₘ 0) :=
  List.not_nodup_pair

theorem Nodup.erase [DecidableEq α] (a : α) {l} : Nodup l → Nodup (l.erase a) :=
  nodup_of_le (erase_le _ _)

theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodup s) :
    a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le (Multiset.sub_le_self ..) h, fun h' => by
      refine count_eq_zero.1 ?_ h
      rw [count_sub a s t, Nat.sub_eq_zero_iff_le]
      exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le Multiset.le_sub_add h₁) h₂⟩

end Nodup

end Multiset
