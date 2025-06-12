/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.ZeroCons

/-!
# Counting multiplicity in a multiset

-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section

variable (p : α → Prop) [DecidablePred p]


/-! ### countP -/


/-- `countP p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countP (s : Multiset α) : ℕ :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]
theorem coe_countP (l : List α) : countP p l = l.countP p :=
  rfl

@[simp]
theorem countP_zero : countP p 0 = 0 :=
  rfl

variable {p}

@[simp]
theorem countP_cons_of_pos {a : α} (s) : p a → countP p (a ::ₘ s) = countP p s + 1 :=
  Quot.inductionOn s <| by simpa using fun _ => List.countP_cons_of_pos (p := (p ·))

@[simp]
theorem countP_cons_of_neg {a : α} (s) : ¬p a → countP p (a ::ₘ s) = countP p s :=
  Quot.inductionOn s <| by simpa using fun _ => List.countP_cons_of_neg (p := (p ·))

variable (p)

theorem countP_cons (b : α) (s) : countP p (b ::ₘ s) = countP p s + if p b then 1 else 0 :=
  Quot.inductionOn s <| by simp [List.countP_cons]

theorem countP_le_card (s) : countP p s ≤ card s :=
  Quot.inductionOn s fun _l => countP_le_length (p := (p ·))

theorem card_eq_countP_add_countP (s) : card s = countP p s + countP (fun x => ¬p x) s :=
  Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]
theorem countP_le_of_le {s t} (h : s ≤ t) : countP p s ≤ countP p t :=
  leInductionOn h fun s => s.countP_le

@[simp]
theorem countP_True {s : Multiset α} : countP (fun _ => True) s = card s :=
  Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]
theorem countP_False {s : Multiset α} : countP (fun _ => False) s = 0 :=
  Quot.inductionOn s fun _l => congrFun List.countP_false _

lemma countP_attach (s : Multiset α) : s.attach.countP (fun a : {a // a ∈ s} ↦ p a) = s.countP p :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP, coe_attach, coe_countP, ← List.countP_attach (l := l)]
    rfl

variable {p}

theorem countP_pos {s} : 0 < countP p s ↔ ∃ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp

theorem countP_eq_zero {s} : countP p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]

theorem countP_eq_card {s} : countP p s = card s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_length]

theorem countP_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countP p s :=
  countP_pos.2 ⟨_, h, pa⟩

@[congr]
theorem countP_congr {s s' : Multiset α} (hs : s = s')
    {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀ x ∈ s, p x = p' x) : s.countP p = s'.countP p' := by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : Multiset α → ℕ :=
  countP (a = ·)

@[simp]
theorem coe_count (a : α) (l : List α) : count a (ofList l) = l.count a := by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl

@[simp]
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = count a s + 1 :=
  countP_cons_of_pos _ <| rfl

@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
  countP_cons_of_neg _ <| h

theorem count_le_card (a : α) (s) : count a s ≤ card s :=
  countP_le_card _ _

@[gcongr]
theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
  countP_le_of_le _

theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)

theorem count_cons (a b : α) (s : Multiset α) :
    count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countP_cons (a = ·) _ _

theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 :=
  count_eq_one_of_mem (nodup_singleton a) <| mem_singleton_self a

theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]
lemma count_attach (a : {x // x ∈ s}) : s.attach.count a = s.count ↑a :=
  Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _

theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a ∈ s := by simp [count, countP_pos]

theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 ≤ count a s ↔ a ∈ s := by
  rw [succ_le_iff, count_pos]

@[simp]
theorem count_eq_zero_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
  by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')

@[deprecated (since := "2025-05-23")] alias count_eq_zero_of_not_mem := count_eq_zero_of_notMem

lemma count_ne_zero {a : α} : count a s ≠ 0 ↔ a ∈ s := Nat.pos_iff_ne_zero.symm.trans count_pos

@[simp] lemma count_eq_zero {a : α} : count a s = 0 ↔ a ∉ s := count_ne_zero.not_right

theorem count_eq_card {a : α} {s} : count a s = card s ↔ ∀ x ∈ s, a = x := by
  simp [countP_eq_card, count, @eq_comm _ a]

theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans <| by
    simp only [quot_mk_to_coe, mem_coe, coe_count, decide_eq_true_eq]
    apply perm_iff_count

@[ext]
theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
  ext.2

lemma count_injective : Injective fun (s : Multiset α) a ↦ s.count a :=
  fun _s _t hst ↦ ext' <| congr_fun hst

theorem le_iff_count {s t : Multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
  Quotient.inductionOn₂ s t fun _ _ ↦ by simp [subperm_iff_count]

end

/-! ### Lift a relation to `Multiset`s -/

section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

theorem Rel.countP_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] {s t : Multiset α} (x : α)
    [DecidablePred (r x)] (h : Rel r s t) : countP (r x) s = countP (r x) t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [rel_zero_left.mp h]
  | cons y s ih =>
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons, countP_cons, ih hb2]
    simp only [decide_eq_true_eq, Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

end Rel

section Nodup

variable {s : Multiset α} {a : α}

theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ ∀ a, count a s ≤ 1 :=
  Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, mem_coe, coe_count]
    exact List.nodup_iff_count_le_one

theorem nodup_iff_count_eq_one [DecidableEq α] : Nodup s ↔ ∀ a ∈ s, count a s = 1 :=
  Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a ∈ s) :
    count a s = 1 :=
  nodup_iff_count_eq_one.mp d a h

theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
    count a s = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_notMem h

end Nodup

end Multiset
