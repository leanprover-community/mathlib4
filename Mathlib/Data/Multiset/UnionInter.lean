/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Perm.Lattice
import Mathlib.Data.Multiset.Filter
import Mathlib.Order.MinMax
import Mathlib.Logic.Pairwise

/-!
# Distributive lattice structure on multisets

This file defines an instance `DistribLattice (Multiset α)` using the union and intersection
operators:

* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-! ### Union -/

/-- `s ∪ t` is the multiset such that the multiplicity of each `a` in it is the maximum of the
multiplicity of `a` in `s` and `t`. This is the supremum of multisets. -/
def union (s t : Multiset α) : Multiset α := s - t + t

instance : Union (Multiset α) :=
  ⟨union⟩

lemma union_def (s t : Multiset α) : s ∪ t = s - t + t := rfl

lemma le_union_left : s ≤ s ∪ t := Multiset.le_sub_add
lemma le_union_right : t ≤ s ∪ t := le_add_left _ _
lemma eq_union_left : t ≤ s → s ∪ t = s := Multiset.sub_add_cancel

@[gcongr]
lemma union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
  Multiset.add_le_add_right <| Multiset.sub_le_sub_right h

lemma union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u := by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]
lemma mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]
lemma map_union [DecidableEq β] {f : α → β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s ∪ t) = map f s ∪ map f t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append, List.map_diff finj])

@[simp] lemma zero_union : 0 ∪ s = s := by simp [union_def, Multiset.zero_sub]
@[simp] lemma union_zero : s ∪ 0 = s := by simp [union_def]

@[simp]
lemma count_union (a : α) (s t : Multiset α) : count a (s ∪ t) = max (count a s) (count a t) := by
  simp [(· ∪ ·), union, Nat.sub_add_eq_max]

@[simp] lemma filter_union (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∪ t) = filter p s ∪ filter p t := by simp [(· ∪ ·), union]

/-! ### Intersection -/

/-- `s ∩ t` is the multiset such that the multiplicity of each `a` in it is the minimum of the
multiplicity of `a` in `s` and `t`. This is the infimum of multisets. -/
def inter (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.bagInter p₂

instance : Inter (Multiset α) := ⟨inter⟩

@[simp] lemma inter_zero (s : Multiset α) : s ∩ 0 = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil

@[simp] lemma zero_inter (s : Multiset α) : 0 ∩ s = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]
lemma cons_inter_of_pos (s : Multiset α) : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_pos _ h

@[simp]
lemma cons_inter_of_neg (s : Multiset α) : a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_neg _ h

lemma inter_le_left : s ∩ t ≤ s :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => (bagInter_sublist_left _ _).subperm

lemma inter_le_right : s ∩ t ≤ t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (zero_inter t).symm ▸ zero_le _
  | cons a s IH =>
    by_cases h : a ∈ t
    · simpa [h] using cons_le_cons a (IH (t := t.erase a))
    · simp [h, IH]

lemma le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u := by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intros s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a ∈ u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_notMem <| mt (mem_of_le h₂) h).1 h₁) h₂

@[simp]
lemma mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁, cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

instance instLattice : Lattice (Multiset α) where
  sup := (· ∪ ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· ∩ ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right

@[simp] lemma sup_eq_union (s t : Multiset α) : s ⊔ t = s ∪ t := rfl
@[simp] lemma inf_eq_inter (s t : Multiset α) : s ⊓ t = s ∩ t := rfl

@[simp] lemma le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u := le_inf_iff
@[simp] lemma union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u := sup_le_iff

lemma union_comm (s t : Multiset α) : s ∪ t = t ∪ s := sup_comm ..
lemma inter_comm (s t : Multiset α) : s ∩ t = t ∩ s := inf_comm ..

lemma eq_union_right (h : s ≤ t) : s ∪ t = t := by rw [union_comm, eq_union_left h]

@[gcongr] lemma union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t := sup_le_sup_left h _

lemma union_le_add (s t : Multiset α) : s ∪ t ≤ s + t := union_le (le_add_right ..) (le_add_left ..)

lemma union_add_distrib (s t u : Multiset α) : s ∪ t + u = s + u ∪ (t + u) := by
  simpa [(· ∪ ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm, Multiset.sub_add_eq_sub_sub, Multiset.add_sub_cancel_right]

lemma add_union_distrib (s t u : Multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := by
  rw [Multiset.add_comm, union_add_distrib, s.add_comm, s.add_comm]

lemma cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t

lemma inter_add_distrib (s t u : Multiset α) : s ∩ t + u = (s + u) ∩ (t + u) := by
  by_contra! h
  obtain ⟨a, ha⟩ := lt_iff_cons_le.1 <| h.lt_of_le <| le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
  exact (lt_cons_self (s ∩ t) a).not_ge <| le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_right))

lemma add_inter_distrib (s t u : Multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := by
  rw [Multiset.add_comm, inter_add_distrib, s.add_comm, s.add_comm]

lemma cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := by
  simp

lemma union_add_inter (s t : Multiset α) : s ∪ t + s ∩ t = s + t := by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right le_union_left

lemma sub_add_inter (s t : Multiset α) : s - t + s ∩ t = s := by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a ∈ s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_notMem h, IH]

lemma sub_inter (s t : Multiset α) : s - s ∩ t = s - t :=
  (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]
lemma count_inter (a : α) (s t : Multiset α) : count a (s ∩ t) = min (count a s) (count a t) := by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add, sub_add_inter, count_sub, Nat.sub_add_min_cancel]

@[simp]
lemma coe_inter (s t : List α) : (s ∩ t : Multiset α) = (s.bagInter t : List α) := by ext; simp

instance instDistribLattice : DistribLattice (Multiset α) where
  le_sup_inf s t u := ge_of_eq <| ext.2 fun a ↦ by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]

@[simp] lemma filter_inter (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∩ t) = filter p s ∩ filter p t :=
  le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right)) <|
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]
theorem replicate_inter (n : ℕ) (x : α) (s : Multiset α) :
    replicate n x ∩ s = replicate (min n (s.count x)) x := by
  ext y
  rw [count_inter, count_replicate, count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]
theorem inter_replicate (s : Multiset α) (n : ℕ) (x : α) :
    s ∩ replicate n x = replicate (min (s.count x) n) x := by
  rw [inter_comm, replicate_inter, min_comm]

end sub

theorem inter_add_sub_of_add_eq_add [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q) :
    (N ∩ Q) + (P - M) = N := by
  ext x
  rw [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.mem_add, Multiset.count_add]
  omega

/-! ### Disjoint multisets -/


/-- `Disjoint s t` means that `s` and `t` have no elements in common. -/
@[deprecated _root_.Disjoint (since := "2024-11-01")]
protected def Disjoint (s t : Multiset α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → a ∈ t → False

theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := by
  refine ⟨fun h a hs ht ↦ ?_, fun h u hs ht ↦ ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha ↦ h (subset_of_le hs ha) (subset_of_le ht ha)

alias ⟨_root_.Disjoint.notMem_of_mem_left_multiset, _⟩ := disjoint_left

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_left_multiset := Disjoint.notMem_of_mem_left_multiset

@[simp, norm_cast]
theorem coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂ :=
  disjoint_left

@[deprecated (since := "2024-11-01")] protected alias Disjoint.symm := _root_.Disjoint.symm
@[deprecated (since := "2024-11-01")] protected alias disjoint_comm := _root_.disjoint_comm

theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  disjoint_comm.trans disjoint_left

alias ⟨_root_.Disjoint.notMem_of_mem_right_multiset, _⟩ := disjoint_right

@[deprecated (since := "2025-05-23")]
alias _root_.Disjoint.not_mem_of_mem_right_multiset := Disjoint.notMem_of_mem_right_multiset

theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : Multiset α} (h : s ⊆ u) (d : Disjoint u t) :
    Disjoint s t :=
  disjoint_left.mpr fun ha ↦ disjoint_left.mp d <| h ha

theorem disjoint_of_subset_right {s t u : Multiset α} (h : t ⊆ u) (d : Disjoint s u) :
    Disjoint s t :=
  (disjoint_of_subset_left h d.symm).symm

@[deprecated (since := "2024-11-01")] protected alias disjoint_of_le_left := Disjoint.mono_left
@[deprecated (since := "2024-11-01")] protected alias disjoint_of_le_right := Disjoint.mono_right

@[simp]
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l := disjoint_bot_left

@[simp]
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [disjoint_left]

@[simp]
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [_root_.disjoint_comm, singleton_disjoint]

@[simp]
theorem disjoint_add_left {s t u : Multiset α} :
    Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u := by simp [disjoint_left, or_imp, forall_and]

@[simp]
theorem disjoint_add_right {s t u : Multiset α} :
    Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [_root_.disjoint_comm, disjoint_add_left]; tauto

@[simp]
theorem disjoint_cons_left {a : α} {s t : Multiset α} :
    Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
  (@disjoint_add_left _ {a} s t).trans <| by rw [singleton_disjoint]

@[simp]
theorem disjoint_cons_right {a : α} {s t : Multiset α} :
    Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm, disjoint_cons_left]; tauto

theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s ∩ t = 0 ↔ Disjoint s t := by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} :
    Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=  disjoint_sup_left

@[simp]
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} :
    Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right

theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s + t = s ∪ t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]

lemma add_eq_union_left_of_le [DecidableEq α] {s t u : Multiset α} (h : t ≤ s) :
    u + s = u ∪ t ↔ Disjoint u s ∧ s = t := by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0

lemma add_eq_union_right_of_le [DecidableEq α] {x y z : Multiset α} (h : z ≤ y) :
    x + y = x ∪ z ↔ y = z ∧ Disjoint x y := by
  simpa only [and_comm] using add_eq_union_left_of_le h

theorem disjoint_map_map {f : α → γ} {g : β → γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ ∀ a ∈ s, ∀ b ∈ t, f a ≠ g b := by
  simp [disjoint_iff_ne]

theorem map_set_pairwise {f : α → β} {r : β → β → Prop} {m : Multiset α}
    (h : { a | a ∈ m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b ∈ m.map f }.Pairwise r :=
  fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

section Nodup

variable {s t : Multiset α} {a : α}

theorem nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t :=
  Quotient.inductionOn₂ s t fun _ _ => by simp [nodup_append]

theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2

theorem Nodup.add_iff (d₁ : Nodup s) (d₂ : Nodup t) : Nodup (s + t) ↔ Disjoint s t := by
  simp [nodup_add, d₁, d₂]

lemma Nodup.inter_left [DecidableEq α] (t) : Nodup s → Nodup (s ∩ t) := nodup_of_le inter_le_left
lemma Nodup.inter_right [DecidableEq α] (s) : Nodup t → Nodup (s ∩ t) := nodup_of_le inter_le_right

@[simp]
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s ∪ t) ↔ Nodup s ∧ Nodup t :=
  ⟨fun h => ⟨nodup_of_le le_union_left h, nodup_of_le le_union_right h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

end Nodup

end Multiset
