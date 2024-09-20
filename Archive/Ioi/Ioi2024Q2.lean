/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.List.Sections
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.List
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.SlimCheck

theorem List.leftpad_of_length_le {α : Type*} (n : ℕ) (a : α) (l : List α) (h : n ≤ l.length) :
    l.leftpad n a = l := by simp [leftpad, h]

lemma List.IsPrefix.iff_getElem {α : Type*} {l₁ l₂ : List α} :
    l₁ <+: l₂ ↔ ∃ (h : l₁.length ≤ l₂.length), ∀ x : Fin l₁.length, l₁[x] = l₂[x] where
  mp h := ⟨h.length_le, fun _ ↦ h.getElem _⟩
  mpr h := by
    obtain ⟨hl, h⟩ := h
    induction l₂ generalizing l₁
    · simpa using hl
    case cons head tail tail_ih =>
    cases l₁
    · simp
    case cons head2 tail2 =>
    simp [Fin.forall_fin_succ] at hl h
    simp only [h.1, cons_prefix_cons, true_and]
    apply tail_ih hl h.2

lemma List.IsPrefix.eq_of_length_le {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂)
    (h₂ : l₂.length ≤ l₁.length) : l₁ = l₂ :=
  h.eq_of_length (h₂.antisymm' h.length_le)

def List.splitSizes {α : Type*} : List α → List ℕ → List (List α)
| _, [] => []
| x, n::ns =>
  let (x0, x1) := x.splitAt n
  x0 :: x1.splitSizes ns

@[simp]
theorem List.length_splitSizes {α : Type*} (l : List α) (sz : List ℕ) :
    (l.splitSizes sz).length = sz.length := by
  induction sz generalizing l
  · simp [splitSizes]
  · simp [splitSizes, ‹∀ (l : List α), _›]

@[simp]
theorem List.join_splitSizes {α : Type*} (l : List α) (sz : List ℕ) (h : l.length ≤ sz.sum) :
    (l.splitSizes sz).join = l := by
  induction sz generalizing l
  · simp_all [splitSizes]
  case cons head tail ih =>
    simp only [splitSizes, splitAt_eq, join_cons]
    rw [ih, take_append_drop]
    simpa [add_comm] using h

theorem List.length_mem_splitSizes {α : Type*} (l : List α) (sz : List ℕ) (b : ℕ)
    (h : ∀ n ∈ sz, n ≤ b) : ∀ l₂ ∈ l.splitSizes sz, l₂.length ≤ b := by
  induction sz generalizing l
  · simp [splitSizes]
  case cons _ _ ih =>
    simp at h
    simp [splitSizes, h]
    apply ih _ h.2

def Finset.next {n : ℕ} (s : Finset (Fin n)) : Equiv.Perm (Fin n) := (s.sort (· ≤ ·)).formPerm

theorem Finset.next_lt_iff {n : ℕ} (s : Finset (Fin n)) (hs : s.Nontrivial) (v : Fin n) :
    s.next v < v ↔ v = s.max' hs.nonempty := by
  rw [Finset.max'_eq_sorted_last, next]
  constructor
  · intro hv
    contrapose! hv
    by_cases hv2 : v ∈ s
    · rw [← mem_sort (· ≤ ·)] at hv2
      have := List.indexOf_lt_length.2 hv2
      rw [← List.getElem_indexOf this] at hv ⊢
      rw [List.formPerm_apply_lt_getElem]
      apply List.Sorted.rel_get_of_lt
      · simp
      · refine Set.Ici_subset_Ioi.mp fun ⦃a⦄ ↦ id
      · simp
      · replace hv : List.indexOf v (sort (fun x1 x2 ↦ x1 ≤ x2) s) ≠
          (sort (fun x1 x2 ↦ x1 ≤ x2) s).length - 1 := fun x ↦ hv (by simp [x])
        omega
    · rw [List.formPerm_apply_of_not_mem]
      simpa
  · rintro rfl
    rw [List.formPerm_apply_getElem, Nat.sub_one_add_one]
    · simp only [length_sort, Nat.mod_self]
      apply lt_of_le_of_ne
      · apply List.Sorted.rel_get_of_le
        · simp
        · simp
      · simp [List.Nodup.getElem_inj_iff]
        replace hs := Finset.one_lt_card_iff_nontrivial.2 hs
        omega
    · simp only [length_sort, ne_eq, card_eq_zero]
      rintro rfl
      simp at hs
    · simp



lemma Fin.intCast_val_sub {n : ℕ} (a b : Fin n) :
    ((a - b).val : ℤ) = a.val - b.val + if b ≤ a then 0 else n := by
  split
  · rw [Fin.sub_val_of_le]
    omega
    assumption
  · simp at ‹¬b ≤ a›
    rw [Fin.coe_sub_iff_lt.2 ‹_›]
    omega

theorem cyc_sum {n : ℕ} (s : Finset (Fin n)) (hs : s.Nontrivial) :
    ∑ v ∈ s, (s.next v - v).val = n := by
  zify
  simp only [Fin.intCast_val_sub, Nat.cast_ite, Nat.cast_zero, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  conv =>
    enter [1, 1, 1]
    apply (s.sum_map s.next (fun x : Fin n ↦ (x.val : ℤ))).symm
  rw [Finset.map_eq_of_subset]
  · simp only [sub_self, zero_add, not_not]
    simp_rw (config := { singlePass := true }) [← ite_not, not_le,
      Finset.next_lt_iff s hs, Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
    rw [Finset.filter_eq']
    simp [Finset.max'_mem]
  · intro x hx
    simp at hx
    rw [← Finset.mem_sort (· ≤ ·)]
    rw [(show x = s.next (s.next.symm x) by simp)]
    apply List.formPerm_apply_mem_of_mem
    simpa

def List.pad (l : List Bool) (n : ℕ) : List Bool :=
  (false :: l).leftpad n true

lemma List.length_pad (l : List Bool) {n : ℕ} (hl : l.length < n) : (l.pad n).length = n := by
  simpa [pad]

def List.unpad (l : List Bool) : List Bool :=
  (l.dropWhile id).tail

def List.unpad_pad (l : List Bool) (n : ℕ) : (l.pad n).unpad = l := by
  simp [pad, leftpad, unpad]

def Aisha := List Bool → Finset (Fin 31) → List (Mathlib.Vector Bool 31) →
  Option (Mathlib.Vector Bool 31)

def Basma := List (Mathlib.Vector Bool 31) → List Bool

def Aisha.ValidPreRun (aisha : Aisha) (msg : List Bool) (comp : Finset (Fin 31))
    (run : List (Mathlib.Vector Bool 31)) : Prop :=
  ∀ i : Fin run.length, (aisha msg comp (run.take i)).any
    (fun v ↦ ∀ j ∉ comp, run[i][j] = v[j])

def Aisha.Small (aisha : Aisha) : Prop :=
  ∀ msg comp run, 1 ≤ msg.length → msg.length ≤ 1024 → comp.card = 15 →
      aisha.ValidPreRun msg comp run → run.length ≤ 66

def Aisha.ValidRun (aisha : Aisha) (msg : List Bool) (comp : Finset (Fin 31))
    (run : List (Mathlib.Vector Bool 31)) : Prop :=
  aisha.ValidPreRun msg comp run ∧ aisha msg comp run = none

def Aisha.Correct (aisha : Aisha) (basma : Basma) : Prop :=
  ∀ msg comp run, 1 ≤ msg.length → msg.length ≤ 1024 →
    comp.card = 15 → aisha.ValidRun msg comp run → basma run = msg

def SimpleAisha := List Bool → Finset (Fin 31) → List (Mathlib.Vector Bool 31)

def SimpleAisha.toAisha (self : SimpleAisha) : Aisha :=
  fun msg comp sf ↦ (self (msg.pad 1025) comp).get? sf.length

def SimpleBasma := List (Mathlib.Vector Bool 31) → List Bool

def SimpleBasma.toBasma (self : SimpleBasma) : Basma :=
  fun run ↦ (self run).unpad

theorem SimpleAisha.toAisha_prefix_of_validPreRun (self : SimpleAisha) (msg : List Bool)
    (comp : Finset (Fin 31)) (run : List (Mathlib.Vector Bool 31))
    (h : self.toAisha.ValidPreRun msg comp run) :
    ∀ v ∉ comp, run.map (·[v]) <+: (self (msg.pad 1025) comp).map (·[v]) := by
  intro v hv
  simp only [Aisha.ValidPreRun] at h
  rw [List.IsPrefix.iff_getElem]
  use ?a
  · intro x
    rw [Fin.getElem_fin, Fin.getElem_fin]
    simp only [Fin.getElem_fin, List.getElem_map]
    specialize h (x.cast (by simp))
    simp only [Fin.getElem_fin, Fin.coe_cast, toAisha, List.length_take, List.get?_eq_getElem?] at h
    rw [min_eq_left, List.getElem?_eq_getElem] at h
    simp only [Option.any_some, decide_eq_true_eq] at h
    apply h v hv
    simpa using x.2.le
  · cases run
    · simp
    · simp at h
      rw [Fin.forall_fin_succ'] at h
      obtain ⟨-, h⟩ := h
      simp [toAisha] at h
      simp only [Fin.getElem_fin, List.map_cons, List.length_cons, List.length_map, Nat.succ_le_iff]
      by_contra! nh
      absurd List.getElem?_len_le nh
      rintro h2
      simp [h2] at h

theorem SimpleAisha.toAisha_eq_of_validRun (self : SimpleAisha) (msg : List Bool)
    (comp : Finset (Fin 31)) (run : List (Mathlib.Vector Bool 31))
    (h : self.toAisha.ValidRun msg comp run) :
    ∀ v ∉ comp, run.map (·[v]) = (self (msg.pad 1025) comp).map (·[v]) := by
  simp only [Aisha.ValidRun] at h
  intro v hv
  apply (self.toAisha_prefix_of_validPreRun msg comp run h.1 v hv).eq_of_length_le
  simpa [toAisha] using h.2

def SimpleAisha.winningStrat' (msg : List Bool) (comp : Finset (Fin 31)) :
    List (List Bool) :=
  (msg.splitSizes ((List.finRange 31).map (fun v ↦ if v ∈ compᶜ then
    65 - (compᶜ.next v - v).val else 0))).map
    (fun l ↦ l.pad 66)

@[simp]
lemma SimpleAisha.winningStrat'_length (msg : List Bool) (comp : Finset (Fin 31)) :
    (winningStrat' msg comp).length = 31 := by
  simp [winningStrat']

@[simp]
lemma SimpleAisha.winningStrat'_length_of_mem (msg : List Bool)
    (comp : Finset (Fin 31)) : ∀ x ∈ winningStrat' msg comp, x.length = 66 := by
  intro x hx
  simp only [winningStrat', Finset.mem_compl, Fin.isValue, dite_not, List.mem_map] at hx
  obtain ⟨a, ha1, rfl⟩ := hx
  apply List.length_pad
  apply Nat.lt_succ_of_le
  revert a
  apply List.length_mem_splitSizes
  simp
  intro a
  split <;> simp

def SimpleAisha.winningStrat : SimpleAisha := fun msg comp ↦
    (List.finRange 66).map (fun x ↦ ⟨(List.finRange 31).map fun y ↦
      ((winningStrat' msg comp)[y]'(by simp))[x]'(by
        rw [SimpleAisha.winningStrat'_length_of_mem msg comp]
        · simp
        · apply List.getElem_mem
        ),
      by simp⟩)

def Aisha.winningStrat : Aisha := SimpleAisha.winningStrat.toAisha

def SimpleBasma.winningStrat_msg (msg : Mathlib.Vector (List Bool) 31) (comp : Finset (Fin 31)) :
    List Bool :=
  (List.finRange 31).bind fun i ↦ if i ∈ comp then [] else msg[i].unpad

def SimpleBasma.winningStrat_comp (msg : Mathlib.Vector (List Bool) 31) (comp : Finset (Fin 31)) :
    List Bool :=
  (List.finRange 31).bind fun i ↦ if i ∈ comp then [] else msg[i].unpad

def SimpleBasma.winningStrat : SimpleBasma := fun run ↦ sorry

def Basma.winningStrat : Basma := SimpleBasma.winningStrat.toBasma

theorem IOI2024Q2 :
    Aisha.winningStrat.Small ∧
      Aisha.winningStrat.Correct Basma.winningStrat := by
  sorry
