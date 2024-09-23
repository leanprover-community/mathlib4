/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic.Zify
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Prod.Lex

open Mathlib

section Setup

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

theorem List.length_splitSizes_getElem {α : Type*} (l : List α) (sz : List ℕ) { i : ℕ }
    { hi : i < (l.splitSizes sz).length } :
    (l.splitSizes sz)[i].length ≤ sz[i]'(by simpa using hi) := by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitSizes, splitAt_eq]
    cases i
    · simp
    · simp only [getElem_cons_succ]
      apply tail_ih

theorem List.join_splitSizes {α : Type*} (l : List α) (sz : List ℕ) (h : l.length ≤ sz.sum) :
    (l.splitSizes sz).join = l := by
  induction sz generalizing l
  · simp_all [splitSizes]
  case cons head tail ih =>
    simp only [splitSizes, splitAt_eq, join_cons]
    rw [ih, take_append_drop]
    simpa [add_comm] using h

theorem List.splitSizes_map_length {α : Type*} (l : List α) (sz : List ℕ) (h : l.length = sz.sum) :
    (l.splitSizes sz).map length = sz := by
  induction sz generalizing l
  · simp_all [splitSizes]
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitSizes, splitAt_eq, map_cons, length_take, h, le_add_iff_nonneg_right, zero_le,
      min_eq_left, cons.injEq, true_and]
    rw [ih]
    simp [h]

theorem List.splitSizes_length_getElem {α : Type*} (l : List α) (sz : List ℕ)
    (h : l.length = sz.sum) (i : ℕ) (hi : i < (l.splitSizes sz).length) :
    (l.splitSizes sz)[i].length = sz[i]'(by simpa using hi) := by
  have := splitSizes_map_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi

theorem List.length_mem_splitSizes {α : Type*} (l : List α) (sz : List ℕ) (b : ℕ)
    (h : ∀ n ∈ sz, n ≤ b) : ∀ l₂ ∈ l.splitSizes sz, l₂.length ≤ b := by
  induction sz generalizing l
  · simp [splitSizes]
  case cons _ _ ih =>
    simp at h
    simp [splitSizes, h]
    apply ih _ h.2

theorem List.exists_mem_mem_of_mem_zipWith {α β γ : Type*} (f : α → β → γ) (xs : List α)
    (ys : List β) (v : γ) (h : v ∈ zipWith f xs ys) : ∃ x ∈ xs, ∃ y ∈ ys, f x y = v := by
  induction xs generalizing ys
  · simp at h
  case cons headX tailX ihX =>
  cases ys
  · simp at h
  case cons headY tailY =>
  simp only [zipWith_cons_cons, mem_cons] at h
  obtain h | h := h
  · simp [h]
  · obtain ⟨x, hx, y, hy, h⟩ := ihX _ h
    use x, (by simp [hx]), y, (by simp [hy]), h

def List.mtranspose {α : Type*} : List (List α) → List (List α)
| [] => []
| [a] => a.map ([·])
| a :: b => zipWith cons a (mtranspose b)

@[simp]
lemma List.mtranspose_nil {α : Type*} : ([] : List (List α)).mtranspose = [] := rfl

@[simp]
lemma List.mtranspose_single {α : Type*} (l : List α) : [l].mtranspose = l.map ([·]) := rfl

theorem List.length_of_mem_mtranspose {α : Type*} (l : List (List α)) :
    ∀ v ∈ l.mtranspose, v.length = l.length := by
  induction l
  · simp
  case cons head tail tail_ih =>
  cases tail
  · simp
  simp only [length_cons, mtranspose] at tail_ih ⊢
  intro v hv
  obtain ⟨_, _, v', hv', rfl⟩ := exists_mem_mem_of_mem_zipWith _ _ _ _ hv
  simp only [length_cons, add_left_inj]
  exact tail_ih _ hv'

theorem List.length_mtranspose {α : Type*} (l : List (List α)) :
    l.mtranspose.length = (l.map List.length).minimum?.getD 0 := by
  induction l
  · simp
  case cons head tail tail_ih =>
  cases tail
  · simp [List.minimum?_cons]
  simp only [mtranspose, length_zipWith, tail_ih, map_cons, minimum?_cons, Option.getD_some,
    foldl_cons, foldl_assoc]

theorem List.forall_mtranspose_length_le {α : Type*} (l : List (List α)) :
    ∀ v ∈ l, l.mtranspose.length ≤ v.length := by
  rw [List.length_mtranspose]
  intro v hv
  cases hl : (l.map length).minimum?
  · simp
  simp only [Option.getD_some]
  by_contra! nh
  apply Nat.add_one_le_of_lt at nh
  rw [List.le_minimum?_iff (by simp) hl] at nh
  specialize nh v.length (by simp only [mem_map]; use v, hv)
  omega

theorem List.mtranspose_getElem {α : Type*} (l : List (List α)) (i : ℕ)
    (hi : i < l.mtranspose.length) :
    l.mtranspose[i] = l.pmap (fun x hx ↦ x[i]'hx)
      (fun a ha ↦ hi.trans_le (forall_mtranspose_length_le l a ha)) := by
  induction l
  · simp at hi
  case cons head tail tail_ih =>
  cases tail
  · simp
  case cons head tail =>
  simp only [mtranspose, getElem_zipWith]
  rw [tail_ih]
  simp

theorem List.mtranspose_pmap_getElem {α : Type*} (l : List (List α)) (i : ℕ)
    (hi : i < l.length) :
    l.mtranspose.pmap (·[i]'·) (fun a ha ↦ List.length_of_mem_mtranspose l a ha ▸ hi) = l[i] := by
  induction l generalizing i
  · simp at hi
  case cons head tail tail_ih =>
  cases tail
  · simp [pmap_map]
  case cons head2 tail =>
  simp [mtranspose]
  generalize_proofs hp
  cases i
  · simp
    sorry
  · simp
    sorry

theorem Mathlib.Vector.getElem_def {n : ℕ} {α : Type*} (v : Vector α n)
    (i : ℕ) {hi : i < n} : v[i] = v.toList[i]'(by simpa) := rfl

theorem Mathlib.Vector.toList_getElem {n : ℕ} {α : Type*} (v : Vector α n)
    (i : ℕ) {hi : i < v.toList.length} : v.toList[i] = v[i]'(by simp_all) := rfl

def List.transpose' {α : Type*} {n : ℕ} (l : List (Vector α n)) : Vector (List α) n :=
  if hl : l.length = 0 then ⟨List.replicate n [], by simp⟩ else
  ⟨(l.map Vector.toList).mtranspose, by
    conv_lhs =>
      rw [length_mtranspose]
      lhs
      tactic =>
        convert List.minimum?_replicate_of_pos (by simp : min n n = n) (Nat.pos_of_ne_zero hl)
        simp [List.eq_replicate]
    simp⟩

lemma List.transpose'_getElem {α : Type*} {n i : ℕ} (l : List (Vector α n)) (hi : i < n) :
    l.transpose'[i] = l.map (·[i]) := by
  simp [transpose']
  split
  · simpa [Vector.getElem_def, ← List.length_eq_zero]
  simp [Vector.getElem_def, List.mtranspose_getElem, List.pmap_map]
  change l.pmap (fun a h ↦ a.toList[i]'(by simpa)) _ = _
  simp

def Mathlib.Vector.transpose {α : Type*} {n : ℕ} (l : Vector (List α) n) : List (Vector α n) :=
  l.toList.mtranspose.pmap Subtype.mk (fun _ b ↦ by simp [List.length_of_mem_mtranspose _ _ b])

lemma Mathlib.Vector.map_getElem_transpose {α : Type*} {n i : ℕ}
    (l : Vector (List α) n) (h : i < n) :
    l.transpose.map (·[i]) = l[i] := by
  simp [transpose, List.map_pmap]
  conv_lhs => simp [Vector.getElem_def]
  conv_rhs => apply (List.mtranspose_pmap_getElem l.toList ..).symm
  apply List.pmap_congr
  simp

lemma Finset.sum_tsub_distrib {ι α : Type*} [OrderedAddCommMonoid α] [Sub α] [ExistsAddOfLE α]
    [OrderedSub α] [ContravariantClass α α (· + ·) (· ≤ ·)] (s : Finset ι) (f : ι → α) (g : ι → α)
    (hfg : ∀ x ∈ s, g x ≤ f x) : ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := by
  induction s using Finset.cons_induction
  · simp
  case cons head tail tail_ih =>
    simp only [mem_cons, forall_eq_or_imp] at hfg
    simp only [sum_cons, tail_ih hfg.2]
    apply tsub_add_tsub_comm
    exact hfg.1
    apply Finset.sum_le_sum hfg.2

def Finset.next {n : ℕ} (s : Finset (Fin n)) : Equiv.Perm (Fin n) := (s.sort (· ≤ ·)).formPerm

theorem Finset.next_ne_iff {n : ℕ} (s : Finset (Fin n)) (hs : s.Nontrivial) (v : Fin n) :
    s.next v ≠ v ↔ v ∈ s := by
  have := List.support_formPerm_of_nodup' (s.sort (· ≤ ·)) (by simp) ?_
  simp only [ne_eq, sort_toFinset, Set.ext_iff, Set.mem_setOf_eq, mem_coe] at this
  exact this v
  intro x
  apply_fun List.length
  simp only [length_sort, List.length_singleton, ne_eq,
    (Finset.one_lt_card_iff_nontrivial.2 hs).ne', not_false_eq_true]

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

@[simp]
lemma List.unpad_pad (l : List Bool) (n : ℕ) : (l.pad n).unpad = l := by
  simp [pad, leftpad, unpad]

def RepApp {α : Type*} (f : α → α) (a b : α) : Prop := ∃ i : ℕ, f^[i] a = b

lemma RepApp_def {α : Type*} (f : α → α) (a b : α) : RepApp f a b ↔ ∃ i : ℕ, f^[i] a = b := Iff.rfl

@[simp, refl]
lemma RepApp_rfl {α : Type*} (f : α → α) (a : α) : RepApp f a a := ⟨0, rfl⟩

@[simp]
lemma RepApp_iterate {α : Type*} (f : α → α) (a : α) (i : ℕ) : RepApp f a (f^[i] a) := ⟨i, rfl⟩

lemma RepApp_isMin_of_nontrivial {α : Type*} {f : α → α} {a b c : α} (hab : a ≠ b)
    (ha : RepApp f a b) (hb : RepApp f b a) (hc : RepApp f a c) : RepApp f c a := by
  obtain ⟨i, rfl⟩ := ha
  have ine : i ≠ 0 := fun h ↦ by simp [h] at hab
  obtain ⟨j, hb⟩ := hb
  rw [← Function.iterate_add_apply] at hb
  obtain ⟨k, rfl⟩ := hc
  use j + i - k % (j + i)
  rw [← Function.iterate_add_apply]
  obtain ⟨l, hl⟩ : j + i ∣ j + i - k % (j + i) + k := by
    rw [← Nat.sub_add_comm, Nat.add_sub_assoc]
    · simp only [Nat.dvd_add_self_left, Nat.dvd_sub_mod]
    · apply Nat.mod_le
    · apply le_of_lt
      apply Nat.mod_lt
      omega
  rw [hl, Function.iterate_mul]
  apply Function.iterate_fixed hb

instance {α : Type*} (f : α → α) : IsPreorder α (RepApp f) where
  refl a := by rfl
  trans a b c ha hb := by
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    simp [← Function.iterate_add_apply]

lemma Function.iterate_cancel' {α : Type*} {f : α → α} {m n : ℕ} {a : α} (ha : f^[m] a = f^[n] a)
    (hnm : n ≤ m) (i : ℕ) (hi : m ≤ i) : f^[i] a = f^[i - (m - n)] a := by
  obtain ⟨i, rfl⟩ := exists_add_of_le hi
  simp only [hnm, add_tsub_tsub_cancel]
  rw [add_comm, Function.iterate_add_apply, Function.iterate_add_apply, ha]

lemma Function.iterate_cancel'' {α : Type*} {f : α → α} {m n : ℕ} {a : α} (ha : f^[m] a = f^[n] a)
    (hnm : n < m) (i : ℕ) : ∃ j < m, f^[i] a = f^[j] a := by
  rcases lt_or_le i m with _ | hi
  · use i
  rw [Function.iterate_cancel' ha hnm.le i hi]
  apply iterate_cancel'' ha hnm

lemma RepApp_iff_repApp_small {α : Type*} [Fintype α] (f : α → α) (a b : α) :
    RepApp f a b ↔ ∃ i < Fintype.card α, f^[i] a = b where
  mp hr := by
    obtain ⟨m, n, hmn, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun v : Fin (Fintype.card α + 1) ↦ f^[v] a) (by simp)
    wlog hmn : n < m
    · exact this f a b hr n m (by omega) h.symm (by omega)
    obtain ⟨i, hi⟩ := hr
    obtain ⟨j, hj, h⟩ := Function.iterate_cancel'' h hmn i
    use j
    simp only [← h, hi, and_true]
    omega
  mpr h := h.elim (fun a ha ↦ ⟨a, ha.2⟩)

instance {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) : DecidableRel (RepApp f) :=
  fun a b ↦ decidable_of_iff' _ (RepApp_iff_repApp_small f a b)

instance {α : Type*} (f : α → α → Prop) [DecidableRel f] [IsPreorder α f] :
  DecidableRel (AntisymmRel.setoid _ f).r := inferInstanceAs (DecidableRel (AntisymmRel f))

theorem Finpartition.ofSetoid_mem_part_iff  {α : Type*} [DecidableEq α] [Fintype α]
    (s : Setoid α) [DecidableRel s.r] (x : α) (y : α) : y ∈ (ofSetoid s).part x ↔ s.r x y := by
  rw [Finpartition.part_eq_of_mem (t := Finset.univ.filter (s.r x))]
  · simp
  · simp [ofSetoid]
  · simpa using s.refl' x

def scc {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) :
    Finpartition (Finset.univ : Finset α) :=
  Finpartition.ofSetoid (AntisymmRel.setoid _ (RepApp f))

lemma scc_part_eq_orbit_of_nontrivial {α : Type*} [Fintype α] [DecidableEq α] (f : α → α)
    (x : α) (hx : ((scc f).part x).Nontrivial) : (scc f).part x = {f^[i] x | i} := by
  obtain ⟨z, hz, hxz⟩ := hx.exists_ne x
  simp only [scc, Finpartition.ofSetoid_mem_part_iff, AntisymmRel.setoid_r, AntisymmRel] at hz
  ext y
  simp only [scc, Finset.mem_coe, Finpartition.ofSetoid_mem_part_iff, AntisymmRel.setoid_r,
    AntisymmRel, Set.mem_setOf_eq, ← RepApp_def]
  exact ⟨And.left, fun h ↦ ⟨h, RepApp_isMin_of_nontrivial hxz.symm hz.1 hz.2 h⟩⟩

lemma scc_congr' {α : Type*} [Fintype α] [DecidableEq α] (f g : α → α) (s : Finset α)
    (hs : s.card ≠ 1) (hfg : ∀ x ∈ s, f x = g x) (hf : s ∈ (scc f).parts) :
    s ∈ (scc g).parts := by
  rcases hs.lt_or_lt with hs | hs
  · simp_all [← Finset.bot_eq_empty, Finpartition.not_bot_mem]
  rw [Finset.one_lt_card_iff_nontrivial] at hs
  obtain ⟨x, hx⟩ := hs.nonempty
  rw [Finset.mem_coe] at hx
  obtain rfl := Finpartition.part_eq_of_mem _ hf hx
  clear hf hx
  suffices (scc f).part x = (scc g).part x by simp [this, Finpartition.part_mem]
  ext z
  have := scc_part_eq_orbit_of_nontrivial f x hs
  rw [← Finset.mem_coe, this]
  simp_rw [← Finset.mem_coe, this] at hfg
  simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff] at hfg
  simp only [Set.mem_setOf_eq]

  sorry

lemma scc_congr {α : Type*} [Fintype α] [DecidableEq α] (f g : α → α) (s : Finset α)
    (hs : s.card ≠ 1) (hfg : ∀ x ∈ s, f x = g x) : s ∈ (scc f).parts ↔ s ∈ (scc g).parts := by
  constructor <;> apply scc_congr' <;> simp_all

theorem Fin.natCast_sub {m n : ℕ} (hmn : m ≤ n) {k : ℕ} [NeZero k] :
    ((n - m : ℕ) : Fin k) = n - m := by
  sorry

end Setup

section Problem

def Aisha := List Bool → Finset (Fin 31) → List (Vector Bool 31) →
  Option (Vector Bool 31)

def Basma := List (Vector Bool 31) → List Bool

def Aisha.ValidPreRun (aisha : Aisha) (msg : List Bool) (comp : Finset (Fin 31))
    (run : List (Vector Bool 31)) : Prop :=
  ∀ i : Fin run.length, (aisha msg comp (run.take i)).any
    (fun v ↦ ∀ j ∉ comp, run[i][j] = v[j])

def Aisha.Small (aisha : Aisha) : Prop :=
  ∀ msg comp run, 1 ≤ msg.length → msg.length ≤ 1024 → comp.card = 15 →
      aisha.ValidPreRun msg comp run → run.length ≤ 66

def Aisha.ValidRun (aisha : Aisha) (msg : List Bool) (comp : Finset (Fin 31))
    (run : List (Vector Bool 31)) : Prop :=
  aisha.ValidPreRun msg comp run ∧ aisha msg comp run = none

def Aisha.Correct (aisha : Aisha) (basma : Basma) : Prop :=
  ∀ msg comp run, 1 ≤ msg.length → msg.length ≤ 1024 →
    comp.card = 15 → aisha.ValidRun msg comp run → basma run = msg

end Problem

def SimpleAisha := List Bool → Finset (Fin 31) → List (Vector Bool 31)

def SimpleAisha.toAisha (self : SimpleAisha) : Aisha :=
  fun msg comp sf ↦ (self (msg.pad 1025) comp).get? sf.length

def SimpleBasma := List (Vector Bool 31) → List Bool

def SimpleBasma.toBasma (self : SimpleBasma) : Basma :=
  fun run ↦ (self run).unpad

theorem SimpleAisha.toAisha_prefix_of_validPreRun (self : SimpleAisha) (msg : List Bool)
    (comp : Finset (Fin 31)) (run : List (Vector Bool 31))
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

theorem SimpleAisha.toAisha_small_of_out (self : SimpleAisha)
    (h : ∀ (msg : List Bool) comp, 1 ≤ msg.length → msg.length ≤ 1024 → comp.card = 15 →
      (self (msg.pad 1025) comp).length ≤ 66) : self.toAisha.Small := by
  intro msg comp run msgl msgu cc hr
  apply SimpleAisha.toAisha_prefix_of_validPreRun at hr
  specialize h msg comp msgl msgu cc
  obtain ⟨x, hx⟩ : compᶜ.Nonempty := by simp [← Finset.card_pos, Finset.card_compl, cc]
  specialize hr x (Finset.mem_compl.1 hx)
  apply List.IsPrefix.length_le at hr
  simp at hr
  omega

theorem SimpleAisha.toAisha_eq_of_validRun (self : SimpleAisha) (msg : List Bool)
    (comp : Finset (Fin 31)) (run : List (Vector Bool 31))
    (h : self.toAisha.ValidRun msg comp run) :
    ∀ v ∉ comp, run.map (·[v]) = (self (msg.pad 1025) comp).map (·[v]) := by
  simp only [Aisha.ValidRun] at h
  intro v hv
  apply (self.toAisha_prefix_of_validPreRun msg comp run h.1 v hv).eq_of_length_le
  simpa [toAisha] using h.2

theorem main_theorem (comp : Finset (Fin 31)) (cc : comp.card = 15) :
  ((List.finRange 31).map (fun v ↦ if v ∈ compᶜ then
    66 - (compᶜ.next v - v).val else 0)).sum = 1025 :=
  calc ((List.finRange 31).map (fun v ↦ if v ∈ compᶜ then
      66 - (compᶜ.next v - v).val else 0)).sum
    _ = ∑ v : Fin 31, if v ∈ compᶜ then 66 - (compᶜ.next v - v).val else 0 := by
      simp [Fin.sum_univ_def]
    _ = ∑ v ∈ compᶜ, (66 - (compᶜ.next v - v).val) := by
      simp only [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ v ∈ compᶜ, 66 - ∑ v ∈ compᶜ, (compᶜ.next v - v).val := by
      rw [Finset.sum_tsub_distrib]
      intros
      omega
    _ = 1025 := by simp [Finset.card_compl, cc, ← Finset.one_lt_card_iff_nontrivial, cyc_sum]

def SimpleAisha.winningStrat' (msg : List Bool) (comp : Finset (Fin 31)) :
    Vector (List Bool) 31 :=
  ⟨(msg.splitSizes ((List.finRange 31).map (fun v ↦ if v ∈ compᶜ then
    66 - (compᶜ.next v - v).val else 0))).map
    (fun l ↦ l.pad 66), by simp⟩

@[simp]
lemma SimpleAisha.winningStrat'_length_of_mem (msg : List Bool)
    (comp : Finset (Fin 31)) (hc : compᶜ.Nontrivial) :
    ∀ x ∈ (winningStrat' msg comp).toList, x.length = 66 := by
  intro x hx
  simp only [winningStrat', Vector.toList_mk, List.mem_map] at hx
  obtain ⟨a, ha1, rfl⟩ := hx
  apply List.length_pad
  apply Nat.lt_succ_of_le
  revert a
  apply List.length_mem_splitSizes
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  intro a
  split_ifs with h
  · rw [← Finset.next_ne_iff _ hc] at h
    omega
  · simp

def SimpleAisha.winningStrat : SimpleAisha := fun msg comp ↦
  (winningStrat' msg comp).transpose

def Aisha.winningStrat : Aisha := SimpleAisha.winningStrat.toAisha

def Mathlib.Vector.enumFin {α : Type*} {n : ℕ} (v : Vector α n) :
    Vector (Fin n × α) n := ⟨(List.finRange n).zip v.toList, by simp⟩

@[simp]
def Mathlib.Vector.enumFin_getElem_fst {α : Type*} {n i : ℕ} (v : Vector α n) (hi : i < n) :
    v.enumFin[i].1 = ⟨i, hi⟩ := by simp [enumFin, getElem_def]

@[simp]
def Mathlib.Vector.enumFin_getElem_snd {α : Type*} {n i : ℕ} (v : Vector α n) (hi : i < n) :
    v.enumFin[i].2 = v[i] := by simp [enumFin, getElem_def]

def SimpleBasma.winningStrat_msg (msg : Vector (List Bool) 31) (comp : Finset (Fin 31)) :
    List Bool :=
  msg.enumFin.toList.bind fun ⟨i, m⟩ ↦ if i ∈ comp then [] else m.unpad

instance {α : Type*} [DecidableEq α] : DecidableEq (Lex α) := inferInstanceAs (DecidableEq α)

private def SimpleBasma.next_l (msg : Vector (List Bool) 31) (v : Fin 31) : Fin 31 :=
  v + 66 - msg[v].unpad.length

def SimpleBasma.winningStrat_comp.f (msg : Vector (List Bool) 31) (v : Fin 31) : Fin 31 :=
  v + 66 - msg[v].unpad.length

@[irreducible]
def SimpleBasma.winningStrat_comp (msg : Vector (List Bool) 31) :
    Finset (Fin 31) :=
  ofLex (scc (SimpleBasma.winningStrat_comp.f msg) |>.parts.image
    (fun a ↦ toLex (a.card, Finset.Colex.toColex a)) |>.max'
    (by simp [Finpartition.parts_nonempty_iff, Finset.univ_eq_empty_iff])) |>.2.ofColexᶜ

def SimpleBasma.winningStrat : SimpleBasma := fun run ↦
  let run' : Vector (List Bool) 31 := run.transpose'
  SimpleBasma.winningStrat_msg run' (SimpleBasma.winningStrat_comp run')

def Basma.winningStrat : Basma := SimpleBasma.winningStrat.toBasma

theorem IOI2024Q2 : Aisha.winningStrat.Small ∧ Aisha.winningStrat.Correct Basma.winningStrat := by
  constructor
  · apply SimpleAisha.toAisha_small_of_out
    intro msg comp msgb msgu cc
    simp [SimpleAisha.winningStrat, Vector.transpose, List.length_mtranspose]
    conv_lhs =>
      lhs
      tactic =>
        convert List.minimum?_replicate_of_pos (by simp : min 66 66 = 66) (by simp : 0 < 31)
        simp only [List.eq_replicate, List.length_map, Vector.toList_length, List.mem_map,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, true_and]
        apply SimpleAisha.winningStrat'_length_of_mem
        simp [← Finset.one_lt_card_iff_nontrivial, Finset.card_compl, cc]
    simp
  · intro msg comp run msgb msgu cc hr
    apply SimpleAisha.toAisha_eq_of_validRun at hr
    simp only [Basma.winningStrat, SimpleBasma.toBasma, SimpleBasma.winningStrat]
    let run' : Vector (List Bool) 31 := run.transpose'
    let msg' : Vector (List Bool) 31 := SimpleAisha.winningStrat' (msg.pad 1025) comp
    replace hr : ∀ v ∉ comp, run'[v] = msg'[v] := by
      intro v hv
      specialize hr v hv
      simp only [Fin.getElem_fin, SimpleAisha.winningStrat] at hr
      simp only [Fin.getElem_fin, List.transpose'_getElem, hr, Vector.map_getElem_transpose, run',
        msg']
    change (SimpleBasma.winningStrat_msg run' (SimpleBasma.winningStrat_comp run')).unpad = _
    convert List.unpad_pad _ 1025
    have ccc : compᶜ.card = 16 := by simp [cc, Finset.card_compl]
    have : SimpleBasma.winningStrat_comp run' = comp := by
      unfold SimpleBasma.winningStrat_comp
      trans (ofLex (toLex (16, Finset.Colex.toColex compᶜ))).2.ofColexᶜ
      on_goal 2 => simp
      with_reducible congr 4
      have hmem : compᶜ ∈ (scc (SimpleBasma.winningStrat_comp.f run')).parts := by
        rw [scc_congr (g := (SimpleBasma.winningStrat_comp.f msg'))]
        rw [scc_congr (g := fun v ↦ compᶜ.next v)]
        ·
          sorry
        · simp [ccc]
        · intro x hx
          simp only [SimpleBasma.winningStrat_comp.f, Fin.isValue, Fin.getElem_fin,
            Fin.cast_val_eq_self, msg']
          simp only [Fin.isValue, SimpleAisha.winningStrat',
            Vector.getElem_def, Vector.toList_mk, List.getElem_map, List.unpad_pad]
          rw [List.splitSizes_length_getElem]
          · simp only [Fin.isValue, List.getElem_map, List.getElem_finRange, Fin.eta, hx,
            ↓reduceIte]
            rw [Fin.natCast_sub]
            · simp
              sorry
            · trans 31 <;> simp
          · rw [main_theorem comp cc, List.length_pad]
            omega
        · simp [ccc]
        · intro x hx
          specialize hr x (Finset.mem_compl.1 hx)
          simp only [SimpleBasma.winningStrat_comp.f, hr, Fin.getElem_fin]
      apply le_antisymm
      · simp only [Finset.mem_image, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq,
        Finset.Colex.toColex.injEq, exists_eq_right_right] at hmem
        simp only [Finset.max'_le_iff, Finset.mem_image, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
        intro b hb
        by_contra! nh
        have : b ≠ compᶜ := fun h ↦ by simp [h, ccc] at nh
        replace nh := Prod.Lex.monotone_fst _ _ nh.le
        simp only [ofLex_toLex] at nh
        suffices compᶜ.card + b.card ≤ ∑ v ∈ (scc (SimpleBasma.winningStrat_comp.f run')).parts,
              v.card by
          simp [Finpartition.sum_card_parts] at this
          omega
        exact Finset.add_le_sum (by simp) hmem hb this.symm

      · apply Finset.le_max'
        simp [ccc, hmem]
    rw [this, SimpleBasma.winningStrat_msg]
    trans msg'.toList.bind (·.unpad)
    · unfold List.bind
      congr 1
      apply List.ext_getElem
      · simp
      intro n h₁ h₂
      simp only [List.getElem_map, Vector.toList_getElem,
        Vector.enumFin_getElem_fst, Vector.enumFin_getElem_snd]
      split_ifs with h
      · simp only [SimpleAisha.winningStrat', Finset.mem_compl, Vector.getElem_def,
        Vector.toList_mk, List.getElem_map, List.getElem_attach, ite_not, List.unpad_pad,
        List.nil_eq, msg']
        apply List.eq_nil_of_length_eq_zero
        apply Nat.eq_zero_of_le_zero
        convert List.length_splitSizes_getElem _ _
        simp [h]
      · congr 1
        exact hr _ h
    simp only [List.bind, SimpleAisha.winningStrat', Vector.toList_mk,
      List.map_map, msg']
    conv =>
      enter [1, 1, 1, x]
      simp only [Finset.mem_compl, Function.comp_apply, Vector.toList_mk, List.unpad_pad]
    simp only [List.map_id_fun', id_eq]
    apply List.join_splitSizes
    simp only [List.pad, List.leftpad_length, List.length_cons, Nat.reduceLeDiff, msgu, max_eq_left,
      main_theorem comp cc]

#min_imports
