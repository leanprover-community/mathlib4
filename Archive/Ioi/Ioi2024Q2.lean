/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Colex
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.List.Transpose
import Mathlib.Data.Vector.Transpose
import Mathlib.Data.List.SplitLengths
import ImportGraph.Imports

open Mathlib

section Setup

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

theorem cyc_sum {n : ℕ} (s : Finset (Fin n)) (hs : s.Nontrivial) :
    ∑ v ∈ s, (s.next v - v).val = n := by
  zify
  simp only [Fin.intCast_val_sub_eq_ite, Nat.cast_ite, Nat.cast_zero, Finset.sum_add_distrib,
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
  ⟨(msg.splitLengths ((List.finRange 31).map (fun v ↦ if v ∈ compᶜ then
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
  apply List.length_mem_splitLengths
  simp only [List.mem_map, List.mem_finRange, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  intro a
  split_ifs with h
  · rw [← Finset.next_ne_iff _ hc] at h
    omega
  · simp

def SimpleAisha.winningStrat : SimpleAisha := fun msg comp ↦
  (winningStrat' msg comp).listTranspose

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
  SimpleBasma.winningStrat_msg run.vectorTranspose
    (SimpleBasma.winningStrat_comp run.vectorTranspose)

def Basma.winningStrat : Basma := SimpleBasma.winningStrat.toBasma

theorem IOI2024Q2 : Aisha.winningStrat.Small ∧ Aisha.winningStrat.Correct Basma.winningStrat := by
  constructor
  · apply SimpleAisha.toAisha_small_of_out
    intro msg comp _ _ cc
    simp [SimpleAisha.winningStrat, Vector.listTranspose, List.length_ttranspose]
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
    let run' : Vector (List Bool) 31 := run.vectorTranspose
    let msg' : Vector (List Bool) 31 := SimpleAisha.winningStrat' (msg.pad 1025) comp
    replace hr : ∀ v ∉ comp, run'[v] = msg'[v] := by
      intro v hv
      specialize hr v hv
      simp only [Fin.getElem_fin, SimpleAisha.winningStrat] at hr
      simp only [Fin.getElem_fin, List.vectorTranspose_getElem, hr, run',
        msg']
      apply Vector.map_getElem_listTranspose
      intro x hx
      rw [SimpleAisha.winningStrat'_length_of_mem (msg.pad 1025) comp ?cnt _ hx,
        SimpleAisha.winningStrat'_length_of_mem (msg.pad 1025) comp ?cnt]
      · simp [Vector.getElem_def, List.getElem_mem]
      · simp [← Finset.one_lt_card_iff_nontrivial, Finset.card_compl, cc]
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
        · simp only [mem_scc_perm_iff, ← Finset.card_pos, ccc, Nat.ofNat_pos, Finset.coe_compl,
            true_and, Finset.next]
          convert List.Nodup.isCycleOn_formPerm _ using 1
          · ext
            simp
          · simp
        · simp [ccc]
        · intro x hx
          simp only [SimpleBasma.winningStrat_comp.f, Fin.isValue, Fin.getElem_fin,
            Fin.cast_val_eq_self, msg']
          simp only [Fin.isValue, SimpleAisha.winningStrat',
            Vector.getElem_def, Vector.toList_mk, List.getElem_map, List.unpad_pad]
          rw [List.splitLengths_length_getElem]
          · simp only [Fin.isValue, List.getElem_map, List.getElem_finRange, Fin.eta, hx,
            ↓reduceIte]
            rw [Nat.cast_sub]
            · simp
              ring_nf
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
        convert List.length_splitLengths_getElem _ _
        simp [h]
      · congr 1
        exact hr _ h
    simp only [List.bind, SimpleAisha.winningStrat', Vector.toList_mk,
      List.map_map, msg']
    conv =>
      enter [1, 1, 1, x]
      simp only [Finset.mem_compl, Function.comp_apply, Vector.toList_mk, List.unpad_pad]
    simp only [List.map_id_fun', id_eq]
    apply List.join_splitLengths
    simp only [List.pad, List.leftpad_length, List.length_cons, Nat.reduceLeDiff, msgu, max_eq_left,
      main_theorem comp cc]
