/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import GreensRelations.Order
import GreensRelations.FactorizationForest.Basic

/-!
# Combine Splits Construction

This file contains the construction of `combineSplits` which is used to merge local
Ramsey splits over open intervals into a global split.
-/

namespace FactorizationForest

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- The Simon complexity associated with an element `x`. -/
noncomputable abbrev nSElement (x : S) : ℕ :=
  let currentCost := nD (IsGreenD.eqvClass x)
  let strictlyAbove := Finset.univ.filter
    (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
  let maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
  currentCost + maxAbove
termination_by (Finset.univ.filter
  (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)).card
decreasing_by
  have h_lt : GreenJClass.mk x < GreenJClass.mk y :=
    (Finset.mem_filter.mp _hy).right
  have h_le : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ⊆
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
                grind
  have h_ne : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ≠
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
                grind
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

open Classical in
/-- The maximum Simon complexity over all elements in the semigroup `S`. -/
noncomputable abbrev nS (S : Type*) [Semigroup S] [Fintype S] : ℕ :=
  let all_vals := Finset.univ.image (fun (x : S) => nSElement x)
  if h : all_vals.Nonempty then
    Finset.max' all_vals h
  else
    0

/-- The Simon complexity of any element is strictly positive. -/
lemma nSElement_pos (x : S) : 0 < nSElement x := by
  rw [nSElement]
  have h_pos : 0 < nD (IsGreenD.eqvClass x) := nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩
  omega

/-- `Fin (nSElement x)` is nonempty since `nSElement` is
  always positive. -/
instance instNonemptyFin_nSElement (x : S) :
    Nonempty (Fin (nSElement x)) :=
  Fin.pos_iff_nonempty.mp (nSElement_pos x)

open Classical in
/-- Constructs the sequence of indices `x_i` used to build the regular or irregular splits. -/
noncomputable abbrev buildXSeq (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (x : α) : List α :=
  let candidates := Finset.univ.filter (fun y => x < y ∧ IsGreenD (σ.σ x y) a)
  if h : candidates.Nonempty then
    let y := Finset.min' candidates h
    x :: buildXSeq a σ y
  else
    [x]
termination_by (Finset.univ.filter (fun z => x < z)).card
decreasing_by
  have h_mem := Finset.min'_mem _ h
  obtain ⟨_, h_x_lt_y, _⟩ := Finset.mem_filter.mp h_mem
  have h_le : Finset.univ.filter (fun z => y < z) ⊆ Finset.univ.filter (fun z => x < z) :=
    fun _ hz => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, lt_trans h_x_lt_y
      (Finset.mem_filter.mp hz).2⟩
  have h_ne : Finset.univ.filter (fun z => y < z) ≠ Finset.univ.filter (fun z => x < z) :=
    fun heq => lt_irrefl y (Finset.mem_filter.mp (heq.symm ▸ Finset.mem_filter.mpr
    ⟨Finset.mem_univ y, h_x_lt_y⟩ : y ∈ _)).2
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

/-- A subtype representing the elements strictly between `xs[i]` and `xs[i+1]`. -/
abbrev OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) :=
  { y : α // ∃ (h1 : i < xs.length),
    xs.get ⟨i, h1⟩ < y ∧ ∀ (h2 : i + 1 < xs.length), y < xs.get ⟨i + 1, h2⟩ }

/-- A strictly increasing sequence covering a domain bounds any element `x` either
within an interval or at one of the sequence points. -/
lemma list_interval_covers {α : Type*} [LinearOrder α] (x : α) :
    ∀ (xs : List α), x ∉ xs →
    (∃ y ∈ xs, y < x) →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (hi_succ_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, hi_succ_lt⟩
| [], _, ⟨_, hy, _⟩ => nomatch hy
| a :: tail, h_not_in, h_lb => by
  by_cases h_tail : ∃ y ∈ tail, y < x
  · obtain ⟨i, hi, hlt, hgt⟩ :=
      list_interval_covers x tail (fun h => h_not_in (List.Mem.tail _ h)) h_tail
    exact ⟨i + 1, by simp; omega, hlt, fun h => hgt (by simp at h; omega)⟩
  · grind

/-- The elements built by `buildXSeq` cover the interval starting at the initial element. -/
lemma buildXSeq_covers {S α : Type*} [Semigroup S] [Fintype S] [LinearOrder α] [Fintype α]
    (a : S) (σ : MultiplicativeLabeling S α) (x₀ : α) (x : α) (h_x0_le_x : x₀ ≤ x) :
    x ∉ buildXSeq a σ x₀ → ∃ (i : ℕ) (hi_lt : i < (buildXSeq a σ x₀).length),
    (buildXSeq a σ x₀).get ⟨i, hi_lt⟩ < x ∧ ∀ (hi_succ_lt : i + 1 < (buildXSeq a σ x₀).length),
    x < (buildXSeq a σ x₀).get ⟨i + 1, hi_succ_lt⟩ := by
  intro h_not_in
  have h_x0_in : x₀ ∈ buildXSeq a σ x₀ := by
    rw [buildXSeq]
    grind
  have h_lb : ∃ y ∈ buildXSeq a σ x₀, y < x :=
    ⟨x₀, h_x0_in, lt_of_le_of_ne h_x0_le_x (fun heq => h_not_in (heq ▸ h_x0_in))⟩
  exact list_interval_covers x (buildXSeq a σ x₀) h_not_in h_lb

/-- The sequence generated by `buildXSeq` has a strictly positive length. -/
lemma buildXSeq_length_pos (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (w : α) : 0 < (buildXSeq a σ w).length := by
  classical
  rw [buildXSeq]
  split_ifs <;> exact Nat.zero_lt_succ _

/-- The first element of `buildXSeq` is exactly the initial element provided. -/
lemma buildXSeq_head (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (w : α) (h : 0 < (buildXSeq a σ w).length) :
    (buildXSeq a σ w).get ⟨0, h⟩ = w := by
  classical
  generalize h_xs : buildXSeq a σ w = xs at h ⊢
  have h_eq : buildXSeq a σ w =
    if h_cond : (Finset.univ.filter (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty then
      w :: buildXSeq a σ (Finset.min' _ h_cond)
    else [w] := by rw [buildXSeq]
  grind

/-- properties of `buildXSeq`. -/
lemma buildXSeq_properties (a : S) {α : Type*} [LinearOrder α] [Fintype α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a)) (w : α) :
    (∀ y ∈ buildXSeq a σ w, w ≤ y) ∧
    (∀ x ∈ buildXSeq a σ w, ∀ y ∈ buildXSeq a σ w, x < y → IsGreenD (σ.σ x y) a) ∧
    (∀ (i : ℕ) (hi_lt : i < (buildXSeq a σ w).length) (y : α),
      (buildXSeq a σ w).get ⟨i, hi_lt⟩ < y →
      (∀ hi_succ_lt : i + 1 < (buildXSeq a σ w).length, y <
      (buildXSeq a σ w).get ⟨i + 1, hi_succ_lt⟩) →
      ¬ IsGreenD (σ.σ ((buildXSeq a σ w).get ⟨i, hi_lt⟩) y) a) ∧
    (∀ (i j : ℕ) (hi_lt : i < (buildXSeq a σ w).length) (hj_lt : j < (buildXSeq a σ w).length),
      i < j → (buildXSeq a σ w).get ⟨i, hi_lt⟩ < (buildXSeq a σ w).get ⟨j, hj_lt⟩) := by
  classical
  have h_eq : buildXSeq a σ w =
    if h_cond : (Finset.univ.filter (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty then
      w :: buildXSeq a σ (Finset.min' _ h_cond)
    else [w] := by rw [buildXSeq]
  by_cases h : (Finset.univ.filter (fun y => w < y ∧ IsGreenD (σ.σ w y) a)).Nonempty
  · let w' := Finset.min' _ h
    have hw' : w < w' ∧ IsGreenD (σ.σ w w') a := Finset.mem_filter.mp (Finset.min'_mem _ h) |>.right
    have ih := buildXSeq_properties a σ h_img w'
    obtain ⟨ih_ge, ih_range, ih_gap, ih_mono⟩ := ih
    have h_xs : buildXSeq a σ w = w :: buildXSeq a σ w' := by rw [h_eq, dif_pos h]
    constructor
    · grind
    constructor
    · intro x hx y hy hlt
      rw [h_xs] at hx hy
      exact match List.mem_cons.mp hx, List.mem_cons.mp hy with
      | Or.inl hx_eq, Or.inl hy_eq => by
        rw [hx_eq, hy_eq] at hlt
        nomatch (lt_irrefl w hlt)
      | Or.inl hx_eq, Or.inr hy_tail => hx_eq ▸ isGreenD_of_prefix a σ h_img w w' y hw'.1
        (ih_ge y hy_tail) hw'.2
      | Or.inr hx_tail, Or.inl hy_eq => by
        rw [hy_eq] at hlt
        nomatch (lt_irrefl w (lt_trans (lt_of_lt_of_le hw'.1 (ih_ge x hx_tail)) hlt))
      | Or.inr hx_tail, Or.inr hy_tail => ih_range x hx_tail y hy_tail hlt
    constructor
    · intro i hi_lt y h_lt h_gt h_D
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt h_lt h_gt h_D ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero =>
        have hy_mem : y ∈ Finset.univ.filter (fun z => w < z ∧ IsGreenD (σ.σ w z) a) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_lt, h_D⟩
        have hw'_le_y : w' ≤ y := Finset.min'_le _ _ hy_mem
        have hw_len_lt : 1 < (w :: buildXSeq a σ w').length := by
          simp only [List.length_cons, Nat.succ_lt_succ_iff]
          exact buildXSeq_length_pos a σ w'
        have h_y_lt_w' : y < w' := buildXSeq_head a σ w' _ ▸ h_gt hw_len_lt
        exact lt_irrefl _ (lt_of_lt_of_le h_y_lt_w' hw'_le_y)
      | succ i' =>
        have hi_tail : i' < (buildXSeq a σ w').length := Nat.succ_lt_succ_iff.mp hi_lt
        exact ih_gap i' hi_tail y h_lt (fun hi_succ_lt => h_gt (Nat.succ_lt_succ hi_succ_lt)) h_D
    · intro i j hi_lt hj_lt hij
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt hj_lt ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero =>
        cases j with
        | zero => nomatch (lt_irrefl _ hij)
        | succ j' =>
          have hj_tail : j' < (buildXSeq a σ w').length := Nat.succ_lt_succ_iff.mp hj_lt
          exact lt_of_lt_of_le hw'.1 (ih_ge _ (List.mem_iff_get.mpr ⟨⟨j', hj_tail⟩, rfl⟩))
      | succ i' =>
        cases j with
        | zero => nomatch (Nat.not_lt_zero _ (lt_trans (Nat.zero_lt_succ _) hij))
        | succ j' =>
          have hi_tail : i' < (buildXSeq a σ w').length := Nat.succ_lt_succ_iff.mp hi_lt
          have hj_tail : j' < (buildXSeq a σ w').length := Nat.succ_lt_succ_iff.mp hj_lt
          exact ih_mono i' j' hi_tail hj_tail (Nat.succ_lt_succ_iff.mp hij)
  · have h_xs : buildXSeq a σ w = [w] := by rw [h_eq, dif_neg h]
    constructor
    · grind
    constructor
    · grind
    constructor
    · intro i hi_lt y h_lt h_gt h_D
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt h_lt h_gt h_D ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero =>
        exact h ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_lt, h_D⟩⟩
      | succ i' =>
        nomatch (Nat.not_lt_zero i' (Nat.succ_lt_succ_iff.mp hi_lt))
    · intro i j hi_lt hj_lt hij
      generalize h_xs_gen : buildXSeq a σ w = xs at hi_lt hj_lt ⊢
      rw [h_xs] at h_xs_gen
      subst h_xs_gen
      cases i with
      | zero =>
        cases j with
        | zero => nomatch (lt_irrefl _ hij)
        | succ j' => nomatch (Nat.not_lt_zero _ (Nat.succ_lt_succ_iff.mp hj_lt))
      | succ i' =>
        nomatch (Nat.not_lt_zero _ (Nat.succ_lt_succ_iff.mp hi_lt))
termination_by (Finset.univ.filter (fun z => w < z)).card
decreasing_by
  classical
  have hw_lt : w < Finset.min' _ h := (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1
  have h_le : Finset.univ.filter (fun z => (Finset.min' _ h) < z) ⊆ Finset.univ.filter
    (fun z => w < z) := fun _ hz => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1, lt_trans
      hw_lt (Finset.mem_filter.mp hz).2⟩
  have h_ne : Finset.univ.filter (fun z => (Finset.min' _ h) < z) ≠ Finset.univ.filter
    (fun z => w < z) := fun heq => lt_irrefl _ (Finset.mem_filter.mp
      (heq.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_lt⟩ : (Finset.min' _ h) ∈ _)).2
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

/-- An element in an open interval `OpenIntervalType` cannot be an element of the sequence `xs`. -/
lemma not_mem_of_openInterval {α : Type*} [LinearOrder α] {xs : List α}
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length),
    i < j → xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩) (i : ℕ) (z : α)
    (h_in : ∃ (hi_lt : i < xs.length), xs.get ⟨i, hi_lt⟩ < z ∧ ∀ (hi_succ_lt : i + 1 < xs.length),
    z < xs.get ⟨i + 1, hi_succ_lt⟩) : z ∉ xs := by
  intro hz_mem
  obtain ⟨j, hz_eq⟩ := List.mem_iff_get.mp hz_mem
  grind

/-- If two elements are related by an interval split,
they must belong to the same interval in `buildXSeq`. -/
lemma buildXSeq_same_interval_of_splitRelation {α : Type*} [LinearOrder α] {n : ℕ}
    (xs : List α)
    (s : Split α n)
    (C : ℕ)
    (h_xs_mono : ∀ (i j : ℕ) (h1 : i < xs.length) (h2 : j < xs.length), i < j →
      xs.get ⟨i, h1⟩ < xs.get ⟨j, h2⟩)
    (rank_ge_diff_of_mem : ∀ z, z ∈ xs → C ≤ (s z).val)
    (rank_lt_diff_of_not_mem : ∀ z, z ∉ xs → (s z).val < C)
    (p q : α)
    (hp : p ∉ xs) (hq : q ∉ xs)
    (hsr_pq : SplitRelation s p q)
    (i j : ℕ)
    (p_oi : OpenIntervalType xs i) (q_oi : OpenIntervalType xs j)
    (hp_eq : p_oi.val = p) (hq_eq : q_oi.val = q) :
    i = j := by
  obtain ⟨hi_lt, h_lt_pi, h_gt_pi⟩ := p_oi.prop
  obtain ⟨hj_lt, h_lt_qj, h_gt_qj⟩ := q_oi.prop
  rw [hp_eq] at h_lt_pi h_gt_pi
  rw [hq_eq] at h_lt_qj h_gt_qj
  rcases lt_trichotomy i j with h_ij | rfl | h_ji
  · exfalso
    have hi1 : i + 1 < xs.length := by omega
    have h_px : p < xs.get ⟨i + 1, hi1⟩ := h_gt_pi hi1
    have h_xj : xs.get ⟨i + 1, hi1⟩ ≤ xs.get ⟨j, hj_lt⟩ :=
      (Nat.succ_le_of_lt h_ij).eq_or_lt.elim (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
        (fun h => le_of_lt (h_xs_mono _ _ _ _ h))
    have h_pq : p < q := lt_trans h_px (lt_of_le_of_lt h_xj h_lt_qj)
    have hb := hsr_pq.right _ ((min_eq_left (le_of_lt h_pq)).symm ▸ le_of_lt h_px)
      ((max_eq_right (le_of_lt h_pq)).symm ▸ le_trans h_xj (le_of_lt h_lt_qj))
    have h1 := rank_ge_diff_of_mem _ (xs.get_mem ⟨_, hi1⟩)
    have h2 := rank_lt_diff_of_not_mem p hp
    rw [min_eq_left (le_of_lt h_pq)] at hb
    have := Fin.le_iff_val_le_val.mp hb
    omega
  · rfl
  · exfalso
    have hj1 : j + 1 < xs.length := by omega
    have h_qx : q < xs.get ⟨j + 1, hj1⟩ := h_gt_qj hj1
    have h_xi : xs.get ⟨j + 1, hj1⟩ ≤ xs.get ⟨i, hi_lt⟩ :=
      (Nat.succ_le_of_lt h_ji).eq_or_lt.elim (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
        (fun h => le_of_lt (h_xs_mono _ _ _ _ h))
    have h_qp : q < p := lt_trans h_qx (lt_of_le_of_lt h_xi h_lt_pi)
    have hb := hsr_pq.right _ ((min_eq_right (le_of_lt h_qp)).symm ▸ le_of_lt h_qx)
      ((max_eq_left (le_of_lt h_qp)).symm ▸ le_trans h_xi (le_of_lt h_lt_pi))
    have h1 := rank_ge_diff_of_mem _ (xs.get_mem ⟨_, hj1⟩)
    have h2 := rank_lt_diff_of_not_mem q hq
    rw [min_eq_right (le_of_lt h_qp)] at hb
    have := Fin.le_iff_val_le_val.mp hb
    omega

/-- Constructs splits for all open intervals using the inductive hypothesis. -/
lemma build_interval_splits_of_ih {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (_ : α) (xs : List α)
    (_ : ∀ (i j : ℕ) (h1 : i < xs.length) (h2 : j < xs.length), i < j →
      xs.get ⟨i, h1⟩ < xs.get ⟨j, h2⟩)
    (h_not_D : ∀ (i : ℕ) (h1 : i < xs.length) (y : α) (_ : xs.get ⟨i, h1⟩ < y)
      (_ : ∀ h2 : i + 1 < xs.length, y < xs.get ⟨i + 1, h2⟩),
      ¬ IsGreenD (σ.σ (xs.get ⟨i, h1⟩) y) a)
    (ih : ∀ b : S, nSElement b < nSElement a →
      ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
      (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
      ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∀ i [Nonempty (OpenIntervalType xs i)],
      ∃ (s : Split (OpenIntervalType xs i) (nSElement a)),
      IsRamsey (⟨fun x y => σ.σ x.val y.val, fun x y z hx hy => σ.prop x.val y.val z.val hx hy⟩ :
      MultiplicativeLabeling S (OpenIntervalType xs i)) s ∧
      ∀ z, (s z).val < nSElement a - nD (IsGreenD.eqvClass a) := by
  intro i h_ne
  let Y := OpenIntervalType xs i
  let y_min := Finset.min' (Finset.univ : Finset Y) Finset.univ_nonempty
  let y_max := Finset.max' (Finset.univ : Finset Y) Finset.univ_nonempty
  let σ_Y : MultiplicativeLabeling S (OpenIntervalType xs i) :=
    ⟨fun x y => σ.σ x.val y.val, fun x y z hx hy => σ.prop x.val y.val z.val hx hy⟩
  classical
  have h_eq_a : nSElement a = nD (IsGreenD.eqvClass a) + (Finset.univ.filter
    (fun (y : S) => GreenJClass.mk a < GreenJClass.mk y)).attach.sup
    (fun ⟨y, _hy⟩ => nSElement y) := by
    conv => lhs; unfold nSElement
  by_cases h_lt : y_min < y_max
  · let b := σ_Y.σ y_min y_max
    obtain ⟨h1, h_x_lt_ymin, _⟩ := y_min.prop
    obtain ⟨_, _, h_ymax_gt⟩ := y_max.prop
    let x_val := xs.get ⟨i, h1⟩
    have h_x_lt_ymax : x_val < y_max.val := lt_trans h_x_lt_ymin h_lt
    have h_b_le : GreenJClass.mk (σ.σ x_val y_max.val) ≤ GreenJClass.mk b := by
      rw [(σ.prop x_val y_min.val y_max.val h_x_lt_ymin h_lt).symm]
      exact IsGreenJRel.mul_left (σ.σ x_val y_min.val) rfl
    have h_a_le : GreenJClass.mk a ≤ GreenJClass.mk (σ.σ x_val y_max.val) :=
      h_img x_val y_max.val h_x_lt_ymax
    have h_a_ne_b : GreenJClass.mk a ≠ GreenJClass.mk b := fun heq =>
      have h_eq_mid : GreenJClass.mk (σ.σ x_val y_max.val) = GreenJClass.mk a :=
        le_antisymm (heq ▸ h_b_le) h_a_le
      h_not_D i h1 y_max.val h_x_lt_ymax h_ymax_gt (isGreenD_of_isGreenJ
        (GreenJClass.mk_eq_mk_iff.mp h_eq_mid))
    have h_b_in : b ∈ Finset.univ.filter (fun y : S => GreenJClass.mk a < GreenJClass.mk y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ b, lt_of_le_of_ne (le_trans h_a_le h_b_le) h_a_ne_b⟩
    have h_sup : nSElement b ≤ _ := Finset.le_sup (f := fun ⟨y, _hy⟩ => nSElement y)
      (Finset.mem_attach _ ⟨b, h_b_in⟩)
    have h_lt_a : nSElement b < nSElement a := by
      have := nD_pos _ ⟨a, rfl⟩
      rw [h_eq_a]
      omega
    have h_img_b : labelingIn σ_Y (jUp b) :=
      fun u v huv => labeling_factor_le_J σ y_min.val u.val v.val y_max.val
      (Finset.min'_le _ _ (Finset.mem_univ u)) huv (Finset.le_max' _ _ (Finset.mem_univ v))
    obtain ⟨s_b, _, hs_b_ramsey⟩ := ih b h_lt_a xs i σ_Y h_img_b
    have hsr_iff : ∀ u v, SplitRelation (fun x => ⟨(s_b x).val,
      Nat.lt_trans (s_b x).isLt h_lt_a⟩) u v ↔ SplitRelation s_b u v :=
      fun u v => ⟨fun ⟨heq, hb⟩ => ⟨Fin.ext (by have h_val := congrArg Fin.val heq; exact h_val),
        fun z h1 h2 => Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp (hb z h1 h2))⟩,
                  fun ⟨heq, hb⟩ => ⟨Fin.ext (by have h_val := congrArg Fin.val heq; exact h_val),
                    fun z h1 h2 => Fin.le_iff_val_le_val.mpr
                      (Fin.le_iff_val_le_val.mp (hb z h1 h2))⟩⟩
    have hs_b_lift_ramsey : IsRamsey σ_Y
      (fun x => ⟨(s_b x).val, Nat.lt_trans (s_b x).isLt h_lt_a⟩) :=
      And.intro
        (fun u v huv hsr => hs_b_ramsey.1 u v huv ((hsr_iff u v).mp hsr))
        (fun x y u v hx hu hxy huv hxu => hs_b_ramsey.2 x y u v hx hu ((hsr_iff x y).mp hxy)
          ((hsr_iff u v).mp huv) ((hsr_iff x u).mp hxu))
    have h_bound : ∀ z, ((fun x => ⟨(s_b x).val, Nat.lt_trans (s_b x).isLt h_lt_a⟩ :
      Split _ (nSElement a)) z).val < nSElement a - nD (IsGreenD.eqvClass a) := fun z => by
      have hz := (s_b z).isLt
      change (s_b z).val < _
      rw [h_eq_a]
      omega
    exact ⟨fun x => ⟨(s_b x).val, Nat.lt_trans (s_b x).isLt h_lt_a⟩,
      And.intro hs_b_lift_ramsey h_bound⟩
  · have h_ramsey_vacuous : IsRamsey σ_Y (fun _ => ⟨0, nSElement_pos a⟩) :=
      And.intro
        (fun u v huv _ => nomatch (h_lt (lt_of_le_of_lt (Finset.min'_le _ _ (Finset.mem_univ u))
          (lt_of_lt_of_le huv (Finset.le_max' _ _ (Finset.mem_univ v))))))
        (fun x y _ _ hxy _ _ _ _ => nomatch (h_lt (lt_of_le_of_lt
          (Finset.min'_le _ _ (Finset.mem_univ x)) (lt_of_lt_of_le hxy
            (Finset.le_max' _ _ (Finset.mem_univ y))))))
    have h_Delta_pos : 0 < nSElement a - nD (IsGreenD.eqvClass a) := by
      obtain ⟨y, h1, hw_lt_y, h_y_lt_z⟩ := Classical.choice h_ne
      let b := σ.σ (xs.get ⟨i, h1⟩) y
      have h_a_ne_b : GreenJClass.mk a ≠ GreenJClass.mk b := fun heq =>
        h_not_D i h1 y hw_lt_y h_y_lt_z (isGreenD_of_isGreenJ
          (GreenJClass.mk_eq_mk_iff.mp heq.symm))
      have h_b_in : b ∈ Finset.univ.filter (fun y : S => GreenJClass.mk a < GreenJClass.mk y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, lt_of_le_of_ne
          (h_img (xs.get ⟨i, h1⟩) y hw_lt_y) h_a_ne_b⟩
      have h_sup : nSElement b ≤ _ := Finset.le_sup (f := fun ⟨y, _hy⟩ => nSElement y)
        (Finset.mem_attach _ ⟨b, h_b_in⟩)
      have h_pos := nSElement_pos b
      rw [h_eq_a]
      omega
    exact ⟨fun _ => ⟨0, nSElement_pos a⟩, And.intro h_ramsey_vacuous (fun _ => h_Delta_pos)⟩

/-- Combines an overarching regular split with interval-specific splits to form
a single split over the entire domain. -/
noncomputable abbrev combineSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) := fun x =>
  if hx : x ∈ xs then
    rankX ⟨x, hx⟩
  else if h_ex : ∃ i, ∃ (h1 : i < xs.length),
    xs.get ⟨i, h1⟩ < x ∧ ∀ (h2 : i + 1 < xs.length), x < xs.get ⟨i + 1, h2⟩ then
    @sY (Classical.choose h_ex) ⟨⟨x, Classical.choose_spec h_ex⟩⟩
      ⟨x, Classical.choose_spec h_ex⟩
  else
    ⟨0, nSElement_pos a⟩

/-- Two open intervals based on a strictly increasing sequence are disjoint. -/
lemma openInterval_unique {α : Type*} [LinearOrder α] (xs : List α)
    (h_mono : ∀ (i j : ℕ) (h1 : i < xs.length)
    (h2 : j < xs.length), i < j → xs.get ⟨i, h1⟩ < xs.get ⟨j, h2⟩)
    (x : α) (i k : ℕ) (hi : i < xs.length) (hk : k < xs.length)
    (hlt_i : xs.get ⟨i, hi⟩ < x) (hgt_i : ∀ h2 : i + 1 < xs.length, x < xs.get ⟨i + 1, h2⟩)
    (hlt_k : xs.get ⟨k, hk⟩ < x) (hgt_k : ∀ h2 : k + 1 < xs.length, x < xs.get ⟨k + 1, h2⟩) :
    i = k := by
  rcases lt_trichotomy i k with h | rfl | h
  · exfalso
    grind
  · rfl
  · exfalso
    grind

/-- The `combineSplits` function preserves the Ramsey property
for elements within the same open interval. -/
lemma combineSplits_interval_ramsey {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], Split (OpenIntervalType xs i) (nSElement a))
    (C : ℕ)
    (h_mono : ∀ (i j : ℕ) (h1 : i < xs.length) (h2 : j < xs.length),
    i < j → xs.get ⟨i, h1⟩ < xs.get ⟨j, h2⟩)
    (h_covers : ∀ x, x ∉ xs → ∃ i, ∃ h1 : i < xs.length, xs.get ⟨i, h1⟩ < x ∧ ∀ h2 :
    i + 1 < xs.length, x < xs.get ⟨i + 1, h2⟩) (h_sY_bound : ∀ i [Nonempty (OpenIntervalType xs i)]
    (z : OpenIntervalType xs i), (sY i z).val < C) (h_rankX_bound : ∀ x, C ≤ (rankX x).val) :
    ∀ x y, x ∉ xs → x < y → SplitRelation (combineSplits a xs rankX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧ SplitRelation (@sY i ⟨x_val⟩) x_val y_val := by
  intros x y hx_not_in hlt hsr
  obtain ⟨i, hx_lt, h_lt_x, h_gt_x⟩ := h_covers x hx_not_in
  let x_val : OpenIntervalType xs i := ⟨x, hx_lt, h_lt_x, h_gt_x⟩
  have h_r : ∀ w (hw_not : w ∉ xs) k (w_val : OpenIntervalType xs k), w_val.val = w →
      combineSplits a xs rankX sY w = @sY k ⟨w_val⟩ w_val := fun w hw_not k w_val hw_eq => by
    simp only [combineSplits, dif_neg hw_not]
    have hw_ex : ∃ m, ∃ hm : m < xs.length, xs.get ⟨m, hm⟩ < w ∧
      ∀ h2, w < xs.get ⟨m + 1, h2⟩ := ⟨k, hw_eq ▸ w_val.prop⟩
    rw [dif_pos hw_ex]
    have heq_idx : Classical.choose hw_ex = k := by
      obtain ⟨hk1, hlt1, hgt1⟩ := Classical.choose_spec hw_ex
      obtain ⟨hk2, hlt2, hgt2⟩ := w_val.prop
      have hlt2_w : xs.get ⟨k, hk2⟩ < w := hw_eq ▸ hlt2
      have hgt2_w : ∀ h2, w < xs.get ⟨k + 1, h2⟩ := fun h2 => hw_eq ▸ hgt2 h2
      exact openInterval_unique xs h_mono w _ k hk1 hk2 hlt1 hgt1 hlt2_w hgt2_w
    haveI h_nonempty : Nonempty (OpenIntervalType xs k) := ⟨w_val⟩
    have helper : ∀ k' (hk' : Nonempty _) (heq : k' = k) wk', wk'.val = w_val.val →
      @sY k' hk' wk' = @sY k ⟨w_val⟩ w_val := by
        rintro k' hk' rfl wk' h_val
        rw [Subtype.ext h_val]
    exact helper (Classical.choose hw_ex) _ heq_idx _ hw_eq.symm
  have hs_x_val : (combineSplits a xs rankX sY x).val < C :=
    (h_r x hx_not_in i x_val rfl).symm ▸ @h_sY_bound i ⟨x_val⟩ x_val
  have hy_not_in : y ∉ xs := fun hy_in => by
    have hs_y_val : C ≤ (combineSplits a xs rankX sY y).val := by
      simp only [combineSplits, dif_pos hy_in]
      exact h_rankX_bound ⟨y, hy_in⟩
    have h_eq : (combineSplits a xs rankX sY x).val = (combineSplits a xs rankX sY y).val :=
      congrArg Fin.val hsr.left
    omega
  obtain ⟨j, hy_lt, h_lt_y, h_gt_y⟩ := h_covers y hy_not_in
  have hij : i = j := by
    rcases lt_trichotomy i j with h_ij | rfl | h_ji
    · have hi1 : i + 1 < xs.length := by omega
      let z := xs.get ⟨i + 1, hi1⟩
      have hz_in : z ∈ xs := xs.get_mem ⟨i + 1, hi1⟩
      have h_z_gt_y : y < z := by
        by_contra h_not_lt
        have hz_bound : min x y ≤ z ∧ z ≤ max x y := by
          rw [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
          exact ⟨le_of_lt (h_gt_x hi1), not_lt.mp h_not_lt⟩
        have h_sz_val : C ≤ (combineSplits a xs rankX sY z).val := by
          simp only [combineSplits, dif_pos hz_in]
          exact h_rankX_bound ⟨z, hz_in⟩
        have h_le_val := Fin.le_iff_val_le_val.mp (hsr.right z hz_bound.1 hz_bound.2)
        rw [min_eq_left (le_of_lt hlt)] at h_le_val
        omega
      have h_z_le_j : z ≤ xs.get ⟨j, hy_lt⟩ :=
        (Nat.succ_le_of_lt h_ij).eq_or_lt.elim
          (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
          (fun h => le_of_lt (h_mono _ _ _ _ h))
      nomatch (lt_irrefl y (lt_of_lt_of_le (lt_of_lt_of_le h_z_gt_y h_z_le_j)
        (le_of_lt h_lt_y)))
    · rfl
    · have hj1 : j + 1 < xs.length := by omega
      have h_w_le_x : xs.get ⟨j + 1, hj1⟩ ≤ xs.get ⟨i, hx_lt⟩ :=
        (Nat.succ_le_of_lt h_ji).eq_or_lt.elim
          (fun e => le_of_eq (congrArg xs.get (Fin.ext e)))
          (fun h => le_of_lt (h_mono _ _ _ _ h))
      nomatch (lt_irrefl x (lt_trans hlt (lt_of_lt_of_le (h_gt_y hj1)
        (le_trans h_w_le_x (le_of_lt h_lt_x)))))
  subst hij
  let y_val : OpenIntervalType xs i := ⟨y, hy_lt, h_lt_y, h_gt_y⟩
  haveI : Nonempty (OpenIntervalType xs i) := ⟨x_val⟩
  exact ⟨i, x_val, y_val, rfl, rfl, by
    have h_rx : combineSplits a xs rankX sY x = sY i x_val := h_r x hx_not_in i x_val rfl
    have h_ry : combineSplits a xs rankX sY y = sY i y_val := h_r y hy_not_in i y_val rfl
    exact ⟨Fin.ext (h_ry.symm ▸ h_rx.symm ▸ congrArg Fin.val hsr.left), fun z_val hz1 hz2 =>
      Fin.le_iff_val_le_val.mpr (by
        have hz_not_in : z_val.val ∉ xs := not_mem_of_openInterval h_mono i z_val.val z_val.prop
        have h_rz : combineSplits a xs rankX sY z_val.val = sY i z_val :=
          h_r z_val.val hz_not_in i z_val rfl
        have h_bound_val := Fin.le_iff_val_le_val.mp (hsr.right z_val.val hz1 hz2)
        have hs_min_eq : combineSplits a xs rankX sY (min x y) = sY i (min x_val y_val) := by
          rcases min_choice x y with h | h
          · have hxy : x ≤ y := by
              rw [← h]
              exact min_le_right x y
            have h_le : x_val ≤ y_val := hxy
            rw [min_eq_left h_le, h, h_rx]
          · have hyx : y ≤ x := by
              rw [← h]
              exact min_le_left x y
            have h_le : y_val ≤ x_val := hyx
            rw [min_eq_right h_le, h, h_ry]
        exact congrArg Fin.val hs_min_eq.symm ▸ congrArg Fin.val h_rz.symm ▸ h_bound_val
      )⟩
  ⟩

/-- Proves the normalization and Ramsey properties for the combined split. -/
lemma combineSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α) (C : ℕ)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (rankX : {x // x ∈ xs} → Fin (nSElement a))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)], IsRamsey (σ_Y i) (sY i))
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs → ∃ (i : ℕ) (h1 : i < xs.length), xs.get ⟨i, h1⟩ < x ∧
      ∀ (h2 : i + 1 < xs.length), x < xs.get ⟨i + 1, h2⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (z : OpenIntervalType xs i), (sY i z).val < C)
    (h_rankX_ge : ∀ x (hx : x ∈ xs), C ≤ (rankX ⟨x, hx⟩).val)
    (h_xs_mono : ∀ (i j : ℕ) (h1 : i < xs.length)
      (h2 : j < xs.length), i < j → xs.get ⟨i, h1⟩ < xs.get ⟨j, h2⟩)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (combineSplits a xs rankX sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val)
    (h_X_ramsey_1 : ∀ x y, x ∈ xs → y ∈ xs → x < y →
      SplitRelation (combineSplits a xs rankX sY) x y →
      σ.σ x y * σ.σ x y = σ.σ x y)
    (h_X_ramsey_2 : ∀ x y u v, x ∈ xs → y ∈ xs → u ∈ xs → v ∈ xs → x < y → u < v →
      SplitRelation (combineSplits a xs rankX sY) x y →
      SplitRelation (combineSplits a xs rankX sY) u v →
      SplitRelation (combineSplits a xs rankX sY) x u →
      σ.σ x y = σ.σ u v)
    (h_min_norm : (combineSplits a xs rankX sY
      (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty)).val = nSElement a - 1)
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
    Finset.univ_nonempty).val = nSElement a - 1) : IsNormalized (combineSplits a xs rankX sY) ∧
    IsRamsey σ (combineSplits a xs rankX sY) := by
  constructor
  · apply Fin.ext
    simp only [combineSplits]
    rw [h_min_norm, h_max_val]
  · have rank_lt_diff_of_not_mem : ∀ z, z ∉ xs →
        (combineSplits a xs rankX sY z).val < C := by
      intro z hz
      have h_ex := h_cov z hz
      simp only [combineSplits, hz, h_ex, ↓reduceDIte]
      exact @hsY_strict _ ⟨⟨z, Classical.choose_spec h_ex⟩⟩ ⟨z, Classical.choose_spec h_ex⟩
    have rank_ge_diff_of_mem : ∀ z, z ∈ xs →
        C ≤ (combineSplits a xs rankX sY z).val := by
      intro z hz
      have h_val : (combineSplits a xs rankX sY z).val = (rankX ⟨z, hz⟩).val := by
        simp only [combineSplits, dif_pos hz]
      rw [h_val]
      exact h_rankX_ge z hz
    have mem_of_sr_mem : ∀ p q, p ∈ xs →
        SplitRelation (combineSplits a xs rankX sY) p q → q ∈ xs := by
      intro p q hp hsr_pq
      by_contra hnq
      have hq_lt := rank_lt_diff_of_not_mem q hnq
      have hp_ge := rank_ge_diff_of_mem p hp
      have hpq_eq := congrArg Fin.val hsr_pq.left
      omega
    have not_mem_of_sr_not_mem : ∀ p q, p ∉ xs →
        SplitRelation (combineSplits a xs rankX sY) p q → q ∉ xs := by
      intro p q hp hsr_pq hq
      have hp_lt := rank_lt_diff_of_not_mem p hp
      have hq_ge := rank_ge_diff_of_mem q hq
      have hpq_eq := congrArg Fin.val hsr_pq.left
      omega
    have same_interval : ∀ (p q : α),
        p ∉ xs → q ∉ xs →
        SplitRelation (combineSplits a xs rankX sY) p q →
        ∀ (i j : ℕ) (p_oi : OpenIntervalType xs i) (q_oi : OpenIntervalType xs j),
        p_oi.val = p → q_oi.val = q → i = j := by
      exact buildXSeq_same_interval_of_splitRelation xs (combineSplits a xs rankX sY) C
        h_xs_mono rank_ge_diff_of_mem rank_lt_diff_of_not_mem
    constructor
    · intro x y hlt hsr
      by_cases hx : x ∈ xs
      · have hy : y ∈ xs := mem_of_sr_mem x y hx hsr
        exact h_X_ramsey_1 x y hx hy hlt hsr
      · obtain ⟨i, x_val, y_val, rfl, rfl, hsr_Y⟩ := h_interval_ramsey x y hx hlt hsr
        simpa only [h_σ_Y] using (@hsY_ramsey i ⟨x_val⟩).1 x_val y_val hlt hsr_Y
    · intro x y u v hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu
      by_cases hx : x ∈ xs
      · have hu := mem_of_sr_mem x u hx hsr_xu
        have hy := mem_of_sr_mem x y hx hsr_xy
        have hv := mem_of_sr_mem u v hu hsr_uv
        exact h_X_ramsey_2 x y u v hx hy hu hv hlt_xy hlt_uv hsr_xy hsr_uv hsr_xu
      · have hu := not_mem_of_sr_not_mem x u hx hsr_xu
        obtain ⟨i, x_oi, y_oi, hx_eq, hy_eq, hsr_Y_xy⟩ := h_interval_ramsey _ _ hx hlt_xy hsr_xy
        obtain ⟨j, u_oi, v_oi, hu_eq, hv_eq, hsr_Y_uv⟩ := h_interval_ramsey _ _ hu hlt_uv hsr_uv
        have hij : i = j := same_interval x u hx hu hsr_xu i j x_oi u_oi hx_eq hu_eq
        subst hij
        have hsr_Y_xu : SplitRelation (@sY i ⟨x_oi⟩) x_oi u_oi := by
          have sY_val_eq : ∀ (z_oi : OpenIntervalType xs i),
              haveI : Nonempty (OpenIntervalType xs i) := ⟨z_oi⟩
              (combineSplits a xs rankX sY z_oi.val).val = (sY i z_oi).val := by
            intro z_oi
            have hz_not_in : z_oi.val ∉ xs := not_mem_of_openInterval h_xs_mono i z_oi.val z_oi.prop
            have hz_ex : ∃ k, ∃ h1 : k < xs.length, xs.get ⟨k, h1⟩ < z_oi.val ∧
              ∀ h2 : k + 1 < xs.length, z_oi.val < xs.get ⟨k + 1, h2⟩ := ⟨i, z_oi.prop⟩
            simp only [combineSplits, dif_neg hz_not_in, dif_pos hz_ex]
            have heq_idx : Classical.choose hz_ex = i := by
              obtain ⟨hk_lt, hlt_k, hgt_k⟩ := Classical.choose_spec hz_ex
              obtain ⟨hi_lt, hlt_i, hgt_i⟩ := z_oi.prop
              rcases lt_trichotomy (Classical.choose hz_ex) i with h | h | h
              · exfalso
                grind
              · exact h
              · exfalso
                have hi_succ_lt : i + 1 < xs.length := by omega
                have h_z_lt := hgt_i hi_succ_lt
                rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with heq | hlt
                · have h_eq : xs.get ⟨i + 1, hi_succ_lt⟩ = xs.get ⟨Classical.choose hz_ex, hk_lt⟩ :=
                    congrArg xs.get (Fin.ext heq)
                  rw [h_eq] at h_z_lt
                  exact lt_irrefl _ (lt_trans h_z_lt hlt_k)
                · have h_le := le_of_lt (h_xs_mono _ _ hi_succ_lt hk_lt hlt)
                  exact lt_irrefl _ (lt_trans h_z_lt (lt_of_le_of_lt h_le hlt_k))
            have helper : ∀ (k : ℕ) (hk_nonempty : Nonempty (OpenIntervalType xs k)) (hk : k = i),
              ∀ (zk : OpenIntervalType xs k) (zi : OpenIntervalType xs i),
              haveI : Nonempty (OpenIntervalType xs i) := ⟨zi⟩
              zk.val = zi.val → (@sY k hk_nonempty zk).val = (sY i zi).val := by
              intro k hk_nonempty hk zk zi h_val
              subst hk
              have h_eq : zk = zi := Subtype.ext h_val
              rw [h_eq]
            exact helper (Classical.choose hz_ex) ⟨⟨z_oi.val, Classical.choose_spec hz_ex⟩⟩
              heq_idx ⟨z_oi.val, Classical.choose_spec hz_ex⟩ z_oi rfl
          constructor
          · apply Fin.ext
            have h_eq := congrArg Fin.val hsr_xu.left
            haveI : Nonempty (OpenIntervalType xs i) := ⟨x_oi⟩
            exact (sY_val_eq u_oi).symm ▸ (sY_val_eq x_oi).symm ▸ hu_eq ▸ hx_eq ▸ h_eq
          · intro z_oi hz1 hz2
            have hz1_alpha : min x u ≤ z_oi.val := hu_eq ▸ hx_eq ▸ hz1
            have hz2_alpha : z_oi.val ≤ max x u := hu_eq ▸ hx_eq ▸ hz2
            have h_bound_val := Fin.le_iff_val_le_val.mp (hsr_xu.right z_oi.val hz1_alpha hz2_alpha)
            apply Fin.le_iff_val_le_val.mpr
            haveI : Nonempty (OpenIntervalType xs i) := ⟨x_oi⟩
            have hs_min_eq : (combineSplits a xs rankX sY (min x u)).val =
              (sY i (min x_oi u_oi)).val := by
              rcases min_choice x u with h | h
              · have h_le : x_oi ≤ u_oi :=
                  (hu_eq ▸ hx_eq ▸ h.symm ▸ min_le_right x u : x_oi.val ≤ u_oi.val)
                rw [h, ← hx_eq, min_eq_left h_le, sY_val_eq x_oi]
              · have h_le : u_oi ≤ x_oi :=
                  (hu_eq ▸ hx_eq ▸ h.symm ▸ min_le_left x u : u_oi.val ≤ x_oi.val)
                rw [h, ← hu_eq, min_eq_right h_le, sY_val_eq u_oi]
            exact hs_min_eq.symm ▸ (sY_val_eq z_oi).symm ▸ h_bound_val
        have h_ramsey := (@hsY_ramsey i ⟨x_oi⟩).2 x_oi y_oi u_oi v_oi
          (hx_eq.symm ▸ hy_eq.symm ▸ hlt_xy : x_oi.val < y_oi.val)
          (hu_eq.symm ▸ hv_eq.symm ▸ hlt_uv : u_oi.val < v_oi.val)
          hsr_Y_xy hsr_Y_uv hsr_Y_xu
        exact hx_eq ▸ hy_eq ▸ hu_eq ▸ hv_eq ▸ (h_σ_Y i x_oi y_oi) ▸ (h_σ_Y i u_oi v_oi) ▸ h_ramsey

end FactorizationForest
