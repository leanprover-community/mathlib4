/-
Copyright (c) 2024 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson, Robert Y. Lewis, Keeley Hoek
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Hom.Basic

/-!
# Finite order homomorphisms.

The fundamental order homomorphisms between `Fin (n + 1)` and `Fin n`.

* `Fin.succAbove p i` : `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`.
* `Fin.succAboveEmb p` : `Fin.succAbove p` as an `OrderEmbedding`.
* `Fin.predAbove p i` : surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`.
-/

open Nat Function

namespace Fin

variable {n : ℕ}

section SuccAbove

/-- `succAbove p i` embeds `Fin n` into `Fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) (i : Fin n) : Fin (n + 1) :=
  if castSucc i < p then i.castSucc else i.succ

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `castSucc` when the resulting `i.castSucc < p`. -/
theorem succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : castSucc i < p) :
    p.succAbove i = castSucc i := if_pos h
#align fin.succ_above_below Fin.succAbove_of_castSucc_lt

theorem succAbove_of_succ_le (p : Fin (n + 1)) (i : Fin n) (h : succ i ≤ p) :
    p.succAbove i = castSucc i :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p ≤ castSucc i) :
    p.succAbove i = i.succ := if_neg h.not_lt
#align fin.succ_above_above Fin.succAbove_of_le_castSucc

theorem succAbove_of_lt_succ (p : Fin (n + 1)) (i : Fin n) (h : p < succ i) :
    p.succAbove i = succ i := succAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

theorem succAbove_succ_of_lt (p i : Fin n) (h : p < i) :
    succAbove p.succ i = i.succ := succAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)
theorem succAbove_succ_of_le (p i : Fin n) (h : i ≤ p) :
    succAbove p.succ i = i.castSucc := succAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h)
@[simp]
theorem succAbove_succ_self (j : Fin n) : j.succ.succAbove j = j.castSucc :=
  succAbove_succ_of_le _ _ le_rfl

theorem succAbove_castSucc_of_lt (p i : Fin n) (h : i < p) :
    succAbove p.castSucc i = i.castSucc :=
  succAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.mpr h)
theorem succAbove_castSucc_of_le (p i : Fin n) (h : p ≤ i) :
    succAbove p.castSucc i = i.succ :=
  succAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h)
@[simp]
theorem succAbove_castSucc_self (j : Fin n) : succAbove j.castSucc j = j.succ :=
  succAbove_castSucc_of_le _ _ le_rfl

theorem succAbove_pred_of_lt (p i : Fin (n + 1)) (h : p < i) (hi := ((zero_le p).trans_lt h).ne') :
    succAbove p (i.pred hi) = i := by
  rw [succAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h), succ_pred]
theorem succAbove_pred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hi : i ≠ 0):
    succAbove p (i.pred hi) = (i.pred hi).castSucc := succAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)
@[simp]
theorem succAbove_pred_self (p : Fin (n + 1)) (h : p ≠ 0) :
    succAbove p (p.pred h) = (p.pred h).castSucc := succAbove_pred_of_le _ _ le_rfl h

theorem succAbove_castPred_of_lt (p i : Fin (n + 1)) (h : i < p)
    (hi := ((le_last p).trans_lt' h).ne) : succAbove p (i.castPred hi) = i := by
  rw [succAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h), castSucc_castPred]
theorem succAbove_castPred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hi : i ≠ last n):
    succAbove p (i.castPred hi) = (i.castPred hi).succ :=
  succAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)
theorem succAbove_castPred_self (p : Fin (n + 1)) (h: p ≠ last n):
    succAbove p (p.castPred h) = (p.castPred h).succ :=
  succAbove_castPred_of_le _ _ le_rfl h

theorem succAbove_rev_left (p : Fin (n + 1)) (i : Fin n) :
    p.rev.succAbove i = (p.succAbove i.rev).rev := by
  obtain h | h := (rev p).succ_le_or_le_castSucc i
  · rw [succAbove_of_succ_le _ _ h,
      succAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), rev_succ, rev_rev]
  · rw [succAbove_of_le_castSucc _ _ h,
      succAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), rev_castSucc, rev_rev]
theorem succAbove_rev_right (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i.rev = (p.rev.succAbove i).rev := by
  rw [succAbove_rev_left, rev_rev]

/-- Embedding `i : Fin n` into `Fin (n + 1)` with a hole around `p : Fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  rcases p.castSucc_lt_or_lt_succ i with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h]
    exact h.ne
  · rw [succAbove_of_lt_succ _ _ h]
    exact h.ne'
#align fin.succ_above_ne Fin.succAbove_ne
theorem ne_succAbove (p : Fin (n + 1)) (i : Fin n) : p ≠ p.succAbove i :=
(succAbove_ne _ _).symm

theorem strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun i =>
    (castSucc_lt_succ i).le
#align fin.succ_above_aux Fin.strictMono_succAbove

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (strictMono_succAbove x).injective
#align fin.succ_above_right_injective Fin.succAbove_right_injective

/-- Given a fixed pivot `x : Fin (n + 1)`, `x.succAbove` is injective -/
theorem succAbove_right_inj {i j : Fin n} (x : Fin (n + 1)) :
    x.succAbove i = x.succAbove j ↔ i = j :=
  succAbove_right_injective.eq_iff
#align fin.succ_above_right_inj Fin.succAbove_right_inj

theorem succAbove_lt_succAbove_iff {i j : Fin n} (p : Fin (n + 1)) :
    succAbove p i < succAbove p j ↔ i < j := (strictMono_succAbove p).lt_iff_lt
theorem succAbove_le_succAbove_iff {i j : Fin n} (p : Fin (n + 1)) :
    succAbove p i ≤ succAbove p j ↔ i ≤ j := (strictMono_succAbove p).le_iff_le

/--  `Fin.succAbove p` as an `OrderEmbedding`. -/
@[simps! apply toEmbedding]
def succAboveEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)
#align fin.succ_above Fin.succAboveEmb

@[simp]
theorem succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · exact castSucc_zero'
  · exact bot_lt_iff_ne_bot.mpr ha
#align fin.succ_above_ne_zero_zero Fin.succAbove_ne_zero_zero

theorem succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAbove b = 0 ↔ b = 0 := by
  rw [← succAbove_ne_zero_zero ha, succAbove_right_inj]
#align fin.succ_above_eq_zero_iff Fin.succAbove_eq_zero_iff

theorem succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAbove b ≠ 0 :=
  mt (succAbove_eq_zero_iff ha).mp hb
#align fin.succ_above_ne_zero Fin.succAbove_ne_zero

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : succAbove (0 : Fin (n + 1)) = Fin.succ :=
  rfl
#align fin.succ_above_zero Fin.succAbove_zero

theorem succAbove_zero_apply (i : Fin n) : succAbove 0 i = succ i := by rw [succAbove_zero]

@[simp]
theorem succAbove_ne_last_last {a : Fin (n + 2)} (h : a ≠ last (n + 1)) :
    a.succAbove (last n) = last (n + 1) := by
  rw [succAbove_of_lt_succ _ _ (succ_last _ ▸ lt_top_iff_ne_top.mpr h), succ_last]

theorem succAbove_eq_last_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last _) :
    a.succAbove b = last _ ↔ b = last _ := by
  simp [← succAbove_ne_last_last ha, succAbove_right_inj]

theorem succAbove_ne_last {a : Fin (n + 2)} {b : Fin (n + 1)}
    (ha : a ≠ last _) (hb : b ≠ last _) : a.succAbove b ≠ last _ :=
  mt (succAbove_eq_last_iff ha).mp hb

/-- Embedding `Fin n` into `Fin (n + 1)` with a hole around `last n` embeds by `castSucc`. -/
@[simp]
theorem succAbove_last : succAbove (last n) = castSucc := by
  ext
  simp only [succAbove_of_castSucc_lt, castSucc_lt_last]
#align fin.succ_above_last Fin.succAbove_last

theorem succAbove_last_apply (i : Fin n) : succAbove (last n) i = castSucc i := by
  rw [succAbove_last]
#align fin.succ_above_last_apply Fin.succAbove_last_apply

@[deprecated] theorem succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) :
    castSucc i < p ∨ p ≤ castSucc i := lt_or_ge (castSucc i) p
#align fin.succ_above_lt_ge Fin.succAbove_lt_ge

@[deprecated castSucc_lt_or_lt_succ] alias succAbove_lt_gt := castSucc_lt_or_lt_succ

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
theorem succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ castSucc i < p := by
  cases' castSucc_lt_or_lt_succ p i with H H
  · rwa [iff_true_right H, succAbove_of_castSucc_lt _ _ H]
  · rw [castSucc_lt_iff_succ_le, iff_false_right H.not_le, succAbove_of_lt_succ _ _ H]
    exact H.le.not_lt
#align fin.succ_above_lt_iff Fin.succAbove_lt_iff_castSucc_lt

theorem succAbove_lt_iff_succ_le (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i < p ↔ succ i ≤ p := by
  rw [succAbove_lt_iff_castSucc_lt, castSucc_lt_iff_succ_le]

/-- Embedding `i : Fin n` into `Fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p ≤ castSucc i := by
  cases' castSucc_lt_or_lt_succ p i with H H
  · rw [iff_false_right H.not_le, succAbove_of_castSucc_lt _ _ H]
    exact H.le.not_lt
  · rwa [succAbove_of_lt_succ _ _ H, iff_true_left H, le_castSucc_iff]
#align fin.lt_succ_above_iff Fin.lt_succAbove_iff_le_castSucc

theorem lt_succAbove_iff_lt_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAbove i ↔ p < succ i := by
  rw [lt_succAbove_iff_le_castSucc, le_castSucc_iff]

/-- Embedding a positive `Fin n` results in a positive `Fin (n + 1)` -/
theorem succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H : castSucc i < p
  · simpa [succAbove_of_castSucc_lt _ _ H] using castSucc_pos' h
  · simp [succAbove_of_le_castSucc _ _ (le_of_not_lt H)]
#align fin.succ_above_pos Fin.succAbove_pos

theorem castPred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : castSucc x < y)
    (h' := ((le_last y).trans_lt' ((succAbove_lt_iff_castSucc_lt _ _).mpr h)).ne) :
    (y.succAbove x).castPred h' = x := by
  rw [castPred_eq_iff_eq_castSucc, succAbove_of_castSucc_lt _ _ h]
#align fin.cast_lt_succ_above Fin.castPred_succAbove

theorem pred_succAbove (x : Fin n) (y : Fin (n + 1)) (h : y ≤ castSucc x)
    (h' := (y.zero_le.trans_lt <| (lt_succAbove_iff_le_castSucc _ _).2 h).ne') :
    (y.succAbove x).pred h' = x := by simp only [succAbove_of_le_castSucc _ _ h, pred_succ]
#align fin.pred_succ_above Fin.pred_succAbove

theorem exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  cases' h.lt_or_lt with hlt hlt
  exacts [⟨_, succAbove_castPred_of_lt _ _ hlt⟩, ⟨_, succAbove_pred_of_lt _ _ hlt⟩]
#align fin.exists_succ_above_eq Fin.exists_succAbove_eq

@[simp]
theorem exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x := by
  refine' ⟨_, exists_succAbove_eq⟩
  rintro ⟨y, rfl⟩
  exact succAbove_ne _ _
#align fin.exists_succ_above_eq_iff Fin.exists_succAbove_eq_iff

/-- The range of `p.succAbove` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff
#align fin.range_succ_above Fin.range_succAbove

@[simp]
theorem range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ := by
  rw [← succAbove_zero]
  exact range_succAbove (0 : Fin (n + 1))
#align fin.range_succ Fin.range_succ

/-- `succAbove` is injective at the pivot -/
theorem succAbove_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succAbove] using congr_arg (fun f : Fin n → Fin (n + 1) => (Set.range f)ᶜ) h
#align fin.succ_above_left_injective Fin.succAbove_left_injective

/-- `succAbove` is injective at the pivot -/
@[simp]
theorem succAbove_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succAbove_left_injective.eq_iff
#align fin.succ_above_left_inj Fin.succAbove_left_inj

@[simp]
theorem zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ := by
  rfl
#align fin.zero_succ_above Fin.zero_succAbove

@[simp]
theorem succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : succAbove i.succ 0 = 0 :=
  succAbove_of_castSucc_lt i.succ 0 (by simp only [castSucc_zero', succ_pos])
#align fin.succ_succ_above_zero Fin.succ_succAbove_zero

/-- `succ` commutes with `succAbove`. -/
@[simp]
theorem succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAbove j.succ = (i.succAbove j).succ := by
  rcases lt_or_le i (succ j) with (h | h)
  · rw [succAbove_of_lt_succ _ _ h, succAbove_succ_of_lt _ _ h]
  · rwa [succAbove_of_castSucc_lt _ _ h, succAbove_succ_of_le, succ_castSucc]
#align fin.succ_succ_above_succ Fin.succ_succAbove_succ

/-- `castSucc` commutes with `succAbove`. -/
@[simp]
theorem castSucc_succAbove_castSucc {n : ℕ} {i : Fin (n + 1)} {j : Fin n} :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases le_or_lt i (castSucc j) with (h | h)
  · rw [succAbove_of_le_castSucc _ _ h, succAbove_castSucc_of_le _ _ h, succ_castSucc]
  · rw [succAbove_of_castSucc_lt _ _ h, succAbove_castSucc_of_lt _ _ h]

/-- `pred` commutes with `succAbove`. -/
theorem pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  simp_rw [← succ_inj (b := pred (succAbove a b) hk), ← succ_succAbove_succ, succ_pred]
#align fin.pred_succ_above_pred Fin.pred_succAbove_pred

/-- `castPred` commutes with `succAbove`. -/
theorem castPred_succAbove_castPred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ last (n + 1))
    (hb : b ≠ last n) (hk := succAbove_ne_last ha hb) :
    (a.castPred ha).succAbove (b.castPred hb) = (a.succAbove b).castPred hk := by
  simp_rw [← castSucc_inj (b := (a.succAbove b).castPred hk), ← castSucc_succAbove_castSucc,
    castSucc_castPred]

/-- `rev` commutes with `succAbove`. -/
lemma rev_succAbove (p : Fin (n + 1)) (i : Fin n) :
    rev (succAbove p i) = succAbove (rev p) (rev i) := by
  rw [succAbove_rev_left, rev_rev]

--@[simp] -- Porting note: can be proved by `simp`
theorem one_succAbove_zero {n : ℕ} : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  rfl
#align fin.one_succ_above_zero Fin.one_succAbove_zero

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succAbove_zero` or `succ_succAbove_zero`. -/
@[simp]
theorem succ_succAbove_one {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAbove 1 = (i.succAbove 0).succ := by
  rw [← succ_zero_eq_one']
  convert succ_succAbove_succ i 0
#align fin.succ_succ_above_one Fin.succ_succAbove_one

@[simp]
theorem one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ := by
  have := succ_succAbove_succ 0 j
  rwa [succ_zero_eq_one, zero_succAbove] at this
#align fin.one_succ_above_succ Fin.one_succAbove_succ

@[simp]
theorem one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 := by
  have := succ_succAbove_succ (0 : Fin (n + 2)) (0 : Fin (n + 2))
  simp only [succ_zero_eq_one, val_zero, Nat.cast_zero, zero_succAbove, succ_one_eq_two] at this
  exact this
#align fin.one_succ_above_one Fin.one_succAbove_one

end SuccAbove

section PredAbove

/-- `predAbove p i` surjects `i : Fin (n+1)` into `Fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : castSucc p < i then pred i ((zero_le _).trans_lt h).ne'
  else castPred i ((le_of_not_lt h).trans_lt (castSucc_lt_last _)).ne
#align fin.pred_above Fin.predAbove

theorem predAbove_of_le_castSucc (p : Fin n) (i : Fin (n + 1)) (h : i ≤ castSucc p)
    (hi := (h.trans_lt (castSucc_lt_last _)).ne) :
    p.predAbove i = i.castPred hi := dif_neg h.not_lt
#align fin.pred_above_below Fin.predAbove_of_le_castSucc
theorem predAbove_of_lt_succ (p : Fin n) (i : Fin (n + 1)) (h : i < succ p)
    (hi := ((le_last _).trans_lt' h).ne) :
    p.predAbove i = i.castPred hi := predAbove_of_le_castSucc _ _ (le_castSucc_iff.mpr h)

theorem predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : castSucc p < i)
    (hi := ((zero_le _).trans_lt h).ne') :
    p.predAbove i = i.pred hi := dif_pos h
#align fin.pred_above_above Fin.predAbove_of_castSucc_lt
theorem predAbove_of_succ_le (p : Fin n) (i : Fin (n + 1)) (h : succ p ≤ i)
    (hi := (h.trans_lt' (succ_pos _)).ne') :
    p.predAbove i = i.pred hi := predAbove_of_castSucc_lt _ _ (castSucc_lt_iff_succ_le.mpr h)

theorem predAbove_succ_of_lt (p i : Fin n) (h : i < p) (hi := succ_ne_last_of_lt h) :
    p.predAbove (succ i) = (i.succ).castPred hi := by
  rw [predAbove_of_lt_succ _ _ (succ_lt_succ_iff.mpr h)]
theorem predAbove_succ_of_le (p i : Fin n) (h : p ≤ i) :
    p.predAbove (succ i) = i := by
  rw [predAbove_of_succ_le _ _ (succ_le_succ_iff.mpr h), pred_succ]
@[simp]
theorem predAbove_succ_self (p : Fin n) : p.predAbove (succ p) = p :=
  predAbove_succ_of_le _ _ le_rfl

theorem predAbove_castSucc_of_lt (p i : Fin n) (h : p < i) (hi := castSucc_ne_zero_of_lt h) :
    p.predAbove (castSucc i) = i.castSucc.pred hi := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_castSucc_iff.mpr h)]
theorem predAbove_castSucc_of_le (p i : Fin n) (h : i ≤ p) :
    p.predAbove (castSucc i) = i := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_le_castSucc_iff.mpr h), castPred_castSucc]
@[simp]
theorem predAbove_castSucc_self (p : Fin n) : p.predAbove (castSucc p) = p :=
  predAbove_castSucc_of_le _ _ le_rfl

theorem predAbove_pred_of_lt (p i : Fin (n + 1)) (h : i < p) (hp := ((zero_le i).trans_lt h).ne')
    (hi := ((le_last p).trans_lt' h).ne) : (pred p hp).predAbove i = castPred i hi := by
  rw [predAbove_of_lt_succ _ _ (succ_pred _ _ ▸ h)]
theorem predAbove_pred_of_le (p i : Fin (n + 1)) (h : p ≤ i) (hp : p ≠ 0)
    (hi := (h.trans_lt' (pos_of_ne_zero hp)).ne') : (pred p hp).predAbove i = pred i hi := by
  rw [predAbove_of_succ_le _ _ (succ_pred _ _ ▸ h)]
theorem predAbove_pred_self (p : Fin (n + 1)) (hp : p ≠ 0) :
    (pred p hp).predAbove p = pred p hp := predAbove_pred_of_le _ _ le_rfl hp

theorem predAbove_castPred_of_lt (p i : Fin (n + 1)) (h : p < i)
    (hp := ((le_last i).trans_lt' h).ne) (hi := ((zero_le p).trans_lt h).ne') :
    (castPred p hp).predAbove i = pred i hi := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_castPred _ _ ▸ h)]
theorem predAbove_castPred_of_le (p i : Fin (n + 1)) (h : i ≤ p) (hp : p ≠ last n)
    (hi := (h.trans_lt (lt_top_iff_ne_top.mpr hp)).ne) :
    (castPred p hp).predAbove i = castPred i hi := by
  rw [predAbove_of_le_castSucc _ _ (castSucc_castPred _ _ ▸ h)]
theorem predAbove_castPred_self (p : Fin (n + 1)) (hp : p ≠ last n) :
    (castPred p hp).predAbove p = castPred p hp := predAbove_castPred_of_le _ _ le_rfl hp

theorem predAbove_rev_left (p : Fin n) (i : Fin (n + 1)) :
    p.rev.predAbove i = (p.predAbove i.rev).rev := by
  obtain h | h := (rev i).succ_le_or_le_castSucc p
  · rw [predAbove_of_succ_le _ _ h, rev_pred,
      predAbove_of_le_castSucc _ _ (rev_succ _ ▸ (le_rev_iff.mpr h)), castPred_inj, rev_rev]
  · rw [predAbove_of_le_castSucc _ _ h, rev_castPred,
      predAbove_of_succ_le _ _ (rev_castSucc _ ▸ (rev_le_iff.mpr h)), pred_inj, rev_rev]
theorem predAbove_rev_right (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i.rev = (p.rev.predAbove i).rev := by
  rw [predAbove_rev_left, rev_rev]

@[simp]
theorem predAbove_right_zero [NeZero n] {i : Fin n} : predAbove (i : Fin n) 0 = 0 := by
  cases n
  · exact i.elim0
  · rw [predAbove_of_le_castSucc _ _ (zero_le _), castPred_zero]

@[simp]
theorem predAbove_zero_succ [NeZero n] {i : Fin n} : predAbove 0 (i.succ) = i := by
  rw [predAbove_succ_of_le _ _ (Fin.zero_le' _)]
@[simp]
theorem succ_predAbove_zero [NeZero n] {j : Fin (n + 1)} (h : j ≠ 0) :
    succ (predAbove 0 j) = j := by
  rcases exists_succ_eq_of_ne_zero h with ⟨k, rfl⟩
  rw [predAbove_zero_succ]
@[simp]
theorem predAbove_zero_of_ne_zero [NeZero n] {i : Fin (n + 1)} (hi : i ≠ 0) :
    predAbove 0 i = i.pred hi := by
  rw [← exists_succ_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_zero_succ
#align fin.pred_above_zero Fin.predAbove_zero_of_ne_zero
theorem predAbove_zero [NeZero n] {i : Fin (n + 1)}:
    predAbove (0 : Fin n) i = if hi : i = 0 then 0 else i.pred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_zero]
  · rw [predAbove_zero_of_ne_zero hi]

@[simp]
theorem predAbove_right_last {i : Fin (n + 1)} : predAbove i (last (n + 1)) = last n := by
  rw [predAbove_of_castSucc_lt _ _ (castSucc_lt_last _), pred_last]
@[simp]
theorem predAbove_last_castSucc {i : Fin (n + 1)} :
    predAbove (last n) (i.castSucc) = i := by
  rw [predAbove_of_le_castSucc _ _ ((castSucc_le_castSucc_iff).mpr (le_last _)), castPred_castSucc]
@[simp]
theorem predAbove_last_of_ne_last {i : Fin (n + 2)} (hi : i ≠ last (n + 1)):
    predAbove (last n) i = castPred i hi := by
  rw [← exists_castSucc_eq] at hi
  rcases hi with ⟨y, rfl⟩
  exact predAbove_last_castSucc

theorem predAbove_last_apply {i : Fin (n + 2)} :
    predAbove (last n) i = if hi : i = last _ then last _ else i.castPred hi := by
  split_ifs with hi
  · rw [hi, predAbove_right_last]
  · rw [predAbove_last_of_ne_last hi]
#align fin.pred_above_last_apply Fin.predAbove_last_apply

theorem predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H
#align fin.pred_above_right_monotone Fin.predAbove_right_monotone

theorem predAbove_left_monotone (i : Fin (n + 1)) :
    Monotone fun p => predAbove p i := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
  · rfl
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone

/--  `Fin.predAbove p` as an `OrderHom`. -/
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩

/-- Sending `Fin (n+1)` to `Fin n` by subtracting one from anything above `p`
then back to `Fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ castSucc p) :
    p.castSucc.succAbove (p.predAbove i) = i := by
  obtain h | h := h.lt_or_lt
  · rw [predAbove_of_le_castSucc _ _ h.le, succAbove_castPred_of_lt _ _ h]
  · rw [predAbove_of_castSucc_lt _ _ h, succAbove_pred_of_lt _ _ h]
#align fin.succ_above_pred_above Fin.succAbove_predAbove

/-- Sending `Fin n` into `Fin (n + 1)` with a gap at `p`
then back to `Fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem predAbove_succAbove (p : Fin n) (i : Fin n) :
    p.predAbove ((castSucc p).succAbove i) = i := by
  obtain h | h := le_or_lt p i
  · rw [succAbove_castSucc_of_le _ _ h, predAbove_succ_of_le _ _ h]
  · rw [succAbove_castSucc_of_lt _ _ h, predAbove_castSucc_of_le _ _ h.le]
#align fin.pred_above_succ_above Fin.predAbove_succAbove

/-- `succ` commutes with `predAbove`. -/
@[simp]
theorem succ_predAbove_succ {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h | h := (le_or_lt (succ a) b)
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_succ_of_le _ _ h, succ_pred]
  · rw [predAbove_of_lt_succ _ _ h, predAbove_succ_of_lt _ _ h, succ_castPred_eq_castPred_succ]
#align fin.succ_pred_above_succ Fin.succ_predAbove_succ

/-- `castSucc` commutes with `predAbove`. -/
@[simp]
theorem castSucc_predAbove_castSucc {n : ℕ} (a : Fin n) (b : Fin (n + 1)) :
    a.castSucc.predAbove b.castSucc = (a.predAbove b).castSucc := by
  obtain h | h := (lt_or_le (castSucc a) b)
  · rw [predAbove_of_castSucc_lt _ _ h, predAbove_castSucc_of_lt _ _ h,
      castSucc_pred_eq_pred_castSucc]
  · rw [predAbove_of_le_castSucc _ _ h, predAbove_castSucc_of_le _ _ h, castSucc_castPred]

/-- `rev` commutes with `predAbove`. -/
theorem rev_predAbove {n : ℕ} (p : Fin n) (i : Fin (n + 1)) :
    (predAbove p i).rev = predAbove p.rev i.rev := by
  rw [predAbove_rev_left, rev_rev]

end PredAbove

end Fin
