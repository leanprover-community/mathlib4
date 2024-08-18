/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Theodore Hwa
-/
import Mathlib.SetTheory.Surreal.Multiplication
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.FieldSimp

/-!
# Surreal division

In this file, we prove that if `x` is a nonzero surreal number, then `x⁻¹` (defined in
`Mathlib.SetTheory.Game.Basic`) is a number and is a multiplicative inverse for `x`. We use that
to define the field structure on `Surreal`.

We essentially follow the proof in ONAG [Conway2001], chapter 1, theorem 10, with a few minor
differences explained below. There are four lemmas stated there, (i) through (iv). They are only
proved for positive numbers `x`. Once we have defined the inverse for positive `x`, it is extended
in the obvious way to negative numbers.

The desired final results are (ii) and (iv) which state that `x⁻¹` is a number and is a
multiplicative inverse, respectively.

In our proof, lemmas (i) through (iv) are proved for positive numbers in the section labeled
`Positive` by a series of preliminary lemmas, culminating in the lemma `onag_1_10` which
proves (ii) and (iv) by a joint induction over the two statements. Lemmas (i) and (iii) are used
only within the proof of `onag_1_10` and are not needed as induction hypotheses.

We do not use the notation `x⁻¹` in the proof of lemmas (i) to (iv); we use `x.inv'` instead
since that is the definition for positive `x`. We only use `x⁻¹` at the very end when we define
the inverse for all nonzero surreals, both positive and negative.

## Differences with ONAG

Conway starts by replacing `x` with an equal game which I have called its `normalization`.
However, the normalization is not actually needed until parts (iii) and (iv) of the proof,
so we do not use it until those parts.

For convenience, we split (iii) into 2 lemmas, the Left and Right statements.

The proof of (iii) in ONAG has a minor gap. It does not work for the Left option `x' = 0`. However,
in that case, (iii) reduces to (i). It is treated as a separate case in our proof.

## Notation

Throughout the proof of lemmas (i) to (iv), we use the same notation as in ONAG:

`x` : the positive number whose inverse we are constructing
`x'` : a positive option of `x`, indexed by `i`
`y` : the purported inverse of `x`, as defined by `x.inv'`
`y'` : an option of `y`, indexed by `i'`
`y''` : `(1 + (x' - x) * y') / x'` , the form of any option of `y` besides 0, indexed by `i''`

## References

* [Conway, *On numbers and games*][Conway2001]

-/
open SetTheory
open PGame
open Equiv

variable {x : PGame} (x_num : x.Numeric)

namespace Surreal.Division
section Positive

variable (x_pos : 0 < x)

/-! ### A few random positivity lemmas -/

/-- This applies to an arbitrary `LinearCommOrderedRing` and probably should go elsewhere. -/
lemma inv_pos_of_pos {x y : Surreal} (h_inv: x * y = 1) (h : 0 < x) : 0 < y := by
  apply (pos_iff_pos_of_mul_pos _).mp h
  rw [h_inv]
  exact zero_lt_one

lemma right_pos_of_pos : ∀ j, 0 < x.moveRight j :=
  fun j => lt_trans x_pos (Numeric.lt_moveRight x_num j)

/-! ### Normalization of a positive numeric game -/

/-- If `x` is a positive numeric game, then keeping only the positive Left options then inserting
  0 as a Left option, results in an equal game. This game is called the normalization of `x`.
-/
def normalization (x : PGame) : PGame :=
  match x with
  | ⟨_, r, L, R⟩ => insertLeft ⟨{i // 0 < L i}, r, fun i => L i, R⟩ 0

lemma num_of_normalization_num : (normalization x).Numeric := by
  rcases x with ⟨xl, xr, xL, xR⟩
  rw [normalization]
  apply insertLeft_numeric _ numeric_zero _
  · rw [numeric_def] at x_num ⊢
    simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk, Subtype.forall] at x_num ⊢
    simp only [x_num, implies_true, and_self]
  · rw [PGame.zero_le]
    simpa only [rightMoves_mk, moveRight_mk] using PGame.zero_le.1 <| x_pos.le

lemma eq_normalization_of_pos:
    mk x x_num = mk (normalization x) (num_of_normalization_num x_num x_pos) := by
  rw [mk_eq_mk]
   -- we show: x ≈ x.insertLeft 0 ≈ normalization x
  apply trans <| symm <| insertLeft_equiv_of_lf x_pos.lf
  rw [equiv_def]
  rcases x with ⟨xl, xr, xL, xR⟩
  simp only [normalization, insertLeft]
  constructor <;> (
    rw [le_def]
    simp only [leftMoves_mk, moveLeft_mk, Sum.exists, Sum.elim_inl, Subtype.exists,
      Sum.elim_inr, exists_const, Sum.forall, le_refl, or_true, IsEmpty.exists_iff,
      or_false, implies_true, and_true, moveRight_mk]
  ) <;>
  constructor <;>
  intro i
  · left
    cases' le_or_gf (xL i) 0 with h h
    · right; exact h
    · left; use i, h.lt numeric_zero (x_num.moveLeft _)
  · right; use i
  · left; left; use i
  · right; use i

/-! ### Options of inv' are numeric

  We prove by induction that if `x` is numeric, then the options of `x.inv'` are numeric. Note that
  this does *not* prove that `x.inv'` is numeric, since we have not proven the other condition of
  numericity, that all Left options are less than all Right options. This other condition is
  proven later in `onag_1_10_ii`.
-/

lemma numeric_invVal {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (i : InvTy {i // 0 < L i} r b) :
      (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv') (fun j => (R j).inv')
        (PGame.mk l r L R) i).Numeric := by
  induction i <;> rw [invVal]
  · exact numeric_zero
  all_goals
    case _ i j ih =>
      apply Numeric.mul
      · apply numeric_one.add <| (Numeric.sub _ h5).mul ih
        · first | exact h5.2.1 i | exact h5.2.2 i
      · first | exact h4 i | exact h3 i i.2

lemma inv'_numeric (ih_xl : ∀ i, 0 < x.moveLeft i → (x.moveLeft i).inv'.Numeric)
    (ih_xr : ∀ j, (x.moveRight j).inv'.Numeric) :
    (∀ i, (x.inv'.moveLeft i).Numeric) ∧ (∀ j, (x.inv'.moveRight j).Numeric) := by
  constructor <;> (
    intro i
    rcases x with ⟨xl, xr, xL, xR⟩
    exact numeric_invVal ih_xl ih_xr x_num i
  )

lemma inv'_numeric_left (ih_xl : ∀ i, 0 < x.moveLeft i → (x.moveLeft i).inv'.Numeric)
    (ih_xr : ∀ j, (x.moveRight j).inv'.Numeric) :
    ∀ i, (x.inv'.moveLeft i).Numeric := (inv'_numeric x_num x_pos ih_xl ih_xr).1

lemma inv'_numeric_right (ih_xl : ∀ i, 0 < x.moveLeft i → (x.moveLeft i).inv'.Numeric)
    (ih_xr : ∀ j, (x.moveRight j).inv'.Numeric) :
    ∀ j, (x.inv'.moveRight j).Numeric := (inv'_numeric x_num x_pos ih_xl ih_xr).2

/-! ### Helper lemmas for the main proof

  These lemmas do the heavy lifting within the proof of the main result `onag_1_10`.
  They are stated with additional hypotheses which will be satisfied by induction
  during the main proof.

-/

/-- Given `y''`, return `(x', x'_inv, y')` -/
def components {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (x_pos : 0 < PGame.mk l r L R)
    (i'' : InvTy {i // 0 < L i} r b) : Surreal × Surreal × Surreal :=
  match i'' with
  | InvTy.zero => (0, 0, 0)
  | InvTy.left₁ i j =>
    (mk (R i) (h5.2.2 i), mk (R i).inv' (h4 i),
      mk ((PGame.mk l r L R).inv'.moveLeft j) (by apply inv'_numeric_left <;> tauto))
  | InvTy.left₂ i j =>
    (mk (L i) (h5.2.1 i), mk (L i).inv' (h3 i i.2),
      mk ((PGame.mk l r L R).inv'.moveRight j) (by apply inv'_numeric_right <;> tauto))
  | InvTy.right₁ i j =>
    (mk (L i) (h5.2.1 i), mk (L i).inv' (h3 i i.2),
      mk ((PGame.mk l r L R).inv'.moveLeft j) (by apply inv'_numeric_left <;> tauto))
  | InvTy.right₂ i j =>
    (mk (R i) (h5.2.2 i), mk (R i).inv' (h4 i),
      mk ((PGame.mk l r L R).inv'.moveRight j) (by apply inv'_numeric_right <;> tauto))

/-- The identity `1 - x*y'' = (1 - x * y')*(x' - x)/x'` -/
lemma eq1 {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (x_pos : 0 < PGame.mk l r L R)
    (inv_l : ∀ (i : { i // 0 < L i }), mk (L i) (h5.2.1 i) * mk (L i).inv' (h3 i i.2) = 1)
    (inv_r : ∀ j, mk (R j) (h5.2.2 j) * mk (R j).inv' (h4 j) = 1)
    (i'' : InvTy {i // 0 < L i} r b) :
    let (x', x'_inv, y') := components h3 h4 h5 x_pos i''
    let x := mk (PGame.mk l r L R) h5
    let y'' := match b with
      | false => mk ((PGame.mk l r L R).inv'.moveLeft i'')
        (by apply inv'_numeric_left <;> tauto)
      | true => mk ((PGame.mk l r L R).inv'.moveRight i'')
        (by apply inv'_numeric_right <;> tauto)
    match i'' with
    | InvTy.zero => true
    | _ => 1 - x * y'' = (1 - x * y') * (x' - x) * x'_inv := by
  cases i'' <;> simp only [components]
  all_goals
    simp only [inv', moveLeft_mk, invVal, moveRight_mk]
    rw [mk_mul, mk_add, mk_mul, mk_sub]
    on_goal 2 => first | apply h5.2.1 | apply h5.2.2
    on_goal 2 => exact h5
    on_goal 2 => apply numeric_invVal <;> tauto
    on_goal 2 => exact numeric_one
    on_goal 2 => case _ j _ => first | exact h3 j j.2 | exact h4 j
    simp only [← one_def]
  case' left₁ i j | right₂ i j =>
    specialize inv_r i
    have : IsUnit (mk (R i) (h5.2.2 i)) := by rw [isUnit_iff_exists_inv]; exact ⟨_, inv_r⟩
    lift (mk (R i) (h5.2.2 i)) to Surrealˣ using this with s
    have : mk (R i).inv' (h4 i) = ↑s⁻¹ := Eq.symm (Units.inv_eq_of_mul_eq_one_right inv_r)
  case' left₂ i j | right₁ i j =>
    specialize inv_l i
    have : IsUnit (mk (L i) (h5.2.1 i)) := by rw [isUnit_iff_exists_inv]; exact ⟨_, inv_l⟩
    lift (mk (L i) (h5.2.1 i)) to Surrealˣ using this with s
    have : mk (L i).inv' (h3 i i.2) = ↑s⁻¹ := Eq.symm (Units.inv_eq_of_mul_eq_one_right inv_l)
  all_goals
    rw [this]
    field_simp
    ring

lemma onag_1_10_i' {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) (b : Bool)
    (inv_l : ∀ (i : { i // 0 < L i }), mk (L i) (h5.2.1 i) * mk (L i).inv' (h3 i i.2) = 1)
    (inv_r : ∀ j, mk (R j) (h5.2.2 j) * mk (R j).inv' (h4 j) = 1)
    (x_pos: 0 < PGame.mk l r L R)
    (i' : InvTy {i // 0 < L i} r b) :
    let x := mk (PGame.mk l r L R) h5
    let y' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) i')
      (by apply numeric_invVal <;> tauto)
    match b with
    | false => x * y' < 1
    | true => 1 < x * y' := by
  have ihr_pos : ∀ j, 0 < mk (R j).inv' (h4 j) := by
    intro j
    exact inv_pos_of_pos (inv_r j) (right_pos_of_pos h5 x_pos j)
  have ihl_pos: ∀ (i : {i // 0 < L i}), 0 < mk (L i).inv' (h3 i i.2) := by
    intro i
    exact inv_pos_of_pos (inv_l i) i.2
  induction i' <;> simp only
  · simp [invVal, ← zero_def]
  · case _ j i1 ih =>
      have := eq1 h3 h4 h5 x_pos inv_l inv_r (InvTy.left₁ j i1)
      simp only [inv', moveLeft_mk, components] at this
      simp only at ih
      rw [Iff.symm sub_pos] at ih ⊢
      rw [this]
      simp only [mul_assoc, ih, mul_pos_iff_of_pos_left, ihr_pos, mul_pos_iff_of_pos_right, sub_pos]
      apply Numeric.lt_moveRight
      exact h5
  · case _ j i1 ih =>
      have := eq1 h3 h4 h5 x_pos inv_l inv_r (InvTy.left₂ j i1)
      simp only [inv', moveLeft_mk, components, moveRight_mk] at this
      simp only at ih
      rw [Iff.symm sub_pos]
      rw [Iff.symm sub_neg] at ih
      rw [this]
      simp only [ihl_pos, mul_pos_iff_of_pos_right]
      apply mul_pos_of_neg_of_neg
      · exact ih
      · simp only [sub_neg, mk_lt_mk]
        have := Numeric.moveLeft_lt h5 (j : l)
        simp only [moveLeft_mk] at this
        exact this
  · case _ j i1 ih =>
      have := eq1 h3 h4 h5 x_pos inv_l inv_r (InvTy.right₁ j i1)
      simp only [inv', moveRight_mk, components, moveLeft_mk] at this
      simp only at ih
      rw [Iff.symm sub_pos] at ih
      rw [Iff.symm sub_neg]
      rw [this]
      apply mul_neg_of_neg_of_pos
      · apply mul_neg_of_pos_of_neg
        · exact ih
        · simp only [sub_neg, mk_lt_mk]
          have := Numeric.moveLeft_lt h5 (j : l)
          simp only [moveLeft_mk] at this
          exact this
      · exact ihl_pos j
  · case _ j i1 ih =>
      have := eq1 h3 h4 h5 x_pos inv_l inv_r (InvTy.right₂ j i1)
      simp only [inv', moveRight_mk, components] at this
      simp only at ih
      rw [Iff.symm sub_neg] at ih
      rw [Iff.symm sub_neg]
      rw [this]
      apply mul_neg_of_neg_of_pos
      · apply mul_neg_of_neg_of_pos
        · exact ih
        · simp only [sub_pos, mk_lt_mk]
          apply Numeric.lt_moveRight
          exact h5
      · exact ihr_pos j

/-- The identity `x' * y + x * y' - x' * y' = 1 + x' * (y - y'')` -/
lemma eq2 {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (inv_l : ∀ (i : { i // 0 < L i }), mk (L i) (h5.2.1 i) * mk (L i).inv' (h3 i i.2) = 1)
    (inv_r : ∀ j, mk (R j) (h5.2.2 j) * mk (R j).inv' (h4 j) = 1)
    (inv_numeric : (PGame.mk l r L R).inv'.Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (i'' : InvTy {i // 0 < L i} r b) :
    let (x', _, y') := components h3 h4 h5 x_pos i''
    let x := mk (PGame.mk l r L R) h5
    let y'' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) i'')
      (by apply numeric_invVal <;> tauto)
    let y := mk ((PGame.mk l r L R).inv') inv_numeric
    match i'' with
    | InvTy.zero => true
    | _ => x' * y + x * y' - x' * y' = 1 + x' * (y - y'') := by
  cases i'' <;> simp only [components]
  all_goals
    simp only [invVal]
    rw [mk_mul, mk_add, mk_mul, mk_sub]
    on_goal 2 => first | apply h5.2.1 | apply h5.2.2
    on_goal 2 => exact h5
    on_goal 2 => apply numeric_invVal <;> tauto
    on_goal 2 => exact numeric_one
    on_goal 2 => case _ j _ => first | exact h3 j j.2 | exact h4 j
    simp only [← one_def]
  case' left₁ i j | right₂ i j =>
    apply_fun (fun x => x - mk (R i) (h5.2.2 i) * mk (PGame.mk l r L R).inv' inv_numeric)
      using sub_left_injective
    ring_nf
    conv_lhs => simp [inv']
    specialize inv_r i
    have : IsUnit (mk (R i) (h5.2.2 i)) := by rw [isUnit_iff_exists_inv]; exact ⟨_, inv_r⟩
    lift (mk (R i) (h5.2.2 i)) to Surrealˣ using this with s
    have : mk (R i).inv' (h4 i) = ↑s⁻¹ := Eq.symm (Units.inv_eq_of_mul_eq_one_right inv_r)
  case' left₂ i j | right₁ i j =>
    apply_fun (fun x => x - mk (L i) (h5.2.1 i) * mk (PGame.mk l r L R).inv' inv_numeric)
      using sub_left_injective
    ring_nf
    conv_lhs => simp [inv']
    specialize inv_l i
    have : IsUnit (mk (L i) (h5.2.1 i)) := by rw [isUnit_iff_exists_inv]; exact ⟨_, inv_l⟩
    lift (mk (L i) (h5.2.1 i)) to Surrealˣ using this with s
    have : mk (L i).inv' (h3 i i.2) = ↑s⁻¹ := Eq.symm (Units.inv_eq_of_mul_eq_one_right inv_l)
  all_goals
    rw [this]
    field_simp
    ring

lemma onag_1_10_iii_left' {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric)
    (inv_l : ∀ (i : { i // 0 < L i }), mk (L i) (h5.2.1 i) * mk (L i).inv' (h3 i i.2) = 1)
    (inv_r : ∀ j, mk (R j) (h5.2.2 j) * mk (R j).inv' (h4 j) = 1)
    (inv_numeric : (PGame.mk l r L R).inv'.Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (ij : Sum ({ i // 0 < L i } × InvTy { i // 0 < L i } r false)
      (r × InvTy { i // 0 < L i } r true)) :
    let x := mk (PGame.mk l r L R) h5
    let y := mk ((PGame.mk l r L R).inv') inv_numeric
    match ij with
    | Sum.inl ⟨i, j⟩ =>
      let x' := mk (L i) (h5.2.1 i)
      let y' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply numeric_invVal <;> tauto)
      x' * y + x * y' - x' * y' < 1
    | Sum.inr ⟨i, j⟩ =>
      let x' := mk (R i) (h5.2.2 i)
      let y' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply numeric_invVal <;> tauto)
      x' * y + x * y' - x' * y' < 1 := by
  rcases ij <;> simp only
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.right₁ i j)
      simp only [components] at this
      conv_lhs at this => {
        pattern (occs := *) (PGame.mk l r L R).inv'.moveLeft j
        simp [inv']
      }
      rw [this]
      simp only [add_lt_iff_neg_left]
      apply mul_neg_of_pos_of_neg
      · exact i.2
      · apply sub_neg.mpr
        have := mk_lt_mk_moveRight inv_numeric (InvTy.right₁ i j)
        conv_rhs at this => simp [inv']
        exact this
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.right₂ i j)
      simp only [components] at this
      conv_lhs at this => {
        pattern (occs := *) (PGame.mk l r L R).inv'.moveRight j
        simp [inv']
      }
      rw [this]
      simp only [add_lt_iff_neg_left]
      apply mul_neg_of_pos_of_neg
      · exact right_pos_of_pos h5 x_pos i
      · apply sub_neg.mpr
        have := mk_lt_mk_moveRight inv_numeric (InvTy.right₂ i j)
        conv_rhs at this => simp [inv']
        exact this

lemma onag_1_10_iii_right' {l r} {L : l → PGame} {R : r → PGame}
    (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric)
    (inv_l : ∀ (i : { i // 0 < L i }), mk (L i) (h5.2.1 i) * mk (L i).inv' (h3 i i.2) = 1)
    (inv_r : ∀ j, mk (R j) (h5.2.2 j) * mk (R j).inv' (h4 j) = 1)
    (inv_numeric : (PGame.mk l r L R).inv'.Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (ij : Sum ({ i // 0 < L i } × InvTy { i // 0 < L i } r true)
      (r × InvTy { i // 0 < L i } r false)) :
    let x := mk (PGame.mk l r L R) h5
    let y := mk ((PGame.mk l r L R).inv') inv_numeric
    match ij with
    | Sum.inl ⟨i, j⟩ =>
      let x' := mk (L i) (h5.2.1 i)
      let y' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply numeric_invVal <;> tauto)
      1 < x' * y + x * y' - x' * y'
    | Sum.inr ⟨i, j⟩ =>
      let x' := mk (R i) (h5.2.2 i)
      let y' := mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply numeric_invVal <;> tauto)
      1 < x' * y + x * y' - x' * y' := by
  rcases ij <;> simp only
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.left₂ i j)
      simp only [components] at this
      conv_lhs at this => {
        pattern (occs := *) (PGame.mk l r L R).inv'.moveRight j
        simp [inv']
      }
      rw [this]
      simp only [lt_add_iff_pos_right]
      apply Left.mul_pos
      · exact i.2
      · apply sub_pos.mpr
        have := mk_moveLeft_lt_mk inv_numeric (InvTy.left₂ i j)
        conv_rhs at this => simp [inv']
        exact this
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.left₁ i j)
      simp only [components] at this
      conv_lhs at this => {
        pattern (occs := *) (PGame.mk l r L R).inv'.moveLeft j
        simp [inv']
      }
      rw [this]
      simp only [lt_add_iff_pos_right]
      apply Left.mul_pos
      · exact right_pos_of_pos h5 x_pos i
      · apply sub_pos.mpr
        have := mk_moveLeft_lt_mk inv_numeric (InvTy.left₁ i j)
        conv_rhs at this => simp [inv']
        exact this

/-! ### The main lemma -/

lemma onag_1_10 :
    (x.inv').Numeric ∧ -- (ii)
    x * x.inv' ≈ 1 := by -- (iv)
  induction x
  case mk xl xr xL xR ih_xl ih_xr =>
    set x := PGame.mk xl xr xL xR with x_rfl
    rw [x_rfl] at x_num x_pos
    have x_num' := x_num
    rw [numeric_def] at x_num'
    simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk] at x_num'
    rcases x_num' with ⟨_, xl_num, xr_num⟩
    simp only [xl_num, true_implies, xr_num] at ih_xl ih_xr
    have h3 : ∀ (i : xl), 0 < xL i → (xL i).inv'.Numeric := by
      intros i xlpos
      specialize ih_xl i xlpos
      exact ih_xl.1
    have h4 : ∀ (j : xr), (xR j).inv'.Numeric := by
      intro i
      specialize ih_xr i
      exact (ih_xr (right_pos_of_pos x_num x_pos i)).1
    have inv_l : ∀ (i : { i // 0 < xL i }),
        mk (xL i) (xl_num _) * mk (xL ↑i).inv' (h3 i i.2) = 1 := by
      intro i
      specialize ih_xl i i.2
      have := ih_xl.2
      simpa [← mk_mul, one_def, mk_eq_mk]
    have inv_r : ∀ (j : xr), mk (xR j) (xr_num _) * mk (xR j).inv' (h4 j) = 1 := by
      intro i
      specialize ih_xr i (right_pos_of_pos x_num x_pos i)
      have := ih_xr.2
      simpa [← mk_mul, one_def, mk_eq_mk]

    have onag_1_10_i_left := onag_1_10_i' h3 h4 x_num false inv_l inv_r x_pos
    have onag_1_10_i_right := onag_1_10_i' h3 h4 x_num true inv_l inv_r x_pos
    simp only at onag_1_10_i_left onag_1_10_i_right

    have onag_1_10_ii : (x.inv').Numeric := by
      rw [numeric_def]
      constructor
      · intros i j
        have := lt_trans (onag_1_10_i_left i) (onag_1_10_i_right j)
        apply (mul_lt_mul_left (by simpa only [zero_lt_mk])).mp at this
        rw [mk_lt_mk] at this
        simpa [inv']
      · constructor
        · exact inv'_numeric_left x_num x_pos h3 h4
        · exact inv'_numeric_right x_num x_pos h3 h4

    have onag_1_10_iii_left : ∀ i, ((normalization x) * x.inv').moveLeft i < 1 := by
      have := onag_1_10_iii_left' h3 h4 x_num inv_l inv_r (by rwa [x_rfl] at onag_1_10_ii) x_pos
      rw [x_rfl]
      intro i
      cases i
      · case _ val =>
          rcases val with ⟨i | val, j⟩
          · specialize this (Sum.inl ⟨i, j⟩)
            rw [eq_normalization_of_pos x_num x_pos] at this
            exact this
          · cases val   -- the case `x' = 0`, not mentioned in ONAG
            rw [Game.PGame.lt_iff_game_lt]
            simp only [normalization, insertLeft, inv', mk_mul_moveLeft_inl]
            simp only [Sum.elim_inr, quot_sub, quot_add, quot_zero_mul, add_sub_cancel_left]
            have := onag_1_10_i_left j
            rw [eq_normalization_of_pos x_num x_pos] at this
            exact this
      · case _ val =>
          rcases val with ⟨i, j⟩
          specialize this (Sum.inr ⟨i, j⟩)
          rw [eq_normalization_of_pos x_num x_pos] at this
          exact this

    have onag_1_10_iii_right : ∀ j, 1 < ((normalization x) * x.inv').moveRight j := by
      have := onag_1_10_iii_right' h3 h4 x_num inv_l inv_r (by rwa [x_rfl] at onag_1_10_ii) x_pos
      rw [x_rfl]
      intro i
      cases i
      · case _ val =>
          rcases val with ⟨i | val, j⟩
          · specialize this (Sum.inl ⟨i, j⟩)
            rw [eq_normalization_of_pos x_num x_pos] at this
            exact this
          · cases val  -- the case `x' = 0`, not mentioned in ONAG
            rw [Game.PGame.lt_iff_game_lt]
            simp only [normalization, insertLeft, inv', mk_mul_moveRight_inl]
            simp only [Sum.elim_inr, quot_sub, quot_add, quot_zero_mul, add_sub_cancel_left]
            have := onag_1_10_i_right j
            rw [eq_normalization_of_pos x_num x_pos] at this
            exact this
      · case _ val =>
          rcases val with ⟨i, j⟩
          specialize this (Sum.inr ⟨i, j⟩)
          rw [eq_normalization_of_pos x_num x_pos] at this
          exact this

    have onag_1_10_iv' :
        mk (normalization x) (num_of_normalization_num x_num x_pos) *
          mk (x.inv') onag_1_10_ii = 1 := by
      simp only [← mk_mul, one_def, mk_eq_mk]
      rw [equiv_def]
      constructor <;> rw [le_iff_forall_lf]
      · simp only [one_rightMoves, IsEmpty.forall_iff, and_true]
        intro i
        have := onag_1_10_iii_left i
        exact lf_of_lt this
      · simp only [one_leftMoves, one_moveLeft, forall_const]
        constructor
        · rw [lf_iff_exists_le]
          left
          rcases x with ⟨xl, xr, xL, xR⟩
          use toLeftMovesMul (Sum.inl (Sum.inr (), InvTy.zero))
          simp only [mul_moveLeft_inl, inv', moveLeft_mk, invVal]
          rw [Game.PGame.le_iff_game_le]
          simp only [quot_sub, quot_add, quot_mul_zero, add_sub_cancel_right]
          simp only [normalization, insertLeft, moveLeft_mk, Sum.elim_inr, quot_zero_mul, le_refl]
        · intro j
          have := onag_1_10_iii_right j
          exact lf_of_lt this

    have onag_1_10_iv : x * x.inv' ≈ 1 := by
      suffices mk x x_num * mk x.inv' onag_1_10_ii = 1 by
        simp only [← mk_mul, one_def, mk_eq_mk] at this
        exact this
      rwa [eq_normalization_of_pos x_num x_pos]

    exact ⟨onag_1_10_ii, onag_1_10_iv⟩

lemma onag_1_10_ii : (x.inv').Numeric := (onag_1_10 x_num x_pos).1

lemma onag_1_10_iv : x * x.inv' ≈ 1 := (onag_1_10 x_num x_pos).2

end Positive

lemma inv_surreal (hx : ¬ x ≈ 0) : x * x⁻¹ ≈ 1 := by
  by_cases h : 0 < x
  · rw [inv_eq_of_pos h]
    exact onag_1_10_iv x_num h
  · have x_lf_0 : x ⧏ 0 := by
      apply PGame.not_le.mp
      by_contra bad
      apply lt_or_equiv_of_le at bad
      tauto
    have : 0 < -x := by
      simp only [zero_lt_neg_iff]
      have := le_of_lf x_lf_0 x_num numeric_zero
      exact lt_of_le_of_lf this x_lf_0
    rw [inv_eq_of_lf_zero x_lf_0]
    have := onag_1_10_iv x_num.neg this
    rw [← Quotient.eq] at this ⊢
    simp only [quot_neg_mul, quot_mul_neg] at this ⊢
    exact this

end Surreal.Division

namespace SetTheory.PGame
open Surreal.Division

lemma Numeric.inv (x_num : x.Numeric) : x⁻¹.Numeric := by
  rcases lf_or_equiv_or_gf x 0 with neg | zero | pos
  · have neg_x_pos : 0 < -x := zero_lt_neg_iff.mpr (lt_of_lf neg x_num numeric_zero)
    rw [inv_eq_of_lf_zero neg]
    exact (onag_1_10_ii x_num.neg neg_x_pos).neg
  · rw [inv_eq_of_equiv_zero zero]
    exact numeric_zero
  · have := lt_of_lf pos numeric_zero x_num
    rw [inv_eq_of_pos this]
    apply onag_1_10_ii x_num this

lemma Equiv.inv_congr {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) (eq : x ≈ y) : x⁻¹ ≈ y⁻¹ := by
  by_cases h : x ≈ 0
  · rw [inv_eq_of_equiv_zero h]
    rw [inv_eq_of_equiv_zero (Trans.trans (symm eq) h)]
  · have h' : ¬ (y ≈ 0) := by
      by_contra bad
      exact h (Trans.trans eq bad)
    have : x * y⁻¹ ≈ x * x⁻¹ := by
      calc
        x * y⁻¹ ≈ y * y⁻¹ := mul_congr_left hx hy hy.inv eq
        _        ≈ 1        := inv_surreal hy h'
        _        ≈ x * x⁻¹ := symm (inv_surreal hx h)
    apply Surreal.mul_left_cancel hx hy.inv hx.inv h at this
    exact symm this

end SetTheory.PGame

namespace Surreal

open Division

noncomputable instance : LinearOrderedField Surreal where
  __ := Surreal.instLinearOrderedCommRing
  inv := Surreal.lift (fun x ox ↦ ⟦⟨x⁻¹, ox.inv⟩⟧)
    (fun ox oy eq => Quotient.sound <| inv_congr ox oy eq)
  mul_inv_cancel := by
    rintro ⟨a, oa⟩
    intro nz
    exact Quotient.sound (inv_surreal oa (by
      change ¬ ⟦(⟨a, oa⟩ : Subtype Numeric)⟧ = ⟦⟨0, _⟩⟧ at nz
      simp only [Quotient.eq] at nz
      exact nz
    ))
  inv_zero := Quotient.sound (by
    simp only [PGame.inv_zero]
    exact Subtype.refl _
  )
  nnqsmul := _
  qsmul := _

end Surreal
