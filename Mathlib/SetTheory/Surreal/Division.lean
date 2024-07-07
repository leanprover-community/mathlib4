/-
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Theodore Hwa
-/
import Mathlib.SetTheory.Surreal.Multiplication

/-!
# Surreal division

In this file, we prove that if `x` is a nonzero surreal number, then `x⁻¹` (defined in
`Mathlib.SetTheory.Game.Basic`) is a number and is a multiplicative inverse for `x`. We use that
to define the field structure on `Surreal`.

We essentially follow the proof in ONAG [Conway2001], chapter 1, section 10, with a few minor
differences explained below. There are four lemmas stated there, (i) through (iv). They are only
proved for positive numbers `x`. Once we have defined the inverse for positive `x`, it is extended
in the obvious way to negative numbers.

In our proof, lemmas (i) through (iv) are proved for positive numbers in the section labeled
`Positive` by a series of preliminary lemmas, culminating in the lemma `onag_1_10` which
proves (i) through (iv) by a joint induction over all four statements.

The desired final results are (ii) and (iv) which state that `x⁻¹` is a number and is a
multiplicative inverse, respectively.

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
`y` : the purported inverse of x, as defined by `x.inv'`
`y'` : an option of `y`, indexed by `i'`
`y''` : (1 + (x' - x) * y') / x' , the form of any option of `y` besides 0, indexed by `i''`

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
  apply (pos_iff_pos_of_mul_pos _).mp
  on_goal 2 => exact x
  · exact h
  · simp only [h_inv, zero_lt_one]

lemma right_pos_of_pos : ∀ j, 0 < x.moveRight j := by
  apply le_of_lt at x_pos
  rw [le_iff_forall_lt] at x_pos
  simp only [zero_leftMoves, IsEmpty.forall_iff, true_and] at x_pos
  · exact x_pos
  · exact numeric_zero
  · exact x_num

/-! ### Normalization of a positive numeric game -/

/-- If x is a positive numeric game, then keeping only the positive Left options then inserting
  0 as a Left option, results in an equal game. This game is called the normalization of x.
-/
def normalization (x : PGame) : PGame :=
  match x with
  | ⟨_, r, L, R⟩ => insertLeft ⟨{i // 0 < L i}, r, fun i => L i, R⟩ 0

lemma num_of_normalization_num : (normalization x).Numeric := by
  rcases x with ⟨xl, xr, xL, xR⟩
  simp only [normalization]
  apply numeric_of_insertLeft_numeric
  · rw [numeric_def] at x_num ⊢
    simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk, Subtype.forall] at x_num ⊢
    simp only [x_num, implies_true, and_self]
  · exact numeric_zero
  · rw [PGame.zero_le]
    simp only [rightMoves_mk, moveRight_mk]
    have : 0 ≤ PGame.mk xl xr xL xR := by exact le_of_lt x_pos
    rw [PGame.zero_le] at this
    simp only [rightMoves_mk, moveRight_mk] at this
    exact this

lemma pos_num_eq_normalization :
    Surreal.mk x x_num = Surreal.mk (normalization x) (num_of_normalization_num x_num x_pos) := by
  simp only [mk_eq_mk]
  rw [equiv_def]
  rcases x with ⟨xl, xr, xL, xR⟩
  simp only [normalization, insertLeft]
  constructor <;> (
    rw [le_def]
    simp
  )
  · constructor
    · intro i
      left
      by_contra bad
      simp only [not_or, not_exists, not_and, PGame.not_le] at bad
      rw [lf_iff_lt numeric_zero] at bad
      on_goal 2 =>
        rw [numeric_def] at x_num
        simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk] at x_num
        simp only [x_num]
      rcases bad with ⟨bad1, bad2⟩
      specialize bad1 i bad2
      exact lf_irrefl _ bad1
    · intro j
      right
      use j
  · constructor
    · constructor
      · intros i _
        left
        use i
      · apply lf_of_lt at x_pos
        rw [lf_iff_exists_le] at x_pos
        simp only [leftMoves_mk, moveLeft_mk, zero_rightMoves, IsEmpty.exists_iff, or_false]
          at x_pos
        exact x_pos
    · intro j
      right
      use j

lemma pos_of_normalization_pos_num {x : PGame} (x_num : x.Numeric) (x_pos : 0 < x) :
    0 < normalization x := by
  have := pos_num_eq_normalization x_num x_pos
  simp only [mk_eq_mk] at this
  exact lt_of_lt_of_equiv x_pos this

/-! ### Options of inv' are numeric

  We prove by induction that if x is numeric, then the options of x.inv' are numeric. Note that
  this does *not* prof that x.inv' is numeric, since we have not proven the other condition of
  numericity, that all Left options are less than all Right options. This other condition is
  proven later in `onag_1_10_ii`.
-/

lemma invVal_numeric {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (i : InvTy {i // 0 < L i} r b) :
      (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv') (fun j => (R j).inv')
        (PGame.mk l r L R) i).Numeric := by
  induction i <;> simp only [invVal]
  · exact numeric_zero
  all_goals
    case _ i j ih =>
      apply Numeric.mul
      · apply Numeric.add
        · exact numeric_one
        · apply Numeric.mul
          · apply Numeric.sub
            · first | exact h2 i | exact h1 i
            · exact h5
          · exact ih
      · first | exact h4 i | exact h3 i i.2

lemma inv'_numeric (ih_xl : ∀ i, 0 < x.moveLeft i → (x.moveLeft i).inv'.Numeric)
    (ih_xr : ∀ j, (x.moveRight j).inv'.Numeric) :
    (∀ i, (x.inv'.moveLeft i).Numeric) ∧ (∀ j, (x.inv'.moveRight j).Numeric) := by
  constructor <;> (
    intro i
    rcases x with ⟨xl, xr, xL, xR⟩
    rw [numeric_def] at x_num
    simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk] at *
    simp only [inv', leftMoves_mk, moveLeft_mk] at i ⊢
    apply invVal_numeric
    · simp only [x_num, implies_true]
    · simp only [x_num, implies_true]
    · exact ih_xl
    · exact ih_xr
    · rw [numeric_def]
      simp only [leftMoves_mk, rightMoves_mk, moveLeft_mk, moveRight_mk, x_num, implies_true,
        and_self]
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

/-- Given `y''`, return (x', x'_inv, y') -/
def components {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric)
    (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (x_pos : 0 < PGame.mk l r L R)
    (i'' : InvTy {i // 0 < L i} r b) :=
  match i'' with
  | InvTy.zero => (0, 0, 0)
  | InvTy.left₁ i j =>
    (Surreal.mk (R i) (by tauto), Surreal.mk (R i).inv' (by tauto),
      Surreal.mk ((PGame.mk l r L R).inv'.moveLeft j) (by apply inv'_numeric_left <;> tauto))
  | InvTy.left₂ i j =>
    (Surreal.mk (L i) (by tauto), Surreal.mk (L i).inv' (h3 i i.2),
      Surreal.mk ((PGame.mk l r L R).inv'.moveRight j) (by apply inv'_numeric_right <;> tauto))
  | InvTy.right₁ i j =>
    (Surreal.mk (L i) (by tauto), Surreal.mk (L i).inv' (h3 i i.2),
      Surreal.mk ((PGame.mk l r L R).inv'.moveLeft j) (by apply inv'_numeric_left <;> tauto))
  | InvTy.right₂ i j =>
    (Surreal.mk (R i) (by tauto), Surreal.mk (R i).inv' (by tauto),
      Surreal.mk ((PGame.mk l r L R).inv'.moveRight j) (by apply inv'_numeric_right <;> tauto))

/-- The identity 1 - x*y'' = (1 - x * y')*(x' - x)/x' -/
lemma eq1 {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < L i → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (x_pos : 0 < PGame.mk l r L R)
    (inv_l : ∀ (i : { i // 0 < L i }),
      (Surreal.mk (L i) (by tauto)) * (Surreal.mk (L i).inv' (h3 i i.2)) = 1)
    (inv_r : ∀ j, (Surreal.mk (R j) (by tauto)) * (Surreal.mk (R j).inv' (by tauto)) = 1)
    (i'' : InvTy {i // 0 < L i} r b) :
    let (x', x'_inv, y') := components L R h1 h2 h3 h4 h5 x_pos i''
    let x := Surreal.mk (PGame.mk l r L R) h5
    let y'' := match b with
      | false => Surreal.mk ((PGame.mk l r L R).inv'.moveLeft i'')
        (by apply inv'_numeric_left <;> tauto)
      | true => Surreal.mk ((PGame.mk l r L R).inv'.moveRight i'')
        (by apply inv'_numeric_right <;> tauto)
    match i'' with
    | InvTy.zero => true
    | _ => 1 - x*y'' = (1 - x * y')*(x' - x)*x'_inv := by
  cases i'' <;> simp only [components]
  all_goals
    ring_nf
  on_goal 1 => case' _ j i1' => rw [mul_assoc _ (mk (R j) _) (mk (R j).inv' _), inv_r j]
  on_goal 2 => case' _ j i1 => rw [mul_assoc _ (mk (L j) _) (mk (L j).inv' _), inv_l j]
  on_goal 3 => case' _ j i1 => rw [mul_assoc _ (mk (L j) _) (mk (L j).inv' _), inv_l j]
  on_goal 4 => case' _ j i1' => rw [mul_assoc _ (mk (R j) _) (mk (R j).inv' _), inv_r j]
  all_goals
    ring_nf
    rw [sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    simp only [inv', moveLeft_mk, invVal, moveRight_mk]
    rw [← mul_def, ← add_def, ← mul_def, ← sub_def]
    any_goals
      tauto
    on_goal 2 =>
      apply invVal_numeric <;> tauto
    on_goal 2 => exact numeric_one
    simp only [one_def]
    ring_nf
  · conv in _ * mk (R j) _ * _ * mk (R j).inv' _ => {
      rw [mul_assoc _ (mk (R j) _) _, mul_assoc, mul_comm (mk (R j) _) _, mul_assoc]
    }
    rw [inv_r j]
    simp
  · conv in _ * mk (L j) _ * _ * mk (L j).inv' _ => {
      rw [mul_assoc _ (mk (L j) _) _, mul_assoc, mul_comm (mk (L j) _) _, mul_assoc]
    }
    rw [inv_l j]
    simp
  · conv in _ * mk (L j) _ * _ * mk (L j).inv' _ => {
      rw [mul_assoc _ (mk (L j) _) _, mul_assoc, mul_comm (mk (L j) _) _, mul_assoc]
    }
    rw [inv_l j]
    simp
  · conv in _ * mk (R j) _ * _ * mk (R j).inv' _ => {
      rw [mul_assoc _ (mk (R j) _) _, mul_assoc, mul_comm (mk (R j) _) _, mul_assoc]
    }
    rw [inv_r j]
    simp

lemma onag_1_10_i' {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) (b : Bool)
    (inv_l : ∀ (i : { i // 0 < L i }),
      (Surreal.mk (L i) (by tauto)) * (Surreal.mk (L i).inv' (h3 i i.2)) = 1)
    (inv_r : ∀ j, (Surreal.mk (R j) (by tauto)) * (Surreal.mk (R j).inv' (by tauto)) = 1)
    (x_pos: 0 < PGame.mk l r L R)
    (i' : InvTy {i // 0 < L i} r b) :
    let x := Surreal.mk (PGame.mk l r L R) (by tauto)
    let y' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) i')
      (by apply invVal_numeric <;> tauto)
    match b with
    | false => x * y' < 1
    | true => 1 < x * y' := by
  have ihr_pos : ∀ j, 0 < mk (R j).inv' (by tauto) := by
    intro j
    exact inv_pos_of_pos (inv_r j) (right_pos_of_pos h5 x_pos j)
  have ihl_pos: ∀ (i : {i // 0 < L i}), 0 < mk (L i).inv' (h3 i i.2) := by
    intro i
    exact inv_pos_of_pos (inv_l i) i.2
  induction i' <;> simp only
  · simp [invVal]
  · case _ j i1 ih =>
      have := eq1 L R h1 h2 h3 h4 h5 x_pos inv_l inv_r (InvTy.left₁ j i1)
      simp only [inv', moveLeft_mk, components] at this
      simp only at ih
      rw [Iff.symm sub_pos] at ih ⊢
      rw [this]
      simp only [mul_assoc, ih, mul_pos_iff_of_pos_left, ihr_pos, mul_pos_iff_of_pos_right, sub_pos]
      apply Numeric.lt_moveRight
      exact h5
  · case _ j i1 ih =>
      have := eq1 L R h1 h2 h3 h4 h5 x_pos inv_l inv_r (InvTy.left₂ j i1)
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
      have := eq1 L R h1 h2 h3 h4 h5 x_pos inv_l inv_r (InvTy.right₁ j i1)
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
      have := eq1 L R h1 h2 h3 h4 h5 x_pos inv_l inv_r (InvTy.right₂ j i1)
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

/-- The identity x' * y + x * y' - x' * y' = 1 + x' * (y - y'') -/
lemma eq2 {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric) {b : Bool}
    (inv_l : ∀ (i : { i // 0 < L i }),
      (Surreal.mk (L i) (by tauto)) * (Surreal.mk (L i).inv' (h3 i i.2)) = 1)
    (inv_r : ∀ j, (Surreal.mk (R j) (by tauto)) * (Surreal.mk (R j).inv' (by tauto)) = 1)
    (inv_numeric : ((PGame.mk l r L R).inv').Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (i'' : InvTy {i // 0 < L i} r b) :
    let (x', _, y') := components L R h1 h2 h3 h4 h5 x_pos i''
    let x := Surreal.mk (PGame.mk l r L R) h5
    let y'' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) i'')
      (by apply invVal_numeric <;> tauto)
    let y := Surreal.mk ((PGame.mk l r L R).inv') inv_numeric
    match i'' with
    | InvTy.zero => true
    | _ => x' * y + x * y' - x' * y' = 1 + x' * (y - y'') := by
  cases i'' <;> simp only [components]
  all_goals
    simp only [invVal]
    rw [← mul_def, ← add_def, ← mul_def, ← sub_def]
  any_goals
    tauto
  any_goals
    apply invVal_numeric <;> tauto
  any_goals
    exact numeric_one
  on_goal 3 =>
    case _ j _ => exact h3 j j.2
  on_goal 4 =>
    case _ j _ => exact h3 j j.2
  all_goals
    simp
    ring_nf
    first | simp only [inv_r] | simp only [inv_l]
  · case _ j i1 =>
      apply_fun (fun x => x - mk (R j) (h2 j) * mk (PGame.mk l r L R).inv' inv_numeric)
        using sub_left_injective
      ring_nf
      conv_lhs => simp [inv']
      conv_rhs => {
        rw [mul_assoc (mk (R j) _) _ _, mul_comm (mk (R j) _), mul_assoc]
        simp [inv_r]
        rw [pow_two, mul_assoc (mk (R j) _) _ _, mul_assoc (mk (R j) _) _ _,
          mul_comm (mk (R j) _) (mk (invVal (fun (i : {i // 0 < L i}) => L i) R
            (fun i => (L i).inv') (fun j => (R j).inv') (PGame.mk l r L R) i1) _),
          mul_assoc]
        simp [inv_r]
      }
      ring
  · case _ j i1 =>
      apply_fun (fun x => x - mk (L j) (h1 j) * mk (PGame.mk l r L R).inv' inv_numeric)
        using sub_left_injective
      ring_nf
      conv_lhs => simp [inv']
      conv_rhs => {
        rw [mul_assoc (mk (L j) _) _ _, mul_comm (mk (L j) _), mul_assoc]
        simp [inv_l]
        rw [pow_two, mul_assoc (mk (L j) _) _ _, mul_assoc (mk (L j) _) _ _,
          mul_comm (mk (L j) _) (mk (invVal (fun (i : {i // 0 < L i}) => L i) R
            (fun i => (L i).inv') (fun j => (R j).inv') (PGame.mk l r L R) i1) _),
          mul_assoc]
        simp [inv_l]
      }
      ring
  · case _ j i1 =>
      apply_fun (fun x => x - mk (L j) (h1 j) * mk (PGame.mk l r L R).inv' inv_numeric)
        using sub_left_injective
      ring_nf
      conv_lhs => simp [inv']
      conv_rhs => {
        rw [mul_assoc (mk (L j) _) _ _, mul_comm (mk (L j) _), mul_assoc]
        simp [inv_l]
        rw [pow_two, mul_assoc (mk (L j) _) _ _, mul_assoc (mk (L j) _) _ _,
          mul_comm (mk (L j) _) (mk (invVal (fun (i : {i // 0 < L i}) => L i) R
            (fun i => (L i).inv') (fun j => (R j).inv') (PGame.mk l r L R) i1) _),
          mul_assoc]
        simp [inv_l]
      }
      ring
  · case _ j i1 =>
      apply_fun (fun x => x - mk (R j) (h2 j) * mk (PGame.mk l r L R).inv' inv_numeric)
        using sub_left_injective
      ring_nf
      conv_lhs => simp [inv']
      conv_rhs => {
        rw [mul_assoc (mk (R j) _) _ _, mul_comm (mk (R j) _), mul_assoc]
        simp [inv_r]
        rw [pow_two, mul_assoc (mk (R j) _) _ _, mul_assoc (mk (R j) _) _ _,
          mul_comm (mk (R j) _) (mk (invVal (fun (i : {i // 0 < L i}) => L i) R
            (fun i => (L i).inv') (fun j => (R j).inv') (PGame.mk l r L R) i1) _),
          mul_assoc]
        simp [inv_r]
      }
      ring

lemma onag_1_10_iii_left' {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric)
    (inv_l : ∀ (i : { i // 0 < L i }),
      (Surreal.mk (L i) (by tauto)) * (Surreal.mk (L i).inv' (h3 i i.2)) = 1)
    (inv_r : ∀ j, (Surreal.mk (R j) (by tauto)) * (Surreal.mk (R j).inv' (by tauto)) = 1)
    (inv_numeric : ((PGame.mk l r L R).inv').Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (ij : Sum ({ i // 0 < L i } × InvTy { i // 0 < L i } r false)
      (r × InvTy { i // 0 < L i } r true)) :
    let x := Surreal.mk (PGame.mk l r L R) (by tauto)
    let y := Surreal.mk ((PGame.mk l r L R).inv') inv_numeric
    match ij with
    | Sum.inl ⟨i, j⟩ =>
      let x' := Surreal.mk (L i) (by tauto)
      let y' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply invVal_numeric <;> tauto)
      x' * y + x * y' - x' * y' < 1
    | Sum.inr ⟨i, j⟩ =>
      let x' := Surreal.mk (R i) (by tauto)
      let y' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply invVal_numeric <;> tauto)
      x' * y + x * y' - x' * y' < 1 := by
  rcases ij <;> simp
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 L R h1 h2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.right₁ i j)
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
        have := Surreal.lt_moveRight' inv_numeric (InvTy.right₁ i j)
        conv_rhs at this => {
          simp [inv']
        }
        exact this
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 L R h1 h2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.right₂ i j)
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
        have := Surreal.lt_moveRight' inv_numeric (InvTy.right₂ i j)
        conv_rhs at this => {
          simp [inv']
        }
        exact this

lemma onag_1_10_iii_right' {l r} (L : l → PGame) (R : r → PGame)
    (h1 : ∀ i, (L i).Numeric) (h2 : ∀ j, (R j).Numeric) (h3 : ∀ i, 0 < (L i) → (L i).inv'.Numeric)
    (h4 : ∀ j, (R j).inv'.Numeric) (h5 : (PGame.mk l r L R).Numeric)
    (inv_l : ∀ (i : { i // 0 < L i }),
      (Surreal.mk (L i) (by tauto)) * (Surreal.mk (L i).inv' (h3 i i.2)) = 1)
    (inv_r : ∀ j, (Surreal.mk (R j) (by tauto)) * (Surreal.mk (R j).inv' (by tauto)) = 1)
    (inv_numeric : ((PGame.mk l r L R).inv').Numeric)
    (x_pos: 0 < PGame.mk l r L R)
    (ij : Sum ({ i // 0 < L i } × InvTy { i // 0 < L i } r true)
      (r × InvTy { i // 0 < L i } r false)) :
    let x := Surreal.mk (PGame.mk l r L R) (by tauto)
    let y := Surreal.mk ((PGame.mk l r L R).inv') inv_numeric
    match ij with
    | Sum.inl ⟨i, j⟩ =>
      let x' := Surreal.mk (L i) (by tauto)
      let y' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply invVal_numeric <;> tauto)
      1 < x' * y + x * y' - x' * y'
    | Sum.inr ⟨i, j⟩ =>
      let x' := Surreal.mk (R i) (by tauto)
      let y' := Surreal.mk (invVal (fun (i : {i // 0 < L i}) => L i) R (fun i => (L i).inv')
        (fun j => (R j).inv') (PGame.mk l r L R) j)
        (by apply invVal_numeric <;> tauto)
      1 < x' * y + x * y' - x' * y' := by
  rcases ij <;> simp
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 L R h1 h2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.left₂ i j)
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
        have := Surreal.moveLeft_lt' inv_numeric (InvTy.left₂ i j)
        conv_rhs at this => {
          simp [inv']
        }
        exact this
  · case _ val =>
      rcases val with ⟨i, j⟩
      simp only
      have := eq2 L R h1 h2 h3 h4 h5 inv_l inv_r inv_numeric x_pos (InvTy.left₁ i j)
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
        have := Surreal.moveLeft_lt' inv_numeric (InvTy.left₁ i j)
        conv_rhs at this => {
          simp [inv']
        }
        exact this

/-! ### The main lemma -/

lemma onag_1_10 :
    (∀ i, x * ((x.inv').moveLeft i) < 1) ∧ (∀ j, 1 < x * ((x.inv').moveRight j)) ∧ -- (i)
    (x.inv').Numeric ∧ -- (ii)
    (∀ i, ((normalization x) * x.inv').moveLeft i < 1) ∧ -- (iii) left
    (∀ j, 1 < ((normalization x) * x.inv').moveRight j) ∧ --- (iii) right
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
      exact ih_xl.2.2.1
    have h4 : ∀ (j : xr), (xR j).inv'.Numeric := by
      intro i
      specialize ih_xr i
      exact (ih_xr (right_pos_of_pos x_num x_pos i)).2.2.1
    have inv_l : ∀ (i : { i // 0 < xL i }),
        mk (xL i) (xl_num _) * mk (xL ↑i).inv' (h3 i i.2) = 1 := by
      intro i
      specialize ih_xl i i.2
      have := ih_xl.2.2.2.2.2
      simpa [mul_def, ← one_def, mk_eq_mk]
    have inv_r : ∀ (j : xr), mk (xR j) (xr_num _) * mk (xR j).inv' (h4 j) = 1 := by
      intro i
      specialize ih_xr i (right_pos_of_pos x_num x_pos i)
      have := ih_xr.2.2.2.2.2
      simpa [mul_def, ← one_def, mk_eq_mk]

    have onag_1_10_i :
        (∀ i, x * ((x.inv').moveLeft i) < 1) ∧ (∀ j, 1 < x * ((x.inv').moveRight j)) := by
      simp only [inv', leftMoves_mk, moveLeft_mk, rightMoves_mk, moveRight_mk]
      constructor
      · have := onag_1_10_i' xL xR xl_num xr_num h3 h4 x_num false inv_l inv_r x_pos
        rw [x_rfl]
        simp only [mul_def, ← one_def, mk_lt_mk] at this
        exact this
      · have := onag_1_10_i' xL xR xl_num xr_num h3 h4 x_num true inv_l inv_r x_pos
        rw [x_rfl]
        simp only [← one_def, mul_def, mk_lt_mk] at this
        exact this

    have onag_1_10_ii : (x.inv').Numeric := by
      rw [numeric_def]
      have left_inv_options_numeric : ∀ i, (x.inv'.moveLeft i).Numeric :=
        inv'_numeric_left x_num x_pos h3 h4
      have right_inv_options_numeric : ∀ j, (x.inv'.moveRight j).Numeric :=
        inv'_numeric_right x_num x_pos h3 h4
      constructor
      · intros i j
        have : x * x.inv'.moveLeft i < x * x.inv'.moveRight j := lt_trans (onag_1_10_i.1 i)
          (onag_1_10_i.2 j)
        exact mul_lt_mul_left' x_num (left_inv_options_numeric i) (right_inv_options_numeric j)
          x_pos this
      · constructor
        · exact left_inv_options_numeric
        · exact right_inv_options_numeric

    have onag_1_10_iii_left : ∀ i, ((normalization x) * x.inv').moveLeft i < 1 := by
      have := onag_1_10_iii_left' xL xR xl_num xr_num h3 h4 x_num inv_l inv_r
          (by rwa [x_rfl] at onag_1_10_ii) x_pos
      rw [x_rfl]
      intro i
      cases i
      · case _ val =>
          rcases val with ⟨i | val, j⟩
          · specialize this (Sum.inl ⟨i, j⟩)
            simp only at this
            simp only [normalization, insertLeft]
            conv_lhs at this => {
              lhs
              rhs
              lhs
              rw [pos_num_eq_normalization x_num x_pos]
            }
            simp only [mul_def, add_def, sub_def] at this
            simp only [inv', mk_mul_moveLeft_inl]
            simp only [inv', ← one_def, mk_lt_mk] at this
            exact this
          · cases val
            simp only [normalization, insertLeft, inv', mk_mul_moveLeft_inl]
            rw [Game.PGame.lt_iff_game_lt]
            simp only [quot_sub, quot_add, quot_zero_mul, add_sub_cancel_left]
            have := onag_1_10_i.1
            rw [x_rfl] at this
            specialize this j
            rw [← mk_lt_mk, ← mul_def x_num] at this
            on_goal 2 => exact numeric_one
            have : (normalization x) * (PGame.mk xl xr xL xR).inv'.moveLeft j < 1 := by
              rw [← mk_lt_mk]
              on_goal 3 => exact numeric_one
              on_goal 2 =>
                apply Numeric.mul
                · exact num_of_normalization_num x_num x_pos
                · exact inv'_numeric_left x_num x_pos h3 h4 j
              rw [← mul_def]
              on_goal 2 => exact num_of_normalization_num x_num x_pos
              on_goal 2 =>
                apply inv'_numeric_left x_num x_pos
                · exact h3
                · exact h4
              have eq_norm := pos_num_eq_normalization x_num x_pos
              rwa [← eq_norm]
            simp only [normalization, insertLeft, inv', moveLeft_mk] at this
            exact this
      · case _ val =>
          rcases val with ⟨i, j⟩
          · specialize this (Sum.inr ⟨i, j⟩)
            simp only at this
            simp only [normalization, insertLeft]
            conv_lhs at this => {
              lhs
              rhs
              lhs
              rw [pos_num_eq_normalization x_num x_pos]
            }
            simp only [mul_def, add_def, sub_def] at this
            simp only [inv', mk_mul_moveLeft_inr]
            simp only [inv', ← one_def, mk_lt_mk] at this
            exact this

    have onag_1_10_iii_right : ∀ j, 1 < ((normalization x) * x.inv').moveRight j := by
      have := onag_1_10_iii_right' xL xR xl_num xr_num h3 h4 x_num inv_l inv_r
          (by rwa [x_rfl] at onag_1_10_ii) x_pos
      rw [x_rfl]
      intro i
      cases i
      · case _ val =>
          rcases val with ⟨i | val, j⟩
          · specialize this (Sum.inl ⟨i, j⟩)
            simp only at this
            simp only [normalization, insertLeft]
            conv_rhs at this => {
              lhs
              rhs
              lhs
              rw [pos_num_eq_normalization x_num x_pos]
            }
            simp only [mul_def, add_def, sub_def] at this
            simp only [inv', mk_mul_moveRight_inl]
            simp only [← one_def, inv', mk_lt_mk] at this
            exact this
          · cases val
            simp only [normalization, insertLeft, inv', mk_mul_moveRight_inl]
            rw [Game.PGame.lt_iff_game_lt]
            simp only [quot_sub, quot_add, quot_zero_mul, add_sub_cancel_left]
            have := onag_1_10_i.2
            rw [x_rfl] at this
            specialize this j
            rw [← mk_lt_mk, ← mul_def x_num] at this
            on_goal 2 => exact numeric_one
            have : 1 < (normalization x) * (PGame.mk xl xr xL xR).inv'.moveRight j := by
              rw [← mk_lt_mk]
              on_goal 2 => exact numeric_one
              on_goal 2 =>
                apply Numeric.mul
                · exact num_of_normalization_num x_num x_pos
                · exact inv'_numeric_right x_num x_pos h3 h4 j
              rw [← mul_def]
              on_goal 2 => exact num_of_normalization_num x_num x_pos
              on_goal 2 =>
                apply inv'_numeric_right x_num x_pos
                · exact h3
                · exact h4
              have eq_norm := pos_num_eq_normalization x_num x_pos
              rwa [← eq_norm]
            simp only [normalization, insertLeft, inv', moveRight_mk] at this
            exact this
      · case _ val =>
          rcases val with ⟨i, j⟩
          · specialize this (Sum.inr ⟨i, j⟩)
            simp only at this
            simp only [normalization, insertLeft]
            conv_rhs at this => {
              lhs
              rhs
              lhs
              rw [pos_num_eq_normalization x_num x_pos]
            }
            simp only [mul_def, add_def, sub_def] at this
            simp only [inv', mk_mul_moveRight_inr]
            simp only [← one_def, inv', mk_lt_mk] at this
            exact this

    have onag_1_10_iv' :
        Surreal.mk (normalization x) (num_of_normalization_num x_num x_pos) *
          Surreal.mk (x.inv') onag_1_10_ii = 1 := by
      simp only [mul_def, ← one_def, mk_eq_mk]
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
          simp only [id_eq, mul_moveLeft_inl, mul_moveLeft_inl, insertLeft, moveLeft_mk, inv',
            invVal]
          rw [Game.PGame.le_iff_game_le]
          simp only [quot_sub, quot_add, quot_mul_zero, add_sub_cancel_right]
          simp only [normalization, insertLeft, moveLeft_mk, quot_zero_mul, le_refl]
        · intro j
          have := onag_1_10_iii_right j
          exact lf_of_lt this

    have onag_1_10_iv : x * x.inv' ≈ 1 := by
      suffices Surreal.mk x x_num * Surreal.mk x.inv' onag_1_10_ii = 1 by
        simp only [mul_def, ← one_def, mk_eq_mk] at this
        exact this
      rwa [pos_num_eq_normalization x_num x_pos]

    exact ⟨onag_1_10_i.1, onag_1_10_i.2, onag_1_10_ii, onag_1_10_iii_left,
      onag_1_10_iii_right, onag_1_10_iv⟩

lemma onag_1_10_ii : (x.inv').Numeric := (onag_1_10 x_num x_pos).2.2.1

lemma onag_1_10_iv : x * x.inv' ≈ 1 := (onag_1_10 x_num x_pos).2.2.2.2.2

end Positive

lemma inv_numeric (x_num : x.Numeric) : x⁻¹.Numeric := by
  rcases lf_or_equiv_or_gf x 0 with neg | zero | pos
  · have neg_x_pos : 0 < -x := zero_lt_neg_iff.mpr (lt_of_lf neg x_num numeric_zero)
    rw [inv_eq_of_lf_zero neg]
    exact Numeric.neg (onag_1_10_ii (Numeric.neg x_num) neg_x_pos)
  · rw [inv_eq_of_equiv_zero zero]
    exact numeric_zero
  · have := lt_of_lf pos numeric_zero x_num
    rw [inv_eq_of_pos this]
    apply onag_1_10_ii x_num this

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
    have := onag_1_10_iv (Numeric.neg x_num) this
    rw [← Quotient.eq] at this ⊢
    simp only [quot_neg_mul, quot_mul_neg] at this ⊢
    exact this

lemma inv_congr {x y : PGame} (hx : x.Numeric) (hy : y.Numeric) (eq : x ≈ y) : x⁻¹ ≈ y⁻¹ := by
  by_cases h : x ≈ 0
  · rw [inv_eq_of_equiv_zero h]
    rw [inv_eq_of_equiv_zero (Trans.trans (symm eq) h)]
  · have h' : ¬ (y ≈ 0) := by
      by_contra bad
      exact h (Trans.trans eq bad)
    have : x * y⁻¹ ≈ x * x⁻¹ := by
      calc
        x * y⁻¹ ≈ y * y⁻¹ := mul_congr_left hx hy (inv_numeric hy) eq
        _        ≈ 1        := inv_surreal hy h'
        _        ≈ x * x⁻¹ := symm (inv_surreal hx h)
    apply Surreal.mul_left_cancel hx (inv_numeric hy) (inv_numeric hx) h at this
    exact symm this

end Surreal.Division

namespace Surreal

open Division

noncomputable instance : LinearOrderedField Surreal where
  __ := Surreal.instLinearOrderedCommRing
  inv := Surreal.lift (fun x ox ↦ ⟦⟨x⁻¹, inv_numeric ox⟩⟧)
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
