/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Isabel Longbottom, Kim Morrison, Yuyang Zhao
-/
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.SetTheory.PGame.Order

/-!
# Algebraic structure on pregames

This file defines the operations necessary to make games into an additive commutative group.
Addition is defined for $x = \{xL | xR\}$ and $y = \{yL | yR\}$ by $x + y = \{xL + y, x + yL | xR +
y, x + yR\}$. Negation is defined by $\{xL | xR\} = \{-xR | -xL\}$.

The order structures interact in the expected way with addition, so we have
```
theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x := sorry
theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x := sorry
```

We show that these operations respect the equivalence relation, and hence descend to games. At the
level of games, these operations satisfy all the laws of a commutative group. To prove the necessary
equivalence relations at the level of pregames, the notion of a `Relabelling` of a game is used
(defined in `Mathlib.SetTheory.PGame.Basic`); for example, there is a relabelling between
`x + (y + z)` and `(x + y) + z`.
-/

namespace SetTheory.PGame

open Function Relation

universe u

/-! ### Negation -/


/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : PGame → PGame
  | ⟨l, r, L, R⟩ => ⟨r, l, fun i => neg (R i), fun i => neg (L i)⟩

instance : Neg PGame :=
  ⟨neg⟩

@[simp]
theorem neg_def {xl xr xL xR} : -mk xl xr xL xR = mk xr xl (-xR ·) (-xL ·) :=
  rfl

instance : InvolutiveNeg PGame :=
  { inferInstanceAs (Neg PGame) with
    neg_neg := fun x => by
      induction x with | mk xl xr xL xR ihL ihR => simp_rw [neg_def, ihL, ihR] }

instance : NegZeroClass PGame :=
  { inferInstanceAs (Zero PGame), inferInstanceAs (Neg PGame) with
    neg_zero := by
      dsimp [Zero.zero, Neg.neg, neg]
      congr <;> funext i <;> cases i }

@[simp]
theorem neg_ofLists (L R : List PGame) :
    -ofLists L R = ofLists (R.map fun x => -x) (L.map fun x => -x) := by
  simp only [ofLists, neg_def, List.getElem_map, mk.injEq, List.length_map, true_and]
  constructor
  all_goals
    apply hfunext
    · simp
    · rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩ h
      have :
        ∀ {m n} (_ : m = n) {b : ULift (Fin m)} {c : ULift (Fin n)} (_ : HEq b c),
          (b.down : ℕ) = ↑c.down := by
        rintro m n rfl b c
        simp only [heq_eq_eq]
        rintro rfl
        rfl
      simp only [heq_eq_eq]
      congr 5
      exact this (List.length_map _).symm h

theorem isOption_neg {x y : PGame} : IsOption x (-y) ↔ IsOption (-x) y := by
  rw [isOption_iff, isOption_iff, or_comm]
  cases y
  apply or_congr <;>
    · apply exists_congr
      intro
      rw [neg_eq_iff_eq_neg]
      rfl

@[simp]
theorem isOption_neg_neg {x y : PGame} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]

/-- Use `toLeftMovesNeg` to cast between these two types. -/
theorem leftMoves_neg : ∀ x : PGame, (-x).LeftMoves = x.RightMoves
  | ⟨_, _, _, _⟩ => rfl

/-- Use `toRightMovesNeg` to cast between these two types. -/
theorem rightMoves_neg : ∀ x : PGame, (-x).RightMoves = x.LeftMoves
  | ⟨_, _, _, _⟩ => rfl

/-- Turns a right move for `x` into a left move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesNeg {x : PGame} : x.RightMoves ≃ (-x).LeftMoves :=
  Equiv.cast (leftMoves_neg x).symm

/-- Turns a left move for `x` into a right move for `-x` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesNeg {x : PGame} : x.LeftMoves ≃ (-x).RightMoves :=
  Equiv.cast (rightMoves_neg x).symm

@[simp]
theorem moveLeft_neg {x : PGame} (i) :
    (-x).moveLeft i = -x.moveRight (toLeftMovesNeg.symm i) := by
  cases x
  rfl

@[deprecated moveLeft_neg (since := "2024-10-30")]
alias moveLeft_neg' := moveLeft_neg

theorem moveLeft_neg_toLeftMovesNeg {x : PGame} (i) :
    (-x).moveLeft (toLeftMovesNeg i) = -x.moveRight i := by simp

@[simp]
theorem moveRight_neg {x : PGame} (i) :
    (-x).moveRight i = -x.moveLeft (toRightMovesNeg.symm i) := by
  cases x
  rfl

@[deprecated moveRight_neg (since := "2024-10-30")]
alias moveRight_neg' := moveRight_neg

theorem moveRight_neg_toRightMovesNeg {x : PGame} (i) :
    (-x).moveRight (toRightMovesNeg i) = -x.moveLeft i := by simp

@[deprecated moveRight_neg (since := "2024-10-30")]
theorem moveLeft_neg_symm {x : PGame} (i) :
    x.moveLeft (toRightMovesNeg.symm i) = -(-x).moveRight i := by simp

@[deprecated moveRight_neg (since := "2024-10-30")]
theorem moveLeft_neg_symm' {x : PGame} (i) :
    x.moveLeft i = -(-x).moveRight (toRightMovesNeg i) := by simp

@[deprecated moveLeft_neg (since := "2024-10-30")]
theorem moveRight_neg_symm {x : PGame} (i) :
    x.moveRight (toLeftMovesNeg.symm i) = -(-x).moveLeft i := by simp

@[deprecated moveLeft_neg (since := "2024-10-30")]
theorem moveRight_neg_symm' {x : PGame} (i) :
    x.moveRight i = -(-x).moveLeft (toLeftMovesNeg i) := by simp

@[simp]
theorem forall_leftMoves_neg {x : PGame} {p : (-x).LeftMoves → Prop} :
    (∀ i : (-x).LeftMoves, p i) ↔ (∀ i : x.RightMoves, p (toLeftMovesNeg i)) :=
  toLeftMovesNeg.forall_congr_right.symm

@[simp]
theorem exists_leftMoves_neg {x : PGame} {p : (-x).LeftMoves → Prop} :
    (∃ i : (-x).LeftMoves, p i) ↔ (∃ i : x.RightMoves, p (toLeftMovesNeg i)) :=
  toLeftMovesNeg.exists_congr_right.symm

@[simp]
theorem forall_rightMoves_neg {x : PGame} {p : (-x).RightMoves → Prop} :
    (∀ i : (-x).RightMoves, p i) ↔ (∀ i : x.LeftMoves, p (toRightMovesNeg i)) :=
  toRightMovesNeg.forall_congr_right.symm

@[simp]
theorem exists_rightMoves_neg {x : PGame} {p : (-x).RightMoves → Prop} :
    (∃ i : (-x).RightMoves, p i) ↔ (∃ i : x.LeftMoves, p (toRightMovesNeg i)) :=
  toRightMovesNeg.exists_congr_right.symm

theorem leftMoves_neg_cases {x : PGame} (k) {motive : (-x).LeftMoves → Prop}
    (toLeftMovesNeg : ∀ i, motive <| PGame.toLeftMovesNeg i) :
    motive k := by
  rw [← PGame.toLeftMovesNeg.apply_symm_apply k]
  exact toLeftMovesNeg _

theorem rightMoves_neg_cases {x : PGame} (k) {P : (-x).RightMoves → Prop}
    (h : ∀ i, P <| toRightMovesNeg i) :
    P k := by
  rw [← toRightMovesNeg.apply_symm_apply k]
  exact h _

/-- If `x` has the same moves as `y`, then `-x` has the sames moves as `-y`. -/
lemma Identical.neg : ∀ {x₁ x₂ : PGame}, x₁ ≡ x₂ → -x₁ ≡ -x₂
  | mk _ _ _ _, mk _ _ _ _, ⟨⟨hL₁, hL₂⟩, ⟨hR₁, hR₂⟩⟩ =>
    ⟨⟨fun i ↦ (hR₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hR₂ j).imp (fun _ ↦ Identical.neg)⟩,
      ⟨fun i ↦ (hL₁ i).imp (fun _ ↦ Identical.neg), fun j ↦ (hL₂ j).imp (fun _ ↦ Identical.neg)⟩⟩

/-- If `-x` has the same moves as `-y`, then `x` has the sames moves as `y`. -/
lemma Identical.of_neg : ∀ {x₁ x₂ : PGame}, -x₁ ≡ -x₂ → x₁ ≡ x₂
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R => by
    simpa using Identical.neg (x₁ := mk _ _ (-x₁R ·) (-x₁L ·)) (x₂ := mk _ _ (-x₂R ·) (-x₂L ·))

lemma memₗ_neg_iff : ∀ {x y : PGame},
    x ∈ₗ -y ↔ ∃ z ∈ᵣ y, x ≡ -z
  | mk _ _ _ _, mk _ _ _ _ =>
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

lemma memᵣ_neg_iff : ∀ {x y : PGame},
    x ∈ᵣ -y ↔ ∃ z ∈ₗ y, x ≡ -z
  | mk _ _ _ _, mk _ _ _ _ =>
    ⟨fun ⟨_i, hi⟩ ↦ ⟨_, ⟨_, refl _⟩, hi⟩, fun ⟨_, ⟨i, hi⟩, h⟩ ↦ ⟨i, h.trans hi.neg⟩⟩

/-- If `x` has the same moves as `y`, then `-x` has the same moves as `-y`. -/
def Relabelling.negCongr : ∀ {x y : PGame}, x ≡r y → -x ≡r -y
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨L, R, hL, hR⟩ =>
    ⟨R, L, fun j => (hR j).negCongr, fun i => (hL i).negCongr⟩

private theorem neg_le_lf_neg_iff : ∀ {x y : PGame.{u}}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def]
    constructor
    · rw [and_comm]
      apply and_congr <;> exact forall_congr' fun _ => neg_le_lf_neg_iff.2
    · rw [or_comm]
      apply or_congr <;> exact exists_congr fun _ => neg_le_lf_neg_iff.1
termination_by x y => (x, y)

@[simp]
theorem neg_le_neg_iff {x y : PGame} : -y ≤ -x ↔ x ≤ y :=
  neg_le_lf_neg_iff.1

@[simp]
theorem neg_lf_neg_iff {x y : PGame} : -y ⧏ -x ↔ x ⧏ y :=
  neg_le_lf_neg_iff.2

@[simp]
theorem neg_lt_neg_iff {x y : PGame} : -y < -x ↔ x < y := by
  rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]

@[simp]
theorem neg_identical_neg {x y : PGame} : -x ≡ -y ↔ x ≡ y :=
  ⟨Identical.of_neg, Identical.neg⟩

@[simp]
theorem neg_equiv_neg_iff {x y : PGame} : -x ≈ -y ↔ x ≈ y := by
  show Equiv (-x) (-y) ↔ Equiv x y
  rw [Equiv, Equiv, neg_le_neg_iff, neg_le_neg_iff, and_comm]

@[simp]
theorem neg_fuzzy_neg_iff {x y : PGame} : -x ‖ -y ↔ x ‖ y := by
  rw [Fuzzy, Fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and_comm]

theorem neg_le_iff {x y : PGame} : -y ≤ x ↔ -x ≤ y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]

theorem neg_lf_iff {x y : PGame} : -y ⧏ x ↔ -x ⧏ y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]

theorem neg_lt_iff {x y : PGame} : -y < x ↔ -x < y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]

theorem neg_equiv_iff {x y : PGame} : (-x ≈ y) ↔ (x ≈ -y) := by
  rw [← neg_neg y, neg_equiv_neg_iff, neg_neg]

theorem neg_fuzzy_iff {x y : PGame} : -x ‖ y ↔ x ‖ -y := by
  rw [← neg_neg y, neg_fuzzy_neg_iff, neg_neg]

theorem le_neg_iff {x y : PGame} : y ≤ -x ↔ x ≤ -y := by rw [← neg_neg x, neg_le_neg_iff, neg_neg]

theorem lf_neg_iff {x y : PGame} : y ⧏ -x ↔ x ⧏ -y := by rw [← neg_neg x, neg_lf_neg_iff, neg_neg]

theorem lt_neg_iff {x y : PGame} : y < -x ↔ x < -y := by rw [← neg_neg x, neg_lt_neg_iff, neg_neg]

@[simp]
theorem neg_le_zero_iff {x : PGame} : -x ≤ 0 ↔ 0 ≤ x := by rw [neg_le_iff, neg_zero]

@[simp]
theorem zero_le_neg_iff {x : PGame} : 0 ≤ -x ↔ x ≤ 0 := by rw [le_neg_iff, neg_zero]

@[simp]
theorem neg_lf_zero_iff {x : PGame} : -x ⧏ 0 ↔ 0 ⧏ x := by rw [neg_lf_iff, neg_zero]

@[simp]
theorem zero_lf_neg_iff {x : PGame} : 0 ⧏ -x ↔ x ⧏ 0 := by rw [lf_neg_iff, neg_zero]

@[simp]
theorem neg_lt_zero_iff {x : PGame} : -x < 0 ↔ 0 < x := by rw [neg_lt_iff, neg_zero]

@[simp]
theorem zero_lt_neg_iff {x : PGame} : 0 < -x ↔ x < 0 := by rw [lt_neg_iff, neg_zero]

@[simp]
theorem neg_equiv_zero_iff {x : PGame} : (-x ≈ 0) ↔ (x ≈ 0) := by rw [neg_equiv_iff, neg_zero]

@[simp]
theorem neg_fuzzy_zero_iff {x : PGame} : -x ‖ 0 ↔ x ‖ 0 := by rw [neg_fuzzy_iff, neg_zero]

@[simp]
theorem zero_equiv_neg_iff {x : PGame} : (0 ≈ -x) ↔ (0 ≈ x) := by rw [← neg_equiv_iff, neg_zero]

@[simp]
theorem zero_fuzzy_neg_iff {x : PGame} : 0 ‖ -x ↔ 0 ‖ x := by rw [← neg_fuzzy_iff, neg_zero]

/-! ### Addition and subtraction -/

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
instance : Add PGame.{u} :=
  ⟨fun x y => by
    induction x generalizing y with | mk xl xr _ _ IHxl IHxr => _
    induction y with | mk yl yr yL yR IHyl IHyr => _
    have y := mk yl yr yL yR
    refine ⟨xl ⊕ yl, xr ⊕ yr, Sum.rec ?_ ?_, Sum.rec ?_ ?_⟩
    · exact fun i => IHxl i y
    · exact IHyl
    · exact fun i => IHxr i y
    · exact IHyr⟩

theorem mk_add_moveLeft {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft i =
      i.rec (xL · + mk yl yr yL yR) (mk xl xr xL xR + yL ·) :=
  rfl

theorem mk_add_moveRight {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight i =
      i.rec (xR · + mk yl yr yL yR) (mk xl xr xL xR + yR ·) :=
  rfl

/-- The pre-game `((0 + 1) + ⋯) + 1`.

Note that this is **not** the usual recursive definition `n = {0, 1, … | }`. For instance,
`2 = 0 + 1 + 1 = {0 + 0 + 1, 0 + 1 + 0 | }` does not contain any left option equivalent to `0`. For
an implementation of said definition, see `Ordinal.toPGame`. For the proof that these games are
equivalent, see `Ordinal.toPGame_natCast`. -/
instance : NatCast PGame :=
  ⟨Nat.unaryCast⟩

@[simp]
protected theorem nat_succ (n : ℕ) : ((n + 1 : ℕ) : PGame) = n + 1 :=
  rfl

instance isEmpty_leftMoves_add (x y : PGame.{u}) [IsEmpty x.LeftMoves] [IsEmpty y.LeftMoves] :
    IsEmpty (x + y).LeftMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'

instance isEmpty_rightMoves_add (x y : PGame.{u}) [IsEmpty x.RightMoves] [IsEmpty y.RightMoves] :
    IsEmpty (x + y).RightMoves := by
  cases x
  cases y
  apply isEmpty_sum.2 ⟨_, _⟩
  assumption'

/-- `x + 0` has exactly the same moves as `x`. -/
def addZeroRelabelling : ∀ x : PGame.{u}, x + 0 ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.sumEmpty xl PEmpty, Equiv.sumEmpty xr PEmpty, ?_, ?_⟩ <;> rintro (⟨i⟩ | ⟨⟨⟩⟩) <;>
      apply addZeroRelabelling
termination_by x => x

/-- `x + 0` is equivalent to `x`. -/
theorem add_zero_equiv (x : PGame.{u}) : x + 0 ≈ x :=
  (addZeroRelabelling x).equiv

/-- `0 + x` has exactly the same moves as `x`. -/
def zeroAddRelabelling : ∀ x : PGame.{u}, 0 + x ≡r x
  | ⟨xl, xr, xL, xR⟩ => by
    refine ⟨Equiv.emptySum PEmpty xl, Equiv.emptySum PEmpty xr, ?_, ?_⟩ <;> rintro (⟨⟨⟩⟩ | ⟨i⟩) <;>
      apply zeroAddRelabelling

/-- `0 + x` is equivalent to `x`. -/
theorem zero_add_equiv (x : PGame.{u}) : 0 + x ≈ x :=
  (zeroAddRelabelling x).equiv

/-- Use `toLeftMovesAdd` to cast between these two types. -/
theorem leftMoves_add : ∀ x y : PGame.{u}, (x + y).LeftMoves = (x.LeftMoves ⊕ y.LeftMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Use `toRightMovesAdd` to cast between these two types. -/
theorem rightMoves_add : ∀ x y : PGame.{u}, (x + y).RightMoves = (x.RightMoves ⊕ y.RightMoves)
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩ => rfl

/-- Converts a left move for `x` or `y` into a left move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toLeftMovesAdd {x y : PGame} : x.LeftMoves ⊕ y.LeftMoves ≃ (x + y).LeftMoves :=
  Equiv.cast (leftMoves_add x y).symm

/-- Converts a right move for `x` or `y` into a right move for `x + y` and vice versa.

Even though these types are the same (not definitionally so), this is the preferred way to convert
between them. -/
def toRightMovesAdd {x y : PGame} : x.RightMoves ⊕ y.RightMoves ≃ (x + y).RightMoves :=
  Equiv.cast (rightMoves_add x y).symm

@[simp]
theorem mk_add_moveLeft_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inl i) =
      (mk xl xr xL xR).moveLeft i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_moveLeft_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inl i)) = x.moveLeft i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveRight_inl {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inl i) =
      (mk xl xr xL xR).moveRight i + mk yl yr yL yR :=
  rfl

@[simp]
theorem add_moveRight_inl {x : PGame} (y : PGame) (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inl i)) = x.moveRight i + y := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveLeft_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveLeft (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveLeft i :=
  rfl

@[simp]
theorem add_moveLeft_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveLeft (toLeftMovesAdd (Sum.inr i)) = x + y.moveLeft i := by
  cases x
  cases y
  rfl

@[simp]
theorem mk_add_moveRight_inr {xl xr yl yr} {xL xR yL yR} {i} :
    (mk xl xr xL xR + mk yl yr yL yR).moveRight (Sum.inr i) =
      mk xl xr xL xR + (mk yl yr yL yR).moveRight i :=
  rfl

@[simp]
theorem add_moveRight_inr (x : PGame) {y : PGame} (i) :
    (x + y).moveRight (toRightMovesAdd (Sum.inr i)) = x + y.moveRight i := by
  cases x
  cases y
  rfl

/-- Case on possible left moves of `x + y`. -/
theorem leftMoves_add_cases {x y : PGame} (k) {P : (x + y).LeftMoves → Prop}
    (hl : ∀ i, P <| toLeftMovesAdd (Sum.inl i)) (hr : ∀ i, P <| toLeftMovesAdd (Sum.inr i)) :
    P k := by
  rw [← toLeftMovesAdd.apply_symm_apply k]
  rcases toLeftMovesAdd.symm k with i | i
  · exact hl i
  · exact hr i

/-- Case on possible right moves of `x + y`. -/
theorem rightMoves_add_cases {x y : PGame} (k) {P : (x + y).RightMoves → Prop}
    (hl : ∀ j, P <| toRightMovesAdd (Sum.inl j)) (hr : ∀ j, P <| toRightMovesAdd (Sum.inr j)) :
    P k := by
  rw [← toRightMovesAdd.apply_symm_apply k]
  rcases toRightMovesAdd.symm k with i | i
  · exact hl i
  · exact hr i

instance isEmpty_nat_rightMoves : ∀ n : ℕ, IsEmpty (RightMoves n)
  | 0 => inferInstanceAs (IsEmpty PEmpty)
  | n + 1 => by
    haveI := isEmpty_nat_rightMoves n
    rw [PGame.nat_succ, rightMoves_add]
    infer_instance

/-- `x + y` has exactly the same moves as `y + x`. -/
protected lemma add_comm (x y : PGame) : x + y ≡ y + x :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine Identical.of_equiv (Equiv.sumComm _ _) (Equiv.sumComm _ _) ?_ ?_ <;>
    · rintro (_ | _) <;>
      · dsimp; exact PGame.add_comm _ _
  termination_by (x, y)

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
protected lemma add_assoc (x y z : PGame) : x + y + z ≡ x + (y + z) :=
  match x, y, z with
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => by
    refine Identical.of_equiv (Equiv.sumAssoc _ _ _) (Equiv.sumAssoc _ _ _) ?_ ?_ <;>
    · rintro ((_ | _) | _)
      · exact PGame.add_assoc _ _ _
      · exact PGame.add_assoc (mk _ _ _ _) _ _
      · exact PGame.add_assoc (mk _ _ _ _) (mk _ _ _ _) _
  termination_by (x, y, z)

/-- `x + 0` has exactly the same moves as `x`. -/
protected lemma add_zero : ∀ (x : PGame), x + 0 ≡ x
  | mk xl xr xL xR => by
    refine Identical.of_equiv (Equiv.sumEmpty _ _) (Equiv.sumEmpty _ _) ?_ ?_ <;>
    · rintro (_ | ⟨⟨⟩⟩)
      exact PGame.add_zero _

/-- `0 + x` has exactly the same moves as `x`. -/
protected lemma zero_add (x : PGame) : 0 + x ≡ x :=
  (PGame.add_comm _ _).trans x.add_zero

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
protected lemma neg_add (x y : PGame) : -(x + y) = -x + -y :=
  match x, y with
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ext rfl rfl ?_ ?_ <;>
    · rintro (i | i) _ ⟨rfl⟩
      · exact PGame.neg_add _ _
      · simpa [Equiv.refl, mk_add_moveLeft, mk_add_moveRight] using PGame.neg_add _ _
  termination_by (x, y)

/-- `-(x + y)` has exactly the same moves as `-y + -x`. -/
protected lemma neg_add_rev (x y : PGame) : -(x + y) ≡ -y + -x :=
  Identical.trans (of_eq (x.neg_add y)) (PGame.add_comm _ _)

lemma identical_zero_iff : ∀ (x : PGame),
    x ≡ 0 ↔ IsEmpty x.LeftMoves ∧ IsEmpty x.RightMoves
  | mk xl xr xL xR => by
    constructor
    · rintro ⟨h₁, h₂⟩
      dsimp [Relator.BiTotal, Relator.LeftTotal, Relator.RightTotal] at h₁ h₂
      simp_rw [IsEmpty.forall_iff, and_true, IsEmpty.exists_iff] at h₁ h₂
      exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
    · rintro ⟨h₁, h₂⟩
      exact identical_of_isEmpty _ _

/-- Any game without left or right moves is identical to 0. -/
lemma identical_zero (x : PGame) [IsEmpty x.LeftMoves] [IsEmpty x.RightMoves] : x ≡ 0 :=
  x.identical_zero_iff.mpr ⟨by infer_instance, by infer_instance⟩

protected lemma add_eq_zero : ∀ {x y : PGame}, x + y ≡ 0 ↔ x ≡ 0 ∧ y ≡ 0
  | mk xl xr xL xR, mk yl yr yL yR => by
    simp_rw [identical_zero_iff, leftMoves_add, rightMoves_add, isEmpty_sum]
    tauto

lemma Identical.add_right {x₁ x₂ y} : x₁ ≡ x₂ → x₁ + y ≡ x₂ + y :=
  match x₁, x₂, y with
  | mk x₁l x₁r x₁L x₁R, mk x₂l x₂r x₂L x₂R, mk yl yr yL yR => by
    intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> rintro (_ | _) <;> try exact ⟨.inr _, h.add_right⟩
    · exact (h.1.1 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.1.2 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.2.1 _).elim (⟨.inl ·, ·.add_right⟩)
    · exact (h.2.2 _).elim (⟨.inl ·, ·.add_right⟩)
  termination_by (x₁, x₂, y)

lemma Identical.add_left {x y₁ y₂} (hy : y₁ ≡ y₂) : x + y₁ ≡ x + y₂ :=
  (x.add_comm y₁).trans (hy.add_right.trans (y₂.add_comm x))

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
lemma Identical.add {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ + y₁ ≡ x₂ + y₂ :=
  hx.add_right.trans hy.add_left

lemma memₗ_add_iff {x y₁ y₂ : PGame} :
    x ∈ₗ y₁ + y₂ ↔ (∃ z ∈ₗ y₁, x ≡ z + y₂) ∨ (∃ z ∈ₗ y₂, x ≡ y₁ + z) := by
  obtain ⟨y₁l, y₁r, y₁L, y₁R⟩ := y₁
  obtain ⟨y₂l, y₂r, y₂L, y₂R⟩ := y₂
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨y₁L i, moveLeft_memₗ _ _, hi⟩, .inr ⟨y₂L i, moveLeft_memₗ _ _, hi⟩]
  · rintro (⟨_, ⟨i, hi⟩, h⟩ | ⟨_, ⟨i, hi⟩, h⟩)
    exacts [⟨.inl i, h.trans hi.add_right⟩, ⟨.inr i, h.trans hi.add_left⟩]

lemma memᵣ_add_iff {x y₁ y₂ : PGame} :
    x ∈ᵣ y₁ + y₂ ↔ (∃ z ∈ᵣ y₁, x ≡ z + y₂) ∨ (∃ z ∈ᵣ y₂, x ≡ y₁ + z) := by
  obtain ⟨y₁l, y₁r, y₁L, y₁R⟩ := y₁
  obtain ⟨y₂l, y₂r, y₂L, y₂R⟩ := y₂
  constructor
  · rintro ⟨(i | i), hi⟩
    exacts [.inl ⟨y₁R i, moveRight_memᵣ _ _, hi⟩, .inr ⟨y₂R i, moveRight_memᵣ _ _, hi⟩]
  · rintro (⟨_, ⟨i, hi⟩, h⟩ | ⟨_, ⟨i, hi⟩, h⟩)
    exacts [⟨.inl i, h.trans hi.add_right⟩, ⟨.inr i, h.trans hi.add_left⟩]

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w + y` has the same moves as `x + z`. -/
def Relabelling.addCongr : ∀ {w x y z : PGame.{u}}, w ≡r x → y ≡r z → w + y ≡r x + z
  | ⟨wl, wr, wL, wR⟩, ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩, ⟨L₁, R₁, hL₁, hR₁⟩,
    ⟨L₂, R₂, hL₂, hR₂⟩ => by
    let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩
    let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩
    refine ⟨Equiv.sumCongr L₁ L₂, Equiv.sumCongr R₁ R₂, ?_, ?_⟩ <;> rintro (i | j)
    · exact (hL₁ i).addCongr Hyz
    · exact Hwx.addCongr (hL₂ j)
    · exact (hR₁ i).addCongr Hyz
    · exact Hwx.addCongr (hR₂ j)
termination_by _ x _ z => (x, z)

instance : Sub PGame :=
  ⟨fun x y => x + -y⟩

@[simp]
theorem sub_zero_eq_add_zero (x : PGame) : x - 0 = x + 0 :=
  show x + -0 = x + 0 by rw [neg_zero]

protected lemma sub_zero (x : PGame) : x - 0 ≡ x :=
  _root_.trans (of_eq x.sub_zero_eq_add_zero) x.add_zero

/-- This lemma is named to match `neg_sub'`. -/
protected lemma neg_sub' (x y : PGame) : -(x - y) = -x - -y := PGame.neg_add _ _

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
lemma Identical.sub {x₁ x₂ y₁ y₂ : PGame.{u}} (hx : x₁ ≡ x₂) (hy : y₁ ≡ y₂) : x₁ - y₁ ≡ x₂ - y₂ :=
  hx.add hy.neg

/-- If `w` has the same moves as `x` and `y` has the same moves as `z`,
then `w - y` has the same moves as `x - z`. -/
def Relabelling.subCongr {w x y z : PGame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
  h₁.addCongr h₂.negCongr

/-- `-(x + y)` has exactly the same moves as `-x + -y`. -/
def negAddRelabelling : ∀ x y : PGame, -(x + y) ≡r -x + -y
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩ => by
    refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_⟩
    all_goals
      exact fun j =>
        Sum.casesOn j (fun j => negAddRelabelling _ _) fun j =>
          negAddRelabelling ⟨xl, xr, xL, xR⟩ _
termination_by x y => (x, y)

theorem neg_add_le {x y : PGame} : -(x + y) ≤ -x + -y :=
  (x.neg_add y).le

/-- `x + y` has exactly the same moves as `y + x`. -/
def addCommRelabelling : ∀ x y : PGame.{u}, x + y ≡r y + x
  | mk xl xr xL xR, mk yl yr yL yR => by
    refine ⟨Equiv.sumComm _ _, Equiv.sumComm _ _, ?_, ?_⟩ <;> rintro (_ | _) <;>
      · dsimp
        apply addCommRelabelling
termination_by x y => (x, y)

theorem add_comm_le {x y : PGame} : x + y ≤ y + x :=
  (x.add_comm y).le

theorem add_comm_equiv {x y : PGame} : x + y ≈ y + x :=
  (x.add_comm y).equiv

/-- `(x + y) + z` has exactly the same moves as `x + (y + z)`. -/
def addAssocRelabelling : ∀ x y z : PGame.{u}, x + y + z ≡r x + (y + z)
  | ⟨xl, xr, xL, xR⟩, ⟨yl, yr, yL, yR⟩, ⟨zl, zr, zL, zR⟩ => by
    refine ⟨Equiv.sumAssoc _ _ _, Equiv.sumAssoc _ _ _, ?_, ?_⟩
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yL i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zL i)
    · rintro (⟨i | i⟩ | i)
      · apply addAssocRelabelling
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ (yR i)
      · apply addAssocRelabelling ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ (zR i)
termination_by x y z => (x, y, z)

theorem add_assoc_equiv {x y z : PGame} : x + y + z ≈ x + (y + z) :=
  (x.add_assoc y z).equiv

theorem neg_add_cancel_le_zero : ∀ x : PGame, -x + x ≤ 0
  | ⟨xl, xr, xL, xR⟩ =>
    le_zero.2 fun i => by
      obtain i | i := i
      · -- If Left played in -x, Right responds with the same move in x.
        refine ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), ?_⟩
        convert @neg_add_cancel_le_zero (xR i)
        apply add_moveRight_inr
      · -- If Left in x, Right responds with the same move in -x.
        dsimp
        refine ⟨@toRightMovesAdd ⟨_, _, _, _⟩ _ (Sum.inl i), ?_⟩
        convert @neg_add_cancel_le_zero (xL i)
        apply add_moveRight_inl

theorem zero_le_neg_add_cancel (x : PGame) : 0 ≤ -x + x := by
  rw [← neg_le_neg_iff, neg_zero]
  exact neg_add_le.trans (neg_add_cancel_le_zero _)

theorem neg_add_cancel_equiv (x : PGame) : -x + x ≈ 0 :=
  ⟨neg_add_cancel_le_zero x, zero_le_neg_add_cancel x⟩

theorem add_neg_cancel_le_zero (x : PGame) : x + -x ≤ 0 :=
  add_comm_le.trans (neg_add_cancel_le_zero x)

theorem zero_le_add_neg_cancel (x : PGame) : 0 ≤ x + -x :=
  (zero_le_neg_add_cancel x).trans add_comm_le

theorem add_neg_cancel_equiv (x : PGame) : x + -x ≈ 0 :=
  ⟨add_neg_cancel_le_zero x, zero_le_add_neg_cancel x⟩

theorem sub_self_equiv : ∀ (x : PGame), x - x ≈ 0 :=
  add_neg_cancel_equiv

private theorem add_le_add_right' : ∀ {x y z : PGame}, x ≤ y → x + z ≤ y + z
  | mk xl xr xL xR, mk yl yr yL yR, mk zl zr zL zR => fun h => by
    refine le_def.2 ⟨fun i => ?_, fun i => ?_⟩ <;> obtain i | i := i
    · rw [le_def] at h
      obtain ⟨h_left, h_right⟩ := h
      rcases h_left i with (⟨i', ih⟩ | ⟨j, jh⟩)
      · exact Or.inl ⟨toLeftMovesAdd (Sum.inl i'), add_le_add_right' ih⟩
      · refine Or.inr ⟨toRightMovesAdd (Sum.inl j), ?_⟩
        convert add_le_add_right' jh
        apply add_moveRight_inl
    · exact Or.inl ⟨@toLeftMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
    · rw [le_def] at h
      rcases h.right i with (⟨i, ih⟩ | ⟨j', jh⟩)
      · refine Or.inl ⟨toLeftMovesAdd (Sum.inl i), ?_⟩
        convert add_le_add_right' ih
        apply add_moveLeft_inl
      · exact Or.inr ⟨toRightMovesAdd (Sum.inl j'), add_le_add_right' jh⟩
    · exact
        Or.inr ⟨@toRightMovesAdd _ ⟨_, _, _, _⟩ (Sum.inr i), add_le_add_right' h⟩
termination_by x y z => (x, y, z)

instance addRightMono : AddRightMono PGame :=
  ⟨fun _ _ _ => add_le_add_right'⟩

instance addLeftMono : AddLeftMono PGame :=
  ⟨fun x _ _ h => (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩

theorem add_lf_add_right {y z : PGame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
  suffices z + x ≤ y + x → z ≤ y by
    rw [← PGame.not_le] at h ⊢
    exact mt this h
  fun w =>
  calc
    z ≤ z + 0 := (PGame.add_zero _).symm.le
    _ ≤ z + (x + -x) := add_le_add_left (zero_le_add_neg_cancel x) _
    _ ≤ z + x + -x := (PGame.add_assoc _ _ _).symm.le
    _ ≤ y + x + -x := add_le_add_right w _
    _ ≤ y + (x + -x) := (PGame.add_assoc _ _ _).le
    _ ≤ y + 0 := add_le_add_left (add_neg_cancel_le_zero x) _
    _ ≤ y := (PGame.add_zero _).le

theorem add_lf_add_left {y z : PGame} (h : y ⧏ z) (x) : x + y ⧏ x + z := by
  rw [lf_congr add_comm_equiv add_comm_equiv]
  apply add_lf_add_right h

instance addRightStrictMono : AddRightStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩⟩

instance addLeftStrictMono : AddLeftStrictMono PGame :=
  ⟨fun x _ _ h => ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩⟩

theorem add_lf_add_of_lf_of_le {w x y z : PGame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
  lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)

theorem add_lf_add_of_le_of_lf {w x y z : PGame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
  lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)

theorem add_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
  ⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
    (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : PGame} (h : x ≈ y) : x + z ≈ y + z :=
  add_congr h equiv_rfl

theorem add_congr_right {x y z : PGame} : (y ≈ z) → (x + y ≈ x + z) :=
  add_congr equiv_rfl

theorem sub_congr {w x y z : PGame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
  add_congr h₁ (neg_equiv_neg_iff.2 h₂)

theorem sub_congr_left {x y z : PGame} (h : x ≈ y) : x - z ≈ y - z :=
  sub_congr h equiv_rfl

theorem sub_congr_right {x y z : PGame} : (y ≈ z) → (x - y ≈ x - z) :=
  sub_congr equiv_rfl

theorem le_iff_sub_nonneg {x y : PGame} : x ≤ y ↔ 0 ≤ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans (add_le_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ ≤ y - x + x := add_le_add_right h _
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (PGame.add_zero y).le
      ⟩

theorem lf_iff_sub_zero_lf {x y : PGame} : x ⧏ y ↔ 0 ⧏ y - x :=
  ⟨fun h => (zero_le_add_neg_cancel x).trans_lf (add_lf_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ ⧏ y - x + x := add_lf_add_right h _
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (PGame.add_zero y).le
      ⟩

theorem lt_iff_sub_pos {x y : PGame} : x < y ↔ 0 < y - x :=
  ⟨fun h => lt_of_le_of_lt (zero_le_add_neg_cancel x) (add_lt_add_right h _), fun h =>
    calc
      x ≤ 0 + x := (PGame.zero_add x).symm.le
      _ < y - x + x := add_lt_add_right h _
      _ ≤ y + (-x + x) := (PGame.add_assoc _ _ _).le
      _ ≤ y + 0 := add_le_add_left (neg_add_cancel_le_zero x) _
      _ ≤ y := (PGame.add_zero y).le
      ⟩

/-! ### Interaction of option insertion with negation -/

theorem neg_insertRight_neg (x x' : PGame.{u}) : (-x).insertRight (-x') = -x.insertLeft x' := by
  cases x
  cases x'
  dsimp [insertRight, insertLeft]
  congr! with (i | j)

theorem neg_insertLeft_neg (x x' : PGame.{u}) : (-x).insertLeft (-x') = -x.insertRight x' := by
  rw [← neg_eq_iff_eq_neg, ← neg_insertRight_neg, neg_neg, neg_neg]

/-! ### Special pre-games -/


/-- The pre-game `star`, which is fuzzy with zero. -/
def star : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => 0⟩

@[simp]
theorem star_leftMoves : star.LeftMoves = PUnit :=
  rfl

@[simp]
theorem star_rightMoves : star.RightMoves = PUnit :=
  rfl

@[simp]
theorem star_moveLeft (x) : star.moveLeft x = 0 :=
  rfl

@[simp]
theorem star_moveRight (x) : star.moveRight x = 0 :=
  rfl

instance uniqueStarLeftMoves : Unique star.LeftMoves :=
  PUnit.instUnique

instance uniqueStarRightMoves : Unique star.RightMoves :=
  PUnit.instUnique

theorem zero_lf_star : 0 ⧏ star := by
  rw [zero_lf]
  use default
  rintro ⟨⟩

theorem star_lf_zero : star ⧏ 0 := by
  rw [lf_zero]
  use default
  rintro ⟨⟩

theorem star_fuzzy_zero : star ‖ 0 :=
  ⟨star_lf_zero, zero_lf_star⟩

@[simp]
theorem neg_star : -star = star := by simp [star]

@[simp]
protected theorem zero_lt_one : (0 : PGame) < 1 :=
  lt_of_le_of_lf (zero_le_of_isEmpty_rightMoves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)

/-- The pre-game `up` -/
def up : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => 0, fun _ => star⟩

@[simp]
theorem up_leftMoves : up.LeftMoves = PUnit :=
  rfl

@[simp]
theorem up_rightMoves : up.RightMoves = PUnit :=
  rfl

@[simp]
theorem up_moveLeft (x) : up.moveLeft x = 0 :=
  rfl

@[simp]
theorem up_moveRight (x) : up.moveRight x = star :=
  rfl

@[simp]
theorem up_neg : 0 < up := by
  rw [lt_iff_le_and_lf, zero_lf]
  simp [zero_le_lf, zero_lf_star]

theorem star_fuzzy_up : star ‖ up := by
  unfold Fuzzy
  simp only [← PGame.not_le]
  simp [le_iff_forall_lf]

/-- The pre-game `down` -/
def down : PGame.{u} :=
  ⟨PUnit, PUnit, fun _ => star, fun _ => 0⟩

@[simp]
theorem down_leftMoves : down.LeftMoves = PUnit :=
  rfl

@[simp]
theorem down_rightMoves : down.RightMoves = PUnit :=
  rfl

@[simp]
theorem down_moveLeft (x) : down.moveLeft x = star :=
  rfl

@[simp]
theorem down_moveRight (x) : down.moveRight x = 0 :=
  rfl

@[simp]
theorem down_neg : down < 0 := by
  rw [lt_iff_le_and_lf, lf_zero]
  simp [le_zero_lf, star_lf_zero]

@[simp]
theorem neg_down : -down = up := by simp [up, down]

@[simp]
theorem neg_up : -up = down := by simp [up, down]

theorem star_fuzzy_down : star ‖ down := by
  rw [← neg_fuzzy_neg_iff, neg_down, neg_star]
  exact star_fuzzy_up

instance : ZeroLEOneClass PGame :=
  ⟨PGame.zero_lt_one.le⟩

@[simp]
theorem zero_lf_one : (0 : PGame) ⧏ 1 :=
  PGame.zero_lt_one.lf

end SetTheory.PGame
