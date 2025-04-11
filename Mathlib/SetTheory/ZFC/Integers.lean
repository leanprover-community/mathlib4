/-
Copyright (c) 2025 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import Mathlib.SetTheory.ZFC.Naturals
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-! # ZFC Integers

This file provides a construction of the integers in ZFC based on the construction of natural
numbers. It follows the usual construction of integers as equivalence classes of pairs of natural
numbers.

The theory also comes with usual theorems and arithmetic operations on integers and wraps everything
in a commutative ring structure.

Finally, we show that that the `ZFInt` type is isomorphic to Lean's `Int` type using the
Schröder-Bernstein theorem.
-/

noncomputable section

namespace ZFSet

section Integers

protected abbrev zrel (a b : ZFNat × ZFNat) : Prop := a.1 + b.2 = a.2 + b.1

protected def zrel_eq : Equivalence ZFSet.zrel where
  refl := fun _ => add_comm _ _
  symm := by
    unfold ZFSet.zrel
    intro x y h
    rw [add_comm, add_comm y.2]
    symm
    assumption
  trans := by
    unfold ZFSet.zrel
    intro x y z hxy hyz
    have : x.1 + y.2 + y.1 + z.2 = x.2 + y.1 + y.2 + z.1 := by
      rw [hxy, ← ZFNat.add_assoc, hyz, ZFNat.add_assoc _ _ _]
    rw [add_assoc x.1, add_comm _ (y.2 + y.1), add_assoc, add_assoc x.2, add_comm _ (y.1 + y.2),
      add_comm y.1, ← add_assoc (y.2 + y.1)] at this
    apply add_left_cancel (a := y.2 + y.1)
    simpa only [add_assoc]

protected instance instSetoidZFNatZFNat : Setoid (ZFNat × ZFNat) where
  r := ZFSet.zrel
  iseqv := ZFSet.zrel_eq

abbrev ZFInt := Quotient ZFSet.instSetoidZFNatZFNat

namespace ZFInt

def mk : ZFNat × ZFNat → ZFInt := Quotient.mk''

@[simp]
theorem mk_eq (x : ZFNat × ZFNat) : @Eq ZFInt ⟦x⟧ (mk x) := rfl

@[simp]
theorem mk_out : ∀ x : ZFInt, mk x.out = x := Quotient.out_eq

theorem eq {x y : ZFNat × ZFNat} : mk x = mk y ↔ ZFSet.zrel x y := Quotient.eq

theorem sound {x y : ZFNat × ZFNat} (h : ZFSet.zrel x y) : mk x = mk y := Quotient.sound h

theorem exact {x y : ZFNat × ZFNat} : mk x = mk y → ZFSet.zrel x y := Quotient.exact

abbrev zero : ZFInt := mk (0, 0)
abbrev one : ZFInt := mk (1, 0) -- (0,1) works too

protected instance : Zero ZFInt := ⟨zero⟩
protected instance : One ZFInt := ⟨one⟩

theorem zero_eq : (0 : ZFInt) = mk (0, 0) := rfl
theorem one_eq : (1 : ZFInt) = mk (1, 0) := rfl

theorem mk_eq_zero_iff {n m} : ZFInt.mk (n,m) = 0 ↔ n = m := by
  constructor
  · intro h
    rw [ZFInt.zero_eq, ZFInt.eq, ZFSet.zrel] at h
    exact ZFNat.add_right_cancel.mp h
  · rintro rfl
    exact ZFInt.sound rfl

open ZFNat in
abbrev add (n m : ZFInt) : ZFInt :=
  Quotient.liftOn₂ n m (fun ⟨a, b⟩ ⟨c, d⟩ => mk (a + c, b + d)) fun x y x' y' hx hy => sound (by
    have h1 : x.1 + x'.2 = x.2 + x'.1 := hx
    have h2 : y.1 + y'.2 = y.2 + y'.1 := hy
    simp only [ZFSet.zrel]
    have : x.1 + x'.2 + y.1 + y'.2 = x.2 + x'.1 + y.2 + y'.1 := by
      rw [h1, ← add_assoc, h2, add_assoc]
    conv_lhs => rw [add_assoc, ← add_assoc, ← add_assoc, ZFNat.add_comm y.1, add_assoc, add_assoc,
      ← add_assoc, ZFNat.add_comm y'.2, add_assoc, this]
    conv_rhs => rw [add_assoc]; lhs; rw [← add_assoc]; rhs; rw [add_comm]
    rw [add_assoc])

protected instance : Add ZFInt := ⟨ZFInt.add⟩
theorem add_eq (n m : ZFNat × ZFNat) : mk n + mk m = mk (n.1 + m.1, n.2 + m.2) := rfl

theorem add_assoc (n m k : ZFInt) : n + (m + k) = n + m + k := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  induction k using Quotient.ind
  simp_rw [mk_eq, ZFInt.add_eq, ZFNat.add_assoc]

theorem add_comm (n m : ZFInt) : n + m = m + n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  simp_rw [mk_eq, ZFInt.add_eq, ZFNat.add_comm]

lemma add_left_comm (n m k : ZFInt) : n + (m + k) = m + (n + k) := by
  rw [add_assoc, add_assoc, add_comm n]

lemma add_right_comm (n m k : ZFInt) : (n + m) + k = (n + k) + m := by
  rw [← add_assoc, add_comm m, add_assoc]

@[simp]
theorem add_zero {x : ZFInt} : x + 0 = x := by
  induction x using Quotient.ind
  simp_rw [mk_eq, zero_eq, ZFInt.add_eq, ZFNat.add_zero]

@[simp]
theorem zero_add {x : ZFInt} : 0 + x = x := by
  rw [add_comm, add_zero]

protected abbrev neg (n : ZFInt) : ZFInt :=
  Quotient.liftOn n (fun x => mk (x.2, x.1)) fun x y h => sound (ZFSet.zrel_eq.symm (by
    simp only [ZFSet.zrel]
    rw [ZFNat.add_comm, ZFNat.add_comm y.1, ← ZFSet.zrel]
    assumption))
protected instance : Neg ZFInt := ⟨ZFInt.neg⟩
theorem neg_eq (n : ZFNat × ZFNat) : -mk n = mk (n.2, n.1) := rfl

@[simp]
theorem neg_neg (n : ZFInt) : -(-n) = n := by
  induction n using Quotient.ind
  rw [mk_eq, neg_eq, neg_eq]

@[simp]
theorem neg_zero : -(0 : ZFInt) = 0 := by
  rw [zero_eq, neg_eq]

theorem neg_inj {a b : ZFInt} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← neg_neg a, ← neg_neg b, h], congrArg _⟩

@[simp]
theorem neg_eq_zero {a : ZFInt} : -a = 0 ↔ a = 0 := ZFInt.neg_inj (b := 0)

theorem neg_ne_zero {a : ZFInt} : -a ≠ 0 ↔ a ≠ 0 := not_congr neg_eq_zero

theorem add_left_neg {a : ZFInt} : -a + a = 0 := by
  induction a using Quotient.ind
  apply sound
  rw [ZFNat.add_comm]

theorem add_right_neg (a : ZFInt) : a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg

theorem neg_eq_of_add_eq_zero {a b : ZFInt} (h : a + b = 0) : -a = b := by
  rw [← @add_zero (-a), ← h, add_assoc, add_left_neg, zero_add]

theorem eq_neg_of_eq_neg {a b : ZFInt} (h : a = -b) : b = -a := by
  rw [h, neg_neg]

theorem eq_neg_comm {a b : ZFInt} : a = -b ↔ b = -a := ⟨eq_neg_of_eq_neg, eq_neg_of_eq_neg⟩

theorem neg_eq_comm {a b : ZFInt} : -a = b ↔ -b = a := by
  rw [eq_comm, eq_neg_comm, eq_comm]

theorem neg_add_cancel_left (a b : ZFInt) : -a + (a + b) = b := by
  rw [add_assoc, add_left_neg, zero_add]

theorem add_neg_cancel_left (a b : ZFInt) : a + (-a + b) = b := by
  rw [add_assoc, add_right_neg, zero_add]

theorem add_neg_cancel_right (a b : ZFInt) : a + b + -b = a := by
  rw [← add_assoc, add_right_neg, add_zero]

theorem neg_add_cancel_right (a b : ZFInt) : a + -b + b = a := by
  rw [← add_assoc, add_left_neg, add_zero]

theorem add_left_cancel {a b c : ZFInt} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [add_assoc, add_left_neg, zero_add] at h₁
  exact h₁

@[simp]
theorem neg_add {a b : ZFInt} : -(a + b) = -a + -b := by
  apply add_left_cancel (a := a + b)
  rw [add_right_neg, add_comm a, add_assoc, ← add_assoc b, add_right_neg, add_zero, add_right_neg]

abbrev sub (n m : ZFInt) : ZFInt := n + -m
protected instance : Sub ZFInt := ⟨ZFInt.sub⟩
theorem sub_eq (n m : ZFNat × ZFNat) : mk n - mk m = mk (n.1 + m.2, n.2 + m.1) := rfl

theorem sub_eq_add_neg {a b : ZFInt} : a - b = a + -b := rfl

theorem add_neg_one (i : ZFInt) : i + -1 = i - 1 := rfl

@[simp]
theorem sub_self (a : ZFInt) : a - a = 0 := by rw [sub_eq_add_neg, add_right_neg]

@[simp]
theorem sub_zero (a : ZFInt) : a - 0 = a := by simp [sub_eq_add_neg]

@[simp]
theorem zero_sub (a : ZFInt) : 0 - a = -a := by simp [sub_eq_add_neg]

theorem sub_eq_zero_of_eq {a b : ZFInt} (h : a = b) : a - b = 0 := by rw [h, sub_self]

theorem eq_of_sub_eq_zero {a b : ZFInt} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [sub_eq_add_neg, neg_add_cancel_right] at this

theorem sub_eq_zero {a b : ZFInt} : a - b = 0 ↔ a = b := ⟨eq_of_sub_eq_zero, sub_eq_zero_of_eq⟩

theorem sub_sub (a b c : ZFInt) : a - b - c = a - (b + c) := by
  simp [sub_eq_add_neg, add_assoc]

theorem neg_sub (a b : ZFInt) : -(a - b) = b - a := by
  simp [sub_eq_add_neg, add_comm]

theorem sub_sub_self (a b : ZFInt) : a - (a - b) = b := by
  simp [sub_eq_add_neg, add_assoc, add_right_neg]

@[simp]
theorem sub_neg (a b : ZFInt) : a - -b = a + b := by simp [sub_eq_add_neg]

@[simp]
theorem sub_add_cancel (a b : ZFInt) : a - b + b = a := neg_add_cancel_right a b

@[simp]
theorem add_sub_cancel (a b : ZFInt) : a + b - b = a := add_neg_cancel_right a b

theorem add_sub_assoc (a b c : ZFInt) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

theorem sub_left_cancel (a b c : ZFInt) : a - c = b - c → a = b := by
  intro h
  rwa [← sub_eq_zero, sub_sub, sub_eq_zero, ← add_sub_assoc, add_comm, add_sub_cancel] at h

theorem sub_right_cancel (a b c : ZFInt) : c - a = c - b → a = b := by
  rw [← neg_sub a, ← neg_sub b, neg_inj]
  apply sub_left_cancel

theorem add_eq_sub_iff {a b c : ZFInt} : a + b = c ↔ a = c - b where
  mp := fun h => by rw [← h, add_sub_cancel]
  mpr := fun h => by rw [h, sub_add_cancel]

private abbrev nsmul : ℕ → ZFInt → ZFInt
  | 0, _ => 0
  | n+1, m => m + nsmul n m

private abbrev zsmul (n : ℤ) (x : ZFInt) : ZFInt :=
  match n with
  | .ofNat n => nsmul n x
  | .negSucc n => -nsmul (n+1) x

instance : Std.Associative (α := ZFNat) (· + ·) := ⟨(ZFNat.add_assoc · · · |>.symm)⟩
instance : Std.Commutative (α := ZFNat) (· + ·) := ⟨ZFNat.add_comm⟩

instance : Std.Associative (α := ZFNat) (· * ·) := ⟨ZFNat.mul_assoc⟩
instance : Std.Commutative (α := ZFNat) (· * ·) := ⟨ZFNat.mul_comm⟩

private theorem mul_wf {a b c d s t u v : ZFNat}
  (h₁ : ZFSet.zrel (a, b) (s,t)) (h₂ : ZFSet.zrel (c, d) (u, v)) :
  ZFSet.zrel (a * c + b * d, a * d + b * c) (s * u + t * v, s * v + t * u) := by
  dsimp [ZFSet.zrel] at *

  suffices h₃ : t * c + a * c + b * d + s * v + t * u = a * d + b * c + s * u + t * v + t * c by
    simp_rw [ZFNat.add_comm _ (t*c), ← ZFNat.add_assoc (t*c)] at h₃
    apply ZFNat.add_left_cancel.mp at h₃
    simp_rw [ZFNat.add_assoc, h₃]

  conv in t*c + a*c => rw [← right_distrib, ZFNat.add_comm, h₁, right_distrib]
  conv in _ + t*v + t*c => rw [← ZFNat.add_assoc, ← left_distrib, ZFNat.add_comm v c, h₂,
    left_distrib, ZFNat.add_assoc]

  apply ZFNat.add_right_cancel.mpr

  conv_rhs =>
    rw [ZFNat.add_comm, ZFNat.add_assoc, ZFNat.add_assoc, ← right_distrib, ZFNat.add_comm t a, h₁,
      right_distrib]
    rw [ZFNat.add_comm (b * d + s * d), ZFNat.add_assoc, ← ZFNat.add_assoc,  ← left_distrib s, ← h₂,
      left_distrib]

  ac_rfl

abbrev mul (n m : ZFInt) : ZFInt :=
  Quotient.liftOn₂ n m
    (fun ⟨a, b⟩ ⟨c, d⟩ => mk (a * c + b * d, a * d + b * c)) fun _ _ _ _ => (sound <| mul_wf · ·)

instance : Mul ZFInt := ⟨ZFInt.mul⟩
theorem mul_eq (n m : ZFNat × ZFNat) :
  mk n * mk m = mk (n.1 * m.1 + n.2 * m.2, n.1 * m.2 + n.2 * m.1) := rfl

theorem mul_comm (n m : ZFInt) : n * m = m * n := by
  induction n using Quotient.ind
  induction m using Quotient.ind
  apply sound
  rw [ZFSet.zrel]
  ac_rfl

theorem left_distrib (a b c : ZFInt) : a * (b + c) = a * b + a * c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  rename_i a b c
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  let ⟨c₁, c₂⟩ := c
  apply sound
  simp_rw [ZFNat.left_distrib, ZFSet.zrel]
  ac_rfl

theorem right_distrib (a b c : ZFInt) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm b c]

@[simp]
theorem zero_mul (a : ZFInt) : 0 * a = 0 := by
  induction a using Quotient.ind
  apply sound
  simp_rw [ZFNat.zero_mul]

@[simp]
theorem mul_zero (a : ZFInt) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_assoc (a b c : ZFInt) : a * b * c = a * (b * c) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  apply sound
  simp_rw [ZFSet.zrel, ZFNat.left_distrib, ZFNat.right_distrib]
  ac_rfl

@[simp]
theorem one_mul (a : ZFInt) : 1 * a = a := by
  induction a using Quotient.ind
  apply sound
  simp_rw [ZFNat.one_mul, ZFNat.zero_mul, ZFNat.add_zero]
  apply ZFSet.zrel_eq.refl

@[simp]
theorem mul_one (a : ZFInt) : a * 1 = a := by
  rw [mul_comm, one_mul]

instance : CommRing ZFInt where
  zero := 0
  one := 1
  add := add
  add_assoc _ _ _ := by rw [add_assoc]
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := ZFSet.ZFInt.nsmul
  nsmul_zero _ := rfl
  nsmul_succ _ _ := add_comm _ _
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one
  zsmul := ZFSet.ZFInt.zsmul
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := add_comm _ _
  zsmul_neg' _ _ := rfl
  neg_add_cancel _ := add_left_neg

section Inequalities

instance int_lt : LT ZFInt where
  lt x y := Quotient.liftOn₂ x y
    (fun ⟨a, b⟩ ⟨c, d⟩ => a + d < b + c) fun ⟨a, b⟩ ⟨c, d⟩ ⟨s, t⟩ ⟨u, v⟩ h₁ h₂ => by
      replace h₁ : a + t = b + s := h₁
      replace h₂ : c + v = d + u := h₂
      simp only [eq_iff_iff]
      apply Iff.intro
      · intro lt
        rw [← ZFNat.add_lt_add_iff_right (k := t)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc,
          ZFNat.add_comm t, h₁, ZFNat.add_comm b, ZFNat.add_assoc]
        conv_rhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm]
        rw [ZFNat.add_lt_add_iff_right, ← ZFNat.add_lt_add_iff_right (k := u)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc,
          ZFNat.add_comm u, ← h₂, ZFNat.add_assoc, ZFNat.add_comm, ZFNat.add_assoc]
        conv_rhs at lt => rw [ZFNat.add_comm, ZFNat.add_comm c, ZFNat.add_assoc]
        rwa [ZFNat.add_lt_add_iff_right, ZFNat.add_comm, ZFNat.add_comm u] at lt
      · intro lt
        rw [← ZFNat.add_lt_add_iff_right (k := b)] at lt
        conv_lhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm, ← ZFNat.add_assoc, ← h₁,
          ZFNat.add_assoc]
        conv_rhs at lt => rw [← ZFNat.add_assoc, ZFNat.add_comm]
        rw [ZFNat.add_lt_add_iff_right, ← ZFNat.add_lt_add_iff_right (k := c)] at lt
        conv_lhs at lt => rw [ZFNat.add_comm, ZFNat.add_assoc, h₂, ZFNat.add_comm, ZFNat.add_assoc]
        conv_rhs at lt => rw [ZFNat.add_comm, ZFNat.add_comm u, ZFNat.add_assoc]
        rwa [ZFNat.add_lt_add_iff_right, ZFNat.add_comm c] at lt

instance int_le : LE ZFInt where
  le x y := x < y ∨ x = y

theorem lt_succ {n : ZFInt} : n < n + 1 := by
  induction' n using Quotient.ind with n
  obtain ⟨n, m⟩ := n
  rw [ZFInt.mk_eq, ZFInt.one_eq, ZFInt.add_eq]
  dsimp
  rw [ZFNat.add_zero]
  change n+m < m+(n+1)
  rw [ZFNat.add_comm, ZFNat.add_lt_add_iff_left, ZFNat.add_one_eq_succ]
  exact ZFNat.lt_succ

theorem lt_trans {a b c : ZFInt} : a < b → b < c → a < c := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  induction' c using Quotient.ind with c
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  let ⟨c₁, c₂⟩ := c
  intros h₁ h₂
  let this := ZFNat.add_lt_trans h₁ h₂
  conv at this =>
    conv => lhs; rw [← ZFNat.add_assoc, ZFNat.add_comm b₂, ZFNat.add_comm b₁, ZFNat.add_assoc,
      ZFNat.add_assoc]
    conv => rhs; rw [← ZFNat.add_assoc, ZFNat.add_comm b₁, ZFNat.add_comm b₂, ← ZFNat.add_assoc,
      ZFNat.add_comm b₂, ZFNat.add_assoc, ZFNat.add_assoc]
    rw [ZFNat.add_lt_add_iff_right (k := b₂), ZFNat.add_lt_add_iff_right (k := b₁)]
  assumption

theorem lt_irrefl {a : ZFInt} : ¬ a < a := by
  induction' a using Quotient.ind with a
  let ⟨a₁, a₂⟩ := a
  intro h
  replace h : a₁ + a₂ < a₂ + a₁ := h
  rw [ZFNat.add_comm] at h
  nomatch ZFNat.lt_irrefl h

theorem lt_zero_iff {n m : ZFNat} : m < n ↔ 0 < ZFInt.mk (n,m) := by
  constructor
  · intro h
    induction n using ZFNat.induction generalizing m with
    | zero =>
      rw [ZFInt.zero_eq]
      change 0 + m < 0 + 0
      exact ZFNat.add_lt_add_left h 0
    | succ n ih =>
      rw [ZFInt.zero_eq]
      change 0 + m < 0 + n.succ
      exact ZFNat.add_lt_add_left h 0
  · intro h
    rw [ZFInt.zero_eq] at h
    change 0 + m < 0 + n at h
    exact ZFNat.add_lt_add_iff_left.mp h

theorem neg_one_lt_zero : (-1 : ZFInt) < 0 := add_left_neg ▸ lt_succ (n := (-1))
theorem zero_lt_one : (0 : ZFInt) < 1 := ZFInt.zero_add (x:=1) ▸ lt_succ

theorem le_trans {a b c : ZFInt} : a ≤ b → b ≤ c → a ≤ c := by
  intro h₁ h₂
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · left
      exact lt_trans h₁ h₂
    · left; assumption
  · assumption

theorem le_antisymm {a b : ZFInt} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂
  rcases h₁ with h₁ | rfl
  · rcases h₂ with h₂ | rfl
    · nomatch lt_irrefl <| lt_trans h₁ h₂
    · rfl
  · rfl

theorem le_total {a b : ZFInt} : a ≤ b ∨ b ≤ a := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  let ⟨a₁, a₂⟩ := a
  let ⟨b₁, b₂⟩ := b
  rcases @ZFNat.le_total (a₁ + b₂) (a₂ + b₁) with (_ | _) | (h | h)
  · left; left; assumption
  · left; right; apply sound; assumption
  · right; left; rw [ZFNat.add_comm a₂, ZFNat.add_comm a₁] at h; assumption
  · right; right; apply sound; rw [ZFNat.add_comm a₂, ZFNat.add_comm a₁] at h; assumption

theorem lt_iff_le_not_le {x y : ZFInt} : x < y ↔ x ≤ y ∧ ¬y ≤ x := by
  apply Iff.intro
  · intro
    apply And.intro
    · left
      assumption
    · rintro (_ | rfl)
      · nomatch lt_irrefl (lt_trans ‹_› ‹_›)
      · nomatch lt_irrefl ‹_›
  · rintro ⟨h | rfl, h'⟩
    · assumption
    · simp only [int_le, or_true] at h'
      contradiction

theorem lt_neg_iff {a b : ZFInt} : a < b ↔ -b < -a := by
  constructor <;>
  (
    intro le
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    let ⟨a₁, a₂⟩ := a
    let ⟨b₁, b₂⟩ := b
    rw [ZFInt.mk_eq, ZFInt.mk_eq] at le ⊢
  )
  · change a₁ + b₂ < a₂ + b₁ at le
    change b₂ + a₁ < b₁ + a₂
    rwa [ZFNat.add_comm b₂, ZFNat.add_comm b₁]
  · change b₂ + a₁ < b₁ + a₂ at le
    change a₁ + b₂ < a₂ + b₁
    rwa [ZFNat.add_comm a₂, ZFNat.add_comm a₁]

theorem le_neg_iff {a b : ZFInt} : a ≤ b ↔ -b ≤ -a := by
  constructor <;>
  (
    intro le
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    let ⟨a₁, a₂⟩ := a
    let ⟨b₁, b₂⟩ := b
    rw [ZFInt.mk_eq, ZFInt.mk_eq] at le ⊢
  )
  · rcases le with le | le
    · left
      exact lt_neg_iff.mp le
    · rw [eq, ZFSet.zrel] at le
      right
      rwa [neg_eq, neg_eq, eq, ZFSet.zrel, ZFNat.add_comm b₂, ZFNat.add_comm b₁]
  · rcases le with le | le
    · left
      exact lt_neg_iff.mpr le
    · rw [neg_eq, neg_eq, eq, ZFSet.zrel] at le
      right
      rwa [eq, ZFSet.zrel, ZFNat.add_comm a₁, ZFNat.add_comm a₂]

instance : LinearOrder ZFInt where
  le := int_le.le
  le_refl x := Or.inr rfl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm
  le_total _ _ := le_total
  decidableLE := fun _ _ => Classical.propDecidable ((· ≤ ·) _ _)
  lt_iff_le_not_le _ _ := lt_iff_le_not_le

instance : AddCommGroup ZFInt where
  add := add
  add_assoc := (add_assoc · · · |>.symm)
  zero := zero
  zero_add := @zero_add
  add_zero := @add_zero
  nsmul := nsmul
  nsmul_succ x y := add_comm y (nsmul x y)
  neg := ZFInt.neg
  zsmul := zsmul
  zsmul_succ' x y := add_comm y (nsmul x y)
  neg_add_cancel := @add_left_neg
  add_comm := @add_comm

instance : PartialOrder ZFInt where
  le := int_le.le
  le_refl := le_refl
  le_trans := @le_trans
  lt_iff_le_not_le := @lt_iff_le_not_le
  le_antisymm := @le_antisymm

instance : IsOrderedAddMonoid ZFInt where
  add_le_add_left x y h z := by
    induction' x using Quotient.ind with x
    induction' y using Quotient.ind with y
    induction' z using Quotient.ind with z
    let ⟨x₁, x₂⟩ := x
    let ⟨y₁, y₂⟩ := y
    let ⟨z₁, z₂⟩ := z
    simp_rw [mk_eq] at h ⊢
    rcases h with h | h
    · change x₁ + y₂ < x₂ + y₁ at h
      simp_rw [add_eq]
      left
      change z₁ + x₁ + (z₂ + y₂) < z₂ + x₂ + (z₁ + y₁)
      conv_lhs => rw [← ZFNat.add_assoc, ZFNat.add_comm z₁, ZFNat.add_comm z₂, ZFNat.add_assoc,
        ←ZFNat.add_assoc, ZFNat.add_comm z₂]
      conv_rhs => rw [ZFNat.add_comm z₂, ←ZFNat.add_assoc, ZFNat.add_comm z₂, ZFNat.add_comm z₁,
        ZFNat.add_assoc, ZFNat.add_assoc, ←ZFNat.add_assoc]
      exact ZFNat.add_lt_add_iff_right.mpr h
    · rw [eq, ZFSet.zrel] at h
      dsimp at h
      right
      rw [add_eq, add_eq, eq, ZFSet.zrel]
      dsimp
      conv_lhs => rw [← ZFNat.add_assoc, ZFNat.add_comm z₁, ZFNat.add_comm z₂, ZFNat.add_assoc,
        ←ZFNat.add_assoc, ZFNat.add_comm z₂, h]
      conv_rhs => rw [ZFNat.add_comm z₂, ←ZFNat.add_assoc, ZFNat.add_comm z₂, ZFNat.add_comm z₁,
        ZFNat.add_assoc, ZFNat.add_assoc, ←ZFNat.add_assoc]

end Inequalities

section Induction

lemma ind {P : ZFNat → ZFNat → Prop} (n m : ZFNat) (zero : P 0 0)
  (succ_l : ∀ n m, P n m → P (n+1) m) (succ_r : ∀ n m, P n m → P n (m+1)) : P n m := by
  induction n using ZFNat.induction with
  | zero =>
    induction m using ZFNat.induction with
    | zero => exact zero
    | succ m ih =>
      rw [←ZFNat.add_one_eq_succ]
      exact succ_r 0 m ih
  | succ n ih =>
    rw [←ZFNat.add_one_eq_succ]
    exact succ_l n m ih

lemma induction_pos {P : ZFInt → Prop} (n : ZFInt) (n_pos : 0 ≤ n)
  (zero : P 0) (succ : ∀ k, P k → P (k + 1)) : P n := by
  induction' n using Quotient.ind with n
  obtain ⟨n, m⟩ := n
  rcases ZFNat.instIsStrictTotalOrderLt.trichotomous n m with h | rfl | h
  · exfalso
    rw [ZFInt.lt_zero_iff] at h
    rcases n_pos with n_pos | eq
    · rw [ZFInt.zero_eq] at h n_pos
      change 0 + n < 0 + m at h
      change 0 + m < 0 + n at n_pos
      rw [ZFNat.zero_add, ZFNat.zero_add] at h n_pos
      nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans h n_pos
    · rw [ZFInt.mk_eq] at eq
      rcases ZFInt.mk_eq_zero_iff.mp eq.symm with rfl
      rw [eq] at h
      change n + n < n + n at h
      nomatch ZFNat.lt_irrefl h
  · rcases n_pos with n_pos | eq
    · rw [ZFInt.zero_eq] at n_pos
      change 0 + n < 0 + n at n_pos
      nomatch ZFNat.lt_irrefl n_pos
    · rwa [←eq]
  · let k := n - m
    have : n = k + m := by
      apply ZFNat.eq_add_of_sub_eq _ rfl
      left
      exact h
    rw [this]
    induction k using ZFNat.induction with
    | zero =>
      rw [ZFInt.zero_eq] at zero
      rwa [ZFNat.zero_add, ZFInt.mk_eq, ZFInt.eq (x := (m,m)) (y := (0,0)) |>.mpr rfl]
    | succ k ih =>
      rw [ZFNat.add_comm] at ih
      rw [←ZFNat.add_one_eq_succ, ZFNat.add_comm, ZFNat.add_assoc]
      specialize succ <| ZFInt.mk (m+k,m)
      rw [ZFInt.one_eq, ZFInt.add_eq] at succ
      dsimp at succ
      rw [ZFNat.add_zero, ←ZFInt.mk_eq] at succ
      exact succ ih

lemma induction_neg {P : ZFInt → Prop} (n : ZFInt) (n_neg : n ≤ 0)
  (zero : P 0) (succ : ∀ k, P k → P (k - 1)) : P n := by
  have  : 0 ≤ -n := by rwa [← ZFInt.neg_zero, ZFInt.le_neg_iff, neg_neg n, neg_neg 0]
  letI P' n := P (-n)
  suffices P' (-n) by
    unfold P' at this
    rwa [ZFInt.neg_neg] at this
  have succ' : ∀ k, P' k → P' (k + 1) := by
    intro k hk
    unfold P' at hk ⊢
    rw [ZFInt.neg_add]
    exact succ _ hk
  exact induction_pos (P := P') (-n) this zero succ'

@[induction_eliminator]
theorem induction {P : ZFInt → Prop} (n : ZFInt)
  (zero : P 0) (pos : ∀ k, P k → P (k + 1)) (neg : ∀ k, P k → P (k - 1)) : P n := by
  rcases instIsStrictTotalOrderLt.trichotomous n 0 with h | rfl | h
  · exact induction_neg n (Or.inl h) zero neg
  · exact zero
  · exact induction_pos n (Or.inl h) zero pos

@[cases_eliminator]
theorem sign_cases {P : ZFInt → Prop} (n : ZFInt)
  (zero : P 0) (neg : n < 0 → P n) (pos : 0 < n → P n) : P n := by
  induction n with
  | zero => exact zero
  | pos k ih =>
    rcases lt_trichotomy (k+1) 0 with h | h | h
    · exact neg h
    · rwa [h]
    · exact pos h
  | neg k ih =>
    rcases lt_trichotomy (k-1) 0 with h | h | h
    · exact neg h
    · rwa [h]
    · exact pos h

@[cases_eliminator]
theorem cases {P : ZFInt → Prop} (n : ZFInt) (pos : 0 ≤ n → P n) (neg : n < 0 → P n) : P n := by
  induction n with
  | zero => exact pos (Or.inr rfl)
  | pos n ih =>
    generalize h : n + 1 = m at *
    cases m using sign_cases with
    | zero => exact pos (Or.inr rfl)
    | neg h => exact neg h
    | pos h => exact pos (Or.inl h)
  | neg n ih =>
    generalize h : n - 1 = m at *
    cases m using sign_cases with
    | zero => exact pos (Or.inr rfl)
    | neg h => exact neg h
    | pos h => exact pos (Or.inl h)

end Induction

theorem add_eq_add_sub_eq_sub {a b c d : ZFNat} : a + b = c + d → a - c = d - b := by
  intro h
  have : a = c + d - b := ZFNat.sub_eq_of_eq_add h.symm |>.symm
  subst this
  rw [←ZFNat.sub_add_distrib, ZFNat.add_comm b c, ZFNat.add_sub_add_left c d b]

theorem le_of_lt_succ (n m : ZFInt) : n < m + 1 → n ≤ m := by
  intro h
  induction' n using Quotient.ind with n
  induction' m using Quotient.ind with m
  obtain ⟨a, b⟩ := n
  obtain ⟨c, d⟩ := m
  simp_rw [mk_eq] at h ⊢
  rw [one_eq, add_eq, ZFNat.add_zero] at h
  change a + d < b + (c + 1) at h
  suffices a + d ≤ b + c by
    rcases this with h | h
    · left; exact h
    · right; exact sound h
  rwa [ZFNat.add_assoc, ZFNat.add_one_eq_succ, ←ZFNat.lt_le_iff] at h

theorem lt_succ_of_le (n m : ZFInt) : n ≤ m → n < m + 1 := by
  rintro (h | rfl)
  · trans n+1
    · exact lt_succ
    · exact (add_lt_add_iff_right 1).mpr h
  · exact lt_succ

theorem lt_succ_of_le_iff (n m : ZFInt) : n ≤ m ↔ n < m + 1 where
  mp := lt_succ_of_le n m
  mpr := le_of_lt_succ n m

theorem int_le.dest {n m : ZFInt} : n ≤ m → ∃ k, 0 ≤ k ∧ n + k = m := by
  intro h
  exists m - n
  and_intros
  · exact sub_nonneg_of_le h
  · exact _root_.add_sub_cancel n m

theorem mul_pos_pos_pos (a b : ZFInt) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  obtain ⟨c, d⟩ := b
  obtain ⟨a, b⟩ := a
  simp_rw [mk_eq, zero_eq] at ha hb ⊢
  rw [mul_eq]
  change 0 + d < 0 + c at hb
  change 0 + b < 0 + a at ha
  change 0 + (a * d + b * c) < 0 + (a * c + b * d)
  simp_rw [ZFNat.zero_add] at ha hb ⊢
  rw [ZFNat.sub_add_cancel (Or.inl hb) |>.symm, ZFNat.left_distrib, ZFNat.left_distrib,
    ZFNat.add_comm _ (b*d), ZFNat.add_assoc, ←ZFNat.right_distrib, ←ZFNat.add_assoc,
    ←ZFNat.right_distrib, ZFNat.add_comm, ZFNat.add_lt_add_iff_right, ZFNat.mul_comm b,
    ZFNat.mul_comm a]
  apply ZFNat.mul_lt_mono
  · exact ZFNat.pos_of_ne_zero (ZFNat.sub_ne_zero_of_lt hb).symm
  · exact ha

theorem neg_one_mul (a : ZFInt) : (-1 : ZFInt) * a = -a := by
  induction' a using Quotient.ind with a
  obtain ⟨a, b⟩ := a
  rw [mk_eq, one_eq, neg_eq, mul_eq, neg_eq]
  dsimp
  rw [ZFNat.zero_mul, ZFNat.zero_mul, ZFNat.one_mul, ZFNat.one_mul, ZFNat.zero_add, ZFNat.zero_add]

theorem neg_one_mul_neg_one : (-1 : ZFInt) * (-1) = 1 := by
  rw [one_eq, neg_eq, mul_eq, ZFNat.mul_zero, ZFNat.zero_mul, ZFNat.zero_add, ZFNat.zero_add,
    ZFNat.one_mul, ZFNat.one_mul]

theorem mul_neg_neg (a b : ZFInt) : a * b = -a * -b := by
  rw [←one_mul (a*b), ←neg_one_mul_neg_one, ←mul_assoc, mul_comm, mul_assoc, mul_comm, mul_assoc,
    mul_comm (-1), mul_assoc, mul_comm b, neg_one_mul, neg_one_mul]

theorem neg_mul_distrib (a b : ZFInt) : -(a * b) = -a * b := neg_mul_eq_neg_mul a b

theorem mul_neg_neg_pos (a b : ZFInt) (ha : a < 0) (hb : b < 0) : 0 < a * b := by
  rw [mul_neg_neg]
  exact mul_pos_pos_pos _ _ (Left.neg_pos_iff.mpr ha) (Left.neg_pos_iff.mpr hb)

theorem neg_flip_lt (a : ZFInt) : a < 0 ↔ 0 < -a := Iff.symm Left.neg_pos_iff
theorem neg_flip_le (a : ZFInt) : a ≤ 0 ↔ 0 ≤ -a := Iff.symm neg_nonneg

theorem mul_neg_pos_neg (a b : ZFInt) (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  rw [neg_flip_lt, neg_mul_eq_neg_mul]
  exact mul_pos_pos_pos _ _ ((neg_flip_lt a).mp ha) hb

theorem mul_pos_neg_neg (a b : ZFInt) (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  rw [mul_comm, neg_flip_lt, neg_mul_eq_neg_mul]
  exact mul_pos_pos_pos _ _ ((neg_flip_lt b).mp hb) ha

theorem mul_nonneg_nonneg_nonneg (a b : ZFInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · left
    exact mul_pos_pos_pos a b ha hb
  · right
    rw [mul_zero]
  · right
    rw [zero_mul]
  · right
    rw [zero_mul]

theorem mul_nonpos_nonneg_nonpos (a b : ZFInt) (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  rw [neg_flip_le, neg_mul_eq_neg_mul]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr ha) hb

theorem mul_nonneg_nonpos_nonpos (a b : ZFInt) (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  rw [mul_comm, neg_flip_le, neg_mul_eq_neg_mul]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr hb) ha

theorem mul_nonpos_nonpos_nonneg (a b : ZFInt) (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  rw [mul_neg_neg]
  exact mul_nonneg_nonneg_nonneg _ _ (neg_nonneg.mpr ha) (neg_nonneg.mpr hb)

theorem mul_le_mul_left {n m : ZFInt} (k : ZFInt) (h : n ≤ m) (h' : 0 ≤ k) : k * n ≤ k * m := by
  obtain ⟨l, pos, hl⟩ := int_le.dest h
  have : k * n + k * l = k * m := by rw [←hl, left_distrib]
  rw [←this]
  apply le_add_of_nonneg_right
  exact mul_nonneg_nonneg_nonneg k l h' pos

theorem mul_lt_mul_of_pos_left {n m k : ZFInt} (h : n < m) (hk : k > 0) : k * n < k * m := by
  apply lt_of_lt_of_le (b := k*n+k)
  · exact lt_add_of_pos_right _ hk
  · conv =>
      enter [1,2]
      rw [←mul_one k]
    rw [←left_distrib]
    apply mul_le_mul_left k
    · exact (lt_succ_of_le_iff (n + 1) m).mpr <| (add_lt_add_iff_right 1).mpr h
    · exact le_of_lt hk

theorem pos_of_mul_pos {a b : ZFInt} (h : 0 < a * b) (ha : 0 < a) : 0 < b := by
  classical
  by_contra hb
  rw [not_lt_iff_eq_or_lt] at hb
  rcases hb with rfl | hb
  · rw [mul_zero] at h
    exact lt_irrefl h
  · rcases instIsStrictTotalOrderLt.trichotomous a b with h' | rfl | h'
    · nomatch lt_irrefl <| lt_trans (lt_trans ha h') hb
    · nomatch lt_irrefl <| lt_trans ha hb
    · nomatch lt_irrefl <| lt_trans h <| mul_pos_neg_neg a b ha hb

theorem mul_lt_mul_of_pos_right {n m k : ZFInt} (h : n < m) (hk : k > 0) : n * k < m * k := by
  rw [mul_comm n, mul_comm m]
  exact mul_lt_mul_of_pos_left h hk

theorem mul_pos_iff {a b : ZFInt} : 0 < a * b ↔ (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
  constructor
  · intro h
    cases a with
    | pos pos =>
      rcases pos with pos | rfl
      · left
        and_intros
        · exact pos
        · exact pos_of_mul_pos h pos
      · rw [zero_mul] at h
        nomatch lt_irrefl h
    | neg neg =>
      right
      and_intros
      · exact neg
      · rw [mul_neg_neg] at h
        rw [neg_flip_lt] at neg
        have := pos_of_mul_pos h neg
        rwa [←neg_flip_lt] at this
  · rintro (⟨l, r⟩ | ⟨l, r⟩)
    · exact mul_pos_pos_pos a b l r
    · exact mul_neg_neg_pos a b l r

theorem eq_le_iff {a b : ZFInt} : a = b ↔ a ≤ b ∧ b ≤ a := by
  constructor
  · rintro rfl
    exact ⟨le_refl _, le_refl _⟩
  · rintro ⟨h₁, h₂⟩
    rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | h₂
    · nomatch lt_irrefl <| lt_trans h₁ h₂
    · exact h₂.symm
    · rfl
    · rfl

theorem mul_eq_zero_iff {a b : ZFInt} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    induction' a using Quotient.ind with a
    induction' b using Quotient.ind with b
    let ⟨a₁, a₂⟩ := a
    let ⟨b₁, b₂⟩ := b
    simp_rw [mk_eq, mul_eq, zero_eq, eq, ZFSet.zrel, ZFNat.add_zero] at h ⊢
    rcases ZFNat.instIsStrictTotalOrderLt.trichotomous b₁ b₂ with h' | rfl | h'
    · have := ZFNat.add_eq_add_sub_eq_sub h.symm
      rw [←ZFNat.left_distrib_mul_sub, ←ZFNat.left_distrib_mul_sub] at this
      have b₁b₂_ne_0 : b₂ - b₁ ≠ 0 := by
        intro contr
        rw [ZFNat.sub_eq_zero_imp_le] at contr
        rcases contr with contr | rfl
        · nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans contr h'
        · nomatch ZFNat.lt_irrefl h'
      left
      exact ZFNat.mul_right_cancel_iff b₁b₂_ne_0 |>.mp this
    · right; rfl
    · have := ZFNat.add_eq_add_sub_eq_sub h
      rw [←ZFNat.left_distrib_mul_sub, ←ZFNat.left_distrib_mul_sub] at this
      have b₁b₂_ne_0 : b₁ - b₂ ≠ 0 := by
        intro contr
        rw [ZFNat.sub_eq_zero_imp_le] at contr
        rcases contr with contr | rfl
        · nomatch ZFNat.lt_irrefl <| ZFNat.lt_trans contr h'
        · nomatch ZFNat.lt_irrefl h'
      left
      exact ZFNat.mul_right_cancel_iff b₁b₂_ne_0 |>.mp this
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]

theorem mul_eq_zero_of_ne_zero {a b : ZFInt} : a * b = 0 → a ≠ 0 → b = 0 := by
  intro h h'
  rw [mul_eq_zero_iff] at h
  exact Or.resolve_left h h'

theorem mul_left_cancel_iff {a b n : ZFInt} (h : n ≠ 0) : n * a = n * b ↔ a = b := by
  constructor
  · intro eq
    have : n*a - n*b = 0 := sub_eq_zero_of_eq eq
    rw [ZFInt.sub_eq_add_neg, mul_comm n b, neg_mul_distrib, mul_comm _ n, ←left_distrib,
      mul_eq_zero_iff] at this
    rcases this with rfl | this
    · nomatch h
    · exact eq_of_sub_eq_zero this
  · exact fun h => h ▸ rfl

theorem mul_right_cancel_iff {a b n : ZFInt} (h : n ≠ 0) : a * n = b * n ↔ a = b := by
  rw [mul_comm a n, mul_comm b n]
  exact mul_left_cancel_iff h

instance : CommRing ZFInt where
  add := add
  add_assoc := (add_assoc · · · |>.symm)
  add_comm := add_comm
  zero_add _ := zero_add
  add_zero _ := add_zero
  nsmul := nsmul
  nsmul_succ x y := add_comm y (nsmul x y)
  left_distrib := left_distrib
  right_distrib := right_distrib
  zsmul := zsmul
  zsmul_succ' x y := add_comm y (nsmul x y)
  neg_add_cancel := @add_left_neg

instance : PartialOrder ZFInt where
  le := int_le.le
  le_refl := le_refl
  le_trans := @le_trans
  le_antisymm := @le_antisymm
  lt_iff_le_not_le := @lt_iff_le_not_le

instance : IsOrderedRing ZFInt where
  add_le_add_left _ _ h z := (add_le_add_iff_left z).mpr h
  zero_le_one := Or.inl zero_lt_one
  mul_le_mul_of_nonneg_left _ _ := (mul_le_mul_left · · ·)
  mul_le_mul_of_nonneg_right a b c h h' := by
    rw [mul_comm a, mul_comm b]
    exact mul_le_mul_left c h h'

end ZFInt

abbrev Int := Nat.prod {∅} ∪ ZFSet.prod {∅} Nat

def ofInt : ℤ → ZFSet
  | .ofNat n => ZFSet.pair ∅ (n : ZFNat)
  | .negSucc n => ZFSet.pair (n+1 : ZFNat) ∅

def toZFInt : ℤ → ZFInt
  | .ofNat n => ZFInt.mk (0, ↑n)
  | .negSucc n => ZFInt.mk (↑n+1, 0)

example : ofInt 0 = {{∅}} := by
  dsimp [ofInt, pair]
  ext x
  simp
  intro
  subst x
  ext x
  simp
  exact id

section -- could be another definition
private def ofInt' : (n : ℤ) → PSet
  | .ofNat 0 => {{∅}}
  | .ofNat (n+1) => {{∅}, {∅, .ofNat n}} -- (0, n)
  | .negSucc n => {{.ofNat (n+1)}, {∅, .ofNat (n+1)}} -- (n, 0)

def PInt' : PSet := ⟨ULift ℤ, fun n => ofInt' n.down⟩
def Int' : ZFSet := ZFSet.mk PInt'
end

theorem ZFNat.mem_lift_lift_Nat (n : ℕ) : ↑(↑n : ZFNat) ∈ Nat := by
  induction n with
  | zero => simp only [Nat.cast_zero, ZFNat.nat_zero_eq, ZFNat.zero_in_Nat]
  | succ n ih =>
    simp only [Nat.cast_succ, ZFNat.add_one_eq_succ, ZFNat.succ]
    exact ZFNat.succ_mem_Nat' ih

theorem mem_ofInt_Int (n : ℤ) : ofInt n ∈ Int := by
  induction n using Int.recOn with
  | ofNat n =>
    rw [Int, mem_union, ofInt]
    right
    rw [pair_mem_prod]
    exact ⟨singleton_subset_mem_iff.mp fun _ => id, ZFNat.mem_lift_lift_Nat n⟩
  | negSucc n =>
    rw [Int, mem_union, ofInt]
    left
    rw [pair_mem_prod]
    exact ⟨ZFNat.mem_lift_lift_Nat (n+1), singleton_subset_mem_iff.mp fun _ => id⟩

theorem sub_ofInt_singleton_Int (n : ℤ) : {ofInt n} ⊆ Int := by
  intro
  rw [mem_singleton]
  rintro rfl
  exact mem_ofInt_Int n

lemma Int.nonempty : ZFSet.Int ≠ ∅ := by
  intro h
  rw [ZFSet.ext_iff] at h
  simp only [ZFSet.not_mem_empty, iff_false] at h
  nomatch h (ZFSet.ofInt 0) (ZFSet.mem_ofInt_Int 0)

def π₁ (x : ZFSet) : ZFSet := ⋃₀ (⋂₀ x)

open Classical in -- couldn't find another way
def π₂ (x : ZFSet) : ZFSet :=
  let δ : ZFSet := (⋃₀ x \ ⋂₀ x)
  if δ = ∅ then π₁ x else ⋃₀ δ

@[simp] theorem π₁_pair (x y : ZFSet) : π₁ (x.pair y) = x := by
  unfold π₁ pair
  ext
  rw [sInter_pair, mem_sUnion]
  constructor
  · rintro ⟨w, l, r⟩
    rw [mem_inter, mem_singleton, mem_pair] at l
    rw [l.1] at r
    assumption
  · intro h
    exists x
    rw [mem_inter, mem_singleton, mem_pair]
    exact ⟨⟨rfl, .inl rfl⟩, h⟩

@[simp] theorem pair_inter {x y : ZFSet} : {x} ∩ {x, y} = ({x} : ZFSet) := by
    ext
    rw [mem_inter, mem_singleton, mem_pair]
    constructor
    · rintro ⟨rfl, _ | rfl⟩ <;> rfl
    · rintro rfl
      exact ⟨rfl, .inl rfl⟩

@[simp] theorem pair_union {x y : ZFSet} : {x} ∪ {x, y} = ({x, y} : ZFSet) := by
    ext
    rw [mem_union, mem_singleton, mem_pair]
    exact or_self_left

@[simp] theorem pair_minus {x y : ZFSet} : x ≠ y → {x, y} \ {x} = ({y} : ZFSet) := by
  intro x_ne_y
  ext z
  rw [mem_diff, mem_pair, mem_singleton, mem_singleton]
  constructor
  · rintro ⟨rfl | rfl, r⟩
    · contradiction
    · rfl
  · rintro rfl
    exact ⟨.inr rfl, x_ne_y ∘ Eq.symm⟩

@[simp] theorem π₂_pair (x y : ZFSet) : π₂ (x.pair y) = y := by
  unfold π₂
  dsimp
  split_ifs with h
  · rw [π₁_pair]
    unfold pair at h
    rw [sUnion_pair, pair_union, sInter_pair, pair_inter] at h
    by_cases eq : x = y
    · assumption
    · rw [pair_minus eq, ZFSet.ext_iff] at h
      simp only [mem_singleton, not_mem_empty, iff_false, forall_eq] at h
  · unfold pair at *
    rw [sUnion_pair, pair_union, sInter_pair, pair_inter] at h ⊢
    rw [pair_minus]
    · exact sUnion_singleton
    · intro h'
      rw [h'] at h
      simp [ZFSet.ext_iff] at h

theorem mem_Int_proj_iff {x : ZFSet} (h : x ∈ Int) :
  ∃ n ∈ Nat, (x.π₁ = ∅ ∧ x.π₂ = n) ∨ (x.π₁ = n ∧ x.π₂ = ∅) := by
  simp_rw [mem_union, mem_prod] at h
  rcases h with ⟨a, ha, b, hb, x_eq⟩ | ⟨b, hb, a, ha, x_eq⟩
    <;> (simp at hb; subst x_eq; rw [π₁_pair, π₂_pair]; exists a)
  · exact ⟨ha, .inr ⟨rfl, hb⟩⟩
  · exact ⟨ha, .inl ⟨hb, rfl⟩⟩

theorem mem_Int_proj {x : ZFSet} : x ∈ Int → (x.π₁ = ∅ ∧ x.π₂ ∈ Nat) ∨ (x.π₁ ∈ Nat ∧ x.π₂ = ∅) := by
  intro h
  rcases mem_Int_proj_iff h with ⟨n, hn, ⟨l, r⟩ | ⟨l, r⟩⟩
  · left
    exact ⟨l, r ▸ hn⟩
  · right
    exact ⟨l ▸ hn, r⟩

open Classical in
private def ZFInt.outof : {x // x ∈ Int} → ZFInt := fun ⟨n, hn⟩ =>
  have := mem_Int_proj hn
  if case : n.π₁ = ∅ ∧ n.π₂ ∈ Nat then
    ZFInt.mk ⟨0, n.π₂, case.right⟩
  else
    ZFInt.mk ⟨⟨n.π₁, Or.resolve_left this case |>.left⟩, 0⟩

theorem ZFInt.outof_inj (x y : {x // x ∈ Int}) : outof x = outof y → x = y := by
  let ⟨x, hx⟩ := x
  let ⟨y, hy⟩ := y
  simp [outof]
  intro outof_eq
  split_ifs at outof_eq with h₁ h₂ h₂
    <;> (
      first
      | obtain ⟨l₁, r₁⟩ := h₁
      | obtain ⟨l₁, r₁⟩ := Or.resolve_left (mem_Int_proj hx) h₁
      first
      | obtain ⟨l₂, r₂⟩ := h₂
      | obtain ⟨l₂, r₂⟩ := Or.resolve_left (mem_Int_proj hy) h₂
    )
  · apply exact at outof_eq
    simp [ZFSet.zrel] at outof_eq
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp [ZFSet.zrel] at outof_eq
    obtain ⟨l₃, r₃⟩ := ZFNat.eq_zero_of_add_eq_zero outof_eq.symm
    injection l₃ with l₃
    injection r₃ with r₃
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ l₃ r₃ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp [ZFSet.zrel] at outof_eq
    obtain ⟨l₃, r₃⟩ := ZFNat.eq_zero_of_add_eq_zero outof_eq
    injection l₃ with l₃
    injection r₃ with r₃
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ l₃ r₃ outof_eq; subst_eqs; congr)
  · apply exact at outof_eq
    simp [ZFSet.zrel] at outof_eq
    simp_rw [mem_union, mem_prod] at hx hy
    rcases hx, hy with ⟨⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩,⟨_, _, _, _, rfl⟩|⟨_, _, _, _, rfl⟩⟩
      <;> (simp [π₁_pair, π₂_pair] at l₁ r₁ l₂ r₂ outof_eq; subst_eqs; congr)

theorem ZFNat.mem_Nat_sub_one {n : ZFNat} : (n - 1).1 ∈ Nat := by
  induction n with
  | zero => rw [ZFNat.zero_sub]; exact ZFNat.zero_in_Nat
  | succ n _ =>
    rw [ZFNat.sub_one_eq_pred, ZFNat.add_one_eq_succ, ZFNat.pred_succ]
    rcases n; simpa

theorem ZFNat.mem_Nat_sub {n m : ZFNat} : (n - m).1 ∈ Nat := by
  induction m with
  | zero => rcases n; simpa
  | succ m _ =>
    rw [ZFNat.sub_add_distrib]
    exact ZFNat.mem_Nat_sub_one

theorem mem_Int_empty_not_mem {x : ZFSet} {h : x ∈ Int} : ∅ ∉ x := by
  intro contr
  simp_rw [mem_union, mem_prod] at h
  rcases h with ⟨a, _, b, _, h⟩ | ⟨a, _, b, _, h⟩
  all_goals
    unfold pair at h
    subst h
    rw [mem_insert_iff, mem_singleton] at contr
    rcases contr with contr | contr
    all_goals
      simp only [ZFSet.ext_iff, not_mem_empty, false_iff] at contr
      specialize contr a
      simp at contr

open Classical in
def ZFInt.into (x : ZFInt) : {x // x ∈ Int} :=
  let ⟨a,b⟩ := x.out
  if a < b then
    let n := ZFSet.pair ∅ (b-a).1
    have : n ∈ Int := by
      rw [mem_union]
      right
      rw [mem_prod]
      exact ⟨∅, mem_singleton.mpr rfl, (b-a).1, ZFNat.mem_Nat_sub, rfl⟩
    ⟨n, this⟩
  else
    let n := ZFSet.pair (a-b).1 ∅
    have : n ∈ Int := by
      rw [mem_union]
      left
      rw [mem_prod]
      exact ⟨(a-b).1, ZFNat.mem_Nat_sub, ∅, mem_singleton.mpr rfl, rfl⟩
    ⟨n, this⟩

theorem ZFInt.into_inj_aux (x y : ZFInt) : into x = into y → x.out ≈ y.out := by
  dsimp [into]
  obtain ⟨a, b⟩ := Quotient.out x
  obtain ⟨c, d⟩ := Quotient.out y
  split_ifs with h₁ h₂ h₂ <;> (intro eq; simp at *)
  · apply Subtype.eq at eq
    have := ZFNat.eq_add_of_sub_eq (hle := .inl h₁) (h := eq)
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc (.inl h₂)] at this
    apply ZFNat.eq_add_of_sub_eq (h := this.symm)
    rw [ZFNat.add_comm]
    exact ZFNat.le_trans (.inl h₂) (ZFNat.le_add_right d a)
  · obtain ⟨eq₁, eq₂⟩ := eq
    replace eq₁ : 0 = c - d := Subtype.eq eq₁
    replace eq₂ : b - a = 0 := Subtype.eq eq₂
    have := ZFNat.le_antisymm (ZFNat.sub_eq_zero_imp_le.mp (eq₁.symm)) h₂
    subst this
    rw [eq₁] at eq₂
    apply ZFNat.eq_add_of_sub_eq (.inl h₁) at eq₂
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc h₂] at eq₂
    symm at eq₂
    apply ZFNat.eq_add_of_sub_eq (h := eq₂)
    exact ZFNat.le_add_left c a
  · obtain ⟨eq₁, eq₂⟩ := eq
    replace eq₁ : a - b = 0 := Subtype.eq eq₁
    replace eq₂ : 0 = d - c := Subtype.eq eq₂
    have := ZFNat.le_antisymm (ZFNat.sub_eq_zero_imp_le.mp eq₁) h₁
    subst this
    rw [eq₂] at eq₁
    apply ZFNat.eq_add_of_sub_eq h₁ at eq₁
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc (.inl h₂)] at eq₁
    symm at eq₁
    apply ZFNat.eq_add_of_sub_eq (h := eq₁)
    left
    rw [← @ZFNat.zero_add c]
    apply ZFNat.add_lt_add_of_le_of_lt
    · exact ZFNat.zero_le
    · assumption
  · apply Subtype.eq at eq
    have := ZFNat.eq_add_of_sub_eq (hle := h₁) (h := eq)
    rw [ZFNat.add_comm, ← ZFNat.add_sub_assoc h₂] at this
    apply Eq.symm ∘ ZFNat.eq_add_of_sub_eq (h := this.symm)
    exact ZFNat.le_trans h₂ (ZFNat.le_add_left c b)

theorem ZFInt.into_inj (x y : ZFInt) : into x = into y → x = y := by
  intro h
  apply ZFInt.into_inj_aux at h
  exact Quotient.out_equiv_out.mp h

theorem ZFInt.into.injective : Function.Injective into := into_inj
theorem ZFInt.outof.injective : Function.Injective outof := outof_inj

def ZFInt.EmbeddingZFIntInt : ZFInt ↪ {x // x ∈ Int} where
  toFun := into
  inj' := into.injective
def ZFInt.EmbeddingIntZFInt : {x // x ∈ Int} ↪ ZFInt where
  toFun := outof
  inj' := outof.injective

instance instEquivZFIntInt : ZFInt ≃ {x // x ∈ Int} :=
  Classical.choice (Function.Embedding.antisymm ZFInt.EmbeddingZFIntInt ZFInt.EmbeddingIntZFInt)

instance : Coe ZFInt {x // x ∈ Int} := ⟨instEquivZFIntInt.toFun⟩
instance : Coe {x // x ∈ Int} ZFInt := ⟨instEquivZFIntInt.invFun⟩

instance : LinearOrder {x // x ∈ Int} where
  le := (ZFInt.instLinearOrder.le · ·)
  le_refl := (ZFInt.instLinearOrder.le_refl ·)
  le_trans := (ZFInt.instLinearOrder.le_trans · · ·)
  le_antisymm x y h h' := by
    have := ZFInt.instLinearOrder.le_antisymm x y h h'
    rwa [Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq] at this
  le_total := (ZFInt.instLinearOrder.le_total · ·)
  decidableLE := (ZFInt.instLinearOrder.decidableLE · ·)


/-
NOTE: There is a constructive proof of the Schröder-Bernstein theorem stating
the equi-computability of sets. It is called the Myhill isomorphism and applies
to countable sets only.
-/

end Integers
end ZFSet
end
