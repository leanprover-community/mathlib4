/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module number_theory.pell_matiyasevic
! leanprover-community/mathlib commit 795b501869b9fa7aa716d5fdadd00c03f983a605
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `number_theory.dioph.lean`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`number_theory.pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/


namespace Pell

open Nat

section

variable {d : ℤ}

/-- The property of being a solution to the Pell equation, expressed
  as a property of elements of `ℤ√d`. -/
def IsPell : ℤ√d → Prop
  | ⟨x, y⟩ => x * x - d * y * y = 1
#align pell.is_pell Pell.IsPell

theorem isPell_norm : ∀ {b : ℤ√d}, IsPell b ↔ b * star b = 1
  | ⟨x, y⟩ => by simp [Zsqrtd.ext, is_pell, mul_comm] <;> ring_nf
#align pell.is_pell_norm Pell.isPell_norm

theorem isPell_iff_mem_unitary : ∀ {b : ℤ√d}, IsPell b ↔ b ∈ unitary (ℤ√d)
  | ⟨x, y⟩ => by rw [unitary.mem_iff, is_pell_norm, mul_comm (star _), and_self_iff]
#align pell.is_pell_iff_mem_unitary Pell.isPell_iff_mem_unitary

theorem isPell_mul {b c : ℤ√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c) :=
  isPell_norm.2 (by simp [mul_comm, mul_left_comm, star_mul, is_pell_norm.1 hb, is_pell_norm.1 hc])
#align pell.is_pell_mul Pell.isPell_mul

theorem isPell_star : ∀ {b : ℤ√d}, IsPell b ↔ IsPell (star b)
  | ⟨x, y⟩ => by simp [is_pell, Zsqrtd.star_mk]
#align pell.is_pell_star Pell.isPell_star

end

section

parameter {a : ℕ}(a1 : 1 < a)

include a1

private def d :=
  a * a - 1
#align pell.d pell.d

@[simp]
theorem d_pos : 0 < d :=
  tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (by decide) : 1 * 1 < a * a)
#align pell.d_pos Pell.d_pos

-- TODO(lint): Fix double namespace issue
/-- The Pell sequences, i.e. the sequence of integer solutions to `x ^ 2 - d * y ^ 2 = 1`, where
`d = a ^ 2 - 1`, defined together in mutual recursion. -/
@[nolint dup_namespace]
def pell : ℕ → ℕ × ℕ := fun n =>
  Nat.recOn n (1, 0) fun n xy => (xy.1 * a + d * xy.2, xy.1 + xy.2 * a)
#align pell.pell Pell.pell

/-- The Pell `x` sequence. -/
def xn (n : ℕ) : ℕ :=
  (pell n).1
#align pell.xn Pell.xn

/-- The Pell `y` sequence. -/
def yn (n : ℕ) : ℕ :=
  (pell n).2
#align pell.yn Pell.yn

@[simp]
theorem pell_val (n : ℕ) : pell n = (xn n, yn n) :=
  show pell n = ((pell n).1, (pell n).2) from
    match pell n with
    | (a, b) => rfl
#align pell.pell_val Pell.pell_val

@[simp]
theorem xn_zero : xn 0 = 1 :=
  rfl
#align pell.xn_zero Pell.xn_zero

@[simp]
theorem yn_zero : yn 0 = 0 :=
  rfl
#align pell.yn_zero Pell.yn_zero

@[simp]
theorem xn_succ (n : ℕ) : xn (n + 1) = xn n * a + d * yn n :=
  rfl
#align pell.xn_succ Pell.xn_succ

@[simp]
theorem yn_succ (n : ℕ) : yn (n + 1) = xn n + yn n * a :=
  rfl
#align pell.yn_succ Pell.yn_succ

@[simp]
theorem xn_one : xn 1 = a := by simp
#align pell.xn_one Pell.xn_one

@[simp]
theorem yn_one : yn 1 = 1 := by simp
#align pell.yn_one Pell.yn_one

/-- The Pell `x` sequence, considered as an integer sequence.-/
def xz (n : ℕ) : ℤ :=
  xn n
#align pell.xz Pell.xz

/-- The Pell `y` sequence, considered as an integer sequence.-/
def yz (n : ℕ) : ℤ :=
  yn n
#align pell.yz Pell.yz

section

omit a1

/-- The element `a` such that `d = a ^ 2 - 1`, considered as an integer.-/
def az : ℤ :=
  a
#align pell.az Pell.az

end

theorem asq_pos : 0 < a * a :=
  le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1) <;> rwa [mul_one] at this)
#align pell.asq_pos Pell.asq_pos

theorem dz_val : ↑d = az * az - 1 :=
  have : 1 ≤ a * a := asq_pos
  show ↑(a * a - 1) = _ by rw [Int.ofNat_sub this] <;> rfl
#align pell.dz_val Pell.dz_val

@[simp]
theorem xz_succ (n : ℕ) : xz (n + 1) = xz n * az + ↑d * yz n :=
  rfl
#align pell.xz_succ Pell.xz_succ

@[simp]
theorem yz_succ (n : ℕ) : yz (n + 1) = xz n + yz n * az :=
  rfl
#align pell.yz_succ Pell.yz_succ

/-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
def pellZd (n : ℕ) : ℤ√d :=
  ⟨xn n, yn n⟩
#align pell.pell_zd Pell.pellZd

@[simp]
theorem pellZd_re (n : ℕ) : (pell_zd n).re = xn n :=
  rfl
#align pell.pell_zd_re Pell.pellZd_re

@[simp]
theorem pellZd_im (n : ℕ) : (pell_zd n).im = yn n :=
  rfl
#align pell.pell_zd_im Pell.pellZd_im

theorem isPell_nat {x y : ℕ} : IsPell (⟨x, y⟩ : ℤ√d) ↔ x * x - d * y * y = 1 :=
  ⟨fun h =>
    Int.ofNat.inj
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub h)] <;> exact h),
    fun h =>
    show ((x * x : ℕ) - (d * y * y : ℕ) : ℤ) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h, h] <;> rfl⟩
#align pell.is_pell_nat Pell.isPell_nat

@[simp]
theorem pellZd_succ (n : ℕ) : pell_zd (n + 1) = pell_zd n * ⟨a, 1⟩ := by simp [Zsqrtd.ext]
#align pell.pell_zd_succ Pell.pellZd_succ

theorem isPell_one : IsPell (⟨a, 1⟩ : ℤ√d) :=
  show az * az - d * 1 * 1 = 1 by simp [dz_val] <;> ring
#align pell.is_pell_one Pell.isPell_one

theorem isPell_pellZd : ∀ n : ℕ, IsPell (pell_zd n)
  | 0 => rfl
  | n + 1 => by
    let o := is_pell_one
    simp <;> exact Pell.isPell_mul (is_pell_pell_zd n) o
#align pell.is_pell_pell_zd Pell.isPell_pellZd

@[simp]
theorem pell_eqz (n : ℕ) : xz n * xz n - d * yz n * yz n = 1 :=
  is_pell_pell_zd n
#align pell.pell_eqz Pell.pell_eqz

@[simp]
theorem pell_eq (n : ℕ) : xn n * xn n - d * yn n * yn n = 1 :=
  let pn := pell_eqz n
  have h : (↑(xn n * xn n) : ℤ) - ↑(d * yn n * yn n) = 1 := by
    repeat' rw [Int.ofNat_mul] <;> exact pn
  have hl : d * yn n * yn n ≤ xn n * xn n :=
    Int.le_of_ofNat_le_ofNat <| Int.le.intro <| add_eq_of_eq_sub' <| Eq.symm h
  Int.ofNat.inj (by rw [Int.ofNat_sub hl] <;> exact h)
#align pell.pell_eq Pell.pell_eq

instance dnsq : Zsqrtd.Nonsquare d :=
  ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h] <;> exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.2 (by rw [← this] <;> exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) ≤ n * n + 1 := by rw [this] <;> exact Nat.mul_self_le_mul_self na
    have : n + n ≤ 0 :=
      @Nat.le_of_add_le_add_right (n * n + 1) _ _ (by ring_nf  at this⊢ <;> assumption)
    ne_of_gt d_pos <| by rwa [Nat.eq_zero_of_le_zero ((Nat.le_add_left _ _).trans this)] at h⟩
#align pell.dnsq Pell.dnsq

theorem xn_ge_a_pow : ∀ n : ℕ, a ^ n ≤ xn n
  | 0 => le_refl 1
  | n + 1 => by
    simp [pow_succ'] <;>
      exact le_trans (Nat.mul_le_mul_right _ (xn_ge_a_pow n)) (Nat.le_add_right _ _)
#align pell.xn_ge_a_pow Pell.xn_ge_a_pow

theorem n_lt_a_pow : ∀ n : ℕ, n < a ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => by
    have IH := n_lt_a_pow n
    have : a ^ n + a ^ n ≤ a ^ n * a := by
      rw [← mul_two]
      exact Nat.mul_le_mul_left _ a1
    simp [pow_succ']
    refine' lt_of_lt_of_le _ this
    exact add_lt_add_of_lt_of_le IH (lt_of_le_of_lt (Nat.zero_le _) IH)
#align pell.n_lt_a_pow Pell.n_lt_a_pow

theorem n_lt_xn (n) : n < xn n :=
  lt_of_lt_of_le (n_lt_a_pow n) (xn_ge_a_pow n)
#align pell.n_lt_xn Pell.n_lt_xn

theorem x_pos (n) : 0 < xn n :=
  lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn n)
#align pell.x_pos Pell.x_pos

theorem eq_pell_lem : ∀ (n) (b : ℤ√d), 1 ≤ b → IsPell b → b ≤ pell_zd n → ∃ n, b = pell_zd n
  | 0, b => fun h1 hp hl => ⟨0, @Zsqrtd.le_antisymm _ dnsq _ _ hl h1⟩
  | n + 1, b => fun h1 hp h =>
    have a1p : (0 : ℤ√d) ≤ ⟨a, 1⟩ := trivial
    have am1p : (0 : ℤ√d) ≤ ⟨a, -1⟩ := show (_ : Nat) ≤ _ by simp <;> exact Nat.pred_le _
    have a1m : (⟨a, 1⟩ * ⟨a, -1⟩ : ℤ√d) = 1 := isPell_norm.1 is_pell_one
    if ha : (⟨↑a, 1⟩ : ℤ√d) ≤ b then
      let ⟨m, e⟩ :=
        eq_pell_lem n (b * ⟨a, -1⟩) (by rw [← a1m] <;> exact mul_le_mul_of_nonneg_right ha am1p)
          (isPell_mul hp (isPell_star.1 is_pell_one))
          (by
            have t := mul_le_mul_of_nonneg_right h am1p <;>
              rwa [pell_zd_succ, mul_assoc, a1m, mul_one] at t)
      ⟨m + 1, by
        rw [show b = b * ⟨a, -1⟩ * ⟨a, 1⟩ by rw [mul_assoc, Eq.trans (mul_comm _ _) a1m] <;> simp,
          pell_zd_succ, e]⟩
    else
      suffices ¬1 < b from ⟨0, show b = 1 from (Or.resolve_left (lt_or_eq_of_le h1) this).symm⟩
      fun h1l => by
      cases' b with x y <;>
        exact by
          have bm : (_ * ⟨_, _⟩ : ℤ√d a1) = 1 := Pell.isPell_norm.1 hp
          have y0l : (0 : ℤ√d a1) < ⟨x - x, y - -y⟩ :=
            sub_lt_sub h1l fun hn : (1 : ℤ√d a1) ≤ ⟨x, -y⟩ => by
              have t := mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1) <;>
                  rw [bm, mul_one] at t <;>
                exact h1l t
          have yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩ :=
            show (⟨x, y⟩ - ⟨x, -y⟩ : ℤ√d a1) < ⟨a, 1⟩ - ⟨a, -1⟩ from
              sub_lt_sub ha fun hn : (⟨x, -y⟩ : ℤ√d a1) ≤ ⟨a, -1⟩ => by
                have t :=
                      mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one h1)) a1p <;>
                    rw [bm, one_mul, mul_assoc, Eq.trans (mul_comm _ _) a1m, mul_one] at t <;>
                  exact ha t
          simp at y0l <;> simp at yl2 <;>
            exact
              match y, y0l, (yl2 : (⟨_, _⟩ : ℤ√_) < ⟨_, _⟩) with
              | 0, y0l, yl2 => y0l (le_refl 0)
              | (y + 1 : ℕ), y0l, yl2 =>
                yl2
                  (Zsqrtd.le_of_le_le (le_refl 0)
                    (let t := Int.ofNat_le_ofNat_of_le (Nat.succ_pos y)
                    add_le_add t t))
              | -[y+1], y0l, yl2 => y0l trivial
#align pell.eq_pell_lem Pell.eq_pell_lem

theorem eq_pellZd (b : ℤ√d) (b1 : 1 ≤ b) (hp : IsPell b) : ∃ n, b = pell_zd n :=
  let ⟨n, h⟩ := @Zsqrtd.le_arch d b
  eq_pell_lem n b b1 hp <|
    h.trans <| by
      rw [Zsqrtd.coe_nat_val] <;>
        exact
          Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
            (Int.ofNat_zero_le _)
#align pell.eq_pell_zd Pell.eq_pellZd

/-- Every solution to **Pell's equation** is recursively obtained from the initial solution
`(1,0)` using the recursion `pell`. -/
theorem eq_pell {x y : ℕ} (hp : x * x - d * y * y = 1) : ∃ n, x = xn n ∧ y = yn n :=
  have : (1 : ℤ√d) ≤ ⟨x, y⟩ :=
    match x, hp with
    | 0, (hp : 0 - _ = 1) => by rw [zero_tsub] at hp <;> contradiction
    | x + 1, hp =>
      Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| Nat.succ_pos x) (Int.ofNat_zero_le _)
  let ⟨m, e⟩ := eq_pell_zd ⟨x, y⟩ this (is_pell_nat.2 hp)
  ⟨m,
    match x, y, e with
    | _, _, rfl => ⟨rfl, rfl⟩⟩
#align pell.eq_pell Pell.eq_pell

theorem pellZd_add (m) : ∀ n, pell_zd (m + n) = pell_zd m * pell_zd n
  | 0 => (mul_one _).symm
  | n + 1 => by rw [← add_assoc, pell_zd_succ, pell_zd_succ, pell_zd_add n, ← mul_assoc]
#align pell.pell_zd_add Pell.pellZd_add

theorem xn_add (m n) : xn (m + n) = xn m * xn n + d * yn m * yn n := by
  injection pell_zd_add _ m n with h _ <;>
      repeat' first |rw [← Int.ofNat_add] at h|rw [← Int.ofNat_mul] at h <;>
    exact Int.ofNat.inj h
#align pell.xn_add Pell.xn_add

theorem yn_add (m n) : yn (m + n) = xn m * yn n + yn m * xn n := by
  injection pell_zd_add _ m n with _ h <;>
      repeat' first |rw [← Int.ofNat_add] at h|rw [← Int.ofNat_mul] at h <;>
    exact Int.ofNat.inj h
#align pell.yn_add Pell.yn_add

theorem pellZd_sub {m n} (h : n ≤ m) : pell_zd (m - n) = pell_zd m * star (pell_zd n) := by
  let t := pell_zd_add n (m - n)
  rw [add_tsub_cancel_of_le h] at t <;>
    rw [t, mul_comm (pell_zd _ n) _, mul_assoc, is_pell_norm.1 (is_pell_pell_zd _ _), mul_one]
#align pell.pell_zd_sub Pell.pellZd_sub

theorem xz_sub {m n} (h : n ≤ m) : xz (m - n) = xz m * xz n - d * yz m * yz n := by
  rw [sub_eq_add_neg, ← mul_neg]
  exact congr_arg Zsqrtd.re (pell_zd_sub a1 h)
#align pell.xz_sub Pell.xz_sub

theorem yz_sub {m n} (h : n ≤ m) : yz (m - n) = xz n * yz m - xz m * yz n := by
  rw [sub_eq_add_neg, ← mul_neg, mul_comm, add_comm]
  exact congr_arg Zsqrtd.im (pell_zd_sub a1 h)
#align pell.yz_sub Pell.yz_sub

theorem xy_coprime (n) : (xn n).coprime (yn n) :=
  Nat.coprime_of_dvd' fun k kp kx ky => by
    let p := pell_eq n
    rw [← p] <;>
      exact Nat.dvd_sub (le_of_lt <| Nat.lt_of_sub_eq_succ p) (kx.mul_left _) (ky.mul_left _)
#align pell.xy_coprime Pell.xy_coprime

theorem strictMono_y : StrictMono yn
  | m, 0, h => absurd h <| Nat.not_lt_zero _
  | m, n + 1, h =>
    by
    have : yn m ≤ yn n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strict_mono_y hl)
        fun e => by rw [e]
    simp <;> refine' lt_of_le_of_lt _ (Nat.lt_add_of_pos_left <| x_pos a1 n) <;>
        rw [← mul_one (yn a1 m)] <;>
      exact mul_le_mul this (le_of_lt a1) (Nat.zero_le _) (Nat.zero_le _)
#align pell.strict_mono_y Pell.strictMono_y

theorem strictMono_x : StrictMono xn
  | m, 0, h => absurd h <| Nat.not_lt_zero _
  | m, n + 1, h =>
    by
    have : xn m ≤ xn n :=
      Or.elim (lt_or_eq_of_le <| Nat.le_of_succ_le_succ h) (fun hl => le_of_lt <| strict_mono_x hl)
        fun e => by rw [e]
    simp <;> refine' lt_of_lt_of_le (lt_of_le_of_lt this _) (Nat.le_add_right _ _) <;>
        have t := Nat.mul_lt_mul_of_pos_left a1 (x_pos a1 n) <;>
      rwa [mul_one] at t
#align pell.strict_mono_x Pell.strictMono_x

theorem yn_ge_n : ∀ n, n ≤ yn n
  | 0 => Nat.zero_le _
  | n + 1 =>
    show n < yn (n + 1) from lt_of_le_of_lt (yn_ge_n n) (strict_mono_y <| Nat.lt_succ_self n)
#align pell.yn_ge_n Pell.yn_ge_n

theorem y_mul_dvd (n) : ∀ k, yn n ∣ yn (n * k)
  | 0 => dvd_zero _
  | k + 1 => by
    rw [Nat.mul_succ, yn_add] <;> exact dvd_add (dvd_mul_left _ _) ((y_mul_dvd k).mul_right _)
#align pell.y_mul_dvd Pell.y_mul_dvd

theorem y_dvd_iff (m n) : yn m ∣ yn n ↔ m ∣ n :=
  ⟨fun h =>
    Nat.dvd_of_mod_eq_zero <|
      (Nat.eq_zero_or_pos _).resolve_right fun hp =>
        by
        have co : Nat.coprime (yn m) (xn (m * (n / m))) :=
          Nat.coprime.symm <| (xy_coprime _).coprime_dvd_right (y_mul_dvd m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left fun e => by
            rw [e, Nat.mod_zero] at hp <;> rw [e] at h <;>
              exact ne_of_lt (strict_mono_y a1 hp) (eq_zero_of_zero_dvd h).symm
        rw [← Nat.mod_add_div n m, yn_add] at h <;>
          exact
            not_le_of_gt (strict_mono_y _ <| Nat.mod_lt n m0)
              (Nat.le_of_dvd (strict_mono_y _ hp) <|
                co.dvd_of_dvd_mul_right <|
                  (Nat.dvd_add_iff_right <| (y_mul_dvd _ _ _).mul_left _).2 h),
    fun ⟨k, e⟩ => by rw [e] <;> apply y_mul_dvd⟩
#align pell.y_dvd_iff Pell.y_dvd_iff

theorem xy_modEq_yn (n) :
    ∀ k,
      xn (n * k) ≡ xn n ^ k [MOD yn n ^ 2] ∧ yn (n * k) ≡ k * xn n ^ (k - 1) * yn n [MOD yn n ^ 3]
  | 0 => by constructor <;> simp
  | k + 1 => by
    let ⟨hx, hy⟩ := xy_modeq_yn k
    have L : xn (n * k) * xn n + d * yn (n * k) * yn n ≡ xn n ^ k * xn n + 0 [MOD yn n ^ 2] :=
      (hx.mul_right _).add <|
        modEq_zero_iff_dvd.2 <| by
          rw [pow_succ'] <;>
            exact
              mul_dvd_mul_right
                (dvd_mul_of_dvd_right
                  (modeq_zero_iff_dvd.1 <|
                    (hy.of_dvd <| by simp [pow_succ']).trans <|
                      modeq_zero_iff_dvd.2 <| by simp [-mul_comm, -mul_assoc])
                  _)
                _
    have R :
      xn (n * k) * yn n + yn (n * k) * xn n ≡ xn n ^ k * yn n + k * xn n ^ k * yn n [MOD
        yn n ^ 3] :=
      ModEq.add
          (by
            rw [pow_succ']
            exact hx.mul_right' _) <|
        by
        have : k * xn n ^ (k - 1) * yn n * xn n = k * xn n ^ k * yn n := by
          clear _let_match <;> cases' k with k <;> simp [pow_succ', mul_comm, mul_left_comm]
        rw [← this]
        exact hy.mul_right _
    rw [add_tsub_cancel_right, Nat.mul_succ, xn_add, yn_add, pow_succ' (xn _ n), Nat.succ_mul,
      add_comm (k * xn _ n ^ k) (xn _ n ^ k), right_distrib]
    exact ⟨L, R⟩
#align pell.xy_modeq_yn Pell.xy_modEq_yn

theorem ysq_dvd_yy (n) : yn n * yn n ∣ yn (n * yn n) :=
  modEq_zero_iff_dvd.1 <|
    ((xy_modeq_yn n (yn n)).right.of_dvd <| by simp [pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])
#align pell.ysq_dvd_yy Pell.ysq_dvd_yy

theorem dvd_of_ysq_dvd {n t} (h : yn n * yn n ∣ yn t) : yn n ∣ t :=
  have nt : n ∣ t := (y_dvd_iff n t).1 <| dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt⊢) fun n0l : 0 < n =>
    by
    let ⟨k, ke⟩ := nt
    have : yn n ∣ k * xn n ^ (k - 1) :=
      Nat.dvd_of_mul_dvd_mul_right (strict_mono_y n0l) <|
        modEq_zero_iff_dvd.1 <| by
          have xm := (xy_modeq_yn a1 n k).right <;> rw [← ke] at xm <;>
            exact (xm.of_dvd <| by simp [pow_succ]).symm.trans h.modeq_zero_nat
    rw [ke] <;>
      exact dvd_mul_of_dvd_right (((xy_coprime _ _).pow_leftₓ _).symm.dvd_of_dvd_mul_right this) _
#align pell.dvd_of_ysq_dvd Pell.dvd_of_ysq_dvd

theorem pellZd_succ_succ (n) : pell_zd (n + 2) + pell_zd n = (2 * a : ℕ) * pell_zd (n + 1) := by
  have : (1 : ℤ√d) + ⟨a, 1⟩ * ⟨a, 1⟩ = ⟨a, 1⟩ * (2 * a) :=
    by
    rw [Zsqrtd.coe_nat_val]
    change (⟨_, _⟩ : ℤ√d a1) = ⟨_, _⟩
    rw [dz_val]
    dsimp [az]
    rw [Zsqrtd.ext]
    dsimp
    constructor <;> ring
  simpa [mul_add, mul_comm, mul_left_comm, add_comm] using congr_arg (· * pell_zd a1 n) this
#align pell.pell_zd_succ_succ Pell.pellZd_succ_succ

theorem xy_succ_succ (n) :
    xn (n + 2) + xn n = 2 * a * xn (n + 1) ∧ yn (n + 2) + yn n = 2 * a * yn (n + 1) := by
  have := pell_zd_succ_succ a1 n; unfold pell_zd at this
  erw [Zsqrtd.smul_val (2 * a : ℕ)] at this
  injection this with h₁ h₂
  constructor <;> apply Int.ofNat.inj <;> [simpa using h₁, simpa using h₂]
#align pell.xy_succ_succ Pell.xy_succ_succ

theorem xn_succ_succ (n) : xn (n + 2) + xn n = 2 * a * xn (n + 1) :=
  (xy_succ_succ n).1
#align pell.xn_succ_succ Pell.xn_succ_succ

theorem yn_succ_succ (n) : yn (n + 2) + yn n = 2 * a * yn (n + 1) :=
  (xy_succ_succ n).2
#align pell.yn_succ_succ Pell.yn_succ_succ

theorem xz_succ_succ (n) : xz (n + 2) = (2 * a : ℕ) * xz (n + 1) - xz n :=
  eq_sub_of_add_eq <| by delta xz <;> rw [← Int.ofNat_add, ← Int.ofNat_mul, xn_succ_succ]
#align pell.xz_succ_succ Pell.xz_succ_succ

theorem yz_succ_succ (n) : yz (n + 2) = (2 * a : ℕ) * yz (n + 1) - yz n :=
  eq_sub_of_add_eq <| by delta yz <;> rw [← Int.ofNat_add, ← Int.ofNat_mul, yn_succ_succ]
#align pell.yz_succ_succ Pell.yz_succ_succ

theorem yn_modEq_a_sub_one : ∀ n, yn n ≡ n [MOD a - 1]
  | 0 => by simp
  | 1 => by simp
  | n + 2 =>
    (yn_modeq_a_sub_one n).add_right_cancel <|
      by
      rw [yn_succ_succ, (by ring : n + 2 + n = 2 * (n + 1))]
      exact ((modeq_sub a1.le).mul_left 2).mul (yn_modeq_a_sub_one (n + 1))
#align pell.yn_modeq_a_sub_one Pell.yn_modEq_a_sub_one

theorem yn_modEq_two : ∀ n, yn n ≡ n [MOD 2]
  | 0 => by simp
  | 1 => by simp
  | n + 2 =>
    (yn_modeq_two n).add_right_cancel <|
      by
      rw [yn_succ_succ, mul_assoc, (by ring : n + 2 + n = 2 * (n + 1))]
      exact (dvd_mul_right 2 _).modEq_zero_nat.trans (dvd_mul_right 2 _).zero_modEq_nat
#align pell.yn_modeq_two Pell.yn_modEq_two

section

omit a1

theorem x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
    (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
      y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) :=
  by ring
#align pell.x_sub_y_dvd_pow_lem Pell.x_sub_y_dvd_pow_lem

end

theorem x_sub_y_dvd_pow (y : ℕ) :
    ∀ n, (2 * a * y - y * y - 1 : ℤ) ∣ yz n * (a - y) + ↑(y ^ n) - xz n
  | 0 => by simp [xz, yz, Int.ofNat_zero, Int.ofNat_one]
  | 1 => by simp [xz, yz, Int.ofNat_zero, Int.ofNat_one]
  | n + 2 =>
    by
    have : (2 * a * y - y * y - 1 : ℤ) ∣ ↑(y ^ (n + 2)) - ↑(2 * a) * ↑(y ^ (n + 1)) + ↑(y ^ n) :=
      ⟨-↑(y ^ n),
        by
        simp [pow_succ, mul_add, Int.ofNat_mul, show ((2 : ℕ) : ℤ) = 2 from rfl, mul_comm,
          mul_left_comm]
        ring⟩
    rw [xz_succ_succ, yz_succ_succ, x_sub_y_dvd_pow_lem ↑(y ^ (n + 2)) ↑(y ^ (n + 1)) ↑(y ^ n)]
    exact dvd_sub (dvd_add this <| (x_sub_y_dvd_pow (n + 1)).mul_left _) (x_sub_y_dvd_pow n)
#align pell.x_sub_y_dvd_pow Pell.x_sub_y_dvd_pow

theorem xn_modeq_x2n_add_lem (n j) : xn n ∣ d * yn n * (yn n * xn j) + xn j := by
  have h1 : d * yn n * (yn n * xn j) + xn j = (d * yn n * yn n + 1) * xn j := by
    simp [add_mul, mul_assoc]
  have h2 : d * yn n * yn n + 1 = xn n * xn n := by
    apply Int.ofNat.inj <;> repeat' first |rw [Int.ofNat_add]|rw [Int.ofNat_mul] <;>
      exact add_eq_of_eq_sub' (Eq.symm <| pell_eqz _ _)
  rw [h2] at h1 <;> rw [h1, mul_assoc] <;> exact dvd_mul_right _ _
#align pell.xn_modeq_x2n_add_lem Pell.xn_modeq_x2n_add_lem

theorem xn_modEq_x2n_add (n j) : xn (2 * n + j) + xn j ≡ 0 [MOD xn n] := by
  rw [two_mul, add_assoc, xn_add, add_assoc, ← zero_add 0]
  refine' (dvd_mul_right (xn a1 n) (xn a1 (n + j))).modEq_zero_nat.add _
  rw [yn_add, left_distrib, add_assoc, ← zero_add 0]
  exact
    ((dvd_mul_right _ _).mul_left _).modEq_zero_nat.add (xn_modeq_x2n_add_lem _ _ _).modEq_zero_nat
#align pell.xn_modeq_x2n_add Pell.xn_modEq_x2n_add

theorem xn_modEq_x2n_sub_lem {n j} (h : j ≤ n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] := by
  have h1 : xz n ∣ ↑d * yz n * yz (n - j) + xz j := by
    rw [yz_sub _ h, mul_sub_left_distrib, sub_add_eq_add_sub] <;>
      exact
        dvd_sub
          (by
            delta xz <;> delta yz <;> repeat' first |rw [← Int.ofNat_add]|rw [← Int.ofNat_mul] <;>
                rw [mul_comm (xn a1 j) (yn a1 n)] <;>
              exact Int.coe_nat_dvd.2 (xn_modeq_x2n_add_lem _ _ _))
          ((dvd_mul_right _ _).mul_left _)
  rw [two_mul, add_tsub_assoc_of_le h, xn_add, add_assoc, ← zero_add 0]
  exact
    (dvd_mul_right _ _).modEq_zero_nat.add
      (Int.coe_nat_dvd.1 <| by simpa [xz, yz] using h1).modEq_zero_nat
#align pell.xn_modeq_x2n_sub_lem Pell.xn_modEq_x2n_sub_lem

theorem xn_modEq_x2n_sub {n j} (h : j ≤ 2 * n) : xn (2 * n - j) + xn j ≡ 0 [MOD xn n] :=
  (le_total j n).elim xn_modeq_x2n_sub_lem fun jn =>
    by
    have : 2 * n - j + j ≤ n + j := by
      rw [tsub_add_cancel_of_le h, two_mul] <;> exact Nat.add_le_add_left jn _
    let t := xn_modeq_x2n_sub_lem (Nat.le_of_add_le_add_right this)
    rwa [tsub_tsub_cancel_of_le h, add_comm] at t
#align pell.xn_modeq_x2n_sub Pell.xn_modEq_x2n_sub

theorem xn_modEq_x4n_add (n j) : xn (4 * n + j) ≡ xn j [MOD xn n] :=
  ModEq.add_right_cancel' (xn (2 * n + j)) <| by
    refine' @modeq.trans _ _ 0 _ _ (by rw [add_comm] <;> exact (xn_modeq_x2n_add _ _ _).symm) <;>
        rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_assoc] <;>
      apply xn_modeq_x2n_add
#align pell.xn_modeq_x4n_add Pell.xn_modEq_x4n_add

theorem xn_modEq_x4n_sub {n j} (h : j ≤ 2 * n) : xn (4 * n - j) ≡ xn j [MOD xn n] :=
  have h' : j ≤ 2 * n := le_trans h (by rw [Nat.succ_mul] <;> apply Nat.le_add_left)
  ModEq.add_right_cancel' (xn (2 * n - j)) <| by
    refine' @modeq.trans _ _ 0 _ _ (by rw [add_comm] <;> exact (xn_modeq_x2n_sub _ h).symm) <;>
        rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_tsub_assoc_of_le h'] <;>
      apply xn_modeq_x2n_add
#align pell.xn_modeq_x4n_sub Pell.xn_modEq_x4n_sub

theorem eq_of_xn_modeq_lem1 {i n} : ∀ {j}, i < j → j < n → xn i % xn n < xn j % xn n
  | 0, ij, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, jn =>
    by
    suffices xn j % xn n < xn (j + 1) % xn n from
      (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
        (fun h => lt_trans (eq_of_xn_modeq_lem1 h (le_of_lt jn)) this) fun h => by
        rw [h] <;> exact this
    rw [Nat.mod_eq_of_lt (strict_mono_x _ (Nat.lt_of_succ_lt jn)),
        Nat.mod_eq_of_lt (strict_mono_x _ jn)] <;>
      exact strict_mono_x _ (Nat.lt_succ_self _)
#align pell.eq_of_xn_modeq_lem1 Pell.eq_of_xn_modeq_lem1

theorem eq_of_xn_modeq_lem2 {n} (h : 2 * xn n = xn (n + 1)) : a = 2 ∧ n = 0 := by
  rw [xn_succ, mul_comm] at h <;>
    exact
      by
      have : n = 0 :=
        n.eq_zero_or_pos.resolve_right fun np =>
          ne_of_lt
            (lt_of_le_of_lt (Nat.mul_le_mul_left _ a1)
              (Nat.lt_add_of_pos_right <| mul_pos (d_pos a1) (strict_mono_y a1 np)))
            h
      cases this <;> simp at h <;> exact ⟨h.symm, rfl⟩
#align pell.eq_of_xn_modeq_lem2 Pell.eq_of_xn_modeq_lem2

theorem eq_of_xn_modeq_lem3 {i n} (npos : 0 < n) :
    ∀ {j}, i < j → j ≤ 2 * n → j ≠ n → ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) → xn i % xn n < xn j % xn n
  | 0, ij, _, _, _ => absurd ij (Nat.not_lt_zero _)
  | j + 1, ij, j2n, jnn, ntriv =>
    have lem2 : ∀ k > n, k ≤ 2 * n → (↑(xn k % xn n) : ℤ) = xn n - xn (2 * n - k) := fun k kn k2n =>
      by
      let k2nl :=
        lt_of_add_lt_add_right <|
          show 2 * n - k + k < n + k by
            rw [tsub_add_cancel_of_le]
            rw [two_mul] <;> exact add_lt_add_left kn n
            exact k2n
      have xle : xn (2 * n - k) ≤ xn n := le_of_lt <| strict_mono_x k2nl
      suffices xn k % xn n = xn n - xn (2 * n - k) by rw [this, Int.ofNat_sub xle]
      rw [← Nat.mod_eq_of_lt (Nat.sub_lt (x_pos a1 n) (x_pos a1 (2 * n - k)))]
      apply modeq.add_right_cancel' (xn a1 (2 * n - k))
      rw [tsub_add_cancel_of_le xle]
      have t := xn_modeq_x2n_sub_lem a1 k2nl.le
      rw [tsub_tsub_cancel_of_le k2n] at t
      exact t.trans dvd_rfl.zero_modeq_nat
    (lt_trichotomy j n).elim (fun jn : j < n => eq_of_xn_modeq_lem1 ij (lt_of_le_of_ne jn jnn))
      fun o =>
      o.elim
        (fun jn : j = n => by
          cases jn
          apply Int.lt_of_ofNat_lt_ofNat
          rw [lem2 (n + 1) (Nat.lt_succ_self _) j2n,
            show 2 * n - (n + 1) = n - 1 by
              rw [two_mul, tsub_add_eq_tsub_tsub, add_tsub_cancel_right]]
          refine' lt_sub_left_of_add_lt (Int.ofNat_lt_ofNat_of_lt _)
          cases' lt_or_eq_of_le <| Nat.le_of_succ_le_succ ij with lin ein
          · rw [Nat.mod_eq_of_lt (strict_mono_x _ lin)]
            have ll : xn a1 (n - 1) + xn a1 (n - 1) ≤ xn a1 n :=
              by
              rw [← two_mul, mul_comm,
                show xn a1 n = xn a1 (n - 1 + 1) by rw [tsub_add_cancel_of_le (succ_le_of_lt npos)],
                xn_succ]
              exact le_trans (Nat.mul_le_mul_left _ a1) (Nat.le_add_right _ _)
            have npm : (n - 1).succ = n := Nat.succ_pred_eq_of_pos npos
            have il : i ≤ n - 1 := by
              apply Nat.le_of_succ_le_succ
              rw [npm]
              exact lin
            cases' lt_or_eq_of_le il with ill ile
            · exact lt_of_lt_of_le (Nat.add_lt_add_left (strict_mono_x a1 ill) _) ll
            · rw [ile]
              apply lt_of_le_of_ne ll
              rw [← two_mul]
              exact fun e =>
                ntriv <|
                  by
                  let ⟨a2, s1⟩ :=
                    @eq_of_xn_modeq_lem2 _ a1 (n - 1)
                      (by rwa [tsub_add_cancel_of_le (succ_le_of_lt npos)])
                  have n1 : n = 1 := le_antisymm (tsub_eq_zero_iff_le.mp s1) npos
                  rw [ile, a2, n1] <;> exact ⟨rfl, rfl, rfl, rfl⟩
          · rw [ein, Nat.mod_self, add_zero]
            exact strict_mono_x _ (Nat.pred_lt npos.ne'))
        fun jn : j > n =>
        have lem1 : j ≠ n → xn j % xn n < xn (j + 1) % xn n → xn i % xn n < xn (j + 1) % xn n :=
          fun jn s =>
          (lt_or_eq_of_le (Nat.le_of_succ_le_succ ij)).elim
            (fun h =>
              lt_trans
                (eq_of_xn_modeq_lem3 h (le_of_lt j2n) jn fun ⟨a1, n1, i0, j2⟩ => by
                  rw [n1, j2] at j2n <;> exact absurd j2n (by decide))
                s)
            fun h => by rw [h] <;> exact s
        lem1 (ne_of_gt jn) <|
          Int.lt_of_ofNat_lt_ofNat <|
            by
            rw [lem2 j jn (le_of_lt j2n), lem2 (j + 1) (Nat.le_succ_of_le jn) j2n]
            refine' sub_lt_sub_left (Int.ofNat_lt_ofNat_of_lt <| strict_mono_x _ _) _
            rw [Nat.sub_succ]
            exact Nat.pred_lt (ne_of_gt <| tsub_pos_of_lt j2n)
#align pell.eq_of_xn_modeq_lem3 Pell.eq_of_xn_modeq_lem3

theorem eq_of_xn_modEq_le {i j n} (ij : i ≤ j) (j2n : j ≤ 2 * n) (h : xn i ≡ xn j [MOD xn n])
    (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
  if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine' ne_of_gt _ h
        rw [jn, Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by
          rw [Nat.mod_eq_of_lt (strict_mono_x a1 (Nat.pos_of_ne_zero npos))] <;> exact by decide
        cases' i with i
        exact x0
        rw [jn] at ij'
        exact
          x0.trans
            (eq_of_xn_modeq_lem3 _ (Nat.pos_of_ne_zero npos) (Nat.succ_pos _) (le_trans ij j2n)
              (ne_of_lt ij') fun ⟨a1, n1, _, i2⟩ => by
              rw [n1, i2] at ij' <;> exact absurd ij' (by decide))
      else ne_of_lt (eq_of_xn_modeq_lem3 (Nat.pos_of_ne_zero npos) ij' j2n jn ntriv) h
#align pell.eq_of_xn_modeq_le Pell.eq_of_xn_modEq_le

theorem eq_of_xn_modEq {i j n} (i2n : i ≤ 2 * n) (j2n : j ≤ 2 * n) (h : xn i ≡ xn j [MOD xn n])
    (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) : i = j :=
  (le_total i j).elim
    (fun ij => eq_of_xn_modeq_le ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modeq_le ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm
#align pell.eq_of_xn_modeq Pell.eq_of_xn_modEq

theorem eq_of_xn_modeq' {i j n} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ 4 * n)
    (h : xn j ≡ xn i [MOD xn n]) : j = i ∨ j + i = 4 * n :=
  have i2n : i ≤ 2 * n := by apply le_trans hin <;> rw [two_mul] <;> apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j ≤ 2 * n =>
      eq_of_xn_modeq j2n i2n h fun a2 n1 =>
        ⟨fun j0 i2 => by rw [n1, i2] at hin <;> exact absurd hin (by decide), fun j2 i0 =>
          ne_of_gt ipos i0⟩)
    fun j2n : 2 * n < j =>
    suffices i = 4 * n - j by rw [this, add_tsub_cancel_of_le j4n]
    have j42n : 4 * n - j ≤ 2 * n :=
      @Nat.le_of_add_le_add_right j _ _ <| by
        rw [tsub_add_cancel_of_le j4n, show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n] <;>
          exact Nat.add_le_add_left (le_of_lt j2n) _
    eq_of_xn_modeq i2n j42n
      (h.symm.trans <| by
        let t := xn_modeq_x4n_sub j42n
        rwa [tsub_tsub_cancel_of_le j4n] at t)
      fun a2 n1 =>
      ⟨fun i0 => absurd i0 (ne_of_gt ipos), fun i2 =>
        by
        rw [n1, i2] at hin
        exact absurd hin (by decide)⟩
#align pell.eq_of_xn_modeq' Pell.eq_of_xn_modeq'

theorem modEq_of_xn_modEq {i j n} (ipos : 0 < i) (hin : i ≤ n) (h : xn j ≡ xn i [MOD xn n]) :
    j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
  let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta modeq <;> rw [Nat.mod_eq_of_lt jl]
  have : ∀ j q, xn (j + 4 * n * q) ≡ xn j [MOD xn n] :=
    by
    intro j q; induction' q with q IH; · simp
    rw [Nat.mul_succ, ← add_assoc, add_comm]
    exact (xn_modeq_x4n_add _ _ _).trans IH
  Or.imp (fun ji : j' = i => by rwa [← ji])
    (fun ji : j' + i = 4 * n =>
      (jj.add_right _).trans <| by
        rw [ji]
        exact dvd_rfl.modeq_zero_nat)
    (eq_of_xn_modeq' ipos hin jl.le <|
      (h.symm.trans <| by
          rw [← Nat.mod_add_div j (4 * n)]
          exact this j' _).symm)
#align pell.modeq_of_xn_modeq Pell.modEq_of_xn_modEq

end

theorem xy_modEq_of_modEq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
    ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c]
  | 0 => by constructor <;> rfl
  | 1 => by simp <;> exact ⟨h, modeq.refl 1⟩
  | n + 2 =>
    ⟨(xy_modeq_of_modeq n).left.add_right_cancel <|
        by
        rw [xn_succ_succ a1, xn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modeq_of_modeq (n + 1)).left,
      (xy_modeq_of_modeq n).right.add_right_cancel <|
        by
        rw [yn_succ_succ a1, yn_succ_succ b1]
        exact (h.mul_left _).mul (xy_modeq_of_modeq (n + 1)).right⟩
#align pell.xy_modeq_of_modeq Pell.xy_modEq_of_modEq

theorem matiyasevic {a k x y} :
    (∃ a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔
      1 < a ∧
        k ≤ y ∧
          (x = 1 ∧ y = 0 ∨
            ∃ u v s t b : ℕ,
              x * x - (a * a - 1) * y * y = 1 ∧
                u * u - (a * a - 1) * v * v = 1 ∧
                  s * s - (b * b - 1) * t * t = 1 ∧
                    1 < b ∧
                      b ≡ 1 [MOD 4 * y] ∧
                        b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t ≡ k [MOD 4 * y]) :=
  ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx, ← hy] <;>
        refine'
          ⟨a1,
            (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0] <;> exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
              fun kpos => _⟩ <;>
      exact
        let x := xn a1 k
        let y := yn a1 k
        let m := 2 * (k * y)
        let u := xn a1 m
        let v := yn a1 m
        have ky : k ≤ y := yn_ge_n a1 k
        have yv : y * y ∣ v := (ysq_dvd_yy a1 k).trans <| (y_dvd_iff _ _ _).2 <| dvd_mul_left _ _
        have uco : Nat.coprime u (4 * y) :=
          have : 2 ∣ v :=
            modeq_zero_iff_dvd.1 <| (yn_modeq_two _ _).trans (dvd_mul_right _ _).modEq_zero_nat
          have : Nat.coprime u 2 := (xy_coprime a1 m).coprime_dvd_right this
          (this.mul_right this).mul_right <|
            (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv)
        let ⟨b, ba, bm1⟩ := chinese_remainder uco a 1
        have m1 : 1 < m :=
          have : 0 < k * y := mul_pos kpos (strict_mono_y a1 kpos)
          Nat.mul_le_mul_left 2 this
        have vp : 0 < v := strict_mono_y a1 (lt_trans zero_lt_one m1)
        have b1 : 1 < b :=
          have : xn a1 1 < u := strict_mono_x a1 m1
          have : a < u := by simp at this <;> exact this
          lt_of_lt_of_le a1 <| by
            delta modeq at ba <;> rw [Nat.mod_eq_of_lt this] at ba <;> rw [← ba] <;>
              apply Nat.mod_le
        let s := xn b1 k
        let t := yn b1 k
        have sx : s ≡ x [MOD u] := (xy_modeq_of_modeq b1 a1 ba k).left
        have tk : t ≡ k [MOD 4 * y] :=
          have : 4 * y ∣ b - 1 :=
            Int.coe_nat_dvd.1 <| by rw [Int.ofNat_sub (le_of_lt b1)] <;> exact bm1.symm.dvd
          (yn_modeq_a_sub_one _ _).of_dvd this
        ⟨ky,
          Or.inr
            ⟨u, v, s, t, b, pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
    fun ⟨a1, ky, o⟩ =>
    ⟨a1,
      match o with
      | Or.inl ⟨x1, y0⟩ => by
        rw [y0] at ky <;> rw [Nat.eq_zero_of_le_zero ky, x1, y0] <;> exact ⟨rfl, rfl⟩
      | Or.inr ⟨u, v, s, t, b, xy, uv, st, b1, rem⟩ =>
        match x, y, eq_pell a1 xy, u, v, eq_pell a1 uv, s, t, eq_pell b1 st, rem, ky with
        | _, _, ⟨i, rfl, rfl⟩, _, _, ⟨n, rfl, rfl⟩, _, _, ⟨j, rfl, rfl⟩,
          ⟨(bm1 : b ≡ 1 [MOD 4 * yn a1 i]), (ba : b ≡ a [MOD xn a1 n]), (vp : 0 < yn a1 n),
            (yv : yn a1 i * yn a1 i ∣ yn a1 n), (sx : xn b1 j ≡ xn a1 i [MOD xn a1 n]),
            (tk : yn b1 j ≡ k [MOD 4 * yn a1 i])⟩,
          (ky : k ≤ yn a1 i) =>
          (Nat.eq_zero_or_pos i).elim
            (fun i0 => by simp [i0] at ky <;> rw [i0, ky] <;> exact ⟨rfl, rfl⟩) fun ipos =>
            by
            suffices i = k by rw [this] <;> exact ⟨rfl, rfl⟩
            clear _x o rem xy uv st _match _match _fun_match <;>
              exact
                by
                have iln : i ≤ n :=
                  le_of_not_gt fun hin =>
                    not_lt_of_ge (Nat.le_of_dvd vp (dvd_of_mul_left_dvd yv)) (strict_mono_y a1 hin)
                have yd : 4 * yn a1 i ∣ 4 * n := mul_dvd_mul_left _ <| dvd_of_ysq_dvd a1 yv
                have jk : j ≡ k [MOD 4 * yn a1 i] :=
                  have : 4 * yn a1 i ∣ b - 1 :=
                    Int.coe_nat_dvd.1 <| by rw [Int.ofNat_sub (le_of_lt b1)] <;> exact bm1.symm.dvd
                  ((yn_modeq_a_sub_one b1 _).of_dvd this).symm.trans tk
                have ki : k + i < 4 * yn a1 i :=
                  lt_of_le_of_lt (add_le_add ky (yn_ge_n a1 i)) <| by
                    rw [← two_mul] <;>
                      exact Nat.mul_lt_mul_of_pos_right (by decide) (strict_mono_y a1 ipos)
                have ji : j ≡ i [MOD 4 * n] :=
                  have : xn a1 j ≡ xn a1 i [MOD xn a1 n] :=
                    (xy_modeq_of_modeq b1 a1 ba j).left.symm.trans sx
                  (modeq_of_xn_modeq a1 ipos iln this).resolve_right
                    fun ji : j + i ≡ 0 [MOD 4 * n] =>
                    not_le_of_gt ki <|
                      Nat.le_of_dvd (lt_of_lt_of_le ipos <| Nat.le_add_left _ _) <|
                        modeq_zero_iff_dvd.1 <| (jk.symm.add_right i).trans <| ji.of_dvd yd
                have : i % (4 * yn a1 i) = k % (4 * yn a1 i) := (ji.of_dvd yd).symm.trans jk <;>
                  rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_left _ _) ki),
                    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) ki)] at this⟩⟩
#align pell.matiyasevic Pell.matiyasevic

theorem eq_pow_of_pell_lem {a y k} (hy0 : y ≠ 0) (hk0 : k ≠ 0) (hyk : y ^ k < a) :
    (↑(y ^ k) : ℤ) < 2 * a * y - y * y - 1 :=
  have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : ℤ) < a := Nat.cast_lt.2 hyk
    _ ≤ a ^ 2 - (a - 1) ^ 2 - 1 :=
      by
      rw [sub_sq, mul_one, one_pow, sub_add, sub_sub_cancel, two_mul, sub_sub, ← add_sub,
        le_add_iff_nonneg_right, ← bit0, sub_nonneg, ← Nat.cast_two, Nat.cast_le, Nat.succ_le_iff]
      exact (one_le_iff_ne_zero.2 hy0).trans_lt hya
    _ ≤ a ^ 2 - (a - y) ^ 2 - 1 := by
      have := hya.le
      mono* <;> simpa only [sub_nonneg, Nat.cast_le, Nat.one_le_cast, Nat.one_le_iff_ne_zero]
    _ = 2 * a * y - y * y - 1 := by ring
    
#align pell.eq_pow_of_pell_lem Pell.eq_pow_of_pell_lem

theorem eq_pow_of_pell {m n k} :
    n ^ k = m ↔
      k = 0 ∧ m = 1 ∨
        0 < k ∧
          (n = 0 ∧ m = 0 ∨
            0 < n ∧
              ∃ (w a t z : ℕ)(a1 : 1 < a),
                xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
                  2 * a * n = t + (n * n + 1) ∧
                    m < t ∧
                      n ≤ w ∧ k ≤ w ∧ a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) := by
  constructor
  · rintro rfl
    refine' k.eq_zero_or_pos.imp (fun k0 => k0.symm ▸ ⟨rfl, rfl⟩) fun hk => ⟨hk, _⟩
    refine' n.eq_zero_or_pos.imp (fun n0 => n0.symm ▸ ⟨rfl, zero_pow hk⟩) fun hn => ⟨hn, _⟩
    set w := max n k
    have nw : n ≤ w := le_max_left _ _
    have kw : k ≤ w := le_max_right _ _
    have wpos : 0 < w := hn.trans_le nw
    have w1 : 1 < w + 1 := Nat.succ_lt_succ wpos
    set a := xn w1 w
    have a1 : 1 < a := strict_mono_x w1 wpos
    have na : n ≤ a := nw.trans (n_lt_xn w1 w).le
    set x := xn a1 k
    set y := yn a1 k
    obtain ⟨z, ze⟩ : w ∣ yn w1 w
    exact modeq_zero_iff_dvd.1 ((yn_modeq_a_sub_one w1 w).trans dvd_rfl.modeq_zero_nat)
    have nt : (↑(n ^ k) : ℤ) < 2 * a * n - n * n - 1 :=
      by
      refine' eq_pow_of_pell_lem hn.ne' hk.ne' _
      calc
        n ^ k ≤ n ^ w := Nat.pow_le_pow_of_le_right hn kw
        _ < (w + 1) ^ w := (Nat.pow_lt_pow_of_lt_left (Nat.lt_succ_of_le nw) wpos)
        _ ≤ a := xn_ge_a_pow w1 w
        
    lift (2 * a * n - n * n - 1 : ℤ) to ℕ using (Nat.cast_nonneg _).trans nt.le with t te
    have tm : x ≡ y * (a - n) + n ^ k [MOD t] :=
      by
      apply modeq_of_dvd
      rw [Int.ofNat_add, Int.ofNat_mul, Int.ofNat_sub na, te]
      exact x_sub_y_dvd_pow a1 n k
    have ta : 2 * a * n = t + (n * n + 1) :=
      by
      rw [← @Nat.cast_inj ℤ, Int.ofNat_add, te, sub_sub]
      repeat' first |rw [Nat.cast_add]|rw [Nat.cast_mul]
      rw [Nat.cast_one, sub_add_cancel, Nat.cast_two]
    have zp : a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1 := ze ▸ pell_eq w1 w
    exact ⟨w, a, t, z, a1, tm, ta, Nat.cast_lt.1 nt, nw, kw, zp⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hk0, ⟨rfl, rfl⟩ | ⟨hn0, w, a, t, z, a1, tm, ta, mt, nw, kw, zp⟩⟩)
    · exact pow_zero n
    · exact zero_pow hk0
    have hw0 : 0 < w := hn0.trans_le nw
    have hw1 : 1 < w + 1 := Nat.succ_lt_succ hw0
    rcases eq_pell hw1 zp with ⟨j, rfl, yj⟩
    have hj0 : 0 < j := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      exact lt_irrefl 1 a1
    have wj : w ≤ j :=
      Nat.le_of_dvd hj0
        (modeq_zero_iff_dvd.1 <|
          (yn_modeq_a_sub_one hw1 j).symm.trans <| modeq_zero_iff_dvd.2 ⟨z, yj.symm⟩)
    have hnka : n ^ k < xn hw1 j
    calc
      n ^ k ≤ n ^ j := Nat.pow_le_pow_of_le_right hn0 (le_trans kw wj)
      _ < (w + 1) ^ j := (Nat.pow_lt_pow_of_lt_left (Nat.lt_succ_of_le nw) hj0)
      _ ≤ xn hw1 j := xn_ge_a_pow hw1 j
      
    have nt : (↑(n ^ k) : ℤ) < 2 * xn hw1 j * n - n * n - 1 :=
      eq_pow_of_pell_lem hn0.ne' hk0.ne' hnka
    have na : n ≤ xn hw1 j := (Nat.le_self_pow hk0.ne' _).trans hnka.le
    have te : (t : ℤ) = 2 * xn hw1 j * n - n * n - 1 :=
      by
      rw [sub_sub, eq_sub_iff_add_eq]
      exact_mod_cast ta.symm
    have : xn a1 k ≡ yn a1 k * (xn hw1 j - n) + n ^ k [MOD t] :=
      by
      apply modeq_of_dvd
      rw [te, Nat.cast_add, Nat.cast_mul, Int.ofNat_sub na]
      exact x_sub_y_dvd_pow a1 n k
    have : n ^ k % t = m % t := (this.symm.trans tm).add_left_cancel' _
    rw [← te] at nt
    rwa [Nat.mod_eq_of_lt (Nat.cast_lt.1 nt), Nat.mod_eq_of_lt mt] at this
#align pell.eq_pow_of_pell Pell.eq_pow_of_pell

end Pell

