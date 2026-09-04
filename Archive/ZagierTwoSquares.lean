/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan, Thomas Browning
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Tactic.Linarith

/-!
# Zagier's "one-sentence proof" of Fermat's theorem on sums of two squares

"The involution on the finite set `S = {(x, y, z) : ℕ × ℕ × ℕ | x ^ 2 + 4 * y * z = p}` defined by
```
(x, y, z) ↦ (x + 2 * z, z, y - x - z) if x < y - z
            (2 * y - x, y, x - y + z) if y - z < x < 2 * y
            (x - 2 * y, x - y + z, y) if x > 2 * y
```
has exactly one fixed point, so `|S|` is odd and the involution defined by
`(x, y, z) ↦ (x, z, y)` also has a fixed point." — [Don Zagier](Zagier1990)

This elementary proof (`Nat.Prime.sq_add_sq'`) is independent of `Nat.Prime.sq_add_sq` in
`Mathlib/NumberTheory/SumTwoSquares.lean`, which uses the unique factorisation of `ℤ[i]`.
For a geometric interpretation of the piecewise involution (`Zagier.complexInvo`)
see [Moritz Firsching's MathOverflow answer](https://mathoverflow.net/a/299696).
-/

public section

namespace Zagier

open Finset

/-- A structure holding a triple of natural numbers `(x, y, z)` satisfying
`x * x + 4 * y * z = 4 * k + 1`. -/
@[ext]
structure Triple (k : ℕ) where
  /-- First number -/
  x : ℕ
  /-- Second number -/
  y : ℕ
  /-- Third number -/
  z : ℕ
  /-- The specified equation -/
  eqn : x * x + 4 * y * z = 4 * k + 1
deriving DecidableEq

namespace Triple

variable {k : ℕ} [hk : Fact (4 * k + 1).Prime] (T : Triple k)

omit hk in
lemma x_ne_zero : T.x ≠ 0 := by
  obtain ⟨x, y, z, h⟩ := T
  rintro rfl
  apply_fun (· % 4) at h
  simp [mul_assoc] at h

lemma y_ne_zero : T.y ≠ 0 := by
  obtain ⟨x, y, z, h⟩ := T
  rintro rfl
  have con : IsSquare (4 * k + 1) := ⟨_, by simpa using h.symm⟩
  exact absurd hk.out.prime con.not_prime

lemma z_ne_zero : T.z ≠ 0 := by
  obtain ⟨x, y, z, h⟩ := T
  rintro rfl
  have con : IsSquare (4 * k + 1) := ⟨_, by simpa using h.symm⟩
  exact absurd hk.out.prime con.not_prime

omit hk in
lemma x_bound : T.x ∈ Icc 1 (k + 1) := by
  have nx := T.x_ne_zero
  obtain ⟨x, y, z, h⟩ := T
  exact mem_Icc.mpr ⟨by lia, by nlinarith⟩

lemma y_bound : T.y ∈ Icc 1 k := by
  have ny := T.y_ne_zero
  have nz : 0 < T.z := by grind [T.z_ne_zero]
  obtain ⟨x, y, z, h⟩ := T
  exact mem_Icc.mpr ⟨by lia, by nlinarith⟩

lemma z_bound : T.z ∈ Icc 1 k := by
  have ny : 0 < T.y := by grind [T.y_ne_zero]
  have nz := T.z_ne_zero
  obtain ⟨x, y, z, h⟩ := T
  exact mem_Icc.mpr ⟨by lia, by nlinarith⟩

instance : Fintype (Triple k) where
  elems := (univ : Finset {t : Icc 1 (k + 1) ×ˢ Icc 1 k ×ˢ Icc 1 k //
    t.1.1 * t.1.1 + 4 * t.1.2.1 * t.1.2.2 = 4 * k + 1}).image fun s ↦ ⟨_, _, _, s.2⟩
  complete T := by
    simp_rw [mem_image, mem_univ, true_and]
    refine ⟨⟨⟨(T.x, T.y, T.z), ?_⟩, T.eqn⟩, by ext <;> rfl⟩
    simp only [mem_product]
    exact ⟨T.x_bound, T.y_bound, T.z_bound⟩

/-- The obvious involution `(x, y, z) ↦ (x, z, y)`. -/
def swap : Triple k where
  x := T.x
  y := T.z
  z := T.y
  eqn := by grind [T.eqn]

omit hk in
lemma involutive_swap : (@swap k).Involutive := fun _ ↦ rfl

omit hk in
/-- Fixed points of `swap` yield decompositions of `4 * k + 1` into two squares. -/
lemma sq_add_sq_of_swap_eq_self (sT : T.swap = T) : ∃ a b, a ^ 2 + b ^ 2 = 4 * k + 1 :=
  ⟨T.x, 2 * T.y, by grind [swap]⟩

/-- The complicated involution, defined piecewise according to how `x` compares with
`y - z` and `2 * y`. -/
def mangle : Triple k where
  x := if T.x + T.z < T.y then T.x + 2 * T.z else
    if 2 * T.y < T.x then T.x - 2 * T.y else 2 * T.y - T.x
  y := if T.x + T.z < T.y then T.z else if 2 * T.y < T.x then T.x + T.z - T.y else T.y
  z := if T.x + T.z < T.y then T.y - T.x - T.z else if 2 * T.y < T.x then T.y else T.x + T.z - T.y
  eqn := by
    rw [← T.eqn]
    split_ifs with less more
    · rw [Nat.sub_sub]; zify [less]; lia
    · push Not at less; zify [less, more]; lia
    · push Not at less more; zify [less, more]; lia

lemma involutive_mangle : (@mangle k).Involutive := fun T ↦ by
  ext <;> grind [mangle, T.x_ne_zero, T.z_ne_zero]

/-- The only fixed point of `mangle` is `(1, 1, k)`. -/
lemma eq_of_mangle_eq_self (mT : T.mangle = T) : T = ⟨1, 1, k, by lia⟩ := by
  have xy : T.x = T.y := by grind [mangle]
  have eqn : T.x * (T.x + 4 * T.z) = 4 * k + 1 := by grind [mangle]
  obtain ⟨_, _⟩ | ⟨_, _⟩ := Nat.prime_mul_iff.mp (eqn ▸ hk.out)
  · grind [T.z_ne_zero]
  · ext <;> grind

lemma card_fixedPoints_mangle_eq_one : Fintype.card (@mangle k).fixedPoints = 1 := by
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨⟨1, 1, k, by lia⟩, (by grind [mangle] : mangle _ = _)⟩,
    fun ⟨T, mT⟩ ↦ Subtype.ext (eq_of_mangle_eq_self _ mT)⟩

end Triple

end Zagier

open Zagier.Triple

/-- **Fermat's theorem on sums of two squares** (Wiedijk #20).
Every prime congruent to 1 mod 4 is the sum of two squares, proved using Zagier's involutions. -/
theorem Nat.Prime.sq_add_sq' {p : ℕ} [h : Fact p.Prime] (hp : p % 4 = 1) :
    ∃ a b, a ^ 2 + b ^ 2 = p := by
  rw [← div_add_mod p 4, hp] at h ⊢
  set k := p / 4
  have s2 : swap (k := k)^[2 ^ 1] = id := funext fun T ↦ involutive_swap T
  have m2 : mangle (k := k)^[2 ^ 1] = id := funext fun T ↦ involutive_mangle T
  have q := (Equiv.Perm.card_fixedPoints_modEq s2).symm.trans (Equiv.Perm.card_fixedPoints_modEq m2)
  rw [card_fixedPoints_mangle_eq_one, Nat.ModEq] at q
  replace q : 0 < Fintype.card (@swap k).fixedPoints := by lia
  rw [Fintype.card_pos_iff, nonempty_subtype] at q
  obtain ⟨T, sT⟩ := q
  exact sq_add_sq_of_swap_eq_self _ sT
