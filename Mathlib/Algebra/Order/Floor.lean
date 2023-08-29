/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.CharZero
import Mathlib.Data.Set.Intervals.Group
import Mathlib.Data.Set.Lattice
import Mathlib.Init.Meta.WellFoundedTactics
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

#align_import algebra.order.floor from "leanprover-community/mathlib"@"afdb43429311b885a7988ea15d0bac2aac80f69c"

/-!
# Floor and ceil

## Summary

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.

## Main Definitions

* `FloorSemiring`: An ordered semiring with natural-valued floor and ceil.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `Nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `FloorRing`: A linearly ordered ring with integer-valued floor and ceil.
* `Int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `Int.ceil a`: Least integer `z` such that `a ≤ z`.
* `Int.fract a`: Fractional part of `a`, defined as `a - floor a`.
* `round a`: Nearest integer to `a`. It rounds halves towards infinity.

## Notations

* `⌊a⌋₊` is `Nat.floor a`.
* `⌈a⌉₊` is `Nat.ceil a`.
* `⌊a⌋` is `Int.floor a`.
* `⌈a⌉` is `Int.ceil a`.

The index `₊` in the notations for `Nat.floor` and `Nat.ceil` is used in analogy to the notation
for `nnnorm`.

## TODO

`LinearOrderedRing`/`LinearOrderedSemiring` can be relaxed to `OrderedRing`/`OrderedSemiring` in
many lemmas.

## Tags

rounding, floor, ceil
-/


open Set

variable {F α β : Type*}

/-! ### Floor semiring -/

/-- A `FloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. Please see the above `TODO`. -/
class FloorSemiring (α) [OrderedSemiring α] where
  /-- `FloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`.-/
  floor : α → ℕ
  /-- `FloorSemiring.ceil a` computes the least natural `n` such that `a ≤ (n : α)`.-/
  ceil : α → ℕ
  /-- `FloorSemiring.floor` of a negative element is zero.-/
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- A natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion to `α` is
  smaller than `a`.-/
  gc_floor {a : α} {n : ℕ} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  /-- `FloorSemiring.ceil` is the lower adjoint of the coercion `↑ : ℕ → α`.-/
  gc_ceil : GaloisConnection ceil (↑)
#align floor_semiring FloorSemiring

instance : FloorSemiring ℕ where
  floor := id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id]
    -- ⊢ n✝ ≤ id a✝ ↔ n✝ ≤ a✝
    rfl
    -- 🎉 no goals
  gc_ceil n a := by
    rw [Nat.cast_id]
    -- ⊢ id n ≤ a ↔ n ≤ a
    rfl
    -- 🎉 no goals

namespace Nat

section OrderedSemiring

variable [OrderedSemiring α] [FloorSemiring α] {a : α} {n : ℕ}

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor
#align nat.floor Nat.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil
#align nat.ceil Nat.ceil

@[simp]
theorem floor_nat : (Nat.floor : ℕ → ℕ) = id :=
  rfl
#align nat.floor_nat Nat.floor_nat

@[simp]
theorem ceil_nat : (Nat.ceil : ℕ → ℕ) = id :=
  rfl
#align nat.ceil_nat Nat.ceil_nat

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] [FloorSemiring α] {a : α} {n : ℕ}

theorem le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a :=
  FloorSemiring.gc_floor ha
#align nat.le_floor_iff Nat.le_floor_iff

theorem le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ :=
  (le_floor_iff <| n.cast_nonneg.trans h).2 h
#align nat.le_floor Nat.le_floor

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha
#align nat.floor_lt Nat.floor_lt

theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by rw [Nat.cast_one]
                            -- 🎉 no goals
#align nat.floor_lt_one Nat.floor_lt_one

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_le fun h' => (le_floor h').not_lt h
#align nat.lt_of_floor_lt Nat.lt_of_floor_lt

theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := by exact_mod_cast lt_of_floor_lt h
                                                            -- 🎉 no goals
#align nat.lt_one_of_floor_lt_one Nat.lt_one_of_floor_lt_one

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : α) ≤ a :=
  (le_floor_iff ha).1 le_rfl
#align nat.floor_le Nat.floor_le

theorem lt_succ_floor (a : α) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _
#align nat.lt_succ_floor Nat.lt_succ_floor

theorem lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a
                                                      -- 🎉 no goals
#align nat.lt_floor_add_one Nat.lt_floor_add_one

@[simp]
theorem floor_coe (n : ℕ) : ⌊(n : α)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff, Nat.cast_le]
    -- ⊢ 0 ≤ ↑n
    exact n.cast_nonneg
    -- 🎉 no goals
#align nat.floor_coe Nat.floor_coe

@[simp]
theorem floor_zero : ⌊(0 : α)⌋₊ = 0 := by rw [← Nat.cast_zero, floor_coe]
                                          -- 🎉 no goals
#align nat.floor_zero Nat.floor_zero

@[simp]
theorem floor_one : ⌊(1 : α)⌋₊ = 1 := by rw [← Nat.cast_one, floor_coe]
                                         -- 🎉 no goals
#align nat.floor_one Nat.floor_one

theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    -- ⊢ ⌊0⌋₊ = 0
    exact floor_zero
    -- 🎉 no goals
#align nat.floor_of_nonpos Nat.floor_of_nonpos

theorem floor_mono : Monotone (floor : α → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  -- ⊢ ⌊a⌋₊ ≤ ⌊b⌋₊
  · rw [floor_of_nonpos ha]
    -- ⊢ 0 ≤ ⌊b⌋₊
    exact Nat.zero_le _
    -- 🎉 no goals
  · exact le_floor ((floor_le ha).trans h)
    -- 🎉 no goals
#align nat.floor_mono Nat.floor_mono

theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := by
  obtain ha | ha := le_total a 0
  -- ⊢ n ≤ ⌊a⌋₊ ↔ ↑n ≤ a
  · rw [floor_of_nonpos ha]
    -- ⊢ n ≤ 0 ↔ ↑n ≤ a
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_le
        (not_le_of_lt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha
    -- 🎉 no goals
#align nat.le_floor_iff' Nat.le_floor_iff'

@[simp]
theorem one_le_floor_iff (x : α) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x := by
  exact_mod_cast @le_floor_iff' α _ _ x 1 one_ne_zero
  -- 🎉 no goals
#align nat.one_le_floor_iff Nat.one_le_floor_iff

theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff' hn
#align nat.floor_lt' Nat.floor_lt'

theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  -- Porting note: broken `convert le_floor_iff' Nat.one_ne_zero`
  rw [Nat.lt_iff_add_one_le, zero_add, le_floor_iff' Nat.one_ne_zero, cast_one]
  -- 🎉 no goals
#align nat.floor_pos Nat.floor_pos

theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
  (le_or_lt a 0).resolve_left fun ha => lt_irrefl 0 <| by rwa [floor_of_nonpos ha] at h
                                                          -- 🎉 no goals
#align nat.pos_of_floor_pos Nat.pos_of_floor_pos

theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
  (Nat.cast_lt.2 h).trans_le <| floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le
#align nat.lt_of_lt_floor Nat.lt_of_lt_floor

theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n :=
  le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h
#align nat.floor_le_of_le Nat.floor_le_of_le

theorem floor_le_one_of_le_one (h : a ≤ 1) : ⌊a⌋₊ ≤ 1 :=
  floor_le_of_le <| h.trans_eq <| Nat.cast_one.symm
#align nat.floor_le_one_of_le_one Nat.floor_le_one_of_le_one

@[simp]
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by
  rw [← lt_one_iff, ← @cast_one α]
  -- ⊢ ⌊a⌋₊ < 1 ↔ a < ↑1
  exact floor_lt' Nat.one_ne_zero
  -- 🎉 no goals
#align nat.floor_eq_zero Nat.floor_eq_zero

theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]
#align nat.floor_eq_iff Nat.floor_eq_iff

theorem floor_eq_iff' (hn : n ≠ 0) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt' (Nat.add_one_ne_zero n),
    Nat.lt_add_one_iff, le_antisymm_iff, and_comm]
#align nat.floor_eq_iff' Nat.floor_eq_iff'

theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set α), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩
#align nat.floor_eq_on_Ico Nat.floor_eq_on_Ico

theorem floor_eq_on_Ico' (n : ℕ) :
    ∀ a ∈ (Set.Ico n (n + 1) : Set α), (⌊a⌋₊ : α) = n :=
  fun x hx => by exact_mod_cast floor_eq_on_Ico n x hx
                 -- 🎉 no goals
#align nat.floor_eq_on_Ico' Nat.floor_eq_on_Ico'

@[simp]
theorem preimage_floor_zero : (floor : α → ℕ) ⁻¹' {0} = Iio 1 :=
  ext fun _ => floor_eq_zero
#align nat.preimage_floor_zero Nat.preimage_floor_zero

-- Porting note: in mathlib3 there was no need for the type annotation in `(n:α)`
theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : α → ℕ) ⁻¹' {n} = Ico (n:α) (n + 1) :=
  ext fun _ => floor_eq_iff' hn
#align nat.preimage_floor_of_ne_zero Nat.preimage_floor_of_ne_zero

/-! #### Ceil -/


theorem gc_ceil_coe : GaloisConnection (ceil : α → ℕ) (↑) :=
  FloorSemiring.gc_ceil
#align nat.gc_ceil_coe Nat.gc_ceil_coe

@[simp]
theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
  gc_ceil_coe _ _
#align nat.ceil_le Nat.ceil_le

theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le
#align nat.lt_ceil Nat.lt_ceil

-- porting note: simp can prove this
-- @[simp]
theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : α) < a := by
  rw [← Nat.lt_ceil, Nat.add_one_le_iff]
  -- 🎉 no goals
#align nat.add_one_le_ceil_iff Nat.add_one_le_ceil_iff

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a := by
  rw [← zero_add 1, Nat.add_one_le_ceil_iff, Nat.cast_zero]
  -- 🎉 no goals
#align nat.one_le_ceil_iff Nat.one_le_ceil_iff

theorem ceil_le_floor_add_one (a : α) : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
  rw [ceil_le, Nat.cast_add, Nat.cast_one]
  -- ⊢ a ≤ ↑⌊a⌋₊ + 1
  exact (lt_floor_add_one a).le
  -- 🎉 no goals
#align nat.ceil_le_floor_add_one Nat.ceil_le_floor_add_one

theorem le_ceil (a : α) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl
#align nat.le_ceil Nat.le_ceil

@[simp]
theorem ceil_intCast {α : Type*} [LinearOrderedRing α] [FloorSemiring α] (z : ℤ) :
    ⌈(z : α)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    simp
    -- ⊢ ↑z ≤ ↑a ↔ z ≤ ↑a
    norm_cast
    -- 🎉 no goals
#align nat.ceil_int_cast Nat.ceil_intCast

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]
                                  -- 🎉 no goals
#align nat.ceil_nat_cast Nat.ceil_natCast

theorem ceil_mono : Monotone (ceil : α → ℕ) :=
  gc_ceil_coe.monotone_l
#align nat.ceil_mono Nat.ceil_mono

@[simp]
theorem ceil_zero : ⌈(0 : α)⌉₊ = 0 := by rw [← Nat.cast_zero, ceil_natCast]
                                         -- 🎉 no goals
#align nat.ceil_zero Nat.ceil_zero

@[simp]
theorem ceil_one : ⌈(1 : α)⌉₊ = 1 := by rw [← Nat.cast_one, ceil_natCast]
                                        -- 🎉 no goals
#align nat.ceil_one Nat.ceil_one

@[simp]
theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by rw [← le_zero_iff, ceil_le, Nat.cast_zero]
                                              -- 🎉 no goals
#align nat.ceil_eq_zero Nat.ceil_eq_zero

@[simp]
theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by rw [lt_ceil, cast_zero]
                                          -- 🎉 no goals
#align nat.ceil_pos Nat.ceil_pos

theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)
#align nat.lt_of_ceil_lt Nat.lt_of_ceil_lt

theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n :=
  (le_ceil a).trans (Nat.cast_le.2 h)
#align nat.le_of_ceil_le Nat.le_of_ceil_le

theorem floor_le_ceil (a : α) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  -- ⊢ ⌊a⌋₊ ≤ ⌈a⌉₊
  · rw [floor_of_nonpos ha]
    -- ⊢ 0 ≤ ⌈a⌉₊
    exact Nat.zero_le _
    -- 🎉 no goals
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)
    -- 🎉 no goals
#align nat.floor_le_ceil Nat.floor_le_ceil

theorem floor_lt_ceil_of_lt_of_pos {a b : α} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_lt 0 a with (ha | ha)
  -- ⊢ ⌊a⌋₊ < ⌈b⌉₊
  · rw [floor_lt ha]
    -- ⊢ a < ↑⌈b⌉₊
    exact h.trans_le (le_ceil _)
    -- 🎉 no goals
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]
    -- 🎉 no goals
#align nat.floor_lt_ceil_of_lt_of_pos Nat.floor_lt_ceil_of_lt_of_pos

theorem ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n := by
  rw [← ceil_le, ← not_le, ← ceil_le, not_le,
    tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn)), Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]
#align nat.ceil_eq_iff Nat.ceil_eq_iff

@[simp]
theorem preimage_ceil_zero : (Nat.ceil : α → ℕ) ⁻¹' {0} = Iic 0 :=
  ext fun _ => ceil_eq_zero
#align nat.preimage_ceil_zero Nat.preimage_ceil_zero

-- Porting note: in mathlib3 there was no need for the type annotation in `(↑(n - 1))`
theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : α → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : α) n :=
  ext fun _ => ceil_eq_iff hn
#align nat.preimage_ceil_of_ne_zero Nat.preimage_ceil_of_ne_zero

/-! #### Intervals -/

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Ioo {a b : α} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Ioo a b ↔ x✝ ∈ Ioo ⌊a⌋₊ ⌈b⌉₊
  simp [floor_lt, lt_ceil, ha]
  -- 🎉 no goals
#align nat.preimage_Ioo Nat.preimage_Ioo

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Ico {a b : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Ico a b ↔ x✝ ∈ Ico ⌈a⌉₊ ⌈b⌉₊
  simp [ceil_le, lt_ceil]
  -- 🎉 no goals
#align nat.preimage_Ico Nat.preimage_Ico

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Ioc {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Ioc a b ↔ x✝ ∈ Ioc ⌊a⌋₊ ⌊b⌋₊
  simp [floor_lt, le_floor_iff, hb, ha]
  -- 🎉 no goals
#align nat.preimage_Ioc Nat.preimage_Ioc

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Icc {a b : α} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Icc a b ↔ x✝ ∈ Icc ⌈a⌉₊ ⌊b⌋₊
  simp [ceil_le, hb, le_floor_iff]
  -- 🎉 no goals
#align nat.preimage_Icc Nat.preimage_Icc

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Ioi {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Ioi a ↔ x✝ ∈ Ioi ⌊a⌋₊
  simp [floor_lt, ha]
  -- 🎉 no goals
#align nat.preimage_Ioi Nat.preimage_Ioi

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Ici {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Ici a ↔ x✝ ∈ Ici ⌈a⌉₊
  simp [ceil_le]
  -- 🎉 no goals
#align nat.preimage_Ici Nat.preimage_Ici

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Iio {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Iio a ↔ x✝ ∈ Iio ⌈a⌉₊
  simp [lt_ceil]
  -- 🎉 no goals
#align nat.preimage_Iio Nat.preimage_Iio

-- Porting note: changed `(coe : ℕ → α)` to `(Nat.cast : ℕ → α)`
@[simp]
theorem preimage_Iic {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  -- ⊢ x✝ ∈ Nat.cast ⁻¹' Iic a ↔ x✝ ∈ Iic ⌊a⌋₊
  simp [le_floor_iff, ha]
  -- 🎉 no goals
#align nat.preimage_Iic Nat.preimage_Iic

theorem floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    -- ⊢ ↑b ≤ a + ↑n ↔ b ≤ ⌊a⌋₊ + n
    obtain hb | hb := le_total n b
    -- ⊢ ↑b ≤ a + ↑n ↔ b ≤ ⌊a⌋₊ + n
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      -- ⊢ ↑(n + d) ≤ a + ↑n ↔ n + d ≤ ⌊a⌋₊ + n
      rw [Nat.cast_add, add_comm n, add_comm (n : α), add_le_add_iff_right, add_le_add_iff_right,
        le_floor_iff ha]
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      -- ⊢ ↑b ≤ a + ↑(b + d) ↔ b ≤ ⌊a⌋₊ + (b + d)
      rw [Nat.cast_add, add_left_comm _ b, add_left_comm _ (b : α)]
      -- ⊢ ↑b ≤ ↑b + (a + ↑d) ↔ b ≤ b + (⌊a⌋₊ + d)
      refine' iff_of_true _ le_self_add
      -- ⊢ ↑b ≤ ↑b + (a + ↑d)
      exact le_add_of_nonneg_right <| ha.trans <| le_add_of_nonneg_right d.cast_nonneg
      -- 🎉 no goals
#align nat.floor_add_nat Nat.floor_add_nat

theorem floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  -- Porting note: broken `convert floor_add_nat ha 1`
  rw [←cast_one, floor_add_nat ha 1]
  -- 🎉 no goals
#align nat.floor_add_one Nat.floor_add_one

theorem floor_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + OfNat.ofNat n⌋₊ = ⌊a⌋₊ + OfNat.ofNat n :=
  floor_add_nat ha n

@[simp]
theorem floor_sub_nat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  obtain ha | ha := le_total a 0
  -- ⊢ ⌊a - ↑n⌋₊ = ⌊a⌋₊ - n
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
    -- 🎉 no goals
  cases' le_total a n with h h
  -- ⊢ ⌊a - ↑n⌋₊ = ⌊a⌋₊ - n
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    -- ⊢ ⌊a⌋₊ ≤ n
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
    -- 🎉 no goals
  · rw [eq_tsub_iff_add_eq_of_le (le_floor h), ← floor_add_nat _, tsub_add_cancel_of_le h]
    -- ⊢ 0 ≤ a - ↑n
    exact le_tsub_of_add_le_left ((add_zero _).trans_le h)
    -- 🎉 no goals
#align nat.floor_sub_nat Nat.floor_sub_nat

@[simp]
theorem floor_sub_one [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 := by
  exact_mod_cast floor_sub_nat a 1
  -- 🎉 no goals

@[simp]
theorem floor_sub_ofNat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - OfNat.ofNat n⌋₊ = ⌊a⌋₊ - OfNat.ofNat n :=
  floor_sub_nat a n

theorem ceil_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    rw [← not_lt, ← not_lt, not_iff_not, lt_ceil]
    -- ⊢ ↑b < a + ↑n ↔ b < ⌈a⌉₊ + n
    obtain hb | hb := le_or_lt n b
    -- ⊢ ↑b < a + ↑n ↔ b < ⌈a⌉₊ + n
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      -- ⊢ ↑(n + d) < a + ↑n ↔ n + d < ⌈a⌉₊ + n
      rw [Nat.cast_add, add_comm n, add_comm (n : α), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (lt_add_left _ _ _ hb)
      -- 🎉 no goals
#align nat.ceil_add_nat Nat.ceil_add_nat

theorem ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  -- Porting note: broken `convert ceil_add_nat ha 1`
  rw [cast_one.symm, ceil_add_nat ha 1]
  -- 🎉 no goals
#align nat.ceil_add_one Nat.ceil_add_one

theorem ceil_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + OfNat.ofNat n⌉₊ = ⌈a⌉₊ + OfNat.ofNat n :=
  ceil_add_nat ha n

theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 :=
  lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge
#align nat.ceil_lt_add_one Nat.ceil_lt_add_one

theorem ceil_add_le (a b : α) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [ceil_le, Nat.cast_add]
  -- ⊢ a + b ≤ ↑⌈a⌉₊ + ↑⌈b⌉₊
  exact _root_.add_le_add (le_ceil _) (le_ceil _)
  -- 🎉 no goals
#align nat.ceil_add_le Nat.ceil_add_le

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorSemiring α]

theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋₊ :=
  sub_lt_iff_lt_add.2 <| lt_floor_add_one a
#align nat.sub_one_lt_floor Nat.sub_one_lt_floor

end LinearOrderedRing

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] [FloorSemiring α]

-- TODO: should these lemmas be `simp`? `norm_cast`?

theorem floor_div_nat (a : α) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  cases' le_total a 0 with ha ha
  -- ⊢ ⌊a / ↑n⌋₊ = ⌊a⌋₊ / n
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    -- ⊢ 0 = 0 / n
    · simp
      -- 🎉 no goals
    apply div_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
    -- 🎉 no goals
  obtain rfl | hn := n.eq_zero_or_pos
  -- ⊢ ⌊a / ↑0⌋₊ = ⌊a⌋₊ / 0
  · rw [cast_zero, div_zero, Nat.div_zero, floor_zero]
    -- 🎉 no goals
  refine' (floor_eq_iff _).2 _
  -- ⊢ 0 ≤ a / ↑n
  · exact div_nonneg ha n.cast_nonneg
    -- 🎉 no goals
  constructor
  -- ⊢ ↑(⌊a⌋₊ / n) ≤ a / ↑n
  · exact cast_div_le.trans (div_le_div_of_le_of_nonneg (floor_le ha) n.cast_nonneg)
    -- 🎉 no goals
  rw [div_lt_iff, add_mul, one_mul, ← cast_mul, ← cast_add, ← floor_lt ha]
  -- ⊢ ⌊a⌋₊ < ⌊a⌋₊ / n * n + n
  · exact lt_div_mul_add hn
    -- 🎉 no goals
  · exact cast_pos.2 hn
    -- 🎉 no goals
#align nat.floor_div_nat Nat.floor_div_nat

theorem floor_div_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / OfNat.ofNat n⌋₊ = ⌊a⌋₊ / OfNat.ofNat n :=
  floor_div_nat a n

/-- Natural division is the floor of field division. -/
theorem floor_div_eq_div (m n : ℕ) : ⌊(m : α) / n⌋₊ = m / n := by
  convert floor_div_nat (m : α) n
  -- ⊢ m = ⌊↑m⌋₊
  rw [m.floor_coe]
  -- 🎉 no goals
#align nat.floor_div_eq_div Nat.floor_div_eq_div

end LinearOrderedSemifield

end Nat

/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
theorem subsingleton_floorSemiring {α} [LinearOrderedSemiring α] :
    Subsingleton (FloorSemiring α) := by
  refine' ⟨fun H₁ H₂ => _⟩
  -- ⊢ H₁ = H₂
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  -- ⊢ H₁ = H₂
  have : H₁.floor = H₂.floor := by
    ext a
    cases' lt_or_le a 0 with h h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine' eq_of_forall_le_iff fun n => _
      rw [H₁.gc_floor, H₂.gc_floor] <;> exact h
  cases H₁
  -- ⊢ { floor := floor✝, ceil := ceil✝, floor_of_neg := floor_of_neg✝, gc_floor := …
  cases H₂
  -- ⊢ { floor := floor✝¹, ceil := ceil✝¹, floor_of_neg := floor_of_neg✝¹, gc_floor …
  congr
  -- 🎉 no goals
#align subsingleton_floor_semiring subsingleton_floorSemiring

/-! ### Floor rings -/

/-- A `FloorRing` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)`.
-/
class FloorRing (α) [LinearOrderedRing α] where
  /-- `FloorRing.floor a` computes the greatest integer `z` such that `(z : α) ≤ a`.-/
  floor : α → ℤ
  /-- `FloorRing.ceil a` computes the least integer `z` such that `a ≤ (z : α)`.-/
  ceil : α → ℤ
  /-- `FloorRing.ceil` is the upper adjoint of the coercion `↑ : ℤ → α`.-/
  gc_coe_floor : GaloisConnection (↑) floor
  /-- `FloorRing.ceil` is the lower adjoint of the coercion `↑ : ℤ → α`.-/
  gc_ceil_coe : GaloisConnection ceil (↑)
#align floor_ring FloorRing

instance : FloorRing ℤ where
  floor := id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]
    -- ⊢ a ≤ b ↔ a ≤ id b
    rfl
    -- 🎉 no goals
  gc_ceil_coe a b := by
    rw [Int.cast_id]
    -- ⊢ id a ≤ b ↔ a ≤ b
    rfl
    -- 🎉 no goals

/-- A `FloorRing` constructor from the `floor` function alone. -/
def FloorRing.ofFloor (α) [LinearOrderedRing α] (floor : α → ℤ)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }
                                 -- 🎉 no goals
#align floor_ring.of_floor FloorRing.ofFloor

/-- A `FloorRing` constructor from the `ceil` function alone. -/
def FloorRing.ofCeil (α) [LinearOrderedRing α] (ceil : α → ℤ)
    (gc_ceil_coe : GaloisConnection ceil (↑)) : FloorRing α :=
  { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
                                  -- 🎉 no goals
    gc_ceil_coe }
#align floor_ring.of_ceil FloorRing.ofCeil

namespace Int

variable [LinearOrderedRing α] [FloorRing α] {z : ℤ} {a : α}

/-- `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → ℤ :=
  FloorRing.floor
#align int.floor Int.floor

/-- `Int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil : α → ℤ :=
  FloorRing.ceil
#align int.ceil Int.ceil

/-- `Int.fract a`, the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α :=
  a - floor a
#align int.fract Int.fract

@[simp]
theorem floor_int : (Int.floor : ℤ → ℤ) = id :=
  rfl
#align int.floor_int Int.floor_int

@[simp]
theorem ceil_int : (Int.ceil : ℤ → ℤ) = id :=
  rfl
#align int.ceil_int Int.ceil_int

@[simp]
theorem fract_int : (Int.fract : ℤ → ℤ) = 0 :=
  funext fun x => by simp [fract]
                     -- 🎉 no goals
#align int.fract_int Int.fract_int

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.
@[simp]
theorem floorRing_floor_eq : @FloorRing.floor = @Int.floor :=
  rfl
#align int.floor_ring_floor_eq Int.floorRing_floor_eq

@[simp]
theorem floorRing_ceil_eq : @FloorRing.ceil = @Int.ceil :=
  rfl
#align int.floor_ring_ceil_eq Int.floorRing_ceil_eq

/-! #### Floor -/


-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
theorem gc_coe_floor : GaloisConnection (Int.cast : ℤ → α) floor :=
  FloorRing.gc_coe_floor
#align int.gc_coe_floor Int.gc_coe_floor

theorem le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a :=
  (gc_coe_floor z a).symm
#align int.le_floor Int.le_floor

theorem floor_lt : ⌊a⌋ < z ↔ a < z :=
  lt_iff_lt_of_le_iff_le le_floor
#align int.floor_lt Int.floor_lt

theorem floor_le (a : α) : (⌊a⌋ : α) ≤ a :=
  gc_coe_floor.l_u_le a
#align int.floor_le Int.floor_le

theorem floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := by rw [le_floor, Int.cast_zero]
                                             -- 🎉 no goals
#align int.floor_nonneg Int.floor_nonneg

@[simp]
theorem floor_le_sub_one_iff : ⌊a⌋ ≤ z - 1 ↔ a < z := by rw [← floor_lt, le_sub_one_iff]
                                                         -- 🎉 no goals
#align int.floor_le_sub_one_iff Int.floor_le_sub_one_iff

@[simp]
theorem floor_le_neg_one_iff : ⌊a⌋ ≤ -1 ↔ a < 0 := by
  rw [← zero_sub (1 : ℤ), floor_le_sub_one_iff, cast_zero]
  -- 🎉 no goals
#align int.floor_le_neg_one_iff Int.floor_le_neg_one_iff

theorem floor_nonpos (ha : a ≤ 0) : ⌊a⌋ ≤ 0 := by
  rw [← @cast_le α, Int.cast_zero]
  -- ⊢ ↑⌊a⌋ ≤ 0
  exact (floor_le a).trans ha
  -- 🎉 no goals
#align int.floor_nonpos Int.floor_nonpos

theorem lt_succ_floor (a : α) : a < ⌊a⌋.succ :=
  floor_lt.1 <| Int.lt_succ_self _
#align int.lt_succ_floor Int.lt_succ_floor

@[simp]
theorem lt_floor_add_one (a : α) : a < ⌊a⌋ + 1 := by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a
  -- 🎉 no goals
#align int.lt_floor_add_one Int.lt_floor_add_one

@[simp]
theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋ :=
  sub_lt_iff_lt_add.2 (lt_floor_add_one a)
#align int.sub_one_lt_floor Int.sub_one_lt_floor

@[simp]
theorem floor_intCast (z : ℤ) : ⌊(z : α)⌋ = z :=
  eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]
                                  -- 🎉 no goals
#align int.floor_int_cast Int.floor_intCast

@[simp]
theorem floor_natCast (n : ℕ) : ⌊(n : α)⌋ = n :=
  eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_ofNat, cast_le]
                                  -- 🎉 no goals
#align int.floor_nat_cast Int.floor_natCast

@[simp]
theorem floor_zero : ⌊(0 : α)⌋ = 0 := by rw [← cast_zero, floor_intCast]
                                         -- 🎉 no goals
#align int.floor_zero Int.floor_zero

@[simp]
theorem floor_one : ⌊(1 : α)⌋ = 1 := by rw [← cast_one, floor_intCast]
                                        -- 🎉 no goals
#align int.floor_one Int.floor_one

@[simp] theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(OfNat.ofNat n : α)⌋ = n := floor_natCast n

@[mono]
theorem floor_mono : Monotone (floor : α → ℤ) :=
  gc_coe_floor.monotone_u
#align int.floor_mono Int.floor_mono

theorem floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a := by
  -- Porting note: broken `convert le_floor`
  rw [Int.lt_iff_add_one_le, zero_add, le_floor, cast_one]
  -- 🎉 no goals
#align int.floor_pos Int.floor_pos

@[simp]
theorem floor_add_int (a : α) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor, ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, Int.cast_sub]
    -- 🎉 no goals
#align int.floor_add_int Int.floor_add_int

@[simp]
theorem floor_add_one (a : α) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by
  -- Porting note: broken `convert floor_add_int a 1`
  rw [← cast_one, floor_add_int]
  -- 🎉 no goals
#align int.floor_add_one Int.floor_add_one

theorem le_floor_add (a b : α) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  rw [le_floor, Int.cast_add]
  -- ⊢ ↑⌊a⌋ + ↑⌊b⌋ ≤ a + b
  exact add_le_add (floor_le _) (floor_le _)
  -- 🎉 no goals
#align int.le_floor_add Int.le_floor_add

theorem le_floor_add_floor (a b : α) : ⌊a + b⌋ - 1 ≤ ⌊a⌋ + ⌊b⌋ := by
  rw [← sub_le_iff_le_add, le_floor, Int.cast_sub, sub_le_comm, Int.cast_sub, Int.cast_one]
  -- ⊢ ↑⌊a + b⌋ - 1 - a ≤ ↑⌊b⌋
  refine' le_trans _ (sub_one_lt_floor _).le
  -- ⊢ ↑⌊a + b⌋ - 1 - a ≤ b - 1
  rw [sub_le_iff_le_add', ← add_sub_assoc, sub_le_sub_iff_right]
  -- ⊢ ↑⌊a + b⌋ ≤ a + b
  exact floor_le _
  -- 🎉 no goals
#align int.le_floor_add_floor Int.le_floor_add_floor

@[simp]
theorem floor_int_add (z : ℤ) (a : α) : ⌊↑z + a⌋ = z + ⌊a⌋ := by
  simpa only [add_comm] using floor_add_int a z
  -- 🎉 no goals
#align int.floor_int_add Int.floor_int_add

@[simp]
theorem floor_add_nat (a : α) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := by rw [← Int.cast_ofNat, floor_add_int]
                                                                -- 🎉 no goals
#align int.floor_add_nat Int.floor_add_nat

@[simp]
theorem floor_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + OfNat.ofNat n⌋ = ⌊a⌋ + OfNat.ofNat n :=
  floor_add_nat a n

@[simp]
theorem floor_nat_add (n : ℕ) (a : α) : ⌊↑n + a⌋ = n + ⌊a⌋ := by
  rw [← Int.cast_ofNat, floor_int_add]
  -- 🎉 no goals
#align int.floor_nat_add Int.floor_nat_add

@[simp]
theorem floor_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) :
    ⌊OfNat.ofNat n + a⌋ = OfNat.ofNat n + ⌊a⌋ :=
  floor_nat_add n a

@[simp]
theorem floor_sub_int (a : α) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)
               -- 🎉 no goals
#align int.floor_sub_int Int.floor_sub_int

@[simp]
theorem floor_sub_nat (a : α) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := by rw [← Int.cast_ofNat, floor_sub_int]
                                                                -- 🎉 no goals
#align int.floor_sub_nat Int.floor_sub_nat

@[simp] theorem floor_sub_one (a : α) : ⌊a - 1⌋ = ⌊a⌋ - 1 := by exact_mod_cast floor_sub_nat a 1
                                                                -- 🎉 no goals

@[simp]
theorem floor_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - OfNat.ofNat n⌋ = ⌊a⌋ - OfNat.ofNat n :=
  floor_sub_nat a n

theorem abs_sub_lt_one_of_floor_eq_floor {α : Type*} [LinearOrderedCommRing α] [FloorRing α]
    {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  have : a < ⌊a⌋ + 1 := lt_floor_add_one a
  -- ⊢ |a - b| < 1
  have : b < ⌊b⌋ + 1 := lt_floor_add_one b
  -- ⊢ |a - b| < 1
  have : (⌊a⌋ : α) = ⌊b⌋ := Int.cast_inj.2 h
  -- ⊢ |a - b| < 1
  have : (⌊a⌋ : α) ≤ a := floor_le a
  -- ⊢ |a - b| < 1
  have : (⌊b⌋ : α) ≤ b := floor_le b
  -- ⊢ |a - b| < 1
  exact abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  -- 🎉 no goals
#align int.abs_sub_lt_one_of_floor_eq_floor Int.abs_sub_lt_one_of_floor_eq_floor

theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 := by
  rw [le_antisymm_iff, le_floor, ← Int.lt_add_one_iff, floor_lt, Int.cast_add, Int.cast_one,
    and_comm]
#align int.floor_eq_iff Int.floor_eq_iff

@[simp]
theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a ∈ Ico (0 : α) 1 := by simp [floor_eq_iff]
                                                              -- 🎉 no goals
#align int.floor_eq_zero_iff Int.floor_eq_zero_iff

theorem floor_eq_on_Ico (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩
#align int.floor_eq_on_Ico Int.floor_eq_on_Ico

theorem floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), (⌊a⌋ : α) = n := fun a ha =>
  congr_arg _ <| floor_eq_on_Ico n a ha
#align int.floor_eq_on_Ico' Int.floor_eq_on_Ico'

-- Porting note: in mathlib3 there was no need for the type annotation in `(m:α)`
@[simp]
theorem preimage_floor_singleton (m : ℤ) : (floor : α → ℤ) ⁻¹' {m} = Ico (m : α) (m + 1) :=
  ext fun _ => floor_eq_iff
#align int.preimage_floor_singleton Int.preimage_floor_singleton

/-! #### Fractional part -/


@[simp]
theorem self_sub_floor (a : α) : a - ⌊a⌋ = fract a :=
  rfl
#align int.self_sub_floor Int.self_sub_floor

@[simp]
theorem floor_add_fract (a : α) : (⌊a⌋ : α) + fract a = a :=
  add_sub_cancel'_right _ _
#align int.floor_add_fract Int.floor_add_fract

@[simp]
theorem fract_add_floor (a : α) : fract a + ⌊a⌋ = a :=
  sub_add_cancel _ _
#align int.fract_add_floor Int.fract_add_floor

@[simp]
theorem fract_add_int (a : α) (m : ℤ) : fract (a + m) = fract a := by
  rw [fract]
  -- ⊢ a + ↑m - ↑⌊a + ↑m⌋ = fract a
  simp
  -- 🎉 no goals
#align int.fract_add_int Int.fract_add_int

@[simp]
theorem fract_add_nat (a : α) (m : ℕ) : fract (a + m) = fract a := by
  rw [fract]
  -- ⊢ a + ↑m - ↑⌊a + ↑m⌋ = fract a
  simp
  -- 🎉 no goals
#align int.fract_add_nat Int.fract_add_nat

@[simp]
theorem fract_add_one (a : α) : fract (a + 1) = fract a := by exact_mod_cast fract_add_nat a 1
                                                              -- 🎉 no goals

@[simp]
theorem fract_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] : fract (a + OfNat.ofNat n) = fract a :=
  fract_add_nat a n

@[simp]
theorem fract_int_add (m : ℤ) (a : α) : fract (↑m + a) = fract a := by rw [add_comm, fract_add_int]
                                                                       -- 🎉 no goals
#align int.fract_int_add Int.fract_int_add

@[simp]
theorem fract_nat_add (n : ℕ) (a : α) : fract (↑n + a) = fract a := by rw [add_comm, fract_add_nat]
                                                                       -- 🎉 no goals

@[simp]
theorem fract_one_add (a : α) : fract (1 + a) = fract a := by exact_mod_cast fract_nat_add 1 a
                                                              -- 🎉 no goals

@[simp]
theorem fract_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) : fract (OfNat.ofNat n + a) = fract a :=
  fract_nat_add n a

@[simp]
theorem fract_sub_int (a : α) (m : ℤ) : fract (a - m) = fract a := by
  rw [fract]
  -- ⊢ a - ↑m - ↑⌊a - ↑m⌋ = fract a
  simp
  -- 🎉 no goals
#align int.fract_sub_int Int.fract_sub_int

@[simp]
theorem fract_sub_nat (a : α) (n : ℕ) : fract (a - n) = fract a := by
  rw [fract]
  -- ⊢ a - ↑n - ↑⌊a - ↑n⌋ = fract a
  simp
  -- 🎉 no goals
#align int.fract_sub_nat Int.fract_sub_nat

@[simp]
theorem fract_sub_one (a : α) : fract (a - 1) = fract a := by exact_mod_cast fract_sub_nat a 1
                                                              -- 🎉 no goals

@[simp]
theorem fract_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] : fract (a - OfNat.ofNat n) = fract a :=
  fract_sub_nat a n

-- Was a duplicate lemma under a bad name
#align int.fract_int_nat Int.fract_int_add

theorem fract_add_le (a b : α) : fract (a + b) ≤ fract a + fract b := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_le_sub_iff_left, ← Int.cast_add, Int.cast_le]
  -- ⊢ ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋
  exact le_floor_add _ _
  -- 🎉 no goals
#align int.fract_add_le Int.fract_add_le

theorem fract_add_fract_le (a b : α) : fract a + fract b ≤ fract (a + b) + 1 := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_add, sub_le_sub_iff_left]
  -- ⊢ ↑⌊a + b⌋ - 1 ≤ ↑⌊a⌋ + ↑⌊b⌋
  exact_mod_cast le_floor_add_floor a b
  -- 🎉 no goals
#align int.fract_add_fract_le Int.fract_add_fract_le

@[simp]
theorem self_sub_fract (a : α) : a - fract a = ⌊a⌋ :=
  sub_sub_cancel _ _
#align int.self_sub_fract Int.self_sub_fract

@[simp]
theorem fract_sub_self (a : α) : fract a - a = -⌊a⌋ :=
  sub_sub_cancel_left _ _
#align int.fract_sub_self Int.fract_sub_self

@[simp]
theorem fract_nonneg (a : α) : 0 ≤ fract a :=
  sub_nonneg.2 <| floor_le _
#align int.fract_nonneg Int.fract_nonneg

/-- The fractional part of `a` is positive if and only if `a ≠ ⌊a⌋`. -/
lemma fract_pos : 0 < fract a ↔ a ≠ ⌊a⌋ :=
  (fract_nonneg a).lt_iff_ne.trans $ ne_comm.trans sub_ne_zero
#align int.fract_pos Int.fract_pos

theorem fract_lt_one (a : α) : fract a < 1 :=
  sub_lt_comm.1 <| sub_one_lt_floor _
#align int.fract_lt_one Int.fract_lt_one

@[simp]
theorem fract_zero : fract (0 : α) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]
                                             -- 🎉 no goals
#align int.fract_zero Int.fract_zero

@[simp]
theorem fract_one : fract (1 : α) = 0 := by simp [fract]
                                            -- 🎉 no goals
#align int.fract_one Int.fract_one

theorem abs_fract : |fract a| = fract a :=
  abs_eq_self.mpr <| fract_nonneg a
#align int.abs_fract Int.abs_fract

@[simp]
theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a :=
  abs_eq_self.mpr <| sub_nonneg.mpr (fract_lt_one a).le
#align int.abs_one_sub_fract Int.abs_one_sub_fract

@[simp]
theorem fract_intCast (z : ℤ) : fract (z : α) = 0 := by
  unfold fract
  -- ⊢ ↑z - ↑⌊↑z⌋ = 0
  rw [floor_intCast]
  -- ⊢ ↑z - ↑z = 0
  exact sub_self _
  -- 🎉 no goals
#align int.fract_int_cast Int.fract_intCast

@[simp]
theorem fract_natCast (n : ℕ) : fract (n : α) = 0 := by simp [fract]
                                                        -- 🎉 no goals
#align int.fract_nat_cast Int.fract_natCast

@[simp]
theorem fract_ofNat (n : ℕ) [n.AtLeastTwo] : fract (OfNat.ofNat n : α) = 0 := fract_natCast n

-- porting note: simp can prove this
-- @[simp]
theorem fract_floor (a : α) : fract (⌊a⌋ : α) = 0 :=
  fract_intCast _
#align int.fract_floor Int.fract_floor

@[simp]
theorem floor_fract (a : α) : ⌊fract a⌋ = 0 := by
  rw [floor_eq_iff, Int.cast_zero, zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩
  -- ⊢ 0 ≤ fract a ∧ fract a < 1
                                              -- 🎉 no goals
#align int.floor_fract Int.floor_fract

theorem fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
  ⟨fun h => by
    rw [← h]
    -- ⊢ 0 ≤ fract a ∧ fract a < 1 ∧ ∃ z, a - fract a = ↑z
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
    -- 🎉 no goals
   by
    rintro ⟨h₀, h₁, z, hz⟩
    -- ⊢ fract a = b
    rw [← self_sub_floor, eq_comm, eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq, hz,
      Int.cast_inj, floor_eq_iff, ← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩
    -- ⊢ a - b ≤ a
                    -- 🎉 no goals
                    -- 🎉 no goals
#align int.fract_eq_iff Int.fract_eq_iff

theorem fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
  ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
                           -- ⊢ a - b = ↑(⌊a⌋ - ⌊b⌋)
                                              -- 🎉 no goals
   by
    rintro ⟨z, hz⟩
    -- ⊢ fract a = fract b
    refine' fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, _⟩
    -- ⊢ a - fract b = ↑(z + ⌊b⌋)
    rw [eq_add_of_sub_eq hz, add_comm, Int.cast_add]
    -- ⊢ b + ↑z - fract b = ↑z + ↑⌊b⌋
    exact add_sub_sub_cancel _ _ _⟩
    -- 🎉 no goals
#align int.fract_eq_fract Int.fract_eq_fract

@[simp]
theorem fract_eq_self {a : α} : fract a = a ↔ 0 ≤ a ∧ a < 1 :=
  fract_eq_iff.trans <| and_assoc.symm.trans <| and_iff_left ⟨0, by simp⟩
                                                                    -- 🎉 no goals
#align int.fract_eq_self Int.fract_eq_self

@[simp]
theorem fract_fract (a : α) : fract (fract a) = fract a :=
  fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩
#align int.fract_fract Int.fract_fract

theorem fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
  ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by
    unfold fract
    -- ⊢ a + b - ↑⌊a + b⌋ - (a - ↑⌊a⌋) - (b - ↑⌊b⌋) = ↑(⌊a⌋ + ⌊b⌋ - ⌊a + b⌋)
    simp [sub_eq_add_neg]
    -- ⊢ a + b + -↑⌊a + b⌋ + (↑⌊a⌋ + -a) + (↑⌊b⌋ + -b) = ↑⌊a⌋ + ↑⌊b⌋ + -↑⌊a + b⌋
    abel⟩
    -- 🎉 no goals
    -- 🎉 no goals
#align int.fract_add Int.fract_add

theorem fract_neg {x : α} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  -- ⊢ 0 ≤ 1 - fract x ∧ 1 - fract x < 1 ∧ ∃ z, -x - (1 - fract x) = ↑z
  constructor
  -- ⊢ 0 ≤ 1 - fract x
  · rw [le_sub_iff_add_le, zero_add]
    -- ⊢ fract x ≤ 1
    exact (fract_lt_one x).le
    -- 🎉 no goals
  refine' ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, _⟩
  -- ⊢ -x - (1 - fract x) = ↑(-⌊x⌋ - 1)
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  -- ⊢ -x + fract x = -↑⌊x⌋
  conv in -x => rw [← floor_add_fract x]
  -- ⊢ -(↑⌊x⌋ + fract x) + fract x = -↑⌊x⌋
  simp [-floor_add_fract]
  -- 🎉 no goals
#align int.fract_neg Int.fract_neg

@[simp]
theorem fract_neg_eq_zero {x : α} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and_iff]
  -- ⊢ (∃ z, -x = ↑z) ↔ ∃ z, x = ↑z
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]
  -- ⊢ (∃ z, -x = ↑z) → ∃ z, x = ↑z
                  -- ⊢ ∃ z, x = ↑z
                  -- ⊢ ∃ z, -x = ↑z
                                     -- ⊢ x = ↑(-z)
                                     -- ⊢ -x = ↑(-z)
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align int.fract_neg_eq_zero Int.fract_neg_eq_zero

theorem fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by
  induction' b with c hc
  -- ⊢ ∃ z, fract a * ↑Nat.zero - fract (a * ↑Nat.zero) = ↑z
  · use 0; simp
    -- ⊢ fract a * ↑Nat.zero - fract (a * ↑Nat.zero) = ↑0
           -- 🎉 no goals
  · rcases hc with ⟨z, hz⟩
    -- ⊢ ∃ z, fract a * ↑(Nat.succ c) - fract (a * ↑(Nat.succ c)) = ↑z
    rw [Nat.succ_eq_add_one, Nat.cast_add, mul_add, mul_add, Nat.cast_one, mul_one, mul_one]
    -- ⊢ ∃ z, fract a * ↑c + fract a - fract (a * ↑c + a) = ↑z
    rcases fract_add (a * c) a with ⟨y, hy⟩
    -- ⊢ ∃ z, fract a * ↑c + fract a - fract (a * ↑c + a) = ↑z
    use z - y
    -- ⊢ fract a * ↑c + fract a - fract (a * ↑c + a) = ↑(z - y)
    rw [Int.cast_sub, ← hz, ← hy]
    -- ⊢ fract a * ↑c + fract a - fract (a * ↑c + a) = fract a * ↑c - fract (a * ↑c)  …
    abel
    -- 🎉 no goals
    -- 🎉 no goals
#align int.fract_mul_nat Int.fract_mul_nat

-- Porting note: in mathlib3 there was no need for the type annotation in `(m:α)`
theorem preimage_fract (s : Set α) :
    fract ⁻¹' s = ⋃ m : ℤ, (fun x => x - (m:α)) ⁻¹' (s ∩ Ico (0 : α) 1) := by
  ext x
  -- ⊢ x ∈ fract ⁻¹' s ↔ x ∈ ⋃ (m : ℤ), (fun x => x - ↑m) ⁻¹' (s ∩ Ico 0 1)
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  -- ⊢ fract x ∈ s ↔ ∃ i, x - ↑i ∈ s ∧ x - ↑i ∈ Ico 0 1
  refine' ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, _⟩
  -- ⊢ (∃ i, x - ↑i ∈ s ∧ x - ↑i ∈ Ico 0 1) → fract x ∈ s
  rintro ⟨m, hms, hm0, hm1⟩
  -- ⊢ fract x ∈ s
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  -- ⊢ fract x ∈ s
  exact hms
  -- 🎉 no goals
#align int.preimage_fract Int.preimage_fract

theorem image_fract (s : Set α) : fract '' s = ⋃ m : ℤ, (fun x : α => x - m) '' s ∩ Ico 0 1 := by
  ext x
  -- ⊢ x ∈ fract '' s ↔ x ∈ ⋃ (m : ℤ), (fun x => x - ↑m) '' s ∩ Ico 0 1
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  -- ⊢ (∃ x_1, x_1 ∈ s ∧ fract x_1 = x) ↔ ∃ i, (∃ x_1, x_1 ∈ s ∧ x_1 - ↑i = x) ∧ x  …
                                                    -- ⊢ (∃ x_1, x_1 ∈ s ∧ fract x_1 = x) → ∃ i, (∃ x_1, x_1 ∈ s ∧ x_1 - ↑i = x) ∧ x  …
  · rintro ⟨y, hy, rfl⟩
    -- ⊢ ∃ i, (∃ x, x ∈ s ∧ x - ↑i = fract y) ∧ fract y ∈ Ico 0 1
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
    -- 🎉 no goals
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    -- ⊢ ∃ x, x ∈ s ∧ fract x = y - ↑m
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    -- ⊢ ∃ x, x ∈ s ∧ fract x = y - ↑⌊y⌋
    exact ⟨y, hys, rfl⟩
    -- 🎉 no goals
#align int.image_fract Int.image_fract

section LinearOrderedField

variable {k : Type*} [LinearOrderedField k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a :=
  ⟨(zero_le_mul_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩
#align int.fract_div_mul_self_mem_Ico Int.fract_div_mul_self_mem_Ico

theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a ≠ 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul, ← add_mul, fract_add_floor, div_mul_cancel b ha]
  -- 🎉 no goals
#align int.fract_div_mul_self_add_zsmul_eq Int.fract_div_mul_self_add_zsmul_eq

theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 ≤ a - ⌊a / b⌋ * b :=
  sub_nonneg_of_le <| (le_div_iff hb).1 <| floor_le _
#align int.sub_floor_div_mul_nonneg Int.sub_floor_div_mul_nonneg

theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
  sub_lt_iff_lt_add.2 <| by
    -- Porting note: `← one_add_mul` worked in mathlib3 without the argument
    rw [← one_add_mul _ b, ← div_lt_iff hb, add_comm]
    -- ⊢ a / b < ↑⌊a / b⌋ + 1
    exact lt_floor_add_one _
    -- 🎉 no goals
#align int.sub_floor_div_mul_lt Int.sub_floor_div_mul_lt

theorem fract_div_natCast_eq_div_natCast_mod {m n : ℕ} : fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ fract (↑m / ↑0) = ↑(m % 0) / ↑0
  · simp
    -- 🎉 no goals
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
    -- 🎉 no goals
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
    -- 🎉 no goals
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel' _ hn'.ne', mul_add,
      mul_div_cancel' _ hn'.ne']
    norm_cast
    -- ⊢ ↑m = ↑(m % n) + ↑(n * (m / n))
    rw [← Nat.cast_add, Nat.mod_add_div m n]
    -- 🎉 no goals
#align int.fract_div_nat_cast_eq_div_nat_cast_mod Int.fract_div_natCast_eq_div_natCast_mod

-- TODO Generalise this to allow `n : ℤ` using `Int.fmod` instead of `Int.mod`.
theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ fract (↑m / ↑0) = ↑(m % ↑0) / ↑0
  · simp
    -- 🎉 no goals
  replace hn : 0 < (n : k)
  -- ⊢ 0 < ↑n
  · norm_cast
    -- 🎉 no goals
  have : ∀ {l : ℤ}, 0 ≤ l → fract ((l : k) / n) = ↑(l % n) / n := by
    intros l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_ofNat, ← coe_nat_mod, cast_ofNat, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, coe_nat_nonpos_iff] at hl
      simp [hl, zero_mod]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  -- ⊢ fract (↑↑m₀ / ↑n) = ↑(↑m₀ % ↑n) / ↑n
  · exact this (ofNat_nonneg m₀)
    -- 🎉 no goals
  let q := ⌈↑m₀ / (n : k)⌉
  -- ⊢ fract (↑(-↑m₀) / ↑n) = ↑(-↑m₀ % ↑n) / ↑n
  let m₁ := q * ↑n - (↑m₀ : ℤ)
  -- ⊢ fract (↑(-↑m₀) / ↑n) = ↑(-↑m₀ % ↑n) / ↑n
  have hm₁ : 0 ≤ m₁ := by
    simpa [← @cast_le k, ← div_le_iff hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : ℤ)) : k) / (n : k))
      -- Porting note: the `rw [cast_neg, cast_ofNat]` was `push_cast`
      = fract (-(m₀ : k) / n) := by rw [cast_neg, cast_ofNat]
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : ℤ)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : ℤ) % ↑n) / Nat.cast n := ?_

  · rw [← fract_int_add q, ← mul_div_cancel (q : k) (ne_of_gt hn), ← add_div, ← sub_eq_add_neg]
    -- ⊢ fract ((↑q * ↑n - ↑m₀) / ↑n) = fract (↑m₁ / ↑n)
    -- Porting note: the `simp` was `push_cast`
    simp
    -- 🎉 no goals
  · congr 2
    -- ⊢ m₁ % ↑n = -↑m₀ % ↑n
    change (q * ↑n - (↑m₀ : ℤ)) % ↑n = _
    -- ⊢ (q * ↑n - ↑m₀) % ↑n = -↑m₀ % ↑n
    rw [sub_eq_add_neg, add_comm (q * ↑n), add_mul_emod_self]
    -- 🎉 no goals
#align int.fract_div_int_cast_eq_div_int_cast_mod Int.fract_div_intCast_eq_div_intCast_mod

end LinearOrderedField

/-! #### Ceil -/


-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
theorem gc_ceil_coe : GaloisConnection ceil (Int.cast : ℤ → α) :=
  FloorRing.gc_ceil_coe
#align int.gc_ceil_coe Int.gc_ceil_coe

theorem ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z :=
  gc_ceil_coe a z
#align int.ceil_le Int.ceil_le

theorem floor_neg : ⌊-a⌋ = -⌈a⌉ :=
  eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]
                                  -- 🎉 no goals
#align int.floor_neg Int.floor_neg

theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
  eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]
                                  -- 🎉 no goals
#align int.ceil_neg Int.ceil_neg

theorem lt_ceil : z < ⌈a⌉ ↔ (z : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le
#align int.lt_ceil Int.lt_ceil

@[simp]
theorem add_one_le_ceil_iff : z + 1 ≤ ⌈a⌉ ↔ (z : α) < a := by rw [← lt_ceil, add_one_le_iff]
                                                              -- 🎉 no goals
#align int.add_one_le_ceil_iff Int.add_one_le_ceil_iff

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉ ↔ 0 < a := by
  rw [← zero_add (1 : ℤ), add_one_le_ceil_iff, cast_zero]
  -- 🎉 no goals
#align int.one_le_ceil_iff Int.one_le_ceil_iff

theorem ceil_le_floor_add_one (a : α) : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
  rw [ceil_le, Int.cast_add, Int.cast_one]
  -- ⊢ a ≤ ↑⌊a⌋ + 1
  exact (lt_floor_add_one a).le
  -- 🎉 no goals
#align int.ceil_le_floor_add_one Int.ceil_le_floor_add_one

theorem le_ceil (a : α) : a ≤ ⌈a⌉ :=
  gc_ceil_coe.le_u_l a
#align int.le_ceil Int.le_ceil

@[simp]
theorem ceil_intCast (z : ℤ) : ⌈(z : α)⌉ = z :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]
                                  -- 🎉 no goals
#align int.ceil_int_cast Int.ceil_intCast

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_ofNat, cast_le]
                                  -- 🎉 no goals
#align int.ceil_nat_cast Int.ceil_natCast

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(OfNat.ofNat n : α)⌉ = n := ceil_natCast n

theorem ceil_mono : Monotone (ceil : α → ℤ) :=
  gc_ceil_coe.monotone_l
#align int.ceil_mono Int.ceil_mono

@[simp]
theorem ceil_add_int (a : α) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z := by
  rw [← neg_inj, neg_add', ← floor_neg, ← floor_neg, neg_add', floor_sub_int]
  -- 🎉 no goals
#align int.ceil_add_int Int.ceil_add_int

@[simp]
theorem ceil_add_nat (a : α) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n := by rw [← Int.cast_ofNat, ceil_add_int]
                                                               -- 🎉 no goals
#align int.ceil_add_nat Int.ceil_add_nat

@[simp]
theorem ceil_add_one (a : α) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by
  -- Porting note: broken `convert ceil_add_int a (1 : ℤ)`
  rw [←ceil_add_int a (1 : ℤ), cast_one]
  -- 🎉 no goals
#align int.ceil_add_one Int.ceil_add_one

@[simp]
theorem ceil_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] : ⌈a + OfNat.ofNat n⌉ = ⌈a⌉ + OfNat.ofNat n :=
  ceil_add_nat a n

@[simp]
theorem ceil_sub_int (a : α) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)
               -- 🎉 no goals
#align int.ceil_sub_int Int.ceil_sub_int

@[simp]
theorem ceil_sub_nat (a : α) (n : ℕ) : ⌈a - n⌉ = ⌈a⌉ - n := by
  convert ceil_sub_int a n using 1
  -- ⊢ ⌈a - ↑n⌉ = ⌈a - ↑↑n⌉
  simp
  -- 🎉 no goals
#align int.ceil_sub_nat Int.ceil_sub_nat

@[simp]
theorem ceil_sub_one (a : α) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by
  rw [eq_sub_iff_add_eq, ← ceil_add_one, sub_add_cancel]
  -- 🎉 no goals
#align int.ceil_sub_one Int.ceil_sub_one

@[simp]
theorem ceil_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] : ⌈a - OfNat.ofNat n⌉ = ⌈a⌉ - OfNat.ofNat n :=
  ceil_sub_nat a n

theorem ceil_lt_add_one (a : α) : (⌈a⌉ : α) < a + 1 := by
  rw [← lt_ceil, ← Int.cast_one, ceil_add_int]
  -- ⊢ ⌈a⌉ < ⌈a⌉ + 1
  apply lt_add_one
  -- 🎉 no goals
#align int.ceil_lt_add_one Int.ceil_lt_add_one

theorem ceil_add_le (a b : α) : ⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉ := by
  rw [ceil_le, Int.cast_add]
  -- ⊢ a + b ≤ ↑⌈a⌉ + ↑⌈b⌉
  exact add_le_add (le_ceil _) (le_ceil _)
  -- 🎉 no goals
#align int.ceil_add_le Int.ceil_add_le

theorem ceil_add_ceil_le (a b : α) : ⌈a⌉ + ⌈b⌉ ≤ ⌈a + b⌉ + 1 := by
  rw [← le_sub_iff_add_le, ceil_le, Int.cast_sub, Int.cast_add, Int.cast_one, le_sub_comm]
  -- ⊢ ↑⌈b⌉ ≤ ↑⌈a + b⌉ + 1 - a
  refine' (ceil_lt_add_one _).le.trans _
  -- ⊢ b + 1 ≤ ↑⌈a + b⌉ + 1 - a
  rw [le_sub_iff_add_le', ← add_assoc, add_le_add_iff_right]
  -- ⊢ a + b ≤ ↑⌈a + b⌉
  exact le_ceil _
  -- 🎉 no goals
#align int.ceil_add_ceil_le Int.ceil_add_ceil_le

@[simp]
theorem ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := by rw [lt_ceil, cast_zero]
                                         -- 🎉 no goals
#align int.ceil_pos Int.ceil_pos

@[simp]
theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by rw [← cast_zero, ceil_intCast]
                                        -- 🎉 no goals
#align int.ceil_zero Int.ceil_zero

@[simp]
theorem ceil_one : ⌈(1 : α)⌉ = 1 := by rw [← cast_one, ceil_intCast]
                                       -- 🎉 no goals
#align int.ceil_one Int.ceil_one

theorem ceil_nonneg (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := by exact_mod_cast ha.trans (le_ceil a)
                                                 -- 🎉 no goals
#align int.ceil_nonneg Int.ceil_nonneg

theorem ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z := by
  rw [← ceil_le, ← Int.cast_one, ← Int.cast_sub, ← lt_ceil, Int.sub_one_lt_iff, le_antisymm_iff,
    and_comm]
#align int.ceil_eq_iff Int.ceil_eq_iff

@[simp]
theorem ceil_eq_zero_iff : ⌈a⌉ = 0 ↔ a ∈ Ioc (-1 : α) 0 := by simp [ceil_eq_iff]
                                                              -- 🎉 no goals
#align int.ceil_eq_zero_iff Int.ceil_eq_zero_iff

theorem ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, ⌈a⌉ = z := fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩
#align int.ceil_eq_on_Ioc Int.ceil_eq_on_Ioc

theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z := fun a ha => by
  exact_mod_cast ceil_eq_on_Ioc z a ha
  -- 🎉 no goals
#align int.ceil_eq_on_Ioc' Int.ceil_eq_on_Ioc'

theorem floor_le_ceil (a : α) : ⌊a⌋ ≤ ⌈a⌉ :=
  cast_le.1 <| (floor_le _).trans <| le_ceil _
#align int.floor_le_ceil Int.floor_le_ceil

theorem floor_lt_ceil_of_lt {a b : α} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
  cast_lt.1 <| (floor_le a).trans_lt <| h.trans_le <| le_ceil b
#align int.floor_lt_ceil_of_lt Int.floor_lt_ceil_of_lt

-- Porting note: in mathlib3 there was no need for the type annotation in `(m : α)`
@[simp]
theorem preimage_ceil_singleton (m : ℤ) : (ceil : α → ℤ) ⁻¹' {m} = Ioc ((m : α) - 1) m :=
  ext fun _ => ceil_eq_iff
#align int.preimage_ceil_singleton Int.preimage_ceil_singleton

theorem fract_eq_zero_or_add_one_sub_ceil (a : α) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : α) := by
  cases' eq_or_ne (fract a) 0 with ha ha
  -- ⊢ fract a = 0 ∨ fract a = a + 1 - ↑⌈a⌉
  · exact Or.inl ha
    -- 🎉 no goals
  right
  -- ⊢ fract a = a + 1 - ↑⌈a⌉
  suffices (⌈a⌉ : α) = ⌊a⌋ + 1 by
    rw [this, ← self_sub_fract]
    abel
  norm_cast
  -- ⊢ ⌈a⌉ = ⌊a⌋ + 1
  rw [ceil_eq_iff]
  -- ⊢ ↑(⌊a⌋ + 1) - 1 < a ∧ a ≤ ↑(⌊a⌋ + 1)
  refine' ⟨_, _root_.le_of_lt <| by simp⟩
  -- ⊢ ↑(⌊a⌋ + 1) - 1 < a
  rw [cast_add, cast_one, add_tsub_cancel_right, ← self_sub_fract a, sub_lt_self_iff]
  -- ⊢ 0 < fract a
  exact ha.symm.lt_of_le (fract_nonneg a)
  -- 🎉 no goals
#align int.fract_eq_zero_or_add_one_sub_ceil Int.fract_eq_zero_or_add_one_sub_ceil

theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : α) = a + 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  -- ⊢ ↑⌈a⌉ = a + 1 - (a + 1 - ↑⌈a⌉)
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align int.ceil_eq_add_one_sub_fract Int.ceil_eq_add_one_sub_fract

theorem ceil_sub_self_eq (ha : fract a ≠ 0) : (⌈a⌉ : α) - a = 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  -- ⊢ ↑⌈a⌉ - a = 1 - (a + 1 - ↑⌈a⌉)
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align int.ceil_sub_self_eq Int.ceil_sub_self_eq

/-! #### Intervals -/


-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Ioo {a b : α} : (Int.cast : ℤ → α) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ ⌈b⌉ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Ioo a b ↔ x✝ ∈ Ioo ⌊a⌋ ⌈b⌉
  simp [floor_lt, lt_ceil]
  -- 🎉 no goals
#align int.preimage_Ioo Int.preimage_Ioo

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Ico {a b : α} : (Int.cast : ℤ → α) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Ico a b ↔ x✝ ∈ Ico ⌈a⌉ ⌈b⌉
  simp [ceil_le, lt_ceil]
  -- 🎉 no goals
#align int.preimage_Ico Int.preimage_Ico

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Ioc {a b : α} : (Int.cast : ℤ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Ioc a b ↔ x✝ ∈ Ioc ⌊a⌋ ⌊b⌋
  simp [floor_lt, le_floor]
  -- 🎉 no goals
#align int.preimage_Ioc Int.preimage_Ioc

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Icc {a b : α} : (Int.cast : ℤ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Icc a b ↔ x✝ ∈ Icc ⌈a⌉ ⌊b⌋
  simp [ceil_le, le_floor]
  -- 🎉 no goals
#align int.preimage_Icc Int.preimage_Icc

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Ioi : (Int.cast : ℤ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Ioi a ↔ x✝ ∈ Ioi ⌊a⌋
  simp [floor_lt]
  -- 🎉 no goals
#align int.preimage_Ioi Int.preimage_Ioi

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Ici : (Int.cast : ℤ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Ici a ↔ x✝ ∈ Ici ⌈a⌉
  simp [ceil_le]
  -- 🎉 no goals
#align int.preimage_Ici Int.preimage_Ici

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Iio : (Int.cast : ℤ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Iio a ↔ x✝ ∈ Iio ⌈a⌉
  simp [lt_ceil]
  -- 🎉 no goals
#align int.preimage_Iio Int.preimage_Iio

-- Porting note: changed `(coe : ℤ → α)` to `(Int.cast : ℤ → α)`
@[simp]
theorem preimage_Iic : (Int.cast : ℤ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by
  ext
  -- ⊢ x✝ ∈ Int.cast ⁻¹' Iic a ↔ x✝ ∈ Iic ⌊a⌋
  simp [le_floor]
  -- 🎉 no goals
#align int.preimage_Iic Int.preimage_Iic

end Int

open Int

/-! ### Round -/


section round

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorRing α]

/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
def round (x : α) : ℤ :=
  if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉
#align round round

@[simp]
theorem round_zero : round (0 : α) = 0 := by simp [round]
                                             -- 🎉 no goals
#align round_zero round_zero

@[simp]
theorem round_one : round (1 : α) = 1 := by simp [round]
                                            -- 🎉 no goals
#align round_one round_one

@[simp]
theorem round_natCast (n : ℕ) : round (n : α) = n := by simp [round]
                                                        -- 🎉 no goals
#align round_nat_cast round_natCast

@[simp]
theorem round_ofNat (n : ℕ) [n.AtLeastTwo] : round (OfNat.ofNat n : α) = n := round_natCast n

@[simp]
theorem round_intCast (n : ℤ) : round (n : α) = n := by simp [round]
                                                        -- 🎉 no goals
#align round_int_cast round_intCast

@[simp]
theorem round_add_int (x : α) (y : ℤ) : round (x + y) = round x + y := by
  rw [round, round, Int.fract_add_int, Int.floor_add_int, Int.ceil_add_int, ← apply_ite₂, ite_self]
  -- 🎉 no goals
#align round_add_int round_add_int

@[simp]
theorem round_add_one (a : α) : round (a + 1) = round a + 1 := by
  -- Porting note: broken `convert round_add_int a 1`
  rw [←round_add_int a 1, cast_one]
  -- 🎉 no goals
#align round_add_one round_add_one

@[simp]
theorem round_sub_int (x : α) (y : ℤ) : round (x - y) = round x - y := by
  rw [sub_eq_add_neg]
  -- ⊢ round (x + -↑y) = round x - y
  norm_cast
  -- ⊢ round (x + ↑(-y)) = round x - y
  rw [round_add_int, sub_eq_add_neg]
  -- 🎉 no goals
#align round_sub_int round_sub_int

@[simp]
theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by
  -- Porting note: broken `convert round_sub_int a 1`
  rw [←round_sub_int a 1, cast_one]
  -- 🎉 no goals
#align round_sub_one round_sub_one

@[simp]
theorem round_add_nat (x : α) (y : ℕ) : round (x + y) = round x + y := by
  exact_mod_cast round_add_int x y
  -- 🎉 no goals
#align round_add_nat round_add_nat

@[simp]
theorem round_add_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x + OfNat.ofNat n) = round x + OfNat.ofNat n :=
  round_add_nat x n

@[simp]
theorem round_sub_nat (x : α) (y : ℕ) : round (x - y) = round x - y := by
  exact_mod_cast round_sub_int x y
  -- 🎉 no goals
#align round_sub_nat round_sub_nat

@[simp]
theorem round_sub_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x - OfNat.ofNat n) = round x - OfNat.ofNat n :=
  round_sub_nat x n

@[simp]
theorem round_int_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_int, add_comm]
  -- 🎉 no goals
#align round_int_add round_int_add

@[simp]
theorem round_nat_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_nat, add_comm]
  -- 🎉 no goals
#align round_nat_add round_nat_add

@[simp]
theorem round_ofNat_add (n : ℕ) [n.AtLeastTwo] (x : α) :
    round (OfNat.ofNat n + x) = OfNat.ofNat n + round x :=
  round_nat_add x n

theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by
  simp_rw [round, min_def_lt, two_mul, ← lt_tsub_iff_left]
  -- ⊢ |x - ↑(if fract x < 1 - fract x then ⌊x⌋ else ⌈x⌉)| = if fract x < 1 - fract …
  cases' lt_or_ge (fract x) (1 - fract x) with hx hx
  -- ⊢ |x - ↑(if fract x < 1 - fract x then ⌊x⌋ else ⌈x⌉)| = if fract x < 1 - fract …
  · rw [if_pos hx, if_pos hx, self_sub_floor, abs_fract]
    -- 🎉 no goals
  · have : 0 < fract x := by
      replace hx : 0 < fract x + fract x := lt_of_lt_of_le zero_lt_one (tsub_le_iff_left.mp hx)
      simpa only [← two_mul, zero_lt_mul_left, zero_lt_two] using hx
    rw [if_neg (not_lt.mpr hx), if_neg (not_lt.mpr hx), abs_sub_comm, ceil_sub_self_eq this.ne.symm,
      abs_one_sub_fract]
#align abs_sub_round_eq_min abs_sub_round_eq_min

theorem round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z| := by
  rw [abs_sub_round_eq_min, min_le_iff]
  -- ⊢ fract x ≤ |x - ↑z| ∨ 1 - fract x ≤ |x - ↑z|
  rcases le_or_lt (z : α) x with (hx | hx) <;> [left; right]
  -- ⊢ fract x ≤ |x - ↑z|
  · conv_rhs => rw [abs_eq_self.mpr (sub_nonneg.mpr hx), ← fract_add_floor x, add_sub_assoc]
    -- ⊢ fract x ≤ fract x + (↑⌊x⌋ - ↑z)
    simpa only [le_add_iff_nonneg_right, sub_nonneg, cast_le] using le_floor.mpr hx
    -- 🎉 no goals
  · rw [abs_eq_neg_self.mpr (sub_neg.mpr hx).le]
    -- ⊢ 1 - fract x ≤ -(x - ↑z)
    conv_rhs => rw [← fract_add_floor x]
    -- ⊢ 1 - fract x ≤ -(fract x + ↑⌊x⌋ - ↑z)
    rw [add_sub_assoc, add_comm, neg_add, neg_sub, le_add_neg_iff_add_le, sub_add_cancel,
      le_sub_comm]
    norm_cast
    -- ⊢ ⌊x⌋ ≤ z - 1
    exact floor_le_sub_one_iff.mpr hx
    -- 🎉 no goals
#align round_le round_le

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [FloorRing α]

theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  simp_rw [round, (by simp only [lt_div_iff', two_pos] : 2 * fract x < 1 ↔ fract x < 1 / 2)]
  -- ⊢ (if fract x < 1 / 2 then ⌊x⌋ else ⌈x⌉) = ⌊x + 1 / 2⌋
  cases' lt_or_le (fract x) (1 / 2) with hx hx
  -- ⊢ (if fract x < 1 / 2 then ⌊x⌋ else ⌈x⌉) = ⌊x + 1 / 2⌋
  · conv_rhs => rw [← fract_add_floor x, add_assoc, add_left_comm, floor_int_add]
    -- ⊢ (if fract x < 1 / 2 then ⌊x⌋ else ⌈x⌉) = ⌊x⌋ + ⌊fract x + 1 / 2⌋
    rw [if_pos hx, self_eq_add_right, floor_eq_iff, cast_zero, zero_add]
    -- ⊢ 0 ≤ fract x + 1 / 2 ∧ fract x + 1 / 2 < 1
    constructor
    -- ⊢ 0 ≤ fract x + 1 / 2
    · linarith [fract_nonneg x]
      -- 🎉 no goals
    · linarith
      -- 🎉 no goals
  · have : ⌊fract x + 1 / 2⌋ = 1 := by
      rw [floor_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [fract_lt_one x]
    rw [if_neg (not_lt.mpr hx), ← fract_add_floor x, add_assoc, add_left_comm, floor_int_add,
      ceil_add_int, add_comm _ ⌊x⌋, add_right_inj, ceil_eq_iff, this, cast_one, sub_self]
    constructor
    -- ⊢ 0 < fract x
    · linarith
      -- 🎉 no goals
    · linarith [fract_lt_one x]
      -- 🎉 no goals
#align round_eq round_eq

@[simp]
theorem round_two_inv : round (2⁻¹ : α) = 1 := by
  simp only [round_eq, ← one_div, add_halves', floor_one]
  -- 🎉 no goals
#align round_two_inv round_two_inv

@[simp]
theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by
  simp only [round_eq, ← one_div, add_left_neg, floor_zero]
  -- 🎉 no goals
#align round_neg_two_inv round_neg_two_inv

@[simp]
theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x ∈ Ico (-(1 / 2)) ((1 : α) / 2) := by
  rw [round_eq, floor_eq_zero_iff, add_mem_Ico_iff_left]
  -- ⊢ x ∈ Ico (0 - 1 / 2) (1 - 1 / 2) ↔ x ∈ Ico (-(1 / 2)) (1 / 2)
  norm_num
  -- 🎉 no goals
#align round_eq_zero_iff round_eq_zero_iff

theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq, abs_sub_le_iff]
  -- ⊢ x - ↑⌊x + 1 / 2⌋ ≤ 1 / 2 ∧ ↑⌊x + 1 / 2⌋ - x ≤ 1 / 2
  have := floor_le (x + 1 / 2)
  -- ⊢ x - ↑⌊x + 1 / 2⌋ ≤ 1 / 2 ∧ ↑⌊x + 1 / 2⌋ - x ≤ 1 / 2
  have := lt_floor_add_one (x + 1 / 2)
  -- ⊢ x - ↑⌊x + 1 / 2⌋ ≤ 1 / 2 ∧ ↑⌊x + 1 / 2⌋ - x ≤ 1 / 2
  constructor <;> linarith
  -- ⊢ x - ↑⌊x + 1 / 2⌋ ≤ 1 / 2
                  -- 🎉 no goals
                  -- 🎉 no goals
#align abs_sub_round abs_sub_round

theorem abs_sub_round_div_natCast_eq {m n : ℕ} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  -- ⊢ |↑m / ↑0 - ↑(round (↑m / ↑0))| = ↑(min (m % 0) (0 - m % 0)) / ↑0
  · simp
    -- 🎉 no goals
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min, Nat.cast_min, ← min_div_div_right hn'.le,
    fract_div_natCast_eq_div_natCast_mod, Nat.cast_sub (m.mod_lt hn).le, sub_div, div_self hn'.ne']
#align abs_sub_round_div_nat_cast_eq abs_sub_round_div_natCast_eq

end LinearOrderedField

end round

namespace Nat

variable [LinearOrderedSemiring α] [LinearOrderedSemiring β] [FloorSemiring α] [FloorSemiring β]
  [RingHomClass F α β] {a : α} {b : β}

-- Porting note: no longer needed
-- include β

theorem floor_congr (h : ∀ n : ℕ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 ≤ a ↔ 0 ≤ b := by simpa only [cast_zero] using h 0
  -- ⊢ ⌊a⌋₊ = ⌊b⌋₊
  obtain ha | ha := lt_or_le a 0
  -- ⊢ ⌊a⌋₊ = ⌊b⌋₊
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_le <| h₀.not.mp ha.not_le)]
    -- 🎉 no goals
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)
  -- 🎉 no goals
#align nat.floor_congr Nat.floor_congr

theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _
#align nat.ceil_congr Nat.ceil_congr

theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]
                          -- 🎉 no goals
#align nat.map_floor Nat.map_floor

theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]
                         -- 🎉 no goals
#align nat.map_ceil Nat.map_ceil

end Nat

namespace Int

variable [LinearOrderedRing α] [LinearOrderedRing β] [FloorRing α] [FloorRing β]
  [RingHomClass F α β] {a : α} {b : β}

-- Porting note: no longer needed
-- include β

theorem floor_congr (h : ∀ n : ℤ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋ = ⌊b⌋ :=
  (le_floor.2 <| (h _).1 <| floor_le _).antisymm <| le_floor.2 <| (h _).2 <| floor_le _
#align int.floor_congr Int.floor_congr

theorem ceil_congr (h : ∀ n : ℤ, a ≤ n ↔ b ≤ n) : ⌈a⌉ = ⌈b⌉ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _
#align int.ceil_congr Int.ceil_congr

theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋ = ⌊a⌋ :=
  floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]
                          -- 🎉 no goals
#align int.map_floor Int.map_floor

theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉ = ⌈a⌉ :=
  ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]
                         -- 🎉 no goals
#align int.map_ceil Int.map_ceil

theorem map_fract (f : F) (hf : StrictMono f) (a : α) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]
  -- 🎉 no goals
#align int.map_fract Int.map_fract

end Int

namespace Int

variable [LinearOrderedField α] [LinearOrderedField β] [FloorRing α] [FloorRing β]
  [RingHomClass F α β] {a : α} {b : β}

-- Porting note: no longer needed
-- include β

theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  have H : f 2 = 2 := map_natCast f 2
  -- ⊢ round (↑f a) = round a
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, H]
  -- 🎉 no goals
  -- Porting note: was
  -- simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_bit0, map_one]
  -- Would have thought that `map_natCast` would replace `map_bit0, map_one` but seems not
#align int.map_round Int.map_round

end Int

section FloorRingToSemiring

variable [LinearOrderedRing α] [FloorRing α]

/-! #### A floor ring as a floor semiring -/


-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {a} ha := Int.toNat_of_nonpos (Int.floor_nonpos ha.le)
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_ofNat]
                          -- 🎉 no goals
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_ofNat]
                    -- 🎉 no goals
#align floor_ring.to_floor_semiring FloorRing.toFloorSemiring

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl
#align int.floor_to_nat Int.floor_toNat

theorem Int.ceil_toNat (a : α) : ⌈a⌉.toNat = ⌈a⌉₊ :=
  rfl
#align int.ceil_to_nat Int.ceil_toNat

@[simp]
theorem Nat.floor_int : (Nat.floor : ℤ → ℕ) = Int.toNat :=
  rfl
#align nat.floor_int Nat.floor_int

@[simp]
theorem Nat.ceil_int : (Nat.ceil : ℤ → ℕ) = Int.toNat :=
  rfl
#align nat.ceil_int Nat.ceil_int

variable {a : α}

theorem Nat.cast_floor_eq_int_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]
  -- 🎉 no goals
#align nat.cast_floor_eq_int_floor Nat.cast_floor_eq_int_floor

theorem Nat.cast_floor_eq_cast_int_floor (ha : 0 ≤ a) : (⌊a⌋₊ : α) = ⌊a⌋ := by
  rw [← Nat.cast_floor_eq_int_floor ha, Int.cast_ofNat]
  -- 🎉 no goals
#align nat.cast_floor_eq_cast_int_floor Nat.cast_floor_eq_cast_int_floor

theorem Nat.cast_ceil_eq_int_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg ha)]
  -- 🎉 no goals
#align nat.cast_ceil_eq_int_ceil Nat.cast_ceil_eq_int_ceil

theorem Nat.cast_ceil_eq_cast_int_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : α) = ⌈a⌉ := by
  rw [← Nat.cast_ceil_eq_int_ceil ha, Int.cast_ofNat]
  -- 🎉 no goals
#align nat.cast_ceil_eq_cast_int_ceil Nat.cast_ceil_eq_cast_int_ceil

end FloorRingToSemiring

/-- There exists at most one `FloorRing` structure on a given linear ordered ring. -/
theorem subsingleton_floorRing {α} [LinearOrderedRing α] : Subsingleton (FloorRing α) := by
  refine' ⟨fun H₁ H₂ => _⟩
  -- ⊢ H₁ = H₂
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  -- ⊢ H₁ = H₂
  cases H₁; cases H₂; congr
  -- ⊢ { floor := floor✝, ceil := ceil✝, gc_coe_floor := gc_coe_floor✝, gc_ceil_coe …
            -- ⊢ { floor := floor✝¹, ceil := ceil✝¹, gc_coe_floor := gc_coe_floor✝¹, gc_ceil_ …
                      -- 🎉 no goals
#align subsingleton_floor_ring subsingleton_floorRing

-- Porting note: the `positivity` extensions for `Int.floor`, `Int.ceil`, `ceil` are TODO for now

-- namespace Tactic

-- open Positivity

-- private theorem int_floor_nonneg [LinearOrderedRing α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
--     0 ≤ ⌊a⌋ :=
--   Int.floor_nonneg.2 ha
-- #align tactic.int_floor_nonneg tactic.int_floor_nonneg

-- private theorem int_floor_nonneg_of_pos [LinearOrderedRing α] [FloorRing α] {a : α}
--     (ha : 0 < a) :
--     0 ≤ ⌊a⌋ :=
--   int_floor_nonneg ha.le
-- #align tactic.int_floor_nonneg_of_pos tactic.int_floor_nonneg_of_pos

-- /-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
-- @[positivity]
-- unsafe def positivity_floor : expr → tactic strictness
--   | q(⌊$(a)⌋) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => nonnegative <$> mk_app `` int_floor_nonneg_of_pos [p]
--       | nonnegative p => nonnegative <$> mk_app `` int_floor_nonneg [p]
--       | _ => failed
--   | e => pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `⌊a⌋`"
-- #align tactic.positivity_floor tactic.positivity_floor

-- private theorem nat_ceil_pos [LinearOrderedSemiring α] [FloorSemiring α] {a : α} :
--     0 < a → 0 < ⌈a⌉₊ :=
--   Nat.ceil_pos.2
-- #align tactic.nat_ceil_pos tactic.nat_ceil_pos

-- private theorem int_ceil_pos [LinearOrderedRing α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
--   Int.ceil_pos.2
-- #align tactic.int_ceil_pos tactic.int_ceil_pos

-- /-- Extension for the `positivity` tactic: `ceil` and `Int.ceil` are positive/nonnegative if
-- their input is. -/
-- @[positivity]
-- unsafe def positivity_ceil : expr → tactic strictness
--   | q(⌈$(a)⌉₊) => do
--     let positive p ← core a
--     -- We already know `0 ≤ n` for all `n : ℕ`
--         positive <$>
--         mk_app `` nat_ceil_pos [p]
--   | q(⌈$(a)⌉) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` int_ceil_pos [p]
--       | nonnegative p => nonnegative <$> mk_app `` Int.ceil_nonneg [p]
--       | _ => failed
--   | e => pp e >>=
--       fail ∘ format.bracket "The expression `" "` is not of the form `⌈a⌉₊` nor `⌈a⌉`"
-- #align tactic.positivity_ceil tactic.positivity_ceil

-- end Tactic
