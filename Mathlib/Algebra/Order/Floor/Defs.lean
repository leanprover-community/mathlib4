/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Tactic.Positivity.Core

/-!
# Floor and ceil

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.
We also provide `positivity` extensions to handle floor and ceil.

## Main definitions

* `FloorSemiring`: An ordered semiring with natural-valued floor and ceil.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `Nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `FloorRing`: A linearly ordered ring with integer-valued floor and ceil.
* `Int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `Int.ceil a`: Least integer `z` such that `a ≤ z`.
* `Int.fract a`: Fractional part of `a`, defined as `a - floor a`.

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

assert_not_exists Finset

open Set

variable {F α β : Type*}

/-! ### Floor semiring -/

/-- A `FloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. Please see the above `TODO`. -/
class FloorSemiring (α) [Semiring α] [PartialOrder α] where
  /-- `FloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α → ℕ
  /-- `FloorSemiring.ceil a` computes the least natural `n` such that `a ≤ (n : α)`. -/
  ceil : α → ℕ
  /-- `FloorSemiring.floor` of a negative element is zero. -/
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- A natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion to `α` is
  smaller than `a`. -/
  gc_floor {a : α} {n : ℕ} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  /-- `FloorSemiring.ceil` is the lower adjoint of the coercion `↑ : ℕ → α`. -/
  gc_ceil : GaloisConnection ceil (↑)

instance : FloorSemiring ℕ where
  floor := id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id, id_def]
  gc_ceil n a := by
    rw [Nat.cast_id, id_def]

namespace Nat

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [FloorSemiring α] {a : α} {n : ℕ}

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil

@[simp]
theorem floor_nat : (Nat.floor : ℕ → ℕ) = id :=
  rfl

@[simp]
theorem ceil_nat : (Nat.ceil : ℕ → ℕ) = id :=
  rfl

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

theorem le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a :=
  FloorSemiring.gc_floor ha

theorem le_floor [IsOrderedRing α] (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ :=
  (le_floor_iff <| n.cast_nonneg.trans h).2 h

theorem gc_ceil_coe : GaloisConnection (ceil : α → ℕ) (↑) :=
  FloorSemiring.gc_ceil

@[simp]
theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
  gc_ceil_coe _ _

end OrderedSemiring

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [FloorSemiring α] {a b : α} {n : ℕ}

theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

@[simp]
theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by rw [lt_ceil, cast_zero]

end LinearOrderedSemiring

end Nat

/-! ### Floor rings -/

/-- A `FloorRing` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)`.
-/
class FloorRing (α) [Ring α] [LinearOrder α] where
  /-- `FloorRing.floor a` computes the greatest integer `z` such that `(z : α) ≤ a`. -/
  floor : α → ℤ
  /-- `FloorRing.ceil a` computes the least integer `z` such that `a ≤ (z : α)`. -/
  ceil : α → ℤ
  /-- `FloorRing.ceil` is the upper adjoint of the coercion `↑ : ℤ → α`. -/
  gc_coe_floor : GaloisConnection (↑) floor
  /-- `FloorRing.ceil` is the lower adjoint of the coercion `↑ : ℤ → α`. -/
  gc_ceil_coe : GaloisConnection ceil (↑)

instance : FloorRing ℤ where
  floor := id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id, id_def]
  gc_ceil_coe a b := by
    rw [Int.cast_id, id_def]

/-- A `FloorRing` constructor from the `floor` function alone. -/
def FloorRing.ofFloor (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (floor : α → ℤ)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

/-- A `FloorRing` constructor from the `ceil` function alone. -/
def FloorRing.ofCeil (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] (ceil : α → ℤ)
    (gc_ceil_coe : GaloisConnection ceil (↑)) : FloorRing α :=
  { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
    gc_ceil_coe }

namespace Int

variable [Ring α] [LinearOrder α] [FloorRing α] {z : ℤ} {a b : α}

/-- `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → ℤ :=
  FloorRing.floor

/-- `Int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil : α → ℤ :=
  FloorRing.ceil

/-- `Int.fract a` the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α :=
  a - floor a

@[simp]
theorem floor_int : (Int.floor : ℤ → ℤ) = id :=
  rfl

@[simp]
theorem ceil_int : (Int.ceil : ℤ → ℤ) = id :=
  rfl

@[simp]
theorem fract_int : (Int.fract : ℤ → ℤ) = 0 :=
  funext fun x => by simp [fract]

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

@[simp]
theorem floorRing_floor_eq : @FloorRing.floor = @Int.floor :=
  rfl

@[simp]
theorem floorRing_ceil_eq : @FloorRing.ceil = @Int.ceil :=
  rfl

/-! #### Floor -/

theorem gc_coe_floor : GaloisConnection ((↑) : ℤ → α) floor :=
  FloorRing.gc_coe_floor

theorem le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a :=
  (gc_coe_floor z a).symm

theorem floor_lt : ⌊a⌋ < z ↔ a < z :=
  lt_iff_lt_of_le_iff_le le_floor

@[bound]
theorem floor_le (a : α) : (⌊a⌋ : α) ≤ a :=
  gc_coe_floor.l_u_le a

theorem floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := by rw [le_floor, Int.cast_zero]

@[bound]
theorem floor_nonpos [IsStrictOrderedRing α] (ha : a ≤ 0) : ⌊a⌋ ≤ 0 := by
  rw [← @cast_le α, Int.cast_zero]
  exact (floor_le a).trans ha

/-! #### Ceil -/

theorem gc_ceil_coe : GaloisConnection ceil ((↑) : ℤ → α) :=
  FloorRing.gc_ceil_coe

theorem ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z :=
  gc_ceil_coe a z

theorem lt_ceil : z < ⌈a⌉ ↔ (z : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

@[bound]
theorem le_ceil (a : α) : a ≤ ⌈a⌉ :=
  gc_ceil_coe.le_u_l a

@[bound]
theorem ceil_nonneg [IsStrictOrderedRing α] (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := mod_cast ha.trans (le_ceil a)

@[simp]
theorem ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := by rw [lt_ceil, cast_zero]

end Int

section FloorRingToSemiring

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-! #### A floor ring as a floor semiring -/


-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_nonpos ha.le)
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

theorem Int.ceil_toNat (a : α) : ⌈a⌉.toNat = ⌈a⌉₊ :=
  rfl

@[simp]
theorem Nat.floor_int : (Nat.floor : ℤ → ℕ) = Int.toNat :=
  rfl

@[simp]
theorem Nat.ceil_int : (Nat.ceil : ℤ → ℕ) = Int.toNat :=
  rfl

end FloorRingToSemiring

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

private theorem int_floor_nonneg [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ :=
  Int.floor_nonneg.2 ha

private theorem int_floor_nonneg_of_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ :=
  int_floor_nonneg ha.le

/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊_⌋]
def evalIntFloor : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α' $ir $io $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg_of_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.floor application"

private theorem nat_ceil_pos [Semiring α] [LinearOrder α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉₊]
def evalNatCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α' $ir $io $j $a) =>
    let _i ← synthInstanceQ q(LinearOrder $α')
    let _i ← synthInstanceQ q(IsStrictOrderedRing $α')
    assertInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(nat_ceil_pos (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Nat.ceil application"

private theorem int_ceil_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈_⌉]
def evalIntCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α' $ir $io $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.positive q(int_ceil_pos (α := $α') $pa))
    | .nonnegative pa =>
        let _i ← synthInstanceQ q(IsStrictOrderedRing $α')
        assertInstancesCommute
        pure (.nonnegative q(Int.ceil_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.ceil application"

end Mathlib.Meta.Positivity
