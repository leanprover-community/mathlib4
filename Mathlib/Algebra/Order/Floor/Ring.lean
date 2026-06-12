/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas on `Int.floor`, `Int.ceil` and `Int.fract`

This file contains basic results on the integer-valued floor and ceiling functions, as well as the
fractional part operator.

## TODO

`LinearOrderedRing` can be relaxed to `OrderedRing` in many lemmas.

## Tags

rounding, floor, ceil
-/

public section

assert_not_exists Finset

open Set

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

variable {α : Type*}

theorem int_floor_nonneg [Ring α] [LinearOrder α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ :=
  Int.floor_nonneg.2 ha

theorem int_floor_nonneg_of_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ :=
  int_floor_nonneg ha.le

/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊_⌋]
meta def evalIntFloor : PositivityExt where eval {u α} _zα pα? e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α' $ir $io $j $a) =>
    let some _ := pα? | throwError "no PartialOrder instance"
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg_of_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.floor application"

theorem nat_ceil_pos [Semiring α] [LinearOrder α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉₊]
meta def evalNatCeil : PositivityExt where eval {u α} _zα pα? e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α' $ir $io $j $a) =>
    let some _ := pα? | throwError "no PartialOrder instance"
    let _i ← synthInstanceQ q(LinearOrder $α')
    let _i ← synthInstanceQ q(IsStrictOrderedRing $α')
    assertInstancesCommute
    match ← core q(inferInstance) (some q(inferInstance)) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(nat_ceil_pos (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Nat.ceil application"

theorem int_ceil_pos [Ring α] [LinearOrder α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈_⌉]
meta def evalIntCeil : PositivityExt where eval {u α} _zα pα? e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α' $ir $io $j $a) =>
    let some _ := pα? | throwError "no PartialOrder instance"
    match ← core q(inferInstance) (some q(inferInstance)) a with
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

variable {F R S : Type*}

/-! ### Floor rings -/

namespace Int

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

/-! #### Floor -/

section floor

@[deprecated floor_lt (since := "2025-12-26")]
theorem floor_le_sub_one_iff : ⌊a⌋ ≤ z - 1 ↔ a < z := by rw [← floor_lt, le_sub_one_iff]

@[simp]
theorem floor_le_neg_one_iff : ⌊a⌋ ≤ -1 ↔ a < 0 := by
  simpa using floor_le_iff (z := -1)

theorem lt_succ_floor (a : R) : a < ⌊a⌋.succ :=
  floor_lt.1 <| Int.lt_succ_self _

@[simp, bound]
theorem lt_floor_add_one (a : R) : a < ⌊a⌋ + 1 := by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a

@[gcongr, mono]
theorem floor_mono : Monotone (floor : R → ℤ) :=
  gc_coe_floor.monotone_u

@[bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ := floor_mono hab

theorem floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a := by
  rw [Int.lt_iff_add_one_le, zero_add, le_floor, cast_one]

theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 := by
  rw [le_antisymm_iff, le_floor, ← Int.lt_add_one_iff, floor_lt, Int.cast_add, Int.cast_one,
    and_comm]

@[simp]
theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a ∈ Ico (0 : R) 1 := by simp [floor_eq_iff]

theorem floor_eq_on_Ico (n : ℤ) : ∀ a ∈ Set.Ico (n : R) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩

theorem floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ Set.Ico (n : R) (n + 1), (⌊a⌋ : R) = n := fun a ha =>
  congr_arg _ <| floor_eq_on_Ico n a ha

@[simp]
theorem preimage_floor_singleton (m : ℤ) : (floor : R → ℤ) ⁻¹' {m} = Ico (m : R) (m + 1) :=
  ext fun _ => floor_eq_iff

variable [IsOrderedRing R]

@[simp, bound]
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋ :=
  sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[simp]
theorem floor_intCast (z : ℤ) : ⌊(z : R)⌋ = z :=
  eq_of_forall_le_iff fun a => by rw [le_floor, Int.cast_le]

@[simp]
theorem floor_natCast (n : ℕ) : ⌊(n : R)⌋ = n :=
  eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

@[simp]
theorem floor_zero : ⌊(0 : R)⌋ = 0 := by rw [← cast_zero, floor_intCast]

@[simp]
theorem floor_one : ⌊(1 : R)⌋ = 1 := by rw [← cast_one, floor_intCast]

@[simp] theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋ = ofNat(n) :=
  floor_natCast n

@[simp, push]
theorem floor_add_intCast (a : R) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor, ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, Int.cast_sub]

@[simp, push]
theorem floor_add_one (a : R) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by
  rw [← cast_one, floor_add_intCast]

@[bound]
theorem le_floor_add (a b : R) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  rw [le_floor, Int.cast_add]
  gcongr <;> apply floor_le

@[bound]
theorem le_floor_add_floor (a b : R) : ⌊a + b⌋ - 1 ≤ ⌊a⌋ + ⌊b⌋ := by
  rw [← sub_le_iff_le_add, le_floor, Int.cast_sub, sub_le_comm, Int.cast_sub, Int.cast_one]
  refine le_trans ?_ (sub_one_lt_floor _).le
  rw [sub_le_iff_le_add', ← add_sub_assoc, sub_le_sub_iff_right]
  exact floor_le _

@[simp, push]
theorem floor_intCast_add (z : ℤ) (a : R) : ⌊↑z + a⌋ = z + ⌊a⌋ := by
  simpa only [add_comm] using floor_add_intCast a z

@[simp, push]
theorem floor_add_natCast (a : R) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := by
  rw [← Int.cast_natCast, floor_add_intCast]

@[simp, push]
theorem floor_add_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋ = ⌊a⌋ + ofNat(n) :=
  floor_add_natCast a n

@[simp, push]
theorem floor_natCast_add (n : ℕ) (a : R) : ⌊↑n + a⌋ = n + ⌊a⌋ := by
  rw [← Int.cast_natCast, floor_intCast_add]

@[simp, push]
theorem floor_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : R) :
    ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋ :=
  floor_natCast_add n a

@[simp]
theorem floor_sub_intCast (a : R) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_intCast _ _)

@[simp]
theorem floor_sub_natCast (a : R) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := by
  rw [← Int.cast_natCast, floor_sub_intCast]

@[simp] theorem floor_sub_one (a : R) : ⌊a - 1⌋ = ⌊a⌋ - 1 := mod_cast floor_sub_natCast a 1

@[simp]
theorem floor_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n) :=
  floor_sub_natCast a n

theorem abs_sub_lt_one_of_floor_eq_floor {a b : R} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  wlog h0 : b ≤ a generalizing a b
  · rw [abs_sub_comm]
    exact this h.symm (le_of_not_ge h0)
  calc |a - b|
    _ = a - b := abs_of_nonneg (sub_nonneg_of_le h0)
    _ < ⌊a⌋ + 1 - b := sub_lt_sub_right (lt_floor_add_one a) _
    _ ≤ ⌊a⌋ + 1 - ⌊b⌋ := sub_le_sub_left (floor_le b) _
    _ = 1 := by rw [h, add_sub_cancel_left]

lemma floor_eq_self_iff_mem (a : R) : ⌊a⌋ = a ↔ a ∈ Set.range Int.cast := by
  aesop

theorem floor_lt_self_iff {a : R} : ⌊a⌋ < a ↔ a ∉ range Int.cast :=
  (floor_le a).lt_iff_ne.trans <| (floor_eq_self_iff_mem _).not

section LinearOrderedRing
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R] {a b : R}

theorem mul_cast_floor_div_cancel_of_pos {n : ℤ} (hn : 0 < n) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  refine eq_of_forall_le_iff fun m ↦ ?_
  rw [Int.le_ediv_iff_mul_le hn, le_floor, le_floor, cast_mul,
    mul_le_mul_iff_of_pos_right (cast_pos.mpr hn)]

theorem mul_natCast_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊a * n⌋ / n = ⌊a⌋ := by
  simpa using mul_cast_floor_div_cancel_of_pos (n := n) (by positivity) a

theorem mul_fract_eq_one_iff_exists_int {x : R} {k : R} (hk : 1 < k) :
    k * fract x = 1 ↔ ∃ n : ℤ, k * x = k * n + 1 := by
  rw [fract, mul_sub, sub_eq_iff_eq_add']
  refine ⟨fun hx ↦ ⟨⌊x⌋, hx⟩, ?_⟩
  rintro ⟨n, hn⟩
  convert! hn
  have hk0 : 0 < (k : R) := zero_le_one.trans_lt hk
  rw [floor_eq_iff, ← mul_le_mul_iff_right₀ hk0, ← mul_lt_mul_iff_right₀ hk0, hn]
  simp [mul_add, hk]

theorem cast_mul_floor_div_cancel_of_pos {n : ℤ} (hn : 0 < n) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [Commute.intCast_left, mul_cast_floor_div_cancel_of_pos hn]

theorem natCast_mul_floor_div_cancel {n : ℕ} (hn : n ≠ 0) (a : R) : ⌊n * a⌋ / n = ⌊a⌋ := by
  rw [Nat.cast_comm, mul_natCast_floor_div_cancel hn]

end LinearOrderedRing

section LinearOrderedField
variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {a b : k}

theorem floor_div_cast_of_nonneg {n : ℤ} (hn : 0 ≤ n) (a : k) : ⌊a / n⌋ = ⌊a⌋ / n := by
  obtain rfl | hn := hn.eq_or_lt
  · simp
  nth_rw 2 [← div_mul_cancel₀ (a := a) (ne_of_gt (Int.cast_pos.mpr hn))]
  rw [mul_cast_floor_div_cancel_of_pos hn]

theorem floor_div_natCast (a : k) (n : ℕ) : ⌊a / n⌋ = ⌊a⌋ / n := by
  simpa using floor_div_cast_of_nonneg n.cast_nonneg a

end LinearOrderedField

end floor

/-! #### Fractional part -/

section fract

@[simp]
theorem self_sub_floor (a : R) : a - ⌊a⌋ = fract a :=
  rfl

@[simp]
theorem floor_add_fract (a : R) : (⌊a⌋ : R) + fract a = a :=
  add_sub_cancel _ _

@[simp]
theorem fract_add_floor (a : R) : fract a + ⌊a⌋ = a :=
  sub_add_cancel _ _

@[simp]
theorem self_sub_fract (a : R) : a - fract a = ⌊a⌋ :=
  sub_sub_cancel _ _

@[simp]
theorem fract_sub_self (a : R) : fract a - a = -⌊a⌋ :=
  sub_sub_cancel_left _ _

theorem fract_add (a b : R) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
  ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by unfold fract; grind⟩

variable [IsOrderedRing R]

@[simp]
theorem fract_add_intCast (a : R) (m : ℤ) : fract (a + m) = fract a := by
  rw [fract]
  simp
@[simp]
theorem fract_add_natCast (a : R) (m : ℕ) : fract (a + m) = fract a := by
  rw [fract]
  simp
@[simp]
theorem fract_add_one (a : R) : fract (a + 1) = fract a := mod_cast fract_add_natCast a 1

@[simp]
theorem fract_add_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    fract (a + ofNat(n)) = fract a :=
  fract_add_natCast a n

@[simp]
theorem fract_intCast_add (m : ℤ) (a : R) : fract (↑m + a) = fract a := by
  rw [add_comm, fract_add_intCast]
@[simp]
theorem fract_natCast_add (n : ℕ) (a : R) : fract (↑n + a) = fract a := by
  rw [add_comm, fract_add_natCast]
@[simp]
theorem fract_one_add (a : R) : fract (1 + a) = fract a := mod_cast fract_natCast_add 1 a

@[simp]
theorem fract_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : R) :
    fract (ofNat(n) + a) = fract a :=
  fract_natCast_add n a

@[simp]
theorem fract_sub_intCast (a : R) (m : ℤ) : fract (a - m) = fract a := by
  rw [fract]
  simp
@[simp]
theorem fract_sub_natCast (a : R) (n : ℕ) : fract (a - n) = fract a := by
  rw [fract]
  simp
@[simp]
theorem fract_sub_one (a : R) : fract (a - 1) = fract a := mod_cast fract_sub_natCast a 1

@[simp]
theorem fract_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    fract (a - ofNat(n)) = fract a :=
  fract_sub_natCast a n

-- Was a duplicate lemma under a bad name

theorem fract_add_le (a b : R) : fract (a + b) ≤ fract a + fract b := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_le_sub_iff_left, ← Int.cast_add, Int.cast_le]
  exact le_floor_add _ _

theorem fract_add_fract_le (a b : R) : fract a + fract b ≤ fract (a + b) + 1 := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_add, sub_le_sub_iff_left]
  exact mod_cast le_floor_add_floor a b

@[simp]
theorem fract_nonneg (a : R) : 0 ≤ fract a :=
  sub_nonneg.2 <| floor_le _

/-- The fractional part of `a` is positive if and only if `a ≠ ⌊a⌋`. -/
lemma fract_pos : 0 < fract a ↔ a ≠ ⌊a⌋ :=
  (fract_nonneg a).lt_iff_ne.trans <| ne_comm.trans sub_ne_zero

theorem fract_lt_one (a : R) : fract a < 1 :=
  sub_lt_comm.1 <| sub_one_lt_floor _

@[simp]
theorem fract_zero : fract (0 : R) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]

@[simp]
theorem fract_one : fract (1 : R) = 0 := by simp [fract]

theorem abs_fract : |fract a| = fract a :=
  abs_eq_self.mpr <| fract_nonneg a

@[simp]
theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a :=
  abs_eq_self.mpr <| sub_nonneg.mpr (fract_lt_one a).le

@[simp]
theorem fract_intCast (z : ℤ) : fract (z : R) = 0 := by
  unfold fract
  rw [floor_intCast]
  exact sub_self _

@[simp]
theorem fract_natCast (n : ℕ) : fract (n : R) = 0 := by simp [fract]

@[simp]
theorem fract_ofNat (n : ℕ) [n.AtLeastTwo] :
    fract (ofNat(n) : R) = 0 :=
  fract_natCast n

theorem fract_floor (a : R) : fract (⌊a⌋ : R) = 0 :=
  fract_intCast _

@[simp]
theorem floor_fract (a : R) : ⌊fract a⌋ = 0 := by
  rw [floor_eq_iff, Int.cast_zero, zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩

theorem fract_eq_iff {a b : R} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
  ⟨fun h => by
    rw [← h]
    exact ⟨fract_nonneg _, fract_lt_one _, ⟨⌊a⌋, sub_sub_cancel _ _⟩⟩,
   by
    rintro ⟨h₀, h₁, z, hz⟩
    rw [← self_sub_floor, eq_comm, eq_sub_iff_add_eq, add_comm, ← eq_sub_iff_add_eq, hz]
    refine congrArg Int.cast ?_
    rw [floor_eq_iff, ← hz]
    constructor <;> simpa [sub_eq_add_neg, add_assoc] ⟩

theorem fract_eq_fract {a b : R} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
  ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by unfold fract at h; rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub.1 h]⟩,
   by
    rintro ⟨z, hz⟩
    refine fract_eq_iff.2 ⟨fract_nonneg _, fract_lt_one _, z + ⌊b⌋, ?_⟩
    rw [eq_add_of_sub_eq hz, add_comm, Int.cast_add]
    exact add_sub_sub_cancel _ _ _⟩

@[simp]
theorem fract_eq_self {a : R} : fract a = a ↔ 0 ≤ a ∧ a < 1 :=
  fract_eq_iff.trans <| and_assoc.symm.trans <| and_iff_left ⟨0, by simp⟩

@[simp]
theorem fract_fract (a : R) : fract (fract a) = fract a :=
  fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

theorem fract_eq_zero_iff {a : R} : fract a = 0 ↔ a ∈ range Int.cast := by
  simp [fract_eq_iff, eq_comm]

theorem fract_ne_zero_iff {a : R} : fract a ≠ 0 ↔ a ∉ range Int.cast :=
  fract_eq_zero_iff.not

theorem fract_neg {x : R} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]
theorem fract_neg_eq_zero {x : R} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

theorem fract_mul_natCast (a : R) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by
  induction b with
  | zero => use 0; simp
  | succ c hc =>
    rcases hc with ⟨z, hz⟩
    rw [Nat.cast_add, mul_add, mul_add, Nat.cast_one, mul_one, mul_one]
    rcases fract_add (a * c) a with ⟨y, hy⟩
    use z - y
    rw [Int.cast_sub, ← hz, ← hy]
    abel

theorem preimage_fract (s : Set R) :
    fract ⁻¹' s = ⋃ m : ℤ, (fun x => x - (m : R)) ⁻¹' (s ∩ Ico (0 : R) 1) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  refine ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, ?_⟩
  rintro ⟨m, hms, hm0, hm1⟩
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  exact hms

theorem image_fract (s : Set R) : fract '' s = ⋃ m : ℤ, (fun x : R => x - m) '' s ∩ Ico 0 1 := by
  ext x
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    exact ⟨y, hys, rfl⟩

section LinearOrderedField

variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a :=
  ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

omit [IsOrderedRing k] in
theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a ≠ 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul, ← add_mul, fract_add_floor, div_mul_cancel₀ b ha]

theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 ≤ a - ⌊a / b⌋ * b :=
  sub_nonneg_of_le <| (le_div_iff₀ hb).1 <| floor_le _

theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
  sub_lt_iff_lt_add.2 <| by
    rw [← one_add_mul, ← div_lt_iff₀ hb, add_comm]
    exact lt_floor_add_one _

theorem fract_div_natCast_eq_div_natCast_mod {m n : ℕ} : fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : k) := by
    norm_cast
  refine fract_eq_iff.mpr ⟨?_, ?_, m / n, ?_⟩
  · positivity
  · simpa only [div_lt_one hn', Nat.cast_lt] using m.mod_lt hn
  · rw [sub_eq_iff_eq_add', ← mul_right_inj' hn'.ne', mul_div_cancel₀ _ hn'.ne', mul_add,
      mul_div_cancel₀ _ hn'.ne']
    norm_cast
    rw [← Nat.cast_add, Nat.mod_add_div m n]

theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : ∀ {l : ℤ}, 0 ≤ l → fract ((l : k) / n) = ↑(l % n) / n := by
    intro l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (natCast_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : ℤ)
  have hm₁ : 0 ≤ m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : ℤ)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : ℤ)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : ℤ) % ↑n) / Nat.cast n := ?_
  · rw [← fract_intCast_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg, add_comm (q * ↑n), add_mul_emod_self_right]

end LinearOrderedField

end fract

/-! #### Ceil -/

section ceil

@[deprecated lt_ceil (since := "2025-12-26")]
theorem add_one_le_ceil_iff : z + 1 ≤ ⌈a⌉ ↔ (z : R) < a := by rw [← lt_ceil, add_one_le_iff]

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉ ↔ 0 < a := by
  simpa using le_ceil_iff (z := 1)

@[bound]
theorem ceil_le_floor_add_one (a : R) : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
  rw [ceil_le, Int.cast_add, Int.cast_one]
  exact (lt_floor_add_one a).le

theorem ceil_mono : Monotone (ceil : R → ℤ) :=
  gc_ceil_coe.monotone_l

@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ := ceil_mono hab

theorem ceil_nonneg_of_neg_one_lt (ha : -1 < a) : 0 ≤ ⌈a⌉ := by
  rwa [Int.le_ceil_iff, Int.cast_zero, zero_sub]

theorem ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z := by
  rw [← ceil_le, ← Int.cast_one, ← Int.cast_sub, ← lt_ceil, Int.sub_one_lt_iff, le_antisymm_iff,
    and_comm]

@[simp]
theorem ceil_eq_zero_iff : ⌈a⌉ = 0 ↔ a ∈ Ioc (-1 : R) 0 := by simp [ceil_eq_iff]

theorem ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : R) z, ⌈a⌉ = z := fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩

@[simp]
theorem preimage_ceil_singleton (m : ℤ) : (ceil : R → ℤ) ⁻¹' {m} = Ioc ((m : R) - 1) m :=
  ext fun _ => ceil_eq_iff

variable [IsOrderedRing R]

theorem floor_neg : ⌊-a⌋ = -⌈a⌉ :=
  eq_of_forall_le_iff fun z => by rw [le_neg, ceil_le, le_floor, Int.cast_neg, le_neg]

theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
  eq_of_forall_ge_iff fun z => by rw [neg_le, ceil_le, le_floor, Int.cast_neg, neg_le]

@[simp]
theorem ceil_intCast (z : ℤ) : ⌈(z : R)⌉ = z :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : R)⌉ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉ = ofNat(n) := ceil_natCast n

@[simp]
theorem ceil_add_intCast (a : R) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z := by
  rw [← neg_inj, neg_add', ← floor_neg, ← floor_neg, neg_add', floor_sub_intCast]

@[simp]
theorem ceil_intCast_add (z : ℤ) (a : R) : ⌈z + a⌉ = z + ⌈a⌉ := by
  rw [add_comm, ceil_add_intCast, add_comm]

@[simp]
theorem ceil_add_natCast (a : R) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n := by
  rw [← Int.cast_natCast, ceil_add_intCast]

@[simp]
theorem ceil_natCast_add (n : ℕ) (a : R) : ⌈n + a⌉ = n + ⌈a⌉ :=
  mod_cast ceil_intCast_add n a

@[simp]
theorem ceil_add_one (a : R) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by
  rw [← ceil_add_intCast a (1 : ℤ), cast_one]

@[simp]
theorem ceil_one_add (a : R) : ⌈1 + a⌉ = 1 + ⌈a⌉ :=
  mod_cast ceil_natCast_add 1 a

@[simp]
theorem ceil_add_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉ = ⌈a⌉ + ofNat(n) :=
  ceil_add_natCast a n

@[simp]
theorem ceil_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : R) :
    ⌈ofNat(n) + a⌉ = ofNat(n) + ⌈a⌉ :=
  ceil_natCast_add n a

@[simp]
theorem ceil_sub_intCast (a : R) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_intCast _ _)

@[simp]
theorem ceil_sub_natCast (a : R) (n : ℕ) : ⌈a - n⌉ = ⌈a⌉ - n := by
  convert! ceil_sub_intCast a n using 1
  simp

@[simp]
theorem ceil_sub_one (a : R) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by
  rw [eq_sub_iff_add_eq, ← ceil_add_one, sub_add_cancel]

@[simp]
theorem ceil_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌈a - ofNat(n)⌉ = ⌈a⌉ - ofNat(n) :=
  ceil_sub_natCast a n

@[bound]
theorem ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1 := by
  rw [← lt_ceil, ← Int.cast_one, ceil_add_intCast]
  apply lt_add_one

@[bound]
theorem ceil_add_le (a b : R) : ⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉ := by
  rw [ceil_le, Int.cast_add]
  gcongr <;> apply le_ceil

@[bound]
theorem ceil_add_ceil_le (a b : R) : ⌈a⌉ + ⌈b⌉ ≤ ⌈a + b⌉ + 1 := by
  rw [← le_sub_iff_add_le, ceil_le, Int.cast_sub, Int.cast_add, Int.cast_one, le_sub_comm]
  refine (ceil_lt_add_one _).le.trans ?_
  rw [le_sub_iff_add_le', ← add_assoc, add_le_add_iff_right]
  exact le_ceil _

@[simp]
theorem ceil_zero : ⌈(0 : R)⌉ = 0 := by rw [← cast_zero, ceil_intCast]

@[simp]
theorem ceil_one : ⌈(1 : R)⌉ = 1 := by rw [← cast_one, ceil_intCast]

omit [IsOrderedRing R] in
theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : R) z, (⌈a⌉ : R) = z :=
  fun a ha => congrArg Int.cast (ceil_eq_on_Ioc z a ha)

lemma ceil_eq_self_iff_mem (a : R) : ⌈a⌉ = a ↔ a ∈ Set.range Int.cast := by
  aesop

@[bound]
theorem floor_le_ceil (a : R) : ⌊a⌋ ≤ ⌈a⌉ :=
  cast_le.1 <| (floor_le _).trans <| le_ceil _

@[bound]
theorem floor_lt_ceil_of_lt {a b : R} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
  cast_lt.1 <| (floor_le a).trans_lt <| h.trans_le <| le_ceil b

lemma ceil_eq_floor_add_one_iff_notMem (a : R) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast := by
  refine ⟨fun h ht => ?_, fun h => ?_⟩
  · have h0 := ((floor_eq_self_iff_mem _).mpr ht).trans ((ceil_eq_self_iff_mem _).mpr ht).symm
    rw [h, cast_add, cast_one, left_eq_add] at h0
    exact one_ne_zero h0
  · apply le_antisymm (Int.ceil_le_floor_add_one _)
    rw [add_one_le_iff, lt_ceil]
    exact lt_of_le_of_ne (Int.floor_le a) ((iff_false_right h).mp (floor_eq_self_iff_mem a))

theorem fract_eq_zero_or_add_one_sub_ceil (a : R) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : R) := by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : R) = ⌊a⌋ + 1 by
    rw [this, ← self_sub_fract]
    abel
  rw [← Int.cast_one, ← Int.cast_add]
  refine congrArg Int.cast (ceil_eq_iff.mpr ⟨?_, _root_.le_of_lt <| by simp⟩)
  rw [cast_add, cast_one, add_tsub_cancel_right, ← self_sub_fract a, sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : R) = a + 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

theorem ceil_sub_self_eq (ha : fract a ≠ 0) : (⌈a⌉ : R) - a = 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

end ceil

section LinearOrderedField
variable {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k] {a b : k}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ ≤ a) : b * a < ⌊a⌋ := by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; apply lt_floor_add_one
    _ ≤ ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

lemma ceil_div_ceil_inv_sub_one (ha : 1 ≤ a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by
  obtain rfl | ha := ha.eq_or_lt
  · simp
  have : 0 < a - 1 := by linarith
  refine le_antisymm (ceil_le.2 <| div_le_self (by positivity) ha.le) <| ?_
  rw [le_ceil_iff, sub_lt_comm, div_eq_mul_inv, ← mul_one_sub,
    ← lt_div_iff₀ (sub_pos.2 <| inv_lt_one_of_one_lt₀ ha)]
  convert! ceil_lt_add_one (R := k) _ using 1
  field

lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ ≤ (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b ≤ a) : ⌈a⌉ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField

/-! #### Intervals -/

@[simp]
theorem preimage_Ioo {a b : R} : ((↑) : ℤ → R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ ⌈b⌉ := by
  ext
  simp [floor_lt, lt_ceil]

@[simp]
theorem preimage_Ico {a b : R} : ((↑) : ℤ → R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
theorem preimage_Ioc {a b : R} : ((↑) : ℤ → R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋ := by
  ext
  simp [floor_lt, le_floor]

@[simp]
theorem preimage_Icc {a b : R} : ((↑) : ℤ → R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext
  simp [ceil_le, le_floor]

@[simp]
theorem preimage_Ioi : ((↑) : ℤ → R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by
  ext
  simp [floor_lt]

@[simp]
theorem preimage_Ici : ((↑) : ℤ → R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by
  ext
  simp [ceil_le]

@[simp]
theorem preimage_Iio : ((↑) : ℤ → R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  simp [lt_ceil]

@[simp]
theorem preimage_Iic : ((↑) : ℤ → R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by
  ext
  simp [le_floor]

end Int

namespace Int

variable [Ring R] [LinearOrder R] [Ring S] [LinearOrder S] [FloorRing R] [FloorRing S]
variable [FunLike F R S] [RingHomClass F R S] {a : R} {b : S}

theorem floor_congr (h : ∀ n : ℤ, (n : R) ≤ a ↔ (n : S) ≤ b) : ⌊a⌋ = ⌊b⌋ :=
  (le_floor.2 <| (h _).1 <| floor_le _).antisymm <| le_floor.2 <| (h _).2 <| floor_le _

theorem ceil_congr (h : ∀ n : ℤ, a ≤ n ↔ b ≤ n) : ⌈a⌉ = ⌈b⌉ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

theorem map_floor (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋ = ⌊a⌋ :=
  floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉ = ⌈a⌉ :=
  ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

theorem map_fract (f : F) (hf : StrictMono f) (a : R) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

end Int

namespace Nat

variable [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R] {a : R}

/-- a variant of `Nat.ceil_lt_add_one` with its condition `0 ≤ a` generalized to `-1 < a` -/
@[bound]
lemma ceil_lt_add_one_of_gt_neg_one (ha : -1 < a) : ⌈a⌉₊ < a + 1 := by
  by_cases! h : 0 ≤ a
  · exact ceil_lt_add_one h
  · rw [ceil_eq_zero.mpr h.le, cast_zero]
    exact neg_lt_iff_pos_add.mp ha

end Nat

section FloorRingToSemiring

variable [Ring R] [LinearOrder R] [FloorRing R]

/-! #### A floor ring as a floor semiring -/

variable {a : R}

theorem Int.natCast_floor_eq_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

theorem Int.natCast_ceil_eq_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

theorem Int.natCast_ceil_eq_ceil_of_neg_one_lt (ha : -1 < a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg_of_neg_one_lt ha)]

theorem natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : R) = ⌊a⌋ := by
  rw [← Int.natCast_floor_eq_floor ha, Int.cast_natCast]

theorem natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil ha, Int.cast_natCast]

theorem natCast_ceil_eq_intCast_ceil_of_neg_one_lt (ha : -1 < a) : (⌈a⌉₊ : R) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil_of_neg_one_lt ha, Int.cast_natCast]

end FloorRingToSemiring

/-- There exists at most one `FloorRing` structure on a given linear ordered ring. -/
theorem subsingleton_floorRing {R} [Ring R] [LinearOrder R] : Subsingleton (FloorRing R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.floor = H₂.floor :=
    funext fun a => (H₁.gc_coe_floor.u_unique H₂.gc_coe_floor) fun _ => rfl
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil_coe.l_unique H₂.gc_ceil_coe) fun _ => rfl
  cases H₁; cases H₂; congr
