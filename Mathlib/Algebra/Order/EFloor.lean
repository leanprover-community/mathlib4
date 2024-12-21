/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Data.ENat.Basic

/-!
# Floor in extended nonnegative numbers

## Summary

We define the extended natural number -valued floor functions.

## Main Definitions

* `EFloorSemiring`: An ordered semiring with natural-valued floor.
* `ENat.floor a`: Greatest extended natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.

## Notations

* `⌊a⌋ₑ` is `ENat.floor a`.

The index `ₑ` in the notations for `ENat.floor` indicates the possibility of `+∞` (`⊤`) and
disambiguates from the common floor notation.

## TODO

Add `ENat.ceil`.

## Tags

floor
-/

open Set

variable {F α β : Type*}

/-! ### EFloor semiring -/

/-- A `EFloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ∞` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. -/
class EFloorSemiring (α) [Semiring α] [Preorder α] [CoeTC ℕ∞ α] where
  /-- `EFloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α → ℕ∞
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- An extended natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion
  to `α` is smaller than `a`. -/
  gc_floor {a : α} {n : ℕ∞} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  floor_lt {a : α} {n : ℕ∞} (ha : 0 ≤ a) : floor a < n ↔ a < n

instance : EFloorSemiring ℕ∞ where
  floor := id
  floor_of_neg ha := (ENat.not_lt_zero _ ha).elim
  gc_floor _ := by rfl
  floor_lt _ := by rfl

/-- A type class for types with a consistent coercions from `ℕ` and `ℕ∞`.
The consistency requirements are commutation of the coercion triangle
(`((↑) : ℕ∞ → α) ∘ ((↑) : ℕ → ℕ∞) = ((↑) : ℕ → α)`) and the coercion from `ℕ∞`
respecting order relations `<`, `≤`, and nonnegativity. -/
class CastNatENatClass (α : Type*) [Semiring α] [Preorder α] [CoeTC ℕ∞ α] : Prop where
  cast_nat : ∀ (n : ℕ), (n : ℕ∞) = (n : α)
  cast_enat_lt_iff : ∀ (n m : ℕ∞), (n : α) < (m : α) ↔ n < m
  cast_enat_le_iff : ∀ (n m : ℕ∞), (n : α) ≤ (m : α) ↔ n ≤ m
  cast_nonneg {n : ℕ∞} : (0 : α) ≤ n

@[simp, norm_cast]
lemma ENat.cast_natCast [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n : ℕ} :
    (n : ℕ∞) = (n : α) :=
  CastNatENatClass.cast_nat n

@[simp] lemma ENat.cast_zero [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] :
    (0 : ℕ∞) = (0 : α) := by
  exact_mod_cast ENat.cast_natCast (α := α) (n := 0)

@[simp] lemma ENat.cast_one [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] :
    (1 : ℕ∞) = (1 : α) := by
  exact_mod_cast ENat.cast_natCast (α := α) (n := 1)

@[simp]
lemma cast_enat_lt_iff [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n m : ℕ∞} :
    (n : α) < (m : α) ↔ n < m :=
  CastNatENatClass.cast_enat_lt_iff n m

@[simp]
lemma cast_enat_le_iff [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] {n m : ℕ∞} :
    (n : α) ≤ (m : α) ↔ n ≤ m :=
  CastNatENatClass.cast_enat_le_iff n m

lemma lt_of_cast_enat_lt [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α]
    {n m : ℕ∞} (h : (n : α) < (m : α)) :
    n < m :=
  lt_of_le_of_ne (cast_enat_le_iff.mp h.le) fun con ↦ lt_irrefl _ (con ▸ h)

lemma ENat.cast_nonneg [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [CastNatENatClass α] (n : ℕ∞) :
    0 ≤ (n : α) :=
  CastNatENatClass.cast_nonneg

noncomputable instance : CastNatENatClass ℕ∞ where
  cast_nat _ := rfl
  cast_enat_lt_iff _ _ := by rfl
  cast_enat_le_iff _ _ := by rfl
  cast_nonneg := zero_le _

namespace ENat

section OrderedSemiring

variable [Semiring α] [Preorder α] [CoeTC ℕ∞ α] [EFloorSemiring α] {a : α} {n : ℕ∞}

/-- `⌊a⌋ₑ` is the greatest extended natural number `n` such that `n ≤ a`. If `a` is negative,
then `⌊a⌋ₑ = 0`. -/
def floor : α → ℕ∞ := EFloorSemiring.floor

@[simp]
lemma floor_enat : (ENat.floor : ℕ∞ → ℕ∞) = id := rfl

@[inherit_doc]
notation "⌊" a "⌋ₑ" => ENat.floor a

end OrderedSemiring

open EFloorSemiring in
lemma galoisConnection_coe_floor {α : Type*} [CanonicallyOrderedCommSemiring α]
    [CoeTC ℕ∞ α] [EFloorSemiring α] :
    GaloisConnection (fun (n : ℕ∞) ↦ (n : α)) (fun (a : α) ↦ ⌊a⌋ₑ) := by
  intro n a
  rw [← gc_floor (zero_le a)]
  rfl

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [ZeroLEOneClass α]
variable [CoeTC ℕ∞ α] [EFloorSemiring α] [CastNatENatClass α]
variable {a : α} {n : ℕ∞}

lemma le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋ₑ ↔ (n : α) ≤ a :=
  EFloorSemiring.gc_floor ha

lemma le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋ₑ := (le_floor_iff <| n.cast_nonneg.trans h).2 h

lemma floor_lt (ha : 0 ≤ a) : ⌊a⌋ₑ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| le_floor_iff ha

lemma floor_lt_one (ha : 0 ≤ a) : ⌊a⌋ₑ < 1 ↔ a < 1 := by simpa using (floor_lt ha (n := 1))

lemma lt_of_floor_lt (h : ⌊a⌋ₑ < n) : a < n := lt_of_not_le fun h' => (le_floor h').not_lt h

lemma lt_one_of_floor_lt_one (h : ⌊a⌋ₑ < 1) : a < 1 := by simpa using lt_of_floor_lt h

lemma floor_le (ha : 0 ≤ a) : (⌊a⌋ₑ : α) ≤ a := (le_floor_iff ha).1 le_rfl

@[simp]
lemma floor_enatCast (n : ℕ∞) : ⌊(n : α)⌋ₑ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff n.cast_nonneg]
    exact cast_enat_le_iff

@[simp]
lemma floor_zero : ⌊(0 : α)⌋ₑ = 0 := by
  rw [← Nat.cast_zero, ← floor_enatCast (α := α) 0]
  simp

@[simp]
lemma floor_one : ⌊(1 : α)⌋ₑ = 1 := by
  rw [← Nat.cast_one, ← floor_enatCast (α := α) 1]
  simp

lemma floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋ₑ = 0 :=
  ha.lt_or_eq.elim EFloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

lemma floor_mono : Monotone (floor : α → ℕ∞) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact zero_le _
  · exact le_floor ((floor_le ha).trans h)

@[gcongr]
lemma floor_le_floor : ∀ x y : α, x ≤ y → ⌊x⌋ₑ ≤ ⌊y⌋ₑ := floor_mono

variable [Nontrivial α]

lemma le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋ₑ ↔ (n : α) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, iff_of_false (ENat.pos_of_ne_zero hn).not_le]
    apply not_le_of_lt (ha.trans_lt _)
    refine lt_of_lt_of_le ?_ <| (cast_enat_le_iff (α := α)).mpr <| one_le_iff_ne_zero.mpr hn
    apply lt_of_le_of_ne (by simp [show (0 : α) ≤ (1 : α) from zero_le_one])
    simp
  · exact le_floor_iff ha

@[simp] lemma one_le_floor_iff (x : α) :
    1 ≤ ⌊x⌋ₑ ↔ 1 ≤ x := by
  simp [@le_floor_iff' α _ _ _ _ _ _ x 1 _ one_ne_zero]

lemma floor_lt' (hn : n ≠ 0) : ⌊a⌋ₑ < n ↔ a < n := lt_iff_lt_of_le_iff_le <| le_floor_iff' hn

lemma floor_pos : 0 < ⌊a⌋ₑ ↔ 1 ≤ a := by simpa [← one_le_floor_iff] using one_le_iff_pos.symm

lemma pos_of_floor_pos (h : 0 < ⌊a⌋ₑ) :
    0 < a := by
  rw [floor_pos] at h; exact lt_of_lt_of_le zero_lt_one h

lemma lt_of_lt_floor (h : n < ⌊a⌋ₑ) :
    ↑n < a := by
  apply lt_of_lt_of_le _ <| floor_le (pos_of_floor_pos <| (zero_le n).trans_lt h).le
  rwa [← cast_enat_lt_iff (α := α)] at h

lemma floor_le_of_le (h : a ≤ n) : ⌊a⌋ₑ ≤ n := le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

lemma floor_le_one_of_le_one (h : a ≤ 1) :
    ⌊a⌋ₑ ≤ 1 :=
  floor_le_of_le <| h.trans_eq <| ENat.cast_one.symm

@[simp] lemma floor_eq_zero :
    ⌊a⌋ₑ = 0 ↔ a < 1 := by
  rw [lt_one_iff_eq_zero.symm, ← @cast_one α]
  exact floor_lt' one_ne_zero

@[simp] lemma preimage_floor_zero : (floor : α → ℕ∞) ⁻¹' {0} = Iio 1 := ext fun _ => floor_eq_zero

end LinearOrderedSemiring

end ENat
