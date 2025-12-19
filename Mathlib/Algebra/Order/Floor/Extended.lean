/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.Real.ENatENNReal

import Mathlib.Data.ENNReal.Operations

/-!
# Extended floor and ceil

This file defines the extended floor and ceil functions `ENat.floor, ENat.ceil : ℝ≥0∞ → ℕ∞`.

## Main declarations

* `ENat.floor r`: Greatest extended natural `n` such that `n ≤ r`.
* `ENat.ceil r`: Least extended natural `n` such that `r ≤ n`.

## Notation

* `⌊r⌋ₑ` is `ENat.floor r`.
* `⌈r⌉ₑ` is `ENat.ceil r`.

The index `ₑ` is used in analogy to the notation for `enorm`.

## TODO

The day Mathlib acquires `ENNRat`, it would be good to generalise this file to an `EFloorSemiring`
typeclass.

## Tags

efloor, eceil
-/

public section

open Set
open scoped ENNReal NNReal

namespace ENat
variable {r s : ℝ≥0∞} {n : ℕ∞}

/-- `⌊r⌋ₑ` is the greatest extended natural `n` such that `n ≤ r`. -/
@[expose] noncomputable def floor : ℝ≥0∞ → ℕ∞
  | ∞ => ⊤
  | (r : ℝ≥0) => ⌊r⌋₊

/-- `⌈r⌉ₑ` is the least extended natural `n` such that `r ≤ n` -/
@[expose] noncomputable def ceil : ℝ≥0∞ → ℕ∞
  | ∞ => ⊤
  | (r : ℝ≥0) => ⌈r⌉₊

@[inherit_doc] notation "⌊" r "⌋ₑ" => ENat.floor r
@[inherit_doc] notation "⌈" r "⌉ₑ" => ENat.ceil r

@[simp] lemma floor_top : ⌊∞⌋ₑ = ⊤ := rfl
@[simp] lemma ceil_top : ⌈∞⌉ₑ = ⊤ := rfl
@[simp, norm_cast] lemma floor_coe (r : ℝ≥0) : ⌊r⌋ₑ = ⌊r⌋₊ := rfl
@[simp, norm_cast] lemma ceil_coe (r : ℝ≥0) : ⌈r⌉ₑ = ⌈r⌉₊ := rfl

@[simp] lemma floor_eq_top : ⌊r⌋ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp
@[simp] lemma ceil_eq_top : ⌈r⌉ₑ = ⊤ ↔ r = ∞ := by cases r <;> simp
lemma floor_lt_top : ⌊r⌋ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp
@[simp] lemma ceil_lt_top : ⌈r⌉ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp

@[simp] lemma le_floor : n ≤ ⌊r⌋ₑ ↔ n ≤ r := by cases r <;> cases n <;> simp [Nat.le_floor_iff]
@[simp] lemma ceil_le : ⌈r⌉ₑ ≤ n ↔ r ≤ n := by cases r <;> cases n <;> simp
@[simp] lemma floor_lt : ⌊r⌋ₑ < n ↔ r < n := lt_iff_lt_of_le_iff_le le_floor
@[simp] lemma lt_ceil : n < ⌈r⌉ₑ ↔ n < r := lt_iff_lt_of_le_iff_le ceil_le

lemma gc_toENNReal_floor : GaloisConnection (↑) floor := fun _ _ ↦ le_floor.symm
lemma gc_ceil_toENNReal : GaloisConnection ceil (↑) := fun _ _ ↦ ceil_le

@[bound] lemma floor_le_self : ⌊r⌋ₑ ≤ r := le_floor.1 le_rfl
@[bound] lemma le_ceil_self : r ≤ ⌈r⌉ₑ := ceil_le.1 le_rfl

@[simp] lemma floor_le (hn : n ≠ ⊤) : ⌊r⌋ₑ ≤ n ↔ r < n + 1 := by simp [← lt_add_one_iff hn]

@[simp] lemma le_ceil (hn₀ : n ≠ 0) (hn : n ≠ ⊤) : n ≤ ⌈r⌉ₑ ↔ n - 1 < r := by
  lift n to ℕ using hn
  cases r
  · simp only [ceil_top, le_top, toENNReal_coe, true_iff]
    norm_cast
    exact ENNReal.coe_lt_top
  · simp only [ne_eq, Nat.cast_eq_zero, ceil_coe, Nat.cast_le, toENNReal_coe] at hn₀ ⊢
    norm_cast
    rw [← Nat.add_one_le_ceil_iff, Nat.sub_add_cancel]
    lia

@[simp] lemma lt_floor (hn : n ≠ ⊤) : n < ⌊r⌋ₑ ↔ n + 1 ≤ r := by simp [← add_one_le_iff hn]

@[simp] lemma ceil_lt (hn₀ : n ≠ 0) (hn : n ≠ ⊤) : ⌈r⌉ₑ < n ↔ r ≤ n - 1 := by
  simpa using (le_ceil hn₀ hn).not

lemma floor_mono : Monotone (floor : ℝ≥0∞ → ℕ∞) :=
  fun r s hrs ↦ by simpa using hrs.trans' floor_le_self

lemma ceil_mono : Monotone (ceil : ℝ≥0∞ → ℕ∞) := fun r s hrs ↦ by simpa using hrs.trans le_ceil_self

@[gcongr, bound] lemma floor_le_floor (hrs : r ≤ s) : ⌊r⌋ₑ ≤ ⌊s⌋ₑ := floor_mono hrs
@[gcongr, bound] lemma ceil_le_ceil (hrs : r ≤ s) : ⌈r⌉ₑ ≤ ⌈s⌉ₑ := ceil_mono hrs

@[simp] lemma floor_natCast (n : ℕ∞) : ⌊n⌋ₑ = n := eq_of_forall_le_iff fun r ↦ by simp
@[simp] lemma ceil_natCast (n : ℕ∞) : ⌈n⌉ₑ = n := eq_of_forall_ge_iff fun r ↦ by simp
@[simp] lemma floor_zero : ⌊0⌋ₑ = 0 := by simpa using floor_natCast 0
@[simp] lemma ceil_zero : ⌈0⌉ₑ = 0 := by simpa using ceil_natCast 0
@[simp] lemma floor_one : ⌊1⌋ₑ = 1 := by simpa using floor_natCast 1
@[simp] lemma ceil_one : ⌈1⌉ₑ = 1 := by simpa using ceil_natCast 1
@[simp] lemma floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊ofNat(n)⌋ₑ = ofNat(n) := ENat.floor_natCast n
@[simp] lemma ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈ofNat(n)⌉ₑ = ofNat(n) := ENat.ceil_natCast n

lemma floor_pos : 0 < ⌊r⌋ₑ ↔ 1 ≤ r := by simp
lemma ceil_pos : 0 < ⌈r⌉ₑ ↔ 0 < r := by simp

@[simp] lemma floor_eq_zero : ⌊r⌋ₑ = 0 ↔ r < 1 := by simp [← nonpos_iff_eq_zero]
@[simp] lemma ceil_eq_zero : ⌈r⌉ₑ = 0 ↔ r = 0 := by simpa using ceil_le (n := 0)

@[bound] lemma floor_le_ceil : ⌊r⌋ₑ ≤ ⌈r⌉ₑ := mod_cast floor_le_self.trans le_ceil_self

@[bound] lemma ceil_le_floor_add_one : ∀ r : ℝ≥0∞, ⌈r⌉ₑ ≤ ⌊r⌋ₑ + 1
  | ∞ => le_rfl
  | (r : ℝ≥0) => by simpa using mod_cast Nat.ceil_le_floor_add_one r

lemma floor_lt_ceil (hrs : r < s) : ⌊r⌋ₑ < ⌈s⌉ₑ := floor_lt.2 <| hrs.trans_le le_ceil_self

lemma floor_congr (h : ∀ n : ℕ∞, n ≤ r ↔ n ≤ s) : ⌊r⌋ₑ = ⌊s⌋ₑ := eq_of_forall_le_iff <| by simpa
lemma ceil_congr (h : ∀ n : ℕ∞, r ≤ n ↔ s ≤ n) : ⌈r⌉ₑ = ⌈s⌉ₑ := eq_of_forall_ge_iff <| by simpa

@[simp] lemma floor_add_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌊r + n⌋ₑ = ⌊r⌋ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_add_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact n.floor_add_natCast zero_le'

@[simp] lemma ceil_add_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌈r + n⌉ₑ = ⌈r⌉ₑ + n
  | ∞, _ => by simp
  | _, ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_add_natCast]; norm_cast; exact Nat.ceil_add_natCast zero_le' _

@[simp] lemma floor_toENNReal_add (r : ℝ≥0∞) (n : ℕ∞) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := by
  simp [add_comm, floor_add_toENNReal]

@[simp] lemma ceil_toENNReal_add (r : ℝ≥0∞) (n : ℕ∞) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := by
  simp [add_comm, ceil_add_toENNReal]

@[simp] lemma floor_add_natCast (r : ℝ≥0∞) (n : ℕ) : ⌊r + n⌋ₑ = ⌊r⌋ₑ + n := floor_add_toENNReal r n
@[simp] lemma ceil_add_natCast (r : ℝ≥0∞) (n : ℕ) : ⌈r + n⌉ₑ = ⌈r⌉ₑ + n := ceil_add_toENNReal r n

@[simp] lemma floor_natCast_add (r : ℝ≥0∞) (n : ℕ) : ⌊n + r⌋ₑ = n + ⌊r⌋ₑ := floor_toENNReal_add r n
@[simp] lemma ceil_natCast_add (r : ℝ≥0∞) (n : ℕ) : ⌈n + r⌉ₑ = n + ⌈r⌉ₑ := ceil_toENNReal_add r n

@[simp] lemma floor_add_one (r : ℝ≥0∞) : ⌊r + 1⌋ₑ = ⌊r⌋ₑ + 1 := mod_cast floor_add_natCast r 1
@[simp] lemma ceil_add_one (r : ℝ≥0∞) : ⌈r + 1⌉ₑ = ⌈r⌉ₑ + 1 := mod_cast ceil_add_natCast r 1

@[simp]
lemma floor_add_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌊r + ofNat(n)⌋ₑ = ⌊r⌋ₑ + ofNat(n) :=
  floor_add_natCast r n

@[simp]
lemma ceil_add_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n) :=
  ceil_add_natCast r n

@[simp] lemma floor_sub_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌊r - n⌋ₑ = ⌊r⌋ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : ℕ) => by simp
  | (r : ℝ≥0), ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.floor_sub_natCast ..

@[simp] lemma ceil_sub_toENNReal : ∀ (r : ℝ≥0∞) (n : ℕ∞), ⌈r - n⌉ₑ = ⌈r⌉ₑ - n
  | ∞, ⊤ => by simp
  | ∞, (n : ℕ) => by simp
  | (r : ℝ≥0), ⊤ => by simp
  | (r : ℝ≥0), (n : ℕ) => by
    -- FIXME: Why does `norm_cast` not use `ENNReal.ofNNReal_sub_natCast`?
    norm_cast; rw [← ENNReal.ofNNReal_sub_natCast]; norm_cast; exact Nat.ceil_sub_natCast ..

@[simp] lemma floor_sub_natCast (r : ℝ≥0∞) (n : ℕ) : ⌊r - n⌋ₑ = ⌊r⌋ₑ - n := floor_sub_toENNReal r n
@[simp] lemma ceil_sub_natCast (r : ℝ≥0∞) (n : ℕ) : ⌈r - n⌉ₑ = ⌈r⌉ₑ - n := ceil_sub_toENNReal r n

@[simp] lemma floor_sub_one (r : ℝ≥0∞) : ⌊r - 1⌋ₑ = ⌊r⌋ₑ - 1 := mod_cast floor_sub_toENNReal r 1
@[simp] lemma ceil_sub_one (r : ℝ≥0∞) : ⌈r - 1⌉ₑ = ⌈r⌉ₑ - 1 := mod_cast ceil_sub_toENNReal r 1

@[simp]
lemma floor_sub_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n) :=
  floor_sub_toENNReal r n

@[simp] lemma ceil_sub_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    ⌈r - ofNat(n)⌉ₑ = ⌈r⌉ₑ - ofNat(n) := ceil_sub_toENNReal r n

@[bound]
lemma ceil_lt_add_one (hr : r ≠ ∞) : (⌈r⌉ₑ : ℝ≥0∞) < r + 1 := by
  lift r to ℝ≥0 using hr; simpa using mod_cast Nat.ceil_lt_add_one (zero_le r)

@[bound]
lemma ceil_add_le : ∀ (r s : ℝ≥0∞), ⌈r + s⌉ₑ ≤ ⌈r⌉ₑ + ⌈s⌉ₑ
  | ∞, _ => by simp
  | _, ∞ => by simp
  | (r : ℝ≥0), (s : ℝ≥0) => mod_cast Nat.ceil_add_le r s

@[simp] lemma toENNReal_iSup {ι : Sort*} (f : ι → ℕ∞) :
    toENNReal (⨆ i, f i) = ⨆ i, toENNReal (f i) := eq_of_forall_ge_iff fun _ ↦ by simp [← le_floor]

@[simp] lemma toENNReal_iInf {ι : Sort*} (f : ι → ℕ∞) :
    toENNReal (⨅ i, f i) = ⨅ i, toENNReal (f i) := eq_of_forall_le_iff fun _ ↦ by simp [← ceil_le]

end ENat

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

set_option backward.privateInPublic true in
private alias ⟨_, natCeil_pos⟩ := ENat.ceil_pos

/-- Extension for the `positivity` tactic: `ENat.ceil` is positive if its input is. -/
@[positivity ⌈_⌉ₑ]
meta def evalENatCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ∞), ~q(ENat.ceil $r) =>
    assertInstancesCommute
    match ← core q(inferInstance) q(inferInstance) r with
    | .positive pr =>
      assertInstancesCommute
      pure (.positive q(natCeil_pos $pr))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on ENat.ceil application"

example {r : ℝ≥0∞} (hr : 0 < r) : 0 < ⌈r⌉ₑ := by positivity

end Mathlib.Meta.Positivity
