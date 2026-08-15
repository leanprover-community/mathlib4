/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.Interval
public import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Dyadic
public meta import Mathlib.Tactic.Inclusion.Extension.DyadicReal.Family
public meta import Mathlib.Tactic.Inclusion.ExtensionAPI.Attr

/-!
# Basic dyadic interval operations for real expressions

This file defines the core operations for the `real.dyadic` inclusion family whose computational
implementations are suitable for general use.
-/

set_option linter.style.header false

@[expose] public section

namespace Inclusion

instance : ToSet (Interval Dyadic) ℝ where
  toSet I := (I.map Dyadic.toReal).toSet

def ofNat (n : ℕ) : Interval Dyadic := Interval.singleton Dyadic n

def add (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.lb with
    | some a, some b => some (a + b)
    | _, _ => ⊥
  ub := match x.ub, y.ub with
    | some a, some b => some (a + b)
    | _, _ => ⊤

def neg (x : Interval Dyadic) : Interval Dyadic where
  lb := match x.ub with
    | some a => some (-a)
    | ⊤ => ⊥
  ub := match x.lb with
    | some a => some (-a)
    | ⊥ => ⊤

def sub (x y : Interval Dyadic) : Interval Dyadic where
  lb := match x.lb, y.ub with
    | some a, some b => some (a - b)
    | _, _ => ⊥
  ub := match x.ub, y.lb with
    | some a, some b => some (a - b)
    | _, _ => ⊤

def le (x y : Interval Dyadic) : IntervalBool :=
  match x.ub, y.lb with
  | some xu, some yl => if xu ≤ yl then .true else .undetermined
  | _, _ => .undetermined

theorem mem_univ (r : ℝ) : r ∈ Interval.univ Dyadic := by
  constructor <;> simp [Interval.univ, Interval.map]

@[simp]
lemma toReal_add (a b : Dyadic) :
    Dyadic.toReal (a + b) = Dyadic.toReal a + Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_add]

@[simp]
lemma toReal_neg (a : Dyadic) : Dyadic.toReal (-a) = -Dyadic.toReal a := by
  simp [Dyadic.toReal, Dyadic.toRat_neg]

@[simp]
lemma toReal_sub (a b : Dyadic) :
    Dyadic.toReal (a - b) = Dyadic.toReal a - Dyadic.toReal b := by
  simp [Dyadic.toReal, Dyadic.toRat_sub]

lemma toReal_le_toReal {a b : Dyadic} : Dyadic.toReal a ≤ Dyadic.toReal b ↔ a ≤ b := by
  simp [Dyadic.toReal]

@[simp]
lemma toReal_min (a b : Dyadic) :
    Dyadic.toReal (min a b) = min (Dyadic.toReal a) (Dyadic.toReal b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (toReal_le_toReal.mpr h)]
  · rw [min_eq_right h, min_eq_right (toReal_le_toReal.mpr h)]

@[simp]
lemma toReal_max (a b : Dyadic) :
    Dyadic.toReal (max a b) = max (Dyadic.toReal a) (Dyadic.toReal b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (toReal_le_toReal.mpr h)]
  · rw [max_eq_left h, max_eq_left (toReal_le_toReal.mpr h)]

theorem map_inter (I J : Interval Dyadic) :
    (I.inter J).map Dyadic.toReal = (I.map Dyadic.toReal).inter (J.map Dyadic.toReal) := by
  rcases I with ⟨il, iu⟩
  rcases J with ⟨jl, ju⟩
  cases il <;> cases iu <;> cases jl <;> cases ju <;>
    simp [Interval.inter, Interval.map, toReal_min, toReal_max]

theorem inter_mem {r : ℝ} {I J : Interval Dyadic} (hI : r ∈ I) (hJ : r ∈ J) :
    r ∈ I.inter J := by
  change r ∈ (I.inter J).map Dyadic.toReal
  rw [map_inter]
  exact Refine.mem_refine (Iα := Interval ℝ)
    (hI : r ∈ I.map Dyadic.toReal) (hJ : r ∈ J.map Dyadic.toReal)

instance : Univ (Interval Dyadic) ℝ where
  univ := Interval.univ Dyadic
  mem_univ := mem_univ

instance : Refine (Interval Dyadic) ℝ where
  refine := Interval.inter
  mem_refine := inter_mem

theorem map_hull (I J : Interval Dyadic) :
    (I.hull J).map Dyadic.toReal = (I.map Dyadic.toReal).hull (J.map Dyadic.toReal) := by
  rcases I with ⟨il, iu⟩
  rcases J with ⟨jl, ju⟩
  cases il <;> cases iu <;> cases jl <;> cases ju <;>
    simp [Interval.hull, Interval.map, toReal_min, toReal_max]

theorem hull_mem_left {r : ℝ} {I J : Interval Dyadic} (hI : r ∈ I) : r ∈ I.hull J := by
  change r ∈ (I.hull J).map Dyadic.toReal
  rw [map_hull]
  exact Coarsen.mem_coarsen_left (Iα := Interval ℝ) (hI : r ∈ I.map Dyadic.toReal)

theorem hull_mem_right {r : ℝ} {I J : Interval Dyadic} (hJ : r ∈ J) : r ∈ I.hull J := by
  change r ∈ (I.hull J).map Dyadic.toReal
  rw [map_hull]
  exact Coarsen.mem_coarsen_right (Iα := Interval ℝ) (hJ : r ∈ J.map Dyadic.toReal)

instance : Coarsen (Interval Dyadic) ℝ where
  coarsen := Interval.hull
  mem_coarsen_left := hull_mem_left
  mem_coarsen_right := hull_mem_right

@[inclusionOp real.dyadic]
theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℝ) ∈ ofNat n := by
  constructor
  · exact WithBot.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]
  · exact WithTop.coe_le_coe.mpr <| by
      simp [Dyadic.toReal, Dyadic.toRat_natCast, Semiring.toGrindSemiring_ofNat ℝ n]

@[inclusionOp real.dyadic]
theorem add_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r + s ∈ add x y := by
  match x, y with
  | ⟨xl, xu⟩, ⟨yl, yu⟩ =>
    constructor
    · match xl, yl with
      | ⊥, _ => simp [add, Interval.map]
      | xl, ⊥ => cases xl <;> simp [add, Interval.map]
      | some a, some b =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_add]
          exact add_le_add (WithBot.coe_le_coe.mp hrx.1) (WithBot.coe_le_coe.mp hsy.1)
    · match xu, yu with
      | ⊤, _ => simp [add, Interval.map]
      | xu, ⊤ => cases xu <;> simp [add, Interval.map]
      | some a, some b =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_add]
          exact add_le_add (WithTop.coe_le_coe.mp hrx.2) (WithTop.coe_le_coe.mp hsy.2)

@[inclusionOp real.dyadic]
theorem neg_mem {r : ℝ} {x : Interval Dyadic} (hrx : r ∈ x) : -r ∈ neg x := by
  match x with
  | ⟨xl, xu⟩ =>
    constructor
    · match xu with
      | ⊤ => simp [neg, Interval.map]
      | some a =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_neg]
          exact neg_le_neg (WithTop.coe_le_coe.mp hrx.2)
    · match xl with
      | ⊥ => simp [neg, Interval.map]
      | some a =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_neg]
          exact neg_le_neg (WithBot.coe_le_coe.mp hrx.1)

@[inclusionOp real.dyadic]
theorem sub_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : r - s ∈ sub x y := by
  match x, y with
  | ⟨xl, xu⟩, ⟨yl, yu⟩ =>
    constructor
    · match xl, yu with
      | ⊥, _ => simp [sub, Interval.map]
      | xl, ⊤ => cases xl <;> simp [sub, Interval.map]
      | some a, some b =>
        exact WithBot.coe_le_coe.mpr <| by
          rw [toReal_sub]
          exact sub_le_sub (WithBot.coe_le_coe.mp hrx.1) (WithTop.coe_le_coe.mp hsy.2)
    · match xu, yl with
      | ⊤, _ => simp [sub, Interval.map]
      | xu, ⊥ => cases xu <;> simp [sub, Interval.map]
      | some a, some b =>
        exact WithTop.coe_le_coe.mpr <| by
          rw [toReal_sub]
          exact sub_le_sub (WithTop.coe_le_coe.mp hrx.2) (WithBot.coe_le_coe.mp hsy.1)

theorem mem_intervalBool_true {p : Prop} (hp : p) : p ∈ IntervalBool.true := by
  simpa [ToSet.toSet, IntervalBool.toPropSet] using hp

theorem mem_intervalBool_undetermined (p : Prop) : p ∈ IntervalBool.undetermined := by
  classical
  by_cases hp : p <;> simp [ToSet.toSet, IntervalBool.toPropSet, hp]

@[inclusionOp real.dyadic]
theorem le_mem {r s : ℝ} {x y : Interval Dyadic}
    (hrx : r ∈ x) (hsy : s ∈ y) : (r ≤ s) ∈ le x y := by
  match x, y with
  | ⟨_, some xu⟩, ⟨some yl, _⟩ =>
    simp only [le]
    split_ifs with h
    · apply mem_intervalBool_true
      exact (WithTop.coe_le_coe.mp hrx.2).trans
        ((Monotone.dyadicToReal h).trans (WithBot.coe_le_coe.mp hsy.1))
    · exact mem_intervalBool_undetermined _
  | ⟨_, ⊤⟩, _ | ⟨_, some _⟩, ⟨⊥, _⟩ => exact mem_intervalBool_undetermined _

end Inclusion
