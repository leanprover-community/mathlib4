/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.IntervalArithmetic.Interval
public import Mathlib.Order.Interval.Set.Defs
public meta import Mathlib.Data.Ineq

/-!
## Expr Helpers for Interval Arithmetic Tactics

This file defines several helper functions for working with expressions specific to the interval
arithmetic tactics.
-/

public meta section

open Lean Meta Mathlib IntervalArithmetic

namespace Lean.Expr

/-- If `e` is an `Expr` of the form `x.toSet φ` return `some (x, φ)`. -/
def IntervaltoSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Interval.toSet 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

/-- If `e` is an `Expr` of the form `r ∈ s` return `some (r, s)`. -/
def memSet? (e : Expr) : Option (Expr × Expr) :=
  if !(e.isAppOfArity' ``Membership.mem 5) then none
  else some ⟨e.getArg!' 4, e.getArg!' 3⟩

/-- If `e` is an `Expr` of the form `r ∈ x.toSet φ` return `some (r, x, φ)`. -/
def memIntervaltoSet? (e : Expr) : Option (Expr × Expr × Expr) := do
  let (r,s) ← memSet? e
  let (x, φ) ← IntervaltoSet? s
  return (r, x, φ)

/-- If `e` is an `Expr` of the form `r ∈ x.toSet φ`, and `r, x` are free variables, return
`(r.fvarId!, x.fvarId!, φ)`. -/
def intervalHyp? (e : Expr) : Option (FVarId × FVarId × Expr) := do
  let (r, x, φ) ← memIntervaltoSet? e
  return (← r.fvarId?, ← x.fvarId?, φ)

/-- Given `Expr`s `r, x, φ`, forms the `Expr`: `r ∈ x.toSet φ`. -/
def mkMemInterval (r x φ : Expr) : MetaM Expr := do
  return ← mkAppM ``Membership.mem #[(← mkAppM ``IntervalArithmetic.Interval.toSet #[φ, x]), r]

end Lean.Expr

section

variable {α : Type*} [Preorder α]

lemma le_of_mem_Ici {x a : α} (hx : x ∈ Set.Ici a) : a ≤ x := Set.mem_Ici.mp hx

lemma lt_of_mem_Ioi {x a : α} (hx : x ∈ Set.Ioi a) : a < x := Set.mem_Ioi.mp hx

lemma le_of_mem_Iic {x b : α} (hx : x ∈ Set.Iic b) : x ≤ b := Set.mem_Iic.mp hx

lemma lt_of_mem_Iio {x b : α} (hx : x ∈ Set.Iio b) : x < b := Set.mem_Iio.mp hx

lemma fst_le_of_mem_Ico {x a b : α} (hx : x ∈ Set.Ico a b) : a ≤ x := Set.mem_Ico.mp hx |>.1
lemma lt_snd_of_mem_Ico {x a b : α} (hx : x ∈ Set.Ico a b) : x < b := Set.mem_Ico.mp hx |>.2

lemma fst_lt_of_mem_Ioc {x a b : α} (hx : x ∈ Set.Ioc a b) : a < x := Set.mem_Ioc.mp hx |>.1
lemma le_snd_of_mem_Ioc {x a b : α} (hx : x ∈ Set.Ioc a b) : x ≤ b := Set.mem_Ioc.mp hx |>.2

lemma fst_le_of_mem_Icc {x a b : α} (hx : x ∈ Set.Icc a b) : a ≤ x := Set.mem_Icc.mp hx |>.1
lemma le_snd_of_mem_Icc {x a b : α} (hx : x ∈ Set.Icc a b) : x ≤ b := Set.mem_Icc.mp hx |>.2

lemma fst_lt_of_mem_Ioo {x a b : α} (hx : x ∈ Set.Ioo a b) : a < x := Set.mem_Ioo.mp hx |>.1
lemma lt_snd_of_mem_Ioo {x a b : α} (hx : x ∈ Set.Ioo a b) : x < b := Set.mem_Ioo.mp hx |>.2

lemma mem_Ici_of_le {x a : α} (hax : a ≤ x) : x ∈ Set.Ici a := Set.mem_Ici.mpr hax

lemma mem_Ioi_of_lt {x a : α} (hax : a < x) : x ∈ Set.Ioi a := Set.mem_Ioi.mpr hax

lemma mem_Iic_of_le {x b : α} (hxb : x ≤ b) : x ∈ Set.Iic b := Set.mem_Iic.mpr hxb

lemma mem_Iio_of_lt {x b : α} (hxb : x < b) : x ∈ Set.Iio b := Set.mem_Iio.mpr hxb

lemma mem_Ico_of_le_lt {x a b : α} (hax : a ≤ x) (hxb : x < b) : x ∈ Set.Ico a b :=
  Set.mem_Ico.mpr ⟨hax, hxb⟩

lemma mem_Ioc_of_lt_le {x a b : α} (hax : a < x) (hxb : x ≤ b) : x ∈ Set.Ioc a b :=
  Set.mem_Ioc.mpr ⟨hax, hxb⟩

lemma mem_Icc_of_le_le {x a b : α} (hax : a ≤ x) (hxb : x ≤ b) : x ∈ Set.Icc a b :=
  Set.mem_Icc.mpr ⟨hax, hxb⟩

lemma mem_Ioo_of_lt_lt {x a b : α} (hax : a < x) (hxb : x < b) : x ∈ Set.Ioo a b :=
  Set.mem_Ioo.mpr ⟨hax, hxb⟩

end

inductive IntervalClass
  | Ici : Expr → IntervalClass
  | Ioi : Expr → IntervalClass
  | Iic : Expr → IntervalClass
  | Iio : Expr → IntervalClass
  | Ico : Expr → Expr → IntervalClass
  | Ioc : Expr → Expr → IntervalClass
  | Icc : Expr → Expr → IntervalClass
  | Ioo : Expr → Expr → IntervalClass

/-- If `e` is an `Expr` of the form `Set.Ixy _`, return the corresponding `IntervalClass`. -/
def _root_.Lean.Expr.setInterval? (e : Expr) : Option IntervalClass :=
  match e.getAppFnArgs with
  | (``Set.Ici, #[_, _, a]) => some (.Ici a)
  | (``Set.Ioi, #[_, _, a]) => some (.Ioi a)
  | (``Set.Iic, #[_, _, b]) => some (.Iic b)
  | (``Set.Iio, #[_, _, b]) => some (.Iio b)
  | (``Set.Ico, #[_, _, a, b]) => some (.Ico a b)
  | (``Set.Ioc, #[_, _, a, b]) => some (.Ioc a b)
  | (``Set.Icc, #[_, _, a, b]) => some (.Icc a b)
  | (``Set.Ioo, #[_, _, a, b]) => some (.Ioo a b)
  | _ => none

/-- If `e` is an `Expr` of the form `r ∈ Set.Ixy a? b?`, return the `r` and the corresponding
`IntervalClass`. -/
def _root_.Lean.Expr.memSetInterval? (e : Expr) :
    Option (Expr × IntervalClass) := do
  let (r, s) ← e.memSet?
  let Ixx ← s.setInterval?
  return ⟨r, Ixx⟩

/-- If `e` is a proof of `r ∈ Set.Icc a b`, outputs proofs of `a ≤ r` and `r ≤ b`. Similar
for each `Set.Ixx`. -/
def _root_.Lean.Expr.memSetIntervalToIneqs? (e : Expr) : MetaM (Option Expr × Option Expr) := do
  let t ← inferType e
  let some (r, Ixx) := t.memSetInterval? | return (none, none)
  unless r.isFVar do
    return (none, none)
  match Ixx with
  | .Ici _ =>
      let h ← mkAppM ``le_of_mem_Ici #[e]
      return (some h, none)
  | .Ioi _ =>
      let h ← mkAppM ``lt_of_mem_Ioi #[e]
      return (some h, none)
  | .Iic _ =>
      let h ← mkAppM ``le_of_mem_Iic #[e]
      return (none, some h)
  | .Iio _ =>
      let h ← mkAppM ``lt_of_mem_Iio #[e]
      return (none, some h)
  | .Ico _ _ =>
      let h₁ ← mkAppM ``fst_le_of_mem_Ico #[e]
      let h₂ ← mkAppM ``lt_snd_of_mem_Ico #[e]
      return (some h₁, some h₂)
  | .Ioc _ _ =>
      let h₁ ← mkAppM ``fst_lt_of_mem_Ioc #[e]
      let h₂ ← mkAppM ``le_snd_of_mem_Ioc #[e]
      return (some h₁, some h₂)
  | .Icc _ _ =>
      let h₁ ← mkAppM ``fst_le_of_mem_Icc #[e]
      let h₂ ← mkAppM ``le_snd_of_mem_Icc #[e]
      return (some h₁, some h₂)
  | .Ioo _ _ =>
      let h₁ ← mkAppM ``fst_lt_of_mem_Ioo #[e]
      let h₂ ← mkAppM ``lt_snd_of_mem_Ioo #[e]
      return (some h₁, some h₂)

namespace IntervalArithmetic

/- `Option` version of `ineq?` -/
def _root_.Lean.Expr.ineq?? (e : Expr) : Option (Mathlib.Ineq × Expr × Expr × Expr) := do
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => none

end IntervalArithmetic
