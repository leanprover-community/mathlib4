/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.NegLog
public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Monoid.TypeTags
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Additive valuations attached to multiplicative valuations

A valuation with values in `Mᵐ⁰ = WithZero (Multiplicative M)` carries the same information as an
additive valuation with values in `WithTop M = M ∪ {∞}`, the dictionary between the two being
`WithZero.negLog`, which sends `WithZero.exp m` to `-m` and `0` to `∞`. This file records that
translation.

`Valuation.toAddValuation` already exhibits the bijection
`Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ`, but its codomain is a type synonym for `Γ₀`
itself, whereas an additive valuation is usually taken to have values in a type of the shape
`M ∪ {∞}`. Composing it with the order-and-additive isomorphism `WithZero.orderAddIsoWithTop`
lands in `WithTop M`.

## Main definitions

* `Valuation.addVal`: the additive valuation `R → WithTop M` attached to a valuation
  `v : Valuation R Mᵐ⁰`, sending `x` to `WithZero.negLog (v x)`.
* `Valuation.addValValueGroup`: the additive valuation attached to an arbitrary valuation
  `v : Valuation R Γ₀`, with values in `WithTop` of the value group of `v` written additively.

## Main results

* `Valuation.addVal_eq_top` and `Valuation.addVal_eq_coe`: the two halves of the characterisation
  of `Valuation.addVal`, namely `v.addVal x = ∞ ↔ v x = 0` and
  `v.addVal x = m ↔ v x = WithZero.exp (-m)`.
* `Valuation.addVal_map`: `Valuation.addVal` is natural in `M`, in the sense that pushing `v`
  forward along `WithZero.mapAddHom' f` pushes `v.addVal` forward along `f`.
-/

@[expose] public section

open scoped WithZero

namespace Valuation

open WithZero

variable {R M N : Type*} [Ring R] [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
  [AddCommGroup N] [LinearOrder N] [IsOrderedAddMonoid N]

/-- The additive valuation with values in `WithTop M = M ∪ {∞}` attached to a valuation `v` with
values in `Mᵐ⁰`: it sends `x` to `WithZero.negLog (v x)`, so that `WithZero.exp m ↦ -m` and
`0 ↦ ∞`. -/
def addVal (v : Valuation R Mᵐ⁰) : AddValuation R (WithTop M) :=
  v.toAddValuation.map (orderAddIsoWithTop M).toAddEquiv.toAddMonoidHom rfl
    (orderAddIsoWithTop M).toOrderIso.monotone

@[simp]
lemma addVal_apply (v : Valuation R Mᵐ⁰) (x : R) : v.addVal x = negLog (v x) := rfl

@[simp]
lemma addVal_eq_top {v : Valuation R Mᵐ⁰} {x : R} : v.addVal x = ⊤ ↔ v x = 0 := by
  simp

lemma addVal_eq_coe {v : Valuation R Mᵐ⁰} {x : R} {m : M} :
    v.addVal x = (m : WithTop M) ↔ v x = exp (-m) :=
  negLog_eq_coe

/-- `Valuation.addVal` is natural in `M`: pushing a valuation forward along `WithZero.mapAddHom' f`
pushes its additive valuation forward along `f`. -/
lemma addVal_map (v : Valuation R Mᵐ⁰) {f : M →+ N} (hf : StrictMono f) (x : R) :
    (v.map (mapAddHom' f) (mapAddHom'_strictMono hf).monotone).addVal x =
    WithTop.map f (v.addVal x) :=
  negLog_mapAddHom' f (v x)

/-! ### The additive valuation with values in the value group -/

section ValueGroup

open MonoidWithZeroHom

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)

/-- The additive valuation attached to an arbitrary valuation `v : Valuation R Γ₀`, with values in
`WithTop` of the value group of `v` written additively. -/
noncomputable def addValValueGroup :
    AddValuation R (WithTop (Additive (valueGroup (.ofClass v)))) :=
  addVal (M := Additive (valueGroup (.ofClass v))) v.restrict

@[simp]
lemma addValValueGroup_apply (x : R) :
  v.addValValueGroup x = negLog (M := Additive (valueGroup (.ofClass v))) (v.restrict x) := rfl

end ValueGroup

end Valuation
