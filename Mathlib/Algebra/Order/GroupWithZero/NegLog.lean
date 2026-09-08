/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Hom.Monoid

/-!
# `negLog : Mᵐ⁰ → WithTop M`

This file identifies `Mᵐ⁰ = WithZero (Multiplicative M)` with `WithTop M`, in the form of the
order-and-additive isomorphism `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`.

The underlying map is `WithZero.negLog`, which is `WithZero.log` in its "additive valuation"
reading: instead of the junk value `log 0 = 0` we record `0` as the genuine `⊤`, and we negate,
so that the reversed order on `Mᵐ⁰` becomes the usual order on `WithTop M`.

## Main definitions

* `WithZero.negLog : Mᵐ⁰ → WithTop M`, sending `0 ↦ ⊤` and `exp m ↦ -m`.
* `WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M`, the order-and-additive
  isomorphism underlying it. `(Additive Mᵐ⁰)ᵒᵈ` is the additive-with-`⊤` rendering of `Mᵐ⁰`
  provided by `Mathlib/Algebra/Order/GroupWithZero/Canonical.lean`; this isomorphism turns it
  into the familiar `WithTop M = M ∪ {∞}`.
* `WithZero.mapAddHom : (M →+ N) → (Mᵐ⁰ →*₀ Nᵐ⁰)`, the functoriality of `Mᵐ⁰` in `M`, along
  which `negLog` is natural (`WithZero.negLog_mapAddHom`).
-/

@[expose] public section

open scoped WithZero

namespace WithZero

/-! ### `negLog` -/

section NegLog

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The map `Mᵐ⁰ → WithTop M` sending `0` to `⊤` and `exp m` to `-m`.

This is `WithZero.log` in its "additive valuation" reading: instead of the junk value `log 0 = 0`
we record `0` as the genuine `⊤`, and we negate, so that the reversed order on `Mᵐ⁰` becomes the
usual order on `WithTop M`. -/
def negLog (x : Mᵐ⁰) : WithTop M := expRecOn x ⊤ fun m ↦ ((-m : M) : WithTop M)

@[simp]
lemma negLog_zero : negLog (0 : Mᵐ⁰) = ⊤ := rfl

@[simp]
lemma negLog_exp (m : M) : negLog (exp m) = ((-m : M) : WithTop M) := rfl

@[simp]
lemma negLog_eq_top {x : Mᵐ⁰} : negLog x = ⊤ ↔ x = 0 := by
  induction x using expRecOn <;>
    simp [-WithTop.LinearOrderedAddCommGroup.coe_neg]

@[simp]
lemma negLog_one : negLog (1 : Mᵐ⁰) = 0 := by
  rw [← exp_zero, negLog_exp, neg_zero, WithTop.coe_zero]

lemma negLog_eq_coe {x : Mᵐ⁰} {m : M} : negLog x = (m : WithTop M) ↔ x = exp (-m) := by
  induction x using expRecOn with
  | zero => exact ⟨fun h ↦ absurd h (by simp), fun h ↦ absurd h.symm exp_ne_zero⟩
  | exp a => rw [negLog_exp, WithTop.coe_inj, exp_inj, neg_eq_iff_eq_neg]

lemma negLog_mul (x y : Mᵐ⁰) : negLog (x * y) = negLog x + negLog y := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => rw [← exp_add, negLog_exp, negLog_exp, negLog_exp, neg_add, WithTop.coe_add]

variable [LinearOrder M] [IsOrderedAddMonoid M]

lemma negLog_le_negLog {x y : Mᵐ⁰} : negLog x ≤ negLog y ↔ y ≤ x := by
  induction x using expRecOn with
  | zero => simp
  | exp a =>
    induction y using expRecOn with
    | zero => simp
    | exp b => rw [negLog_exp, negLog_exp, WithTop.coe_le_coe, neg_le_neg_iff, exp_le_exp]

variable (M) in
/-- The order-and-additive isomorphism `(Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M` underlying `negLog`.

`(Additive Mᵐ⁰)ᵒᵈ` is the additive-with-`⊤` rendering of `Mᵐ⁰`; this isomorphism turns it into
the familiar `WithTop M = M ∪ {∞}`. -/
def orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M where
  toFun x := negLog x
  invFun y := y.recTopCoe (0 : Mᵐ⁰) fun m ↦ exp (-m)
  left_inv x := by
    induction x using expRecOn with
    | zero => rfl
    | exp a => change exp (- -a) = exp a; rw [neg_neg]
  right_inv y := by
    induction y using WithTop.recTopCoe with
    | top => rfl
    | coe m => change negLog (exp (-m)) = (m : WithTop M); rw [negLog_exp, neg_neg]
  map_add' := negLog_mul
  map_le_map_iff' := negLog_le_negLog

@[simp]
lemma orderAddIsoWithTop_apply (x : (Additive Mᵐ⁰)ᵒᵈ) : orderAddIsoWithTop M x = negLog x := rfl

end NegLog

/-! ### Functoriality: `Mᵐ⁰ →*₀ Nᵐ⁰` from `M →+ N` -/

section MapAddHom

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The monoid-with-zero hom `Mᵐ⁰ →*₀ Nᵐ⁰` induced by an additive hom `f : M →+ N`.

This is `WithZero.map'` for the multiplicative reading of `f`. -/
def mapAddHom (f : M →+ N) : Mᵐ⁰ →*₀ Nᵐ⁰ := map' (AddMonoidHom.toMultiplicative f)

@[simp]
lemma mapAddHom_exp (f : M →+ N) (m : M) : mapAddHom f (exp m) = exp (f m) := rfl

lemma mapAddHom_strictMono [Preorder M] [Preorder N] {f : M →+ N} (hf : StrictMono f) :
    StrictMono (mapAddHom f) :=
  map'_strictMono fun _ _ h ↦ hf h

/-- `negLog` is natural in `M`. -/
lemma negLog_mapAddHom (f : M →+ N) (x : Mᵐ⁰) :
    negLog (mapAddHom f x) = WithTop.map f (negLog x) := by
  induction x using expRecOn with
  | zero => rfl
  | exp a => rw [mapAddHom_exp, negLog_exp, negLog_exp, WithTop.map_coe, map_neg]

end MapAddHom

end WithZero
