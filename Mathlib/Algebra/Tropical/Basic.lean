/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Order.Hom.Basic
public import Mathlib.Algebra.NeZero

/-!

# Tropical algebraic structures

This file defines algebraic structures of the min/max-tropical numbers, up to the tropical semiring.
All declarations about `MinTropical` are translated to `MaxTropical` using `to_dual`.
Some basic lemmas about conversion from the base type `R` to `MinTropical R`/`MaxTropical R` are
provided, as well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `MinTropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (MinTropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (MinTropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `MinTropical (WithTop R)`.

## Implementation notes

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (MinTropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/

@[expose] public section

assert_not_exists Nat.instMulOneClass

universe u v

variable (R : Type u)

/-- The min-tropicalization of a type `R`. -/
@[to_dual /-- The max-tropicalization of a type `R`. -/]
def MinTropical : Type u :=
  R

/-- The min-tropicalization of a type `R`. -/
@[deprecated MinTropical (since := "2026-07-24")]
def Tropical : Type u :=
  R

variable {R}

namespace MinTropical

/-- Reinterpret `x : R` as an element of `MinTropical R`.
See `MinTropical.tropEquiv` for the equivalence. -/
@[to_dual
/-- Reinterpret `x : R` as an element of `MaxTropical R`.
See `MaxTropical.tropEquiv` for the equivalence. -/]
def trop : R → MinTropical R :=
  id

/-- Reinterpret `x : MinTropical R` as an element of `R`.
See `MinTropical.tropEquiv` for the equivalence. -/
@[to_dual (attr := pp_nodot)
/-- Reinterpret `x : MaxTropical R` as an element of `R`.
See `MaxTropical.tropEquiv` for the equivalence. -/]
def untrop : MinTropical R → R :=
  id

@[to_dual]
theorem trop_injective : Function.Injective (trop : R → MinTropical R) := fun _ _ => id

@[to_dual]
theorem untrop_injective : Function.Injective (untrop : MinTropical R → R) := fun _ _ => id

@[to_dual (attr := simp)]
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem untrop_inj_iff (x y : MinTropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl

@[to_dual (attr := simp)]
theorem trop_untrop (x : MinTropical R) : trop (untrop x) = x :=
  rfl

@[to_dual (attr := simp)]
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl

attribute [irreducible] MinTropical MaxTropical

@[to_dual]
theorem leftInverse_trop : Function.LeftInverse (trop : R → MinTropical R) untrop :=
  trop_untrop

@[to_dual]
theorem rightInverse_trop : Function.RightInverse (trop : R → MinTropical R) untrop :=
  untrop_trop

/-- Reinterpret `x : R` as an element of `MinTropical R`.
See `MinTropical.tropOrderIso` for the order-preserving equivalence. -/
@[to_dual
/-- Reinterpret `x : R` as an element of `MaxTropical R`.
See `MaxTropical.tropOrderIso` for the order-preserving equivalence. -/]
def tropEquiv : R ≃ MinTropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop

@[to_dual (attr := simp)]
theorem tropEquiv_coe_fn : (tropEquiv : R → MinTropical R) = trop :=
  rfl

@[to_dual (attr := simp)]
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : MinTropical R → R) = untrop :=
  rfl

@[to_dual]
theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.eq_symm_apply.symm

@[to_dual]
theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.eq_symm_apply.symm

@[to_dual]
theorem injective_trop : Function.Injective (trop : R → MinTropical R) :=
  tropEquiv.injective

@[to_dual]
theorem injective_untrop : Function.Injective (untrop : MinTropical R → R) :=
  tropEquiv.symm.injective

@[to_dual]
theorem surjective_trop : Function.Surjective (trop : R → MinTropical R) :=
  tropEquiv.surjective

@[to_dual]
theorem surjective_untrop : Function.Surjective (untrop : MinTropical R → R) :=
  tropEquiv.symm.surjective

@[to_dual]
instance [Inhabited R] : Inhabited (MinTropical R) :=
  ⟨trop default⟩

/-- Recursing on an `x' : MinTropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `MinTropical R` via `trop x`. -/
@[to_dual (attr := simp)
/-- Recursing on an `x' : MaxTropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `MaxTropical R` via `trop x`. -/]
def tropRec {F : MinTropical R → Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)

@[to_dual]
instance [DecidableEq R] : DecidableEq (MinTropical R) := fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

@[to_dual]
instance [LE R] : LE (MinTropical R) where le x y := untrop x ≤ untrop y

@[to_dual (attr := simp)]
theorem untrop_le_iff [LE R] {x y : MinTropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl

@[to_dual]
instance [LE R] [DecidableLE R] : DecidableLE (MinTropical R) :=
  inferInstanceAs <| DecidableLE R

@[to_dual]
instance [LT R] : LT (MinTropical R) where lt x y := untrop x < untrop y

@[to_dual (attr := simp)]
theorem untrop_lt_iff [LT R] {x y : MinTropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl

@[to_dual]
instance [LT R] [DecidableLT R] : DecidableLT (MinTropical R) :=
  inferInstanceAs <| DecidableLT R

@[to_dual]
instance [Preorder R] : Preorder (MinTropical R) where
  le_refl := fun x => le_refl (untrop x)
  le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
  lt_iff_le_not_ge := fun _ _ => lt_iff_le_not_ge (α := R)

/-- Reinterpret `x : R` as an element of `MinTropical R`, preserving the order. -/
@[to_dual
/-- Reinterpret `x : R` as an element of `MaxTropical R`, preserving the order. -/]
def tropOrderIso [Preorder R] : R ≃o MinTropical R :=
  { tropEquiv with map_rel_iff' := untrop_le_iff }

@[to_dual (attr := simp)]
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R → MinTropical R) = trop :=
  rfl

@[to_dual (attr := simp)]
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : MinTropical R → R) = untrop :=
  rfl

@[to_dual]
theorem trop_monotone [Preorder R] : Monotone (trop : R → MinTropical R) := fun _ _ => id

@[to_dual]
theorem untrop_monotone [Preorder R] : Monotone (untrop : MinTropical R → R) := fun _ _ => id

@[to_dual]
instance [PartialOrder R] : PartialOrder (MinTropical R) where
  le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h')

@[to_dual]
instance [Top R] : Zero (MinTropical R) :=
  ⟨trop ⊤⟩

@[to_dual]
instance [Top R] : Top (MinTropical R) :=
  ⟨0⟩

@[to_dual (attr := simp)]
theorem untrop_zero [Top R] : untrop (0 : MinTropical R) = ⊤ :=
  rfl

@[to_dual (attr := simp)]
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl

@[to_dual (attr := simp)]
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  nofun

@[to_dual (attr := simp)]
theorem zero_ne_trop_coe (x : R) : 0 ≠ (trop x : MinTropical (WithTop R)) :=
  nofun

@[to_dual (attr := simp)]
theorem le_zero [LE R] [OrderTop R] (x : MinTropical R) : x ≤ 0 :=
  le_top (α := R)

@[to_dual]
instance [LE R] [OrderTop R] : OrderTop (MinTropical R) where
  le_top _ := le_top (α := R)

variable [LinearOrder R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
@[to_dual /-- Tropical addition is the maximum of two underlying elements of `R`. -/]
instance : Add (MinTropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

@[to_dual]
instance : AddCommSemigroup (MinTropical R) where
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[to_dual (attr := simp)]
theorem untrop_add (x y : MinTropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl

@[to_dual (attr := simp)]
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl

@[to_dual (attr := simp)]
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl

@[to_dual]
theorem trop_add_def (x y : MinTropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl

instance : LinearOrder (MinTropical R) where
  le_total := fun a b => le_total (untrop a) (untrop b)
  toDecidableLE := MinTropical.instDecidableLE
  toDecidableEq := MinTropical.instDecidableEq
  toDecidableLT := MinTropical.instDecidableLT
  max := fun a b => trop (max (untrop a) (untrop b))
  max_def := fun a b => untrop_injective (by
    simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
  min := (· + ·)
  min_def := fun a b => untrop_injective (by
    simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp)

@[to_dual existing]
instance _root_.MaxTropical.instLinearOrder : LinearOrder (MaxTropical R) where
  le_total := fun a b => le_total (MaxTropical.untrop a) (MaxTropical.untrop b)
  toDecidableLE := MaxTropical.instDecidableLE
  toDecidableEq := MaxTropical.instDecidableEq
  toDecidableLT := MaxTropical.instDecidableLT
  min := fun a b => MaxTropical.trop (min (MaxTropical.untrop a) (MaxTropical.untrop b))
  min_def := fun a b => MaxTropical.untrop_injective (by
    simp only [min_def, MaxTropical.untrop_le_iff, MaxTropical.untrop_trop]; split_ifs <;> simp)
  max := (· + ·)
  max_def := fun a b => MaxTropical.untrop_injective (by
    simp only [MaxTropical.untrop_add, max_def, MaxTropical.untrop_le_iff]; split_ifs <;> simp)

@[to_dual (attr := simp)]
theorem untrop_sup (x y : MinTropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl

@[to_dual (attr := simp)]
theorem untrop_max (x y : MinTropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl

@[to_dual (attr := simp)]
theorem min_eq_add : (min : MinTropical R → MinTropical R → MinTropical R) = (· + ·) :=
  rfl

@[to_dual (attr := simp)]
theorem inf_eq_add : ((· ⊓ ·) : MinTropical R → MinTropical R → MinTropical R) = (· + ·) :=
  rfl

@[to_dual]
theorem trop_max_def (x y : MinTropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl

@[to_dual]
theorem trop_sup_def (x y : MinTropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl

@[to_dual (attr := simp)]
theorem add_eq_left ⦃x y : MinTropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective (by simpa using h)

@[to_dual (attr := simp)]
theorem add_eq_right ⦃x y : MinTropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective (by simpa using h)

@[to_dual]
theorem add_eq_left_iff {x y : MinTropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]

@[to_dual]
theorem add_eq_right_iff {x y : MinTropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]

@[to_dual]
theorem add_self (x : MinTropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)

@[to_dual]
theorem add_eq_iff {x y z : MinTropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]

@[to_dual (attr := simp)]
theorem add_eq_zero_iff {a b : MinTropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp

@[to_dual]
instance [OrderTop R] : AddCommMonoid (MinTropical R) where
  zero_add _ := untrop_injective (min_top_left _)
  add_zero _ := untrop_injective (min_top_right _)
  nsmul := nsmulRec

end Order

section Monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
@[to_dual /-- Tropical multiplication is the addition in the underlying `R`. -/]
instance [Add R] : Mul (MinTropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

@[to_dual (attr := simp)]
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl

@[to_dual (attr := simp)] theorem untrop_mul [Add R] (x y : MinTropical R) :
    untrop (x * y) = untrop x + untrop y :=
  rfl

@[to_dual]
theorem trop_mul_def [Add R] (x y : MinTropical R) : x * y = trop (untrop x + untrop y) :=
  rfl

/-- The ring structure on `MinTropical R` is the same as on `MaxTropical Rᵒᵈ`. -/
@[to_dual /-- The ring structure on `MaxTropical R` is the same as on `MinTropical Rᵒᵈ`. -/]
def equivMaxTropical [LinearOrder R] [Add R] : MinTropical R ≃+* MaxTropical Rᵒᵈ where
  toFun a := .trop (OrderDual.toDual a.untrop)
  invFun a := .trop (OrderDual.ofDual a.untrop)
  map_add' a b := by simp
  map_mul' a b := by simp

@[to_dual]
instance [Zero R] : One (MinTropical R) :=
  ⟨trop 0⟩

@[to_dual (attr := simp)]
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl

@[to_dual (attr := simp)]
theorem untrop_one [Zero R] : untrop (1 : MinTropical R) = 0 :=
  rfl

@[to_dual]
instance [LinearOrder R] [OrderTop R] [Zero R] : AddMonoidWithOne (MinTropical R) where
  natCast := fun n => if n = 0 then 0 else 1
  natCast_zero := rfl
  natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp)

@[to_dual]
instance [Zero R] : Nontrivial (MinTropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

@[to_dual]
instance [Neg R] : Inv (MinTropical R) :=
  ⟨fun x => trop (-untrop x)⟩

@[to_dual (attr := simp)]
theorem untrop_inv [Neg R] (x : MinTropical R) : untrop x⁻¹ = -untrop x :=
  rfl

@[to_dual]
instance [Sub R] : Div (MinTropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

@[to_dual (attr := simp)]
theorem untrop_div [Sub R] (x y : MinTropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl

@[to_dual]
instance [AddSemigroup R] : Semigroup (MinTropical R) where
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)

@[to_dual]
instance [AddCommSemigroup R] : CommSemigroup (MinTropical R) where
  mul_comm := fun _ _ => untrop_injective (add_comm _ _)

@[to_dual]
instance {α : Type*} [SMul α R] : Pow (MinTropical R) α where pow x n := trop <| n • untrop x

@[to_dual (attr := simp)]
theorem untrop_pow {α : Type*} [SMul α R] (x : MinTropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl

@[to_dual (attr := simp)]
theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl

@[to_dual]
instance [AddZeroClass R] : MulOneClass (MinTropical R) where
  one_mul _ := untrop_injective <| zero_add _
  mul_one _ := untrop_injective <| add_zero _

@[to_dual]
instance [AddMonoid R] : Monoid (MinTropical R) where
  npow := fun n x => x ^ n
  npow_zero := fun _ => untrop_injective <| by simp
  npow_succ := fun _ _ => untrop_injective <| succ_nsmul _ _

@[to_dual (attr := simp)]
theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl

@[to_dual]
instance [AddCommMonoid R] : CommMonoid (MinTropical R) where

@[to_dual]
instance [AddGroup R] : Group (MinTropical R) where
  div_eq_mul_inv := fun _ _ => untrop_injective <| by simp [sub_eq_add_neg]
  inv_mul_cancel := fun _ => untrop_injective <| neg_add_cancel _
  zpow := fun n x => trop <| n • untrop x
  zpow_zero' := fun _ => untrop_injective <| zero_zsmul _
  zpow_succ' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_succ' _ _
  zpow_neg' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_neg' _ _

@[to_dual]
instance [AddCommGroup R] : CommGroup (MinTropical R) where
  mul_comm := fun _ _ => untrop_injective (add_comm _ _)

@[to_dual (attr := simp)]
theorem untrop_zpow [AddGroup R] (x : MinTropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl

@[to_dual (attr := simp)]
theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl

end Monoid

section Distrib

instance mulLeftMono [LE R] [Add R] [AddLeftMono R] : MulLeftMono (MinTropical R) :=
  ⟨fun _ y z h => add_le_add_right (show untrop y ≤ untrop z from h) _⟩

instance mulRightMono [LE R] [Add R] [AddRightMono R] :
    MulRightMono (MinTropical R) :=
  ⟨fun _ y z h => add_le_add_left (show untrop y ≤ untrop z from h) _⟩

instance addLeftMono [LinearOrder R] : AddLeftMono (MinTropical R) :=
  ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩

instance mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] :
    MulLeftStrictMono (MinTropical R) :=
  ⟨fun _ _ _ h => add_lt_add_right (untrop_lt_iff.2 h) _⟩

instance mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] :
    MulRightStrictMono (MinTropical R) :=
  ⟨fun _ y z h => add_lt_add_left (show untrop y < untrop z from h) _⟩


@[to_dual existing]
instance _root_.MaxTropical.mulLeftMono [LE R] [Add R] [AddLeftMono R] :
    MulLeftMono (MaxTropical R) :=
  ⟨fun _ y z h => add_le_add_right (show MaxTropical.untrop y ≤ MaxTropical.untrop z from h) _⟩

@[to_dual existing]
instance _root_.MaxTropical.mulRightMono [LE R] [Add R] [AddRightMono R] :
    MulRightMono (MaxTropical R) :=
  ⟨fun _ y z h => add_le_add_left (show MaxTropical.untrop y ≤ MaxTropical.untrop z from h) _⟩

@[to_dual existing]
instance _root_.MaxTropical.addLeftMono [LinearOrder R] : AddLeftMono (MaxTropical R) :=
  ⟨fun x y z h => by
    rcases le_total x z with hx | hz
    · rw [MaxTropical.add_eq_right hx]
      rcases le_total x y with hx | hx
      · rwa [MaxTropical.add_eq_right hx]
      · rwa [MaxTropical.add_eq_left hx]
    · rw [MaxTropical.add_eq_left hz, MaxTropical.add_eq_left (h.trans hz)]⟩

@[to_dual existing]
instance _root_.MaxTropical.mulLeftStrictMono [LT R] [Add R] [AddLeftStrictMono R] :
    MulLeftStrictMono (MaxTropical R) :=
  ⟨fun _ _ _ h => add_lt_add_right (MaxTropical.untrop_lt_iff.2 h) _⟩

@[to_dual existing]
instance _root_.MaxTropical.mulRightStrictMono [Preorder R] [Add R] [AddRightStrictMono R] :
    MulRightStrictMono (MaxTropical R) :=
  ⟨fun _ y z h => add_lt_add_left (show MaxTropical.untrop y < MaxTropical.untrop z from h) _⟩

@[to_dual]
instance [LinearOrder R] [Add R] [AddLeftMono R] [AddRightMono R] :
    Distrib (MinTropical R) where
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[to_dual (attr := simp)]
theorem add_pow [LinearOrder R] [AddMonoid R] [AddLeftMono R] [AddRightMono R]
    (x y : MinTropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

instance : CommSemiring (MinTropical R) where
  zero_mul := fun _ => untrop_injective (by simp [top_add])
  mul_zero := fun _ => untrop_injective (by simp [add_top])

@[simp]
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : MinTropical R) (n : ℕ) :
    (n + 1) • x = x := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, add_self]

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
theorem mul_eq_zero_iff {R : Type*} [AddCommMonoid R]
    {a b : MinTropical (WithTop R)} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  simp [← untrop_inj_iff, WithTop.add_eq_top]

instance {R : Type*} [AddCommMonoid R] :
    NoZeroDivisors (MinTropical (WithTop R)) :=
  ⟨mul_eq_zero_iff.mp⟩

end Semiring

end MinTropical
