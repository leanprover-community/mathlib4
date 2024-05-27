/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Algebra.SMulWithZero
import Mathlib.Order.Hom.Basic
import Mathlib.Algebra.Order.Ring.Nat

#align_import algebra.tropical.basic from "leanprover-community/mathlib"@"9116dd6709f303dcf781632e15fdef382b0fc579"

/-!

# Tropical algebraic structures

This file defines algebraic structures of the (min-)tropical numbers, up to the tropical semiring.
Some basic lemmas about conversion from the base type `R` to `Tropical R` are provided, as
well as the expected implementations of tropical addition and tropical multiplication.

## Main declarations

* `Tropical R`: The type synonym of the tropical interpretation of `R`.
    If `[LinearOrder R]`, then addition on `R` is via `min`.
* `Semiring (Tropical R)`: A `LinearOrderedAddCommMonoidWithTop R`
    induces a `Semiring (Tropical R)`. If one solely has `[LinearOrderedAddCommMonoid R]`,
    then the "tropicalization of `R`" would be `Tropical (WithTop R)`.

## Implementation notes

The tropical structure relies on `Top` and `min`. For the max-tropical numbers, use
`OrderDual R`.

Inspiration was drawn from the implementation of `Additive`/`Multiplicative`/`Opposite`,
where a type synonym is created with some barebones API, and quickly made irreducible.

Algebraic structures are provided with as few typeclass assumptions as possible, even though
most references rely on `Semiring (Tropical R)` for building up the whole theory.

## References followed

* https://arxiv.org/pdf/math/0408099.pdf
* https://www.mathenjeans.fr/sites/default/files/sujets/tropical_geometry_-_casagrande.pdf

-/


universe u v

variable (R : Type u)

/-- The tropicalization of a type `R`. -/
def Tropical : Type u :=
  R
#align tropical Tropical

variable {R}

namespace Tropical

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropEquiv` for the equivalence.
-/
--@[pp_nodot] Porting note: not implemented in Lean4
def trop : R → Tropical R :=
  id
#align tropical.trop Tropical.trop

/-- Reinterpret `x : Tropical R` as an element of `R`.
See `Tropical.tropEquiv` for the equivalence. -/
--@[pp_nodot] Porting note: not implemented in Lean4
def untrop : Tropical R → R :=
  id
#align tropical.untrop Tropical.untrop

theorem trop_injective : Function.Injective (trop : R → Tropical R) := fun _ _ => id
#align tropical.trop_injective Tropical.trop_injective

theorem untrop_injective : Function.Injective (untrop : Tropical R → R) := fun _ _ => id
#align tropical.untrop_injective Tropical.untrop_injective

@[simp]
theorem trop_inj_iff (x y : R) : trop x = trop y ↔ x = y :=
  Iff.rfl
#align tropical.trop_inj_iff Tropical.trop_inj_iff

@[simp]
theorem untrop_inj_iff (x y : Tropical R) : untrop x = untrop y ↔ x = y :=
  Iff.rfl
#align tropical.untrop_inj_iff Tropical.untrop_inj_iff

@[simp]
theorem trop_untrop (x : Tropical R) : trop (untrop x) = x :=
  rfl
#align tropical.trop_untrop Tropical.trop_untrop

@[simp]
theorem untrop_trop (x : R) : untrop (trop x) = x :=
  rfl
#align tropical.untrop_trop Tropical.untrop_trop

-- Porting note: New attribute seems to fix things
attribute [irreducible] Tropical

theorem leftInverse_trop : Function.LeftInverse (trop : R → Tropical R) untrop :=
  trop_untrop
#align tropical.left_inverse_trop Tropical.leftInverse_trop

theorem rightInverse_trop : Function.RightInverse (trop : R → Tropical R) untrop :=
  untrop_trop
#align tropical.right_inverse_trop Tropical.rightInverse_trop

/-- Reinterpret `x : R` as an element of `Tropical R`.
See `Tropical.tropOrderIso` for the order-preserving equivalence. -/
def tropEquiv : R ≃ Tropical R where
  toFun := trop
  invFun := untrop
  left_inv := untrop_trop
  right_inv := trop_untrop
#align tropical.trop_equiv Tropical.tropEquiv

@[simp]
theorem tropEquiv_coe_fn : (tropEquiv : R → Tropical R) = trop :=
  rfl
#align tropical.trop_equiv_coe_fn Tropical.tropEquiv_coe_fn

@[simp]
theorem tropEquiv_symm_coe_fn : (tropEquiv.symm : Tropical R → R) = untrop :=
  rfl
#align tropical.trop_equiv_symm_coe_fn Tropical.tropEquiv_symm_coe_fn

theorem trop_eq_iff_eq_untrop {x : R} {y} : trop x = y ↔ x = untrop y :=
  tropEquiv.apply_eq_iff_eq_symm_apply
#align tropical.trop_eq_iff_eq_untrop Tropical.trop_eq_iff_eq_untrop

theorem untrop_eq_iff_eq_trop {x} {y : R} : untrop x = y ↔ x = trop y :=
  tropEquiv.symm.apply_eq_iff_eq_symm_apply
#align tropical.untrop_eq_iff_eq_trop Tropical.untrop_eq_iff_eq_trop

theorem injective_trop : Function.Injective (trop : R → Tropical R) :=
  tropEquiv.injective
#align tropical.injective_trop Tropical.injective_trop

theorem injective_untrop : Function.Injective (untrop : Tropical R → R) :=
  tropEquiv.symm.injective
#align tropical.injective_untrop Tropical.injective_untrop

theorem surjective_trop : Function.Surjective (trop : R → Tropical R) :=
  tropEquiv.surjective
#align tropical.surjective_trop Tropical.surjective_trop

theorem surjective_untrop : Function.Surjective (untrop : Tropical R → R) :=
  tropEquiv.symm.surjective
#align tropical.surjective_untrop Tropical.surjective_untrop

instance [Inhabited R] : Inhabited (Tropical R) :=
  ⟨trop default⟩

/-- Recursing on an `x' : Tropical R` is the same as recursing on an `x : R` reinterpreted
as a term of `Tropical R` via `trop x`. -/
@[simp]
def tropRec {F : Tropical R → Sort v} (h : ∀ X, F (trop X)) : ∀ X, F X := fun X => h (untrop X)
#align tropical.trop_rec Tropical.tropRec

instance [DecidableEq R] : DecidableEq (Tropical R) := fun _ _ =>
  decidable_of_iff _ injective_untrop.eq_iff

section Order

instance instLETropical [LE R] : LE (Tropical R) where le x y := untrop x ≤ untrop y

@[simp]
theorem untrop_le_iff [LE R] {x y : Tropical R} : untrop x ≤ untrop y ↔ x ≤ y :=
  Iff.rfl
#align tropical.untrop_le_iff Tropical.untrop_le_iff

instance decidableLE [LE R] [DecidableRel ((· ≤ ·) : R → R → Prop)] :
    DecidableRel ((· ≤ ·) : Tropical R → Tropical R → Prop) := fun x y =>
  ‹DecidableRel (· ≤ ·)› (untrop x) (untrop y)
#align tropical.decidable_le Tropical.decidableLE

instance instLTTropical [LT R] : LT (Tropical R) where lt x y := untrop x < untrop y

@[simp]
theorem untrop_lt_iff [LT R] {x y : Tropical R} : untrop x < untrop y ↔ x < y :=
  Iff.rfl
#align tropical.untrop_lt_iff Tropical.untrop_lt_iff

instance decidableLT [LT R] [DecidableRel ((· < ·) : R → R → Prop)] :
    DecidableRel ((· < ·) : Tropical R → Tropical R → Prop) := fun x y =>
  ‹DecidableRel (· < ·)› (untrop x) (untrop y)
#align tropical.decidable_lt Tropical.decidableLT

instance instPreorderTropical [Preorder R] : Preorder (Tropical R) :=
  { instLETropical, instLTTropical with
    le_refl := fun x => le_refl (untrop x)
    le_trans := fun _ _ _ h h' => le_trans (α := R) h h'
    lt_iff_le_not_le := fun _ _ => lt_iff_le_not_le (α := R) }

/-- Reinterpret `x : R` as an element of `Tropical R`, preserving the order. -/
def tropOrderIso [Preorder R] : R ≃o Tropical R :=
  { tropEquiv with map_rel_iff' := untrop_le_iff }
#align tropical.trop_order_iso Tropical.tropOrderIso

@[simp]
theorem tropOrderIso_coe_fn [Preorder R] : (tropOrderIso : R → Tropical R) = trop :=
  rfl
#align tropical.trop_order_iso_coe_fn Tropical.tropOrderIso_coe_fn

@[simp]
theorem tropOrderIso_symm_coe_fn [Preorder R] : (tropOrderIso.symm : Tropical R → R) = untrop :=
  rfl
#align tropical.trop_order_iso_symm_coe_fn Tropical.tropOrderIso_symm_coe_fn

theorem trop_monotone [Preorder R] : Monotone (trop : R → Tropical R) := fun _ _ => id
#align tropical.trop_monotone Tropical.trop_monotone

theorem untrop_monotone [Preorder R] : Monotone (untrop : Tropical R → R) := fun _ _ => id
#align tropical.untrop_monotone Tropical.untrop_monotone

instance instPartialOrderTropical [PartialOrder R] : PartialOrder (Tropical R) :=
  { instPreorderTropical with le_antisymm := fun _ _ h h' => untrop_injective (le_antisymm h h') }

instance instZeroTropical [Top R] : Zero (Tropical R) :=
  ⟨trop ⊤⟩

instance instTopTropical [Top R] : Top (Tropical R) :=
  ⟨0⟩

@[simp]
theorem untrop_zero [Top R] : untrop (0 : Tropical R) = ⊤ :=
  rfl
#align tropical.untrop_zero Tropical.untrop_zero

@[simp]
theorem trop_top [Top R] : trop (⊤ : R) = 0 :=
  rfl
#align tropical.trop_top Tropical.trop_top

@[simp]
theorem trop_coe_ne_zero (x : R) : trop (x : WithTop R) ≠ 0 :=
  nofun
#align tropical.trop_coe_ne_zero Tropical.trop_coe_ne_zero

@[simp]
theorem zero_ne_trop_coe (x : R) : (0 : Tropical (WithTop R)) ≠ trop x :=
  nofun
#align tropical.zero_ne_trop_coe Tropical.zero_ne_trop_coe

@[simp]
theorem le_zero [LE R] [OrderTop R] (x : Tropical R) : x ≤ 0 :=
  le_top (α := R)
#align tropical.le_zero Tropical.le_zero

instance [LE R] [OrderTop R] : OrderTop (Tropical R) :=
  { instTopTropical with le_top := fun _ => le_top (α := R) }

variable [LinearOrder R]

/-- Tropical addition is the minimum of two underlying elements of `R`. -/
instance : Add (Tropical R) :=
  ⟨fun x y => trop (min (untrop x) (untrop y))⟩

instance instAddCommSemigroupTropical : AddCommSemigroup (Tropical R) where
  add := (· + ·)
  add_assoc _ _ _ := untrop_injective (min_assoc _ _ _)
  add_comm _ _ := untrop_injective (min_comm _ _)

@[simp]
theorem untrop_add (x y : Tropical R) : untrop (x + y) = min (untrop x) (untrop y) :=
  rfl
#align tropical.untrop_add Tropical.untrop_add

@[simp]
theorem trop_min (x y : R) : trop (min x y) = trop x + trop y :=
  rfl
#align tropical.trop_min Tropical.trop_min

@[simp]
theorem trop_inf (x y : R) : trop (x ⊓ y) = trop x + trop y :=
  rfl
#align tropical.trop_inf Tropical.trop_inf

theorem trop_add_def (x y : Tropical R) : x + y = trop (min (untrop x) (untrop y)) :=
  rfl
#align tropical.trop_add_def Tropical.trop_add_def

instance instLinearOrderTropical : LinearOrder (Tropical R) :=
  { instPartialOrderTropical with
    le_total := fun a b => le_total (untrop a) (untrop b)
    decidableLE := Tropical.decidableLE
    max := fun a b => trop (max (untrop a) (untrop b))
    max_def := fun a b => untrop_injective (by
      simp only [max_def, untrop_le_iff, untrop_trop]; split_ifs <;> simp)
    min := (· + ·)
    min_def := fun a b => untrop_injective (by
      simp only [untrop_add, min_def, untrop_le_iff]; split_ifs <;> simp) }

@[simp]
theorem untrop_sup (x y : Tropical R) : untrop (x ⊔ y) = untrop x ⊔ untrop y :=
  rfl
#align tropical.untrop_sup Tropical.untrop_sup

@[simp]
theorem untrop_max (x y : Tropical R) : untrop (max x y) = max (untrop x) (untrop y) :=
  rfl
#align tropical.untrop_max Tropical.untrop_max

@[simp]
theorem min_eq_add : (min : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl
#align tropical.min_eq_add Tropical.min_eq_add

@[simp]
theorem inf_eq_add : ((· ⊓ ·) : Tropical R → Tropical R → Tropical R) = (· + ·) :=
  rfl
#align tropical.inf_eq_add Tropical.inf_eq_add

theorem trop_max_def (x y : Tropical R) : max x y = trop (max (untrop x) (untrop y)) :=
  rfl
#align tropical.trop_max_def Tropical.trop_max_def

theorem trop_sup_def (x y : Tropical R) : x ⊔ y = trop (untrop x ⊔ untrop y) :=
  rfl
#align tropical.trop_sup_def Tropical.trop_sup_def

@[simp]
theorem add_eq_left ⦃x y : Tropical R⦄ (h : x ≤ y) : x + y = x :=
  untrop_injective (by simpa using h)
#align tropical.add_eq_left Tropical.add_eq_left

@[simp]
theorem add_eq_right ⦃x y : Tropical R⦄ (h : y ≤ x) : x + y = y :=
  untrop_injective (by simpa using h)
#align tropical.add_eq_right Tropical.add_eq_right

theorem add_eq_left_iff {x y : Tropical R} : x + y = x ↔ x ≤ y := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_left_iff]
#align tropical.add_eq_left_iff Tropical.add_eq_left_iff

theorem add_eq_right_iff {x y : Tropical R} : x + y = y ↔ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop, ← untrop_le_iff, min_eq_right_iff]
#align tropical.add_eq_right_iff Tropical.add_eq_right_iff

-- Porting note (#10618): removing `simp`. `simp` can prove it
theorem add_self (x : Tropical R) : x + x = x :=
  untrop_injective (min_eq_right le_rfl)
#align tropical.add_self Tropical.add_self

set_option linter.deprecated false in
@[simp]
theorem bit0 (x : Tropical R) : bit0 x = x :=
  add_self x
#align tropical.bit0 Tropical.bit0

theorem add_eq_iff {x y z : Tropical R} : x + y = z ↔ x = z ∧ x ≤ y ∨ y = z ∧ y ≤ x := by
  rw [trop_add_def, trop_eq_iff_eq_untrop]
  simp [min_eq_iff]
#align tropical.add_eq_iff Tropical.add_eq_iff

@[simp]
theorem add_eq_zero_iff {a b : Tropical (WithTop R)} : a + b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_iff]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · exact ⟨rfl, le_antisymm (le_zero _) h⟩
    · exact ⟨le_antisymm (le_zero _) h, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp
#align tropical.add_eq_zero_iff Tropical.add_eq_zero_iff

instance instAddCommMonoidTropical [OrderTop R] : AddCommMonoid (Tropical R) :=
  { instZeroTropical, instAddCommSemigroupTropical with
    zero_add := fun _ => untrop_injective (min_top_left _)
    add_zero := fun _ => untrop_injective (min_top_right _)
    nsmul := nsmulRec }

end Order

section Monoid

/-- Tropical multiplication is the addition in the underlying `R`. -/
instance [Add R] : Mul (Tropical R) :=
  ⟨fun x y => trop (untrop x + untrop y)⟩

@[simp]
theorem trop_add [Add R] (x y : R) : trop (x + y) = trop x * trop y :=
  rfl
#align tropical.trop_add Tropical.trop_add

@[simp]
theorem untrop_mul [Add R] (x y : Tropical R) : untrop (x * y) = untrop x + untrop y :=
  rfl
#align tropical.untrop_mul Tropical.untrop_mul

theorem trop_mul_def [Add R] (x y : Tropical R) : x * y = trop (untrop x + untrop y) :=
  rfl
#align tropical.trop_mul_def Tropical.trop_mul_def

instance instOneTropical [Zero R] : One (Tropical R) :=
  ⟨trop 0⟩

@[simp]
theorem trop_zero [Zero R] : trop (0 : R) = 1 :=
  rfl
#align tropical.trop_zero Tropical.trop_zero

@[simp]
theorem untrop_one [Zero R] : untrop (1 : Tropical R) = 0 :=
  rfl
#align tropical.untrop_one Tropical.untrop_one

instance instAddMonoidWithOneTropical [LinearOrder R] [OrderTop R] [Zero R] :
    AddMonoidWithOne (Tropical R) :=
  { instOneTropical, instAddCommMonoidTropical with
    natCast := fun n => if n = 0 then 0 else 1
    natCast_zero := rfl
    natCast_succ := fun n => (untrop_inj_iff _ _).1 (by cases n <;> simp [Nat.cast]) }

instance [Zero R] : Nontrivial (Tropical (WithTop R)) :=
  ⟨⟨0, 1, trop_injective.ne WithTop.top_ne_coe⟩⟩

instance [Neg R] : Inv (Tropical R) :=
  ⟨fun x => trop (-untrop x)⟩

@[simp]
theorem untrop_inv [Neg R] (x : Tropical R) : untrop x⁻¹ = -untrop x :=
  rfl
#align tropical.untrop_inv Tropical.untrop_inv

instance [Sub R] : Div (Tropical R) :=
  ⟨fun x y => trop (untrop x - untrop y)⟩

@[simp]
theorem untrop_div [Sub R] (x y : Tropical R) : untrop (x / y) = untrop x - untrop y :=
  rfl
#align tropical.untrop_div Tropical.untrop_div

instance instSemigroupTropical [AddSemigroup R] : Semigroup (Tropical R) where
  mul := (· * ·)
  mul_assoc _ _ _ := untrop_injective (add_assoc _ _ _)

instance instCommSemigroupTropical [AddCommSemigroup R] : CommSemigroup (Tropical R) :=
  { instSemigroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

instance {α : Type*} [SMul α R] : Pow (Tropical R) α where pow x n := trop <| n • untrop x

@[simp]
theorem untrop_pow {α : Type*} [SMul α R] (x : Tropical R) (n : α) :
    untrop (x ^ n) = n • untrop x :=
  rfl
#align tropical.untrop_pow Tropical.untrop_pow

@[simp]
theorem trop_smul {α : Type*} [SMul α R] (x : R) (n : α) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_smul Tropical.trop_smul

instance instMulOneClassTropical [AddZeroClass R] : MulOneClass (Tropical R) where
  one := 1
  mul := (· * ·)
  one_mul _ := untrop_injective <| zero_add _
  mul_one _ := untrop_injective <| add_zero _

instance instMonoidTropical [AddMonoid R] : Monoid (Tropical R) :=
  { instMulOneClassTropical, instSemigroupTropical with
    npow := fun n x => x ^ n
    npow_zero := fun _ => untrop_injective <| by simp
    npow_succ := fun _ _ => untrop_injective <| succ_nsmul _ _ }

@[simp]
theorem trop_nsmul [AddMonoid R] (x : R) (n : ℕ) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_nsmul Tropical.trop_nsmul

instance instCommMonoidTropical [AddCommMonoid R] : CommMonoid (Tropical R) :=
  { instMonoidTropical, instCommSemigroupTropical with }

instance instGroupTropical [AddGroup R] : Group (Tropical R) :=
  { instMonoidTropical with
    inv := Inv.inv
    div_eq_mul_inv := fun _ _ => untrop_injective <| by simp [sub_eq_add_neg]
    mul_left_inv := fun _ => untrop_injective <| add_left_neg _
    zpow := fun n x => trop <| n • untrop x
    zpow_zero' := fun _ => untrop_injective <| zero_zsmul _
    zpow_succ' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_succ' _ _
    zpow_neg' := fun _ _ => untrop_injective <| SubNegMonoid.zsmul_neg' _ _ }

instance [AddCommGroup R] : CommGroup (Tropical R) :=
  { instGroupTropical with mul_comm := fun _ _ => untrop_injective (add_comm _ _) }

@[simp]
theorem untrop_zpow [AddGroup R] (x : Tropical R) (n : ℤ) : untrop (x ^ n) = n • untrop x :=
  rfl
#align tropical.untrop_zpow Tropical.untrop_zpow

@[simp]
theorem trop_zsmul [AddGroup R] (x : R) (n : ℤ) : trop (n • x) = trop x ^ n :=
  rfl
#align tropical.trop_zsmul Tropical.trop_zsmul

end Monoid

section Distrib

instance covariant_mul [LE R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· ≤ ·) :=
  ⟨fun _ y z h => add_le_add_left (show untrop y ≤ untrop z from h) _⟩
#align tropical.covariant_mul Tropical.covariant_mul

instance covariant_swap_mul [LE R] [Add R] [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun _ y z h => add_le_add_right (show untrop y ≤ untrop z from h) _⟩
#align tropical.covariant_swap_mul Tropical.covariant_swap_mul

instance covariant_add [LinearOrder R] : CovariantClass (Tropical R) (Tropical R) (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => by
    rcases le_total x y with hx | hy
    · rw [add_eq_left hx, add_eq_left (hx.trans h)]
    · rw [add_eq_right hy]
      rcases le_total x z with hx | hx
      · rwa [add_eq_left hx]
      · rwa [add_eq_right hx]⟩
#align tropical.covariant_add Tropical.covariant_add

instance covariant_mul_lt [LT R] [Add R] [CovariantClass R R (· + ·) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (· * ·) (· < ·) :=
  ⟨fun _ _ _ h => add_lt_add_left (untrop_lt_iff.2 h) _⟩
#align tropical.covariant_mul_lt Tropical.covariant_mul_lt

instance covariant_swap_mul_lt [Preorder R] [Add R]
    [CovariantClass R R (Function.swap (· + ·)) (· < ·)] :
    CovariantClass (Tropical R) (Tropical R) (Function.swap (· * ·)) (· < ·) :=
  ⟨fun _ y z h => add_lt_add_right (show untrop y < untrop z from h) _⟩
#align tropical.covariant_swap_mul_lt Tropical.covariant_swap_mul_lt

instance instDistribTropical [LinearOrder R] [Add R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] :
    Distrib (Tropical R) where
  mul := (· * ·)
  add := (· + ·)
  left_distrib _ _ _ := untrop_injective (min_add_add_left _ _ _).symm
  right_distrib _ _ _ := untrop_injective (min_add_add_right _ _ _).symm

@[simp]
theorem add_pow [LinearOrder R] [AddMonoid R] [CovariantClass R R (· + ·) (· ≤ ·)]
    [CovariantClass R R (Function.swap (· + ·)) (· ≤ ·)] (x y : Tropical R) (n : ℕ) :
    (x + y) ^ n = x ^ n + y ^ n := by
  rcases le_total x y with h | h
  · rw [add_eq_left h, add_eq_left (pow_le_pow_left' h _)]
  · rw [add_eq_right h, add_eq_right (pow_le_pow_left' h _)]
#align tropical.add_pow Tropical.add_pow

end Distrib

section Semiring

variable [LinearOrderedAddCommMonoidWithTop R]

instance : CommSemiring (Tropical R) :=
  { instAddMonoidWithOneTropical,
    instDistribTropical,
    instAddCommMonoidTropical,
    instCommMonoidTropical with
    zero_mul := fun _ => untrop_injective (by simp [top_add])
    mul_zero := fun _ => untrop_injective (by simp [add_top]) }

@[simp]
theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x := by
  induction' n with n IH
  · simp
  · rw [add_nsmul, IH, one_nsmul, add_self]
#align tropical.succ_nsmul Tropical.succ_nsmul

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry
-- Porting note (#10618): removing @[simp], `simp` can prove it
theorem mul_eq_zero_iff {R : Type*} [LinearOrderedAddCommMonoid R] {a b : Tropical (WithTop R)} :
    a * b = 0 ↔ a = 0 ∨ b = 0 := by simp [← untrop_inj_iff, WithTop.add_eq_top]
#align tropical.mul_eq_zero_iff Tropical.mul_eq_zero_iff

instance {R : Type*} [LinearOrderedAddCommMonoid R] : NoZeroDivisors (Tropical (WithTop R)) :=
  ⟨mul_eq_zero_iff.mp⟩

end Semiring

end Tropical
