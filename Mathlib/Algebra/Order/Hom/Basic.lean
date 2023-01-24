/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.hom.basic
! leanprover-community/mathlib commit 70d50ecfd4900dd6d328da39ab7ebd516abe4025
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Tactic.Positivity
import Mathlib.Data.FunLike.Basic

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

* `NonnegHomClass`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `SubadditiveHomClass`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `SubmultiplicativeHomClass`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `MulLEAddHomClass`: `∀ f a b, f (a * b) ≤ f a + f b`
* `NonarchimedeanHomClass`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

## TODO

Finitary versions of the current lemmas.
-/

open Function

variable {ι F α β γ δ : Type _}

/-- `NonnegHomClass F α β` states that `F` is a type of nonnegative morphisms. -/
class NonnegHomClass (F : Type _) (α β : outParam (Type _)) [Zero β] [LE β] extends
  FunLike F α fun _ => β where
  /-- the image of any element is non negative. -/
  map_nonneg (f : F) : ∀ a, 0 ≤ f a
#align nonneg_hom_class NonnegHomClass

/-- `SubadditiveHomClass F α β` states that `F` is a type of subadditive morphisms. -/
class SubadditiveHomClass (F : Type _) (α β : outParam (Type _)) [Add α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  /-- the image of a sum is less or equal than the sum of the images. -/
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
#align subadditive_hom_class SubadditiveHomClass

/-- `SubmultiplicativeHomClass F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubadditiveHomClass]
class SubmultiplicativeHomClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Mul β] [LE β]
  extends FunLike F α fun _ => β where
  /-- the image of a product is less or equal than the product of the images. -/
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b
#align submultiplicative_hom_class SubmultiplicativeHomClass

/-- `MulLEAddHomClass F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubadditiveHomClass]
class MulLEAddHomClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Add β] [LE β]
  extends FunLike F α fun _ => β where
  /-- the image of a product is less or equal than the sum of the images. -/
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b
#align mul_le_add_hom_class MulLEAddHomClass

/-- `NonarchimedeanHomClass F α β` states that `F` is a type of non-archimedean morphisms. -/
class NonarchimedeanHomClass (F : Type _) (α β : outParam (Type _)) [Add α] [LinearOrder β]
  extends FunLike F α fun _ => β where
  /-- the image of a sum is less or equal than the maximum of the images. -/
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)
#align nonarchimedean_hom_class NonarchimedeanHomClass

export NonnegHomClass (map_nonneg)

export SubadditiveHomClass (map_add_le_add)

export SubmultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonarchimedeanHomClass (map_add_le_max)

attribute [simp] map_nonneg

@[to_additive]
theorem le_map_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b
#align le_map_mul_map_div le_map_mul_map_div
#align le_map_add_map_sub le_map_add_map_sub

@[to_additive]
theorem le_map_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b
#align le_map_add_map_div le_map_add_map_div
-- #align le_map_add_map_sub le_map_add_map_sub -- Porting note: TODO: `to_additive` clashes

@[to_additive]
theorem le_map_div_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)
#align le_map_div_mul_map_div le_map_div_mul_map_div
#align le_map_sub_add_map_sub le_map_sub_add_map_sub

@[to_additive]
theorem le_map_div_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)
#align le_map_div_add_map_div le_map_div_add_map_div
-- #align le_map_sub_add_map_sub le_map_sub_add_map_sub -- Porting note: TODO: `to_additive` clashes

--namespace Mathlib.Meta.Positivity

--Porting note: tactic extension commented as decided in the weekly porting meeting
-- /-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
-- @[positivity _ _]
-- unsafe def positivity_map : expr → tactic strictness
--   | expr.app (quote.1 ⇑(%%f)) (quote.1 (%%ₓa)) => nonnegative <$> mk_app `` map_nonneg [f, a]
--   | _ => failed
-- #align tactic.positivity_map tactic.positivity_map

--end Mathlib.Meta.Positivity
