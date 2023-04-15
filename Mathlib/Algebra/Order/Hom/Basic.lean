/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.hom.basic
! leanprover-community/mathlib commit 7ea604785a41a0681eac70c5a82372493dbefc68
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupPower.Order

/-!
# Algebraic order homomorphism classes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `nonneg_hom_class`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `subadditive_hom_class`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `submultiplicative_hom_class`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `mul_le_add_hom_class`: `∀ f a b, f (a * b) ≤ f a + f b`
* `nonarchimedean_hom_class`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

Group norms
* `add_group_seminorm_class`: Homs are nonnegative, subadditive, even and preserve zero.
* `group_seminorm_class`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `add_group_norm_class`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `group_norm_class`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

Ring norms
* `ring_seminorm_class`: Homs are submultiplicative group norms.
* `ring_norm_class`: Homs are ring seminorms that are also additive group norms.
* `mul_ring_seminorm_class`: Homs are ring seminorms that are multiplicative.
* `mul_ring_norm_class`: Homs are ring norms that are multiplicative.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`analysis.normed.group.seminorm` and `analysis.normed.ring.seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/


library_note "out-param inheritance"/--
Diamond inheritance cannot depend on `out_param`s in the following circumstances:
 * there are three classes `top`, `middle`, `bottom`
 * all of these classes have a parameter `(α : out_param _)`
 * all of these classes have an instance parameter `[root α]` that depends on this `out_param`
 * the `root` class has two child classes: `left` and `right`, these are siblings in the hierarchy
 * the instance `bottom.to_middle` takes a `[left α]` parameter
 * the instance `middle.to_top` takes a `[right α]` parameter
 * there is a `leaf` class that inherits from both `left` and `right`.
In that case, given instances `bottom α` and `leaf α`, Lean cannot synthesize a `top α` instance,
even though the hypotheses of the instances `bottom.to_middle` and `middle.to_top` are satisfied.

There are two workarounds:
* You could replace the bundled inheritance implemented by the instance `middle.to_top` with
  unbundled inheritance implemented by adding a `[top α]` parameter to the `middle` class. This is
  the preferred option since it is also more compatible with Lean 4, at the cost of being more work
  to implement and more verbose to use.
* You could weaken the `bottom.to_middle` instance by making it depend on a subclass of
  `middle.to_top`'s parameter, in this example replacing `[left α]` with `[leaf α]`.
-/


open Function

variable {ι F α β γ δ : Type _}

/-! ### Basics -/


#print NonnegHomClass /-
/-- `nonneg_hom_class F α β` states that `F` is a type of nonnegative morphisms. -/
class NonnegHomClass (F : Type _) (α β : outParam <| Type _) [Zero β] [LE β] extends
  FunLike F α fun _ => β where
  map_nonneg (f : F) : ∀ a, 0 ≤ f a
#align nonneg_hom_class NonnegHomClass
-/

#print SubadditiveHomClass /-
/-- `subadditive_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
class SubadditiveHomClass (F : Type _) (α β : outParam <| Type _) [Add α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
#align subadditive_hom_class SubadditiveHomClass
-/

#print SubmultiplicativeHomClass /-
/-- `submultiplicative_hom_class F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubadditiveHomClass]
class SubmultiplicativeHomClass (F : Type _) (α β : outParam <| Type _) [Mul α] [Mul β]
  [LE β] extends FunLike F α fun _ => β where
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b
#align submultiplicative_hom_class SubmultiplicativeHomClass
#align subadditive_hom_class SubadditiveHomClass
-/

#print MulLEAddHomClass /-
/-- `mul_le_add_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubadditiveHomClass]
class MulLEAddHomClass (F : Type _) (α β : outParam <| Type _) [Mul α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b
#align mul_le_add_hom_class MulLEAddHomClass
#align subadditive_hom_class SubadditiveHomClass
-/

#print NonarchimedeanHomClass /-
/-- `nonarchimedean_hom_class F α β` states that `F` is a type of non-archimedean morphisms. -/
class NonarchimedeanHomClass (F : Type _) (α β : outParam <| Type _) [Add α] [LinearOrder β] extends
  FunLike F α fun _ => β where
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)
#align nonarchimedean_hom_class NonarchimedeanHomClass
-/

export NonnegHomClass (map_nonneg)

export SubadditiveHomClass (map_add_le_add)

export SubmultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonarchimedeanHomClass (map_add_le_max)

attribute [simp] map_nonneg

/- warning: le_map_mul_map_div -> le_map_mul_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : CommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f a) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : CommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) a) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f a) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) b) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) b) (Semigroup.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) b) (CommSemigroup.toSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) b) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f b) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align le_map_mul_map_div le_map_mul_map_divₓ'. -/
@[to_additive]
theorem le_map_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b
#align le_map_mul_map_div le_map_mul_map_div
#align le_map_add_map_sub le_map_add_map_sub

/- warning: le_map_add_map_div -> le_map_add_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : AddCommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : MulLEAddHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f a) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f b) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : AddCommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : MulLEAddHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) a) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f a) (HAdd.hAdd.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) b) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) b) (instHAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) b) (AddSemigroup.toAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) b) (AddCommSemigroup.toAddSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) b) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f b) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)))
Case conversion may be inaccurate. Consider using '#align le_map_add_map_div le_map_add_map_divₓ'. -/
@[to_additive]
theorem le_map_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b
#align le_map_add_map_div le_map_add_map_div
#align le_map_add_map_sub le_map_add_map_sub

/- warning: le_map_div_mul_map_div -> le_map_div_mul_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : CommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a c)) (HMul.hMul.{u3, u3, u3} β β β (instHMul.{u3} β (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SubmultiplicativeHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (Semigroup.toHasMul.{u3} β (CommSemigroup.toSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) b c)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : CommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : SubmultiplicativeHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) (HMul.hMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (instHMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (Semigroup.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (CommSemigroup.toSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.164 : α) => β) _x) (SubmultiplicativeHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)))
Case conversion may be inaccurate. Consider using '#align le_map_div_mul_map_div le_map_div_mul_map_divₓ'. -/
@[to_additive]
theorem le_map_div_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)
#align le_map_div_mul_map_div le_map_div_mul_map_div
#align le_map_sub_add_map_sub le_map_sub_add_map_sub

/- warning: le_map_div_add_map_div -> le_map_div_add_map_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : AddCommSemigroup.{u3} β] [_inst_3 : LE.{u3} β] [_inst_4 : MulLEAddHomClass.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u3} β _inst_3 (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a c)) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) a b)) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddSemigroup.toHasAdd.{u3} β (AddCommSemigroup.toAddSemigroup.{u3} β _inst_2)) _inst_3 _inst_4)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) b c)))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : AddCommSemigroup.{u2} β] [_inst_3 : LE.{u2} β] [_inst_4 : MulLEAddHomClass.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3] (f : F) (a : α) (b : α) (c : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) _inst_3 (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a c)) (HAdd.hAdd.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (instHAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (AddSemigroup.toAdd.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (AddCommSemigroup.toAddSemigroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) _inst_2))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) a b)) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddSemigroup.toAdd.{u2} β (AddCommSemigroup.toAddSemigroup.{u2} β _inst_2)) _inst_3 _inst_4) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) b c)))
Case conversion may be inaccurate. Consider using '#align le_map_div_add_map_div le_map_div_add_map_divₓ'. -/
@[to_additive]
theorem le_map_div_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)
#align le_map_div_add_map_div le_map_div_add_map_div
#align le_map_sub_add_map_sub le_map_sub_add_map_sub

/-! ### Group (semi)norms -/


#print AddGroupSeminormClass /-
/-- `add_group_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the additive
group `α`.

You should extend this class when you extend `add_group_seminorm`. -/
class AddGroupSeminormClass (F : Type _) (α β : outParam <| Type _) [AddGroup α]
  [OrderedAddCommMonoid β] extends SubadditiveHomClass F α β where
  map_zero (f : F) : f 0 = 0
  map_neg_eq_map (f : F) (a : α) : f (-a) = f a
#align add_group_seminorm_class AddGroupSeminormClass
-/

#print GroupSeminormClass /-
/-- `group_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the group `α`.

You should extend this class when you extend `group_seminorm`. -/
@[to_additive]
class GroupSeminormClass (F : Type _) (α β : outParam <| Type _) [Group α]
  [OrderedAddCommMonoid β] extends MulLEAddHomClass F α β where
  map_one_eq_zero (f : F) : f 1 = 0
  map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a
#align group_seminorm_class GroupSeminormClass
#align add_group_seminorm_class AddGroupSeminormClass
-/

#print AddGroupNormClass /-
/-- `add_group_norm_class F α` states that `F` is a type of `β`-valued norms on the additive group
`α`.

You should extend this class when you extend `add_group_norm`. -/
class AddGroupNormClass (F : Type _) (α β : outParam <| Type _) [AddGroup α]
  [OrderedAddCommMonoid β] extends AddGroupSeminormClass F α β where
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0
#align add_group_norm_class AddGroupNormClass
-/

#print GroupNormClass /-
/-- `group_norm_class F α` states that `F` is a type of `β`-valued norms on the group `α`.

You should extend this class when you extend `group_norm`. -/
@[to_additive]
class GroupNormClass (F : Type _) (α β : outParam <| Type _) [Group α]
  [OrderedAddCommMonoid β] extends GroupSeminormClass F α β where
  eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1
#align group_norm_class GroupNormClass
#align add_group_norm_class AddGroupNormClass
-/

export AddGroupSeminormClass (map_neg_eq_map)

export GroupSeminormClass (map_one_eq_zero map_inv_eq_map)

export AddGroupNormClass (eq_zero_of_map_eq_zero)

export GroupNormClass (eq_one_of_map_eq_zero)

attribute [simp, to_additive map_zero] map_one_eq_zero

attribute [simp] map_neg_eq_map

attribute [simp, to_additive] map_inv_eq_map

attribute [to_additive] GroupSeminormClass.toMulLeAddHomClass

attribute [to_additive] GroupNormClass.toGroupSeminormClass

/- warning: add_group_seminorm_class.to_zero_hom_class -> AddGroupSeminormClass.toZeroHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : AddGroup.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : AddGroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2], ZeroHomClass.{u1, u2, u3} F α β (AddZeroClass.toHasZero.{u2} α (AddMonoid.toAddZeroClass.{u2} α (SubNegMonoid.toAddMonoid.{u2} α (AddGroup.toSubNegMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2))))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : AddGroup.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : AddGroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2], ZeroHomClass.{u1, u2, u3} F α β (NegZeroClass.toZero.{u2} α (SubNegZeroMonoid.toNegZeroClass.{u2} α (SubtractionMonoid.toSubNegZeroMonoid.{u2} α (AddGroup.toSubtractionMonoid.{u2} α _inst_1)))) (AddMonoid.toZero.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align add_group_seminorm_class.to_zero_hom_class AddGroupSeminormClass.toZeroHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) AddGroupSeminormClass.toZeroHomClass [AddGroup α]
    [OrderedAddCommMonoid β] [AddGroupSeminormClass F α β] : ZeroHomClass F α β :=
  { ‹AddGroupSeminormClass F α β› with }
#align add_group_seminorm_class.to_zero_hom_class AddGroupSeminormClass.toZeroHomClass

section GroupSeminormClass

variable [Group α] [OrderedAddCommMonoid β] [GroupSeminormClass F α β] (f : F) (x y : α)

include α β

/- warning: map_div_le_add -> map_div_le_add is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2))))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f x) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f y))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), LE.le.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (Preorder.toLE.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (PartialOrder.toPreorder.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (OrderedAddCommMonoid.toPartialOrder.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) _inst_2))) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (HAdd.hAdd.{u3, u3, u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (instHAdd.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddZeroClass.toAdd.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddMonoid.toAddZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommMonoid.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2))))) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f x) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f y))
Case conversion may be inaccurate. Consider using '#align map_div_le_add map_div_le_addₓ'. -/
@[to_additive]
theorem map_div_le_add : f (x / y) ≤ f x + f y :=
  by
  rw [div_eq_mul_inv, ← map_inv_eq_map f y]
  exact map_mul_le_add _ _ _
#align map_div_le_add map_div_le_add
#align map_sub_le_add map_sub_le_add

/- warning: map_div_rev -> map_div_rev is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) y x))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y)) (FunLike.coe.{succ u1, succ u2, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) y x))
Case conversion may be inaccurate. Consider using '#align map_div_rev map_div_revₓ'. -/
@[to_additive]
theorem map_div_rev : f (x / y) = f (y / x) := by rw [← inv_div, map_inv_eq_map]
#align map_div_rev map_div_rev
#align map_sub_rev map_sub_rev

/- warning: le_map_add_map_div' -> le_map_add_map_div' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f x) (HAdd.hAdd.{u3, u3, u3} β β β (instHAdd.{u3} β (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2))))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f y) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) y x)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u2, u1, u3} F α β _inst_1 _inst_2] (f : F) (x : α) (y : α), LE.le.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (Preorder.toLE.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (PartialOrder.toPreorder.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommMonoid.toPartialOrder.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2))) (FunLike.coe.{succ u2, succ u1, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u2, u1, u3} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u1, u3} F α β _inst_1 _inst_2 _inst_3)) f x) (HAdd.hAdd.{u3, u3, u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) y x)) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) (instHAdd.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) (AddZeroClass.toAdd.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) (AddMonoid.toAddZeroClass.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) (OrderedAddCommMonoid.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) _inst_2))))) (FunLike.coe.{succ u2, succ u1, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u2, u1, u3} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u1, u3} F α β _inst_1 _inst_2 _inst_3)) f y) (FunLike.coe.{succ u2, succ u1, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u2, u1, u3} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u1, u3} F α β _inst_1 _inst_2 _inst_3)) f (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) y x)))
Case conversion may be inaccurate. Consider using '#align le_map_add_map_div' le_map_add_map_div'ₓ'. -/
@[to_additive]
theorem le_map_add_map_div' : f x ≤ f y + f (y / x) := by
  simpa only [add_comm, map_div_rev, div_mul_cancel'] using map_mul_le_add f (x / y) y
#align le_map_add_map_div' le_map_add_map_div'
#align le_map_add_map_sub' le_map_add_map_sub'

end GroupSeminormClass

example [OrderedAddCommGroup β] : OrderedAddCommMonoid β :=
  inferInstance

/- warning: abs_sub_map_le_div -> abs_sub_map_le_div is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : LinearOrderedAddCommGroup.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))] (f : F) (x : α) (y : α), LE.le.{u3} β (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommGroup.toPartialOrder.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))) (Abs.abs.{u3} β (Neg.toHasAbs.{u3} β (SubNegMonoid.toHasNeg.{u3} β (AddGroup.toSubNegMonoid.{u3} β (AddCommGroup.toAddGroup.{u3} β (OrderedAddCommGroup.toAddCommGroup.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))))) (SemilatticeSup.toHasSup.{u3} β (Lattice.toSemilatticeSup.{u3} β (LinearOrder.toLattice.{u3} β (LinearOrderedAddCommGroup.toLinearOrder.{u3} β _inst_2))))) (HSub.hSub.{u3, u3, u3} β β β (instHSub.{u3} β (SubNegMonoid.toHasSub.{u3} β (AddGroup.toSubNegMonoid.{u3} β (AddCommGroup.toAddGroup.{u3} β (OrderedAddCommGroup.toAddCommGroup.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))) _inst_3))) f x) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))) _inst_3))) f y))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2)))))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 (OrderedCancelAddCommMonoid.toOrderedAddCommMonoid.{u3} β (OrderedAddCommGroup.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u3} β _inst_2))) _inst_3))) f (HDiv.hDiv.{u2, u2, u2} α α α (instHDiv.{u2} α (DivInvMonoid.toHasDiv.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))) x y))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : LinearOrderedAddCommGroup.{u2} β] [_inst_3 : GroupSeminormClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2)))] (f : F) (x : α) (y : α), LE.le.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (Preorder.toLE.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommGroup.toPartialOrder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))) (Abs.abs.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (Neg.toHasAbs.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (NegZeroClass.toNeg.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (SubNegZeroMonoid.toNegZeroClass.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (SubtractionMonoid.toSubNegZeroMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (SubtractionCommMonoid.toSubtractionMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommGroup.toDivisionAddCommMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommGroup.toAddCommGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2))))))) (SemilatticeSup.toSup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (Lattice.toSemilatticeSup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (DistribLattice.toLattice.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (instDistribLattice.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommGroup.toLinearOrder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))))) (HSub.hSub.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) y) ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (instHSub.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (SubNegMonoid.toSub.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddGroup.toSubNegMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommGroup.toAddGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommGroup.toAddCommGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommGroup.toOrderedAddCommGroup.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2)))))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))) _inst_3)) f x) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2)))))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))) _inst_3)) f y))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2)))))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β (LinearOrderedCancelAddCommMonoid.toLinearOrderedAddCommMonoid.{u2} β (LinearOrderedAddCommGroup.toLinearOrderedAddCancelCommMonoid.{u2} β _inst_2))) _inst_3)) f (HDiv.hDiv.{u3, u3, u3} α α α (instHDiv.{u3} α (DivInvMonoid.toDiv.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1))) x y))
Case conversion may be inaccurate. Consider using '#align abs_sub_map_le_div abs_sub_map_le_divₓ'. -/
@[to_additive]
theorem abs_sub_map_le_div [Group α] [LinearOrderedAddCommGroup β] [GroupSeminormClass F α β]
    (f : F) (x y : α) : |f x - f y| ≤ f (x / y) :=
  by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩
#align abs_sub_map_le_div abs_sub_map_le_div
#align abs_sub_map_le_sub abs_sub_map_le_sub

/- warning: group_seminorm_class.to_nonneg_hom_class -> GroupSeminormClass.toNonnegHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : LinearOrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)], NonnegHomClass.{u1, u2, u3} F α β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2))))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : LinearOrderedAddCommMonoid.{u3} β] [_inst_3 : GroupSeminormClass.{u1, u2, u3} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)], NonnegHomClass.{u1, u2, u3} F α β (AddMonoid.toZero.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (LinearOrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align group_seminorm_class.to_nonneg_hom_class GroupSeminormClass.toNonnegHomClassₓ'. -/
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) GroupSeminormClass.toNonnegHomClass [Group α]
    [LinearOrderedAddCommMonoid β] [GroupSeminormClass F α β] : NonnegHomClass F α β :=
  { ‹GroupSeminormClass F α β› with
    map_nonneg := fun f a =>
      (nsmul_nonneg_iff two_ne_zero).1 <|
        by
        rw [two_nsmul, ← map_one_eq_zero f, ← div_self' a]
        exact map_div_le_add _ _ _ }
#align group_seminorm_class.to_nonneg_hom_class GroupSeminormClass.toNonnegHomClass
#align add_group_seminorm_class.to_nonneg_hom_class AddGroupSeminormClass.toNonnegHomClass

section GroupNormClass

variable [Group α] [OrderedAddCommMonoid β] [GroupNormClass F α β] (f : F) {x : α}

include α β

/- warning: map_eq_zero_iff_eq_one -> map_eq_zero_iff_eq_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupNormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) {x : α}, Iff (Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 (GroupNormClass.toGroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)))) f x) (OfNat.ofNat.{u3} β 0 (OfNat.mk.{u3} β 0 (Zero.zero.{u3} β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))))))) (Eq.{succ u2} α x (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))))))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupNormClass.{u2, u1, u3} F α β _inst_1 _inst_2] (f : F) {x : α}, Iff (Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (FunLike.coe.{succ u2, succ u1, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u2, u1, u3} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u1, u3} F α β _inst_1 _inst_2 (GroupNormClass.toGroupSeminormClass.{u2, u1, u3} F α β _inst_1 _inst_2 _inst_3))) f x) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddMonoid.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommMonoid.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))))) (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align map_eq_zero_iff_eq_one map_eq_zero_iff_eq_oneₓ'. -/
@[simp, to_additive]
theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
  ⟨eq_one_of_map_eq_zero _, by
    rintro rfl
    exact map_one_eq_zero _⟩
#align map_eq_zero_iff_eq_one map_eq_zero_iff_eq_one
#align map_eq_zero_iff_eq_zero map_eq_zero_iff_eq_zero

/- warning: map_ne_zero_iff_ne_one -> map_ne_zero_iff_ne_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupNormClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) {x : α}, Iff (Ne.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 (GroupNormClass.toGroupSeminormClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)))) f x) (OfNat.ofNat.{u3} β 0 (OfNat.mk.{u3} β 0 (Zero.zero.{u3} β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))))))) (Ne.{succ u2} α x (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))))))))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u1}} {β : Type.{u3}} [_inst_1 : Group.{u1} α] [_inst_2 : OrderedAddCommMonoid.{u3} β] [_inst_3 : GroupNormClass.{u2, u1, u3} F α β _inst_1 _inst_2] (f : F) {x : α}, Iff (Ne.{succ u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (FunLike.coe.{succ u2, succ u1, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u2, u1, u3} F α β (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))) (AddZeroClass.toAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β _inst_2))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u1, u3} F α β _inst_1 _inst_2 (GroupNormClass.toGroupSeminormClass.{u2, u1, u3} F α β _inst_1 _inst_2 _inst_3))) f x) (OfNat.ofNat.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) 0 (Zero.toOfNat0.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddMonoid.toZero.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommMonoid.toAddMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommMonoid.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))))) (Ne.{succ u1} α x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align map_ne_zero_iff_ne_one map_ne_zero_iff_ne_oneₓ'. -/
@[to_additive]
theorem map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 :=
  (map_eq_zero_iff_eq_one _).Not
#align map_ne_zero_iff_ne_one map_ne_zero_iff_ne_one
#align map_ne_zero_iff_ne_zero map_ne_zero_iff_ne_zero

end GroupNormClass

/- warning: map_pos_of_ne_one -> map_pos_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u2} α] [_inst_2 : LinearOrderedAddCommMonoid.{u3} β] [_inst_3 : GroupNormClass.{u1, u2, u3} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)] (f : F) {x : α}, (Ne.{succ u2} α x (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))))))) -> (LT.lt.{u3} β (Preorder.toLT.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)))) (OfNat.ofNat.{u3} β 0 (OfNat.mk.{u3} β 0 (Zero.zero.{u3} β (AddZeroClass.toHasZero.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)))))))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulLEAddHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)))) (AddZeroClass.toHasAdd.{u3} β (AddMonoid.toAddZeroClass.{u3} β (AddCommMonoid.toAddMonoid.{u3} β (OrderedAddCommMonoid.toAddCommMonoid.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedAddCommMonoid.toPartialOrder.{u3} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2)))) (GroupSeminormClass.toMulLeAddHomClass.{u1, u2, u3} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2) (GroupNormClass.toGroupSeminormClass.{u1, u2, u3} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} β _inst_2) _inst_3)))) f x))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : Group.{u3} α] [_inst_2 : LinearOrderedAddCommMonoid.{u2} β] [_inst_3 : GroupNormClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β _inst_2)] (f : F) {x : α}, (Ne.{succ u3} α x (OfNat.ofNat.{u3} α 1 (One.toOfNat1.{u3} α (InvOneClass.toOne.{u3} α (DivInvOneMonoid.toInvOneClass.{u3} α (DivisionMonoid.toDivInvOneMonoid.{u3} α (Group.toDivisionMonoid.{u3} α _inst_1))))))) -> (LT.lt.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (Preorder.toLT.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (PartialOrder.toPreorder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (OrderedAddCommMonoid.toPartialOrder.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2)))) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) 0 (Zero.toOfNat0.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddMonoid.toZero.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (AddCommMonoid.toAddMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) (LinearOrderedAddCommMonoid.toAddCommMonoid.{u2} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) x) _inst_2))))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.229 : α) => β) _x) (MulLEAddHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (DivInvMonoid.toMonoid.{u3} α (Group.toDivInvMonoid.{u3} α _inst_1)))) (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (OrderedAddCommMonoid.toAddCommMonoid.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β _inst_2))))) (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (OrderedAddCommMonoid.toPartialOrder.{u2} β (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β _inst_2)))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β _inst_2) (GroupNormClass.toGroupSeminormClass.{u1, u3, u2} F α β _inst_1 (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} β _inst_2) _inst_3))) f x))
Case conversion may be inaccurate. Consider using '#align map_pos_of_ne_one map_pos_of_ne_oneₓ'. -/
@[to_additive]
theorem map_pos_of_ne_one [Group α] [LinearOrderedAddCommMonoid β] [GroupNormClass F α β] (f : F)
    {x : α} (hx : x ≠ 1) : 0 < f x :=
  (map_nonneg _ _).lt_of_ne <| ((map_ne_zero_iff_ne_one _).2 hx).symm
#align map_pos_of_ne_one map_pos_of_ne_one
#align map_pos_of_ne_zero map_pos_of_ne_zero

/-! ### Ring (semi)norms -/


#print RingSeminormClass /-
/-- `ring_seminorm_class F α` states that `F` is a type of `β`-valued seminorms on the ring `α`.

You should extend this class when you extend `ring_seminorm`. -/
class RingSeminormClass (F : Type _) (α β : outParam <| Type _) [NonUnitalNonAssocRing α]
  [OrderedSemiring β] extends AddGroupSeminormClass F α β, SubmultiplicativeHomClass F α β
#align ring_seminorm_class RingSeminormClass
-/

#print RingNormClass /-
/-- `ring_norm_class F α` states that `F` is a type of `β`-valued norms on the ring `α`.

You should extend this class when you extend `ring_norm`. -/
class RingNormClass (F : Type _) (α β : outParam <| Type _) [NonUnitalNonAssocRing α]
  [OrderedSemiring β] extends RingSeminormClass F α β, AddGroupNormClass F α β
#align ring_norm_class RingNormClass
-/

#print MulRingSeminormClass /-
/-- `mul_ring_seminorm_class F α` states that `F` is a type of `β`-valued multiplicative seminorms
on the ring `α`.

You should extend this class when you extend `mul_ring_seminorm`. -/
class MulRingSeminormClass (F : Type _) (α β : outParam <| Type _) [NonAssocRing α]
  [OrderedSemiring β] extends AddGroupSeminormClass F α β, MonoidWithZeroHomClass F α β
#align mul_ring_seminorm_class MulRingSeminormClass
-/

#print MulRingNormClass /-
/-- `mul_ring_norm_class F α` states that `F` is a type of `β`-valued multiplicative norms on the
ring `α`.

You should extend this class when you extend `mul_ring_norm`. -/
class MulRingNormClass (F : Type _) (α β : outParam <| Type _) [NonAssocRing α]
  [OrderedSemiring β] extends MulRingSeminormClass F α β, AddGroupNormClass F α β
#align mul_ring_norm_class MulRingNormClass
-/

/- warning: ring_seminorm_class.to_nonneg_hom_class -> RingSeminormClass.toNonnegHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u2} α] [_inst_2 : LinearOrderedSemiring.{u3} β] [_inst_3 : RingSeminormClass.{u1, u2, u3} F α β _inst_1 (StrictOrderedSemiring.toOrderedSemiring.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2))], NonnegHomClass.{u1, u2, u3} F α β (MulZeroClass.toHasZero.{u3} β (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} β (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} β (Semiring.toNonAssocSemiring.{u3} β (StrictOrderedSemiring.toSemiring.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2)))))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (OrderedCancelAddCommMonoid.toPartialOrder.{u3} β (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2)))))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : NonUnitalNonAssocRing.{u2} α] [_inst_2 : LinearOrderedSemiring.{u3} β] [_inst_3 : RingSeminormClass.{u1, u2, u3} F α β _inst_1 (StrictOrderedSemiring.toOrderedSemiring.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2))], NonnegHomClass.{u1, u2, u3} F α β (MonoidWithZero.toZero.{u3} β (Semiring.toMonoidWithZero.{u3} β (StrictOrderedSemiring.toSemiring.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (StrictOrderedSemiring.toPartialOrder.{u3} β (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align ring_seminorm_class.to_nonneg_hom_class RingSeminormClass.toNonnegHomClassₓ'. -/
-- See note [out-param inheritance]
-- See note [lower instance priority]
instance (priority := 100) RingSeminormClass.toNonnegHomClass [NonUnitalNonAssocRing α]
    [LinearOrderedSemiring β] [RingSeminormClass F α β] : NonnegHomClass F α β :=
  AddGroupSeminormClass.toNonnegHomClass
#align ring_seminorm_class.to_nonneg_hom_class RingSeminormClass.toNonnegHomClass

#print MulRingSeminormClass.toRingSeminormClass /-
-- See note [lower instance priority]
instance (priority := 100) MulRingSeminormClass.toRingSeminormClass [NonAssocRing α]
    [OrderedSemiring β] [MulRingSeminormClass F α β] : RingSeminormClass F α β :=
  { ‹MulRingSeminormClass F α β› with map_mul_le_mul := fun f a b => (map_mul _ _ _).le }
#align mul_ring_seminorm_class.to_ring_seminorm_class MulRingSeminormClass.toRingSeminormClass
-/

#print MulRingNormClass.toRingNormClass /-
-- See note [lower instance priority]
instance (priority := 100) MulRingNormClass.toRingNormClass [NonAssocRing α] [OrderedSemiring β]
    [MulRingNormClass F α β] : RingNormClass F α β :=
  { ‹MulRingNormClass F α β›, MulRingSeminormClass.toRingSeminormClass with }
#align mul_ring_norm_class.to_ring_norm_class MulRingNormClass.toRingNormClass
-/

