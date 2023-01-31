/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module algebra.graded_mul_action
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GradedMonoid

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(•) : A i → M j → M (i + j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `GradedMonoid.GHasSmul A M`
* `GradedMonoid.GMulAction A M`

With the `SigmaGraded` locale open, these respectively imbue:

* `HasSmul (GradedMonoid A) (GradedMonoid M)`
* `MulAction (GradedMonoid A) (GradedMonoid M)`

For now, these typeclasses are primarily used in the construction of `DirectSum.GModule.Module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.HasGradedSmul A M` (which provides the obvious `GradedMonoid.GHasSmul A` instance)

which provides the API lemma

* `SetLike.graded_smul_mem_graded`

Note that there is no need for `SetLike.graded_mul_action` or similar, as all the information it
would contain is already supplied by `HasGradedSmul` when the objects within `A` and `M` have
a `MulAction` instance.

## tags

graded action
-/


variable {ι : Type _}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _) (M : ι → Type _)

/-- A graded version of `HasSmul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class GHasSmul [Add ι] where
  smul {i j} : A i → M j → M (i + j)
#align graded_monoid.ghas_smul GradedMonoid.GHasSmul

/-- A graded version of `HasMul.toHasSmul` -/
instance GMul.toGHasSmul [Add ι] [GMul A] : GHasSmul A A where smul := GMul.mul
#align graded_monoid.ghas_mul.to_ghas_smul GradedMonoid.GMul.toGHasSmul

instance GHasSmul.toHasSmul [Add ι] [GHasSmul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun x y ↦ ⟨_, GHasSmul.smul x.snd y.snd⟩⟩
#align graded_monoid.ghas_smul.to_has_smul GradedMonoid.GHasSmul.toHasSmul

theorem mk_smul_mk [Add ι] [GHasSmul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i + j) (GHasSmul.smul a b) :=
  rfl
#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mk

/-- A graded version of `MulAction`. -/
class GMulAction [AddMonoid ι] [GMonoid A] extends GHasSmul A M where
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
#align graded_monoid.gmul_action GradedMonoid.GMulAction

/-- The graded version of `Monoid.toMulAction`. -/
instance GMonoid.toGMulAction [AddMonoid ι] [GMonoid A] : GMulAction A A :=
  { GMul.toGHasSmul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
#align graded_monoid.gmonoid.to_gmul_action GradedMonoid.GMonoid.toGMulAction

instance GMulAction.toMulAction [AddMonoid ι] [GMonoid A] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M)
    where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul
#align graded_monoid.gmul_action.to_mul_action GradedMonoid.GMulAction.toMulAction

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

/-- A version of `GradedMonoid.GHasSmul` for internally graded objects. -/
class SetLike.HasGradedSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
  (A : ι → S) (B : ι → N) : Prop where
  smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j)
#align set_like.has_graded_smul SetLike.HasGradedSmul

instance SetLike.gHasSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.HasGradedSmul A B] :
    GradedMonoid.GHasSmul (fun i ↦ A i) fun i ↦ B i
    where smul a b := ⟨a.val • b.val, SetLike.HasGradedSmul.smul_mem a.2 b.2⟩
#align set_like.ghas_smul SetLike.gHasSmul

@[simp]
theorem SetLike.coe_gHasSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.HasGradedSmul A B] {i j : ι} (x : A i) (y : B j) :
    (@GradedMonoid.GHasSmul.smul ι (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.val • y.val :=
  rfl
#align set_like.coe_ghas_smul SetLike.coe_gHasSmul

/-- Internally graded version of `HasMul.to_hasSmul`. -/
instance SetLike.GradedMul.to_hasGradedSmul [AddMonoid ι] [Monoid R] {S : Type _} [SetLike S R]
    (A : ι → S) [SetLike.GradedMonoid A] : SetLike.HasGradedSmul A A
    where smul_mem _ _ _ _ hi hj := SetLike.GradedMonoid.toGradedMul.mul_mem hi hj
#align set_like.has_graded_mul.to_has_graded_smul SetLike.GradedMul.to_hasGradedSmul

end Subobjects

section HomogeneousElements

variable {S R N M : Type _} [SetLike S R] [SetLike N M]

theorem SetLike.Homogeneous.graded_smul [Add ι] [SMul R M] {A : ι → S} {B : ι → N}
    [SetLike.HasGradedSmul A B] {a : R} {b : M} :
    SetLike.Homogeneous A a → SetLike.Homogeneous B b → SetLike.Homogeneous B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i + j, SetLike.HasGradedSmul.smul_mem hi hj⟩
#align set_like.is_homogeneous.graded_smul SetLike.Homogeneous.graded_smul

end HomogeneousElements
