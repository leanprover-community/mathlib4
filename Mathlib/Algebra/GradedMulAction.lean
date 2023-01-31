/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

! This file was ported from Lean 3 source module algebra.graded_mul_action
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GradedMonoid

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(•) : A i → M j → M (i + j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `graded_monoid.ghas_smul A M`
* `graded_monoid.gmul_action A M`

With the `sigma_graded` locale open, these respectively imbue:

* `has_smul (graded_monoid A) (graded_monoid M)`
* `mul_action (graded_monoid A) (graded_monoid M)`

For now, these typeclasses are primarily used in the construction of `direct_sum.gmodule.module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_smul A M` (which provides the obvious `graded_monoid.ghas_smul A` instance)

which provides the API lemma

* `set_like.graded_smul_mem_graded`

Note that there is no need for `set_like.graded_mul_action` or similar, as all the information it
would contain is already supplied by `has_graded_smul` when the objects within `A` and `M` have
a `mul_action` instance.

## tags

graded action
-/


variable {ι : Type _}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ι → Type _) (M : ι → Type _)

/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class GhasSmul [Add ι] where
  smul {i j} : A i → M j → M (i + j)
#align graded_monoid.ghas_smul GradedMonoid.GhasSmul

/-- A graded version of `has_mul.to_has_smul` -/
instance GMul.toGhasSmul [Add ι] [GMul A] : GhasSmul A A where smul _ _ := GMul.mul
#align graded_monoid.ghas_mul.to_ghas_smul GradedMonoid.GMul.toGhasSmul

instance GhasSmul.toHasSmul [Add ι] [GhasSmul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun (x : GradedMonoid A) (y : GradedMonoid M) => ⟨_, GhasSmul.smul x.snd y.snd⟩⟩
#align graded_monoid.ghas_smul.to_has_smul GradedMonoid.GhasSmul.toHasSmul

theorem mk_smul_mk [Add ι] [GhasSmul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i + j) (GhasSmul.smul a b) :=
  rfl
#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mk

/-- A graded version of `mul_action`. -/
class GmulAction [AddMonoid ι] [GMonoid A] extends GhasSmul A M where
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
#align graded_monoid.gmul_action GradedMonoid.GmulAction

/-- The graded version of `monoid.to_mul_action`. -/
instance GMonoid.toGmulAction [AddMonoid ι] [GMonoid A] : GmulAction A A :=
  { GMul.toGhasSmul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
#align graded_monoid.gmonoid.to_gmul_action GradedMonoid.GMonoid.toGmulAction

instance GmulAction.toMulAction [AddMonoid ι] [GMonoid A] [GmulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M)
    where
  one_smul := GmulAction.one_smul
  mul_smul := GmulAction.mul_smul
#align graded_monoid.gmul_action.to_mul_action GradedMonoid.GmulAction.toMulAction

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type _}

/-- A version of `graded_monoid.ghas_smul` for internally graded objects. -/
class SetLike.HasGradedSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
  (A : ι → S) (B : ι → N) : Prop where
  smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j)
#align set_like.has_graded_smul SetLike.HasGradedSmul

instance SetLike.ghasSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.HasGradedSmul A B] :
    GradedMonoid.GhasSmul (fun i => A i) fun i => B i
    where smul i j a b := ⟨(a : R) • b, SetLike.HasGradedSmul.smul_mem a.2 b.2⟩
#align set_like.ghas_smul SetLike.ghasSmul

@[simp]
theorem SetLike.coe_ghasSmul {S R N M : Type _} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.HasGradedSmul A B] {i j : ι} (x : A i) (y : B j) :
    (@GradedMonoid.GhasSmul.smul ι (fun i => A i) (fun i => B i) _ _ i j x y : M) = (x : R) • y :=
  rfl
#align set_like.coe_ghas_smul SetLike.coe_ghasSmul

/-- Internally graded version of `has_mul.to_has_smul`. -/
instance SetLike.GradedMul.to_hasGradedSmul [AddMonoid ι] [Monoid R] {S : Type _} [SetLike S R]
    (A : ι → S) [SetLike.GradedMonoid A] : SetLike.HasGradedSmul A A
    where smul_mem i j ai bj hi hj := SetLike.GradedMonoid.mul_mem hi hj
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

