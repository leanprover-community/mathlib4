/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.Algebra.GradedMonoid

#align_import algebra.graded_mul_action from "leanprover-community/mathlib"@"861a26926586cd46ff80264d121cdb6fa0e35cc1"

/-!
# Additively-graded multiplicative action structures

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `GradedMonoid A` such that `(•) : A i → M j → M (i +ᵥ j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `GradedMonoid.GSMul A M`
* `GradedMonoid.GMulAction A M`

With the `SigmaGraded` locale open, these respectively imbue:

* `SMul (GradedMonoid A) (GradedMonoid M)`
* `MulAction (GradedMonoid A) (GradedMonoid M)`

For now, these typeclasses are primarily used in the construction of `DirectSum.GModule.Module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`SetLike` subobjects (such as `AddSubmonoid`s, `AddSubgroup`s, or `Submodule`s), this file
provides the `Prop` typeclasses:

* `SetLike.GradedSMul A M` (which provides the obvious `GradedMonoid.GSMul A` instance)

which provides the API lemma

* `SetLike.graded_smul_mem_graded`

Note that there is no need for `SetLike.graded_mul_action` or similar, as all the information it
would contain is already supplied by `GradedSMul` when the objects within `A` and `M` have
a `MulAction` instance.

## Tags

graded action
-/


variable {ιA ιB ιM : Type*}

namespace GradedMonoid

/-! ### Typeclasses -/


section Defs

variable (A : ιA → Type*) (M : ιM → Type*)

/-- A graded version of `SMul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class GSMul [VAdd ιA ιM] where
  /-- The homogeneous multiplication map `smul` -/
  smul {i j} : A i → M j → M (i +ᵥ j)
#align graded_monoid.ghas_smul GradedMonoid.GSMul

/-- A graded version of `Mul.toSMul` -/
instance GMul.toGSMul [Add ιA] [GMul A] : GSMul A A where smul := GMul.mul
#align graded_monoid.ghas_mul.to_ghas_smul GradedMonoid.GMul.toGSMul

instance GSMul.toSMul [VAdd ιA ιM] [GSMul A M] : SMul (GradedMonoid A) (GradedMonoid M) :=
  ⟨fun x y ↦ ⟨_, GSMul.smul x.snd y.snd⟩⟩
#align graded_monoid.ghas_smul.to_has_smul GradedMonoid.GSMul.toSMul

theorem mk_smul_mk [VAdd ιA ιM] [GSMul A M] {i j} (a : A i) (b : M j) :
    mk i a • mk j b = mk (i +ᵥ j) (GSMul.smul a b) :=
  rfl
#align graded_monoid.mk_smul_mk GradedMonoid.mk_smul_mk

/-- A graded version of `MulAction`. -/
class GMulAction [AddMonoid ιA] [VAdd ιA ιM] [GMonoid A] extends GSMul A M where
  /-- One is the neutral element for `•` -/
  one_smul (b : GradedMonoid M) : (1 : GradedMonoid A) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul (a a' : GradedMonoid A) (b : GradedMonoid M) : (a * a') • b = a • a' • b
#align graded_monoid.gmul_action GradedMonoid.GMulAction

/-- The graded version of `Monoid.toMulAction`. -/
instance GMonoid.toGMulAction [AddMonoid ιA] [GMonoid A] : GMulAction A A :=
  { GMul.toGSMul _ with
    one_smul := GMonoid.one_mul
    mul_smul := GMonoid.mul_assoc }
#align graded_monoid.gmonoid.to_gmul_action GradedMonoid.GMonoid.toGMulAction

instance GMulAction.toMulAction [AddMonoid ιA] [GMonoid A] [VAdd ιA ιM] [GMulAction A M] :
    MulAction (GradedMonoid A) (GradedMonoid M) where
  one_smul := GMulAction.one_smul
  mul_smul := GMulAction.mul_smul
#align graded_monoid.gmul_action.to_mul_action GradedMonoid.GMulAction.toMulAction

end Defs

end GradedMonoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/


section Subobjects

variable {R : Type*}

/-- A version of `GradedMonoid.GSMul` for internally graded objects. -/
class SetLike.GradedSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
  (A : ιA → S) (B : ιB → N) : Prop where
  /-- Multiplication is homogeneous -/
  smul_mem : ∀ ⦃i : ιA⦄ ⦃j : ιB⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i +ᵥ j)
#align set_like.has_graded_smul SetLike.GradedSMul

instance SetLike.toGSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] :
    GradedMonoid.GSMul (fun i ↦ A i) fun i ↦ B i where
  smul a b := ⟨a.1 • b.1, SetLike.GradedSMul.smul_mem a.2 b.2⟩
#align set_like.ghas_smul SetLike.toGSMul

/-
Porting note: simpNF linter returns
"Left-hand side does not simplify, when using the simp lemma on itself."
However, simp does indeed solve the following. Possibly related std#71,std#78
example {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [Add ι]
    (A : ι → S) (B : ι → N) [SetLike.GradedSMul A B] {i j : ι} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ι (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.1 • y.1 := by simp
-/
@[simp,nolint simpNF]
theorem SetLike.coe_GSMul {S R N M : Type*} [SetLike S R] [SetLike N M] [SMul R M] [VAdd ιA ιB]
    (A : ιA → S) (B : ιB → N) [SetLike.GradedSMul A B] {i : ιA} {j : ιB} (x : A i) (y : B j) :
    (@GradedMonoid.GSMul.smul ιA ιB (fun i ↦ A i) (fun i ↦ B i) _ _ i j x y : M) = x.1 • y.1 :=
  rfl
#align set_like.coe_ghas_smul SetLike.coe_GSMul

/-- Internally graded version of `Mul.toSMul`. -/
instance SetLike.GradedMul.toGradedSMul [AddMonoid ιA] [Monoid R] {S : Type*} [SetLike S R]
    (A : ιA → S) [SetLike.GradedMonoid A] : SetLike.GradedSMul A A where
  smul_mem _ _ _ _ hi hj := SetLike.GradedMonoid.toGradedMul.mul_mem hi hj
#align set_like.has_graded_mul.to_has_graded_smul SetLike.GradedMul.toGradedSMul

end Subobjects

section HomogeneousElements

variable {S R N M : Type*} [SetLike S R] [SetLike N M]

theorem SetLike.Homogeneous.graded_smul [VAdd ιA ιB] [SMul R M] {A : ιA → S} {B : ιB → N}
    [SetLike.GradedSMul A B] {a : R} {b : M} :
    SetLike.Homogeneous A a → SetLike.Homogeneous B b → SetLike.Homogeneous B (a • b)
  | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨i +ᵥ j, SetLike.GradedSMul.smul_mem hi hj⟩
#align set_like.is_homogeneous.graded_smul SetLike.Homogeneous.graded_smul

end HomogeneousElements
