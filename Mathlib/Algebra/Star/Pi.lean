/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.pi
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, HasStar (f i)] : HasStar (∀ i, f i) where star x i := star (x i)

@[simp]
theorem star_apply [∀ i, HasStar (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl
#align pi.star_apply Pi.star_apply

theorem star_def [∀ i, HasStar (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl
#align pi.star_def Pi.star_def

instance [∀ i, HasInvolutiveStar (f i)] : HasInvolutiveStar (∀ i, f i)
    where star_involutive _ := funext fun _ => star_star _

instance [∀ i, Semigroup (f i)] [∀ i, StarSemigroup (f i)] : StarSemigroup (∀ i, f i)
    where star_mul _ _ := funext fun _ => star_mul _ _

instance [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i)
    where star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiring (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starSemigroup : StarSemigroup (∀ i, f i)) with }

instance {R : Type w} [∀ i, HasSmul R (f i)] [HasStar R] [∀ i, HasStar (f i)]
    [∀ i, StarModule R (f i)] : StarModule R (∀ i, f i)
    where star_smul r x := funext fun i => star_smul r (x i)

theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun i => star_zero _) i a
#align pi.single_star Pi.single_star

end Pi

namespace Function

theorem update_star [∀ i, HasStar (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun i => star) h i a j).symm
#align function.update_star Function.update_star

theorem star_sum_elim {I J α : Type _} (x : I → α) (y : J → α) [HasStar α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) :=
  by
  ext x
  cases x <;> simp
#align function.star_sum_elim Function.star_sum_elim

end Function

