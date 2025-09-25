/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Ring.Pi

/-!
# Basic Results about Star on Pi Types

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Pi/Defs.lean`.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, Star (f i)] [∀ i, TrivialStar (f i)] : TrivialStar (∀ i, f i) where
  star_trivial _ := funext fun _ => star_trivial _

instance [∀ i, InvolutiveStar (f i)] : InvolutiveStar (∀ i, f i) where
  star_involutive _ := funext fun _ => star_star _

instance [∀ i, Mul (f i)] [∀ i, StarMul (f i)] : StarMul (∀ i, f i) where
  star_mul _ _ := funext fun _ => star_mul _ _

instance [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] : StarAddMonoid (∀ i, f i) where
  star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiring (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i)
  where star_add _ _ := funext fun _ => star_add _ _

instance {R : Type w} [∀ i, SMul R (f i)] [Star R] [∀ i, Star (f i)]
    [∀ i, StarModule R (f i)] : StarModule R (∀ i, f i) where
  star_smul r x := funext fun i => star_smul r (x i)

theorem single_star [∀ i, AddMonoid (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I)
    (a : f i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun _ => star_zero _) i a

open scoped ComplexConjugate

@[simp]
lemma conj_apply {ι : Type*} {α : ι → Type*} [∀ i, CommSemiring (α i)] [∀ i, StarRing (α i)]
    (f : ∀ i, α i) (i : ι) : conj f i = conj (f i) := rfl

end Pi

namespace Function

theorem update_star [∀ i, Star (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun _ => star) h i a j).symm

theorem star_sumElim {I J α : Type*} (x : I → α) (y : J → α) [Star α] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

end Function
