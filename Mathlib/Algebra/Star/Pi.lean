/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Star.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Basic Results about Star on Pi Types

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Pi/Defs.lean`.
-/

public section

variable {S ι : Type*} {R : ι → Type*}
namespace Pi

instance [∀ i, Star (R i)] [∀ i, TrivialStar (R i)] : TrivialStar (∀ i, R i) where
  star_trivial _ := funext fun _ => star_trivial _

instance [∀ i, InvolutiveStar (R i)] : InvolutiveStar (∀ i, R i) where
  star_involutive _ := funext fun _ => star_star _

instance [∀ i, Mul (R i)] [∀ i, StarMul (R i)] : StarMul (∀ i, R i) where
  star_mul _ _ := funext fun _ => star_mul _ _

instance [∀ i, AddMonoid (R i)] [∀ i, StarAddMonoid (R i)] : StarAddMonoid (∀ i, R i) where
  star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiring (R i)] [∀ i, StarRing (R i)] : StarRing (∀ i, R i)
  where star_add _ _ := funext fun _ => star_add _ _

instance [∀ i, SMul S (R i)] [Star S] [∀ i, Star (R i)] [∀ i, StarModule S (R i)] :
    StarModule S (∀ i, R i) where
  star_smul r x := funext fun i => star_smul r (x i)

theorem single_star [∀ i, AddMonoid (R i)] [∀ i, StarAddMonoid (R i)] [DecidableEq ι] (i : ι)
    (a : R i) : Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (R i) _) (fun _ => star_zero _) i a

open scoped ComplexConjugate

/-- Unapplied form of `Pi.conj_apply`, tagged `push ←` so that `@[to_fun]` can eta-expand `conj f`
into `fun i ↦ conj (f i)`. -/
@[push ←]
lemma conj_def [∀ i, CommSemiring (R i)] [∀ i, StarRing (R i)] (f : ∀ i, R i) :
    conj f = fun i ↦ conj (f i) := rfl

@[simp]
lemma conj_apply [∀ i, CommSemiring (R i)] [∀ i, StarRing (R i)]
    (f : ∀ i, R i) (i : ι) : conj f i = conj (f i) := rfl

end Pi

namespace IsStarOrtho

open scoped StarRing

variable [∀ i, NonUnitalSemiring (R i)] [∀ i, StarRing (R i)]

lemma pi_iff {x y : ∀ i, R i} : x ⋆⟂ y ↔ ∀ i, x i ⋆⟂ y i := by
  aesop (add simp [isStarOrtho_iff, funext_iff])

protected lemma pi {x y : ∀ i, R i} (h : ∀ i, x i ⋆⟂ y i) : x ⋆⟂ y :=
  pi_iff.mpr h

end IsStarOrtho

namespace Function

theorem update_star [∀ i, Star (R i)] [DecidableEq ι] (h : ∀ i, R i) (i : ι) (a : R i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun _ => star) h i a j).symm

theorem star_sumElim {ι κ R : Type*} (x : ι → R) (y : κ → R) [Star R] :
    star (Sum.elim x y) = Sum.elim (star x) (star y) := by
  ext x; cases x <;> simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr]

end Function
