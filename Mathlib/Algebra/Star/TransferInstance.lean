/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Ring.TransferInstance

/-! # Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

variable {R S : Type*}

@[expose] public section

namespace Equiv

variable (e : R ≃ S)

/-- Transfer `Star` across an `Equiv` -/
protected abbrev star [Star S] : Star R where
  star r := e.symm (star (e r))

/-- Transfer `InvolutiveStar` across an `Equiv` -/
protected abbrev involutiveStar [InvolutiveStar S] : InvolutiveStar R :=
  let _ := e.star
  e.injective.involutiveStar _ fun _ ↦ e.apply_symm_apply _

/-- Transfer `StarMul` across an `Equiv` -/
protected abbrev starMul [Mul S] [StarMul S] :
    letI := e.mul
    StarMul R := by
  let := e.star
  let := e.mul
  apply e.injective.starMul <;> (intros; exact e.apply_symm_apply _)

/-- Transfer `StarAddMonoid` across an `Equiv` -/
protected abbrev starAddMonoid [AddMonoid S] [StarAddMonoid S] :
    letI := e.addMonoid
    StarAddMonoid R := by
  let := e.star
  let := e.addMonoid
  apply e.injective.starAddMonoid <;> (intros; exact e.apply_symm_apply _)

/-- Transfer `StarRing` across an `Equiv` -/
protected abbrev starRing [NonUnitalNonAssocSemiring S] [StarRing S] :
    letI := e.nonUnitalNonAssocSemiring
    StarRing R := by
  let := e.star
  let := e.nonUnitalNonAssocSemiring
  apply e.injective.starRing <;> (intros; exact e.apply_symm_apply _)

end Equiv
