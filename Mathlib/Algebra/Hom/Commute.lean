/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Group.Commute

/-!
# Multiplicative homomorphisms respect semiconjugation and commutation.
-/


section Commute

variable {F M N : Type _} [Mul M] [Mul N] {a x y : M}

@[simp, to_additive]
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h
#align semiconj_by.map SemiconjBy.map

@[simp, to_additive]
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  h.map f
#align commute.map Commute.map

end Commute

