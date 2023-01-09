/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.star.prod
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Prod
import Mathbin.Algebra.Module.Prod

/-!
# `star` on product types

We put a `has_star` structure on product types that operates elementwise.
-/


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

instance [HasStar R] [HasStar S] : HasStar (R × S) where star x := (star x.1, star x.2)

@[simp]
theorem fst_star [HasStar R] [HasStar S] (x : R × S) : (star x).1 = star x.1 :=
  rfl
#align prod.fst_star Prod.fst_star

@[simp]
theorem snd_star [HasStar R] [HasStar S] (x : R × S) : (star x).2 = star x.2 :=
  rfl
#align prod.snd_star Prod.snd_star

theorem star_def [HasStar R] [HasStar S] (x : R × S) : star x = (star x.1, star x.2) :=
  rfl
#align prod.star_def Prod.star_def

instance [HasInvolutiveStar R] [HasInvolutiveStar S] : HasInvolutiveStar (R × S)
    where star_involutive _ := Prod.ext (star_star _) (star_star _)

instance [Semigroup R] [Semigroup S] [StarSemigroup R] [StarSemigroup S] : StarSemigroup (R × S)
    where star_mul _ _ := Prod.ext (star_mul _ _) (star_mul _ _)

instance [AddMonoid R] [AddMonoid S] [StarAddMonoid R] [StarAddMonoid S] : StarAddMonoid (R × S)
    where star_add _ _ := Prod.ext (star_add _ _) (star_add _ _)

instance [NonUnitalSemiring R] [NonUnitalSemiring S] [StarRing R] [StarRing S] : StarRing (R × S) :=
  { Prod.starAddMonoid, (Prod.starSemigroup : StarSemigroup (R × S)) with }

instance {α : Type w} [HasSmul α R] [HasSmul α S] [HasStar α] [HasStar R] [HasStar S]
    [StarModule α R] [StarModule α S] : StarModule α (R × S)
    where star_smul r x := Prod.ext (star_smul _ _) (star_smul _ _)

end Prod

@[simp]
theorem Units.embed_product_star [Monoid R] [StarSemigroup R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) :=
  rfl
#align units.embed_product_star Units.embed_product_star

