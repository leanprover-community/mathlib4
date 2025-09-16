/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Star.Basic

/-!
# Basic Results about Star on Product Type

This file provides basic results about the star on product types defined in
`Mathlib/Algebra/Notation/Prod.lean`.

-/


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

instance [Star R] [Star S] [TrivialStar R] [TrivialStar S] : TrivialStar (R × S) where
  star_trivial _ := Prod.ext (star_trivial _) (star_trivial _)

instance [InvolutiveStar R] [InvolutiveStar S] : InvolutiveStar (R × S) where
  star_involutive _ := Prod.ext (star_star _) (star_star _)

instance [Mul R] [Mul S] [StarMul R] [StarMul S] : StarMul (R × S) where
  star_mul _ _ := Prod.ext (star_mul _ _) (star_mul _ _)

instance [AddMonoid R] [AddMonoid S] [StarAddMonoid R] [StarAddMonoid S] :
    StarAddMonoid (R × S) where
  star_add _ _ := Prod.ext (star_add _ _) (star_add _ _)

instance [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] [StarRing R] [StarRing S] :
    StarRing (R × S) :=
  { inferInstanceAs (StarAddMonoid (R × S)),
    inferInstanceAs (StarMul (R × S)) with }

instance {α : Type w} [SMul α R] [SMul α S] [Star α] [Star R] [Star S]
    [StarModule α R] [StarModule α S] : StarModule α (R × S) where
  star_smul _ _ := Prod.ext (star_smul _ _) (star_smul _ _)

end Prod

theorem Units.embed_product_star [Monoid R] [StarMul R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) :=
  rfl
