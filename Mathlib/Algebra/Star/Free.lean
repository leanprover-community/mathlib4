/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.FreeAlgebra

#align_import algebra.star.free from "leanprover-community/mathlib"@"07c3cf2d851866ff7198219ed3fedf42e901f25c"

/-!
# A *-algebra structure on the free algebra.

Reversing words gives a *-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `Algebra.FreeMonoid` and `Algebra.FreeAlgebra`,
to avoid importing `Algebra.Star.Basic` into the entire hierarchy.
-/


namespace FreeMonoid

variable {α : Type*}

instance : StarSemigroup (FreeMonoid α) where
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := List.reverse_append

@[simp]
theorem star_of (x : α) : star (of x) = of x :=
  rfl
#align free_monoid.star_of FreeMonoid.star_of

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp, nolint simpNF] -- Porting note: dsimp cannot prove this
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl
#align free_monoid.star_one FreeMonoid.star_one

end FreeMonoid

namespace FreeAlgebra

variable {R : Type*} [CommSemiring R] {X : Type*}

/-- The star ring formed by reversing the elements of products -/
instance : StarRing (FreeAlgebra R X) where
  star := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive x := by
    unfold Star.star
    -- ⊢ { star := MulOpposite.unop ∘ ↑(↑(lift R) (MulOpposite.op ∘ ι R)) }.1 ({ star …
    simp only [Function.comp_apply]
    -- ⊢ MulOpposite.unop (↑(↑(lift R) (MulOpposite.op ∘ ι R)) (MulOpposite.unop (↑(↑ …
    refine' FreeAlgebra.induction R X _ _ _ _ x
    · intros
      -- ⊢ MulOpposite.unop (↑(↑(lift R) (MulOpposite.op ∘ ι R)) (MulOpposite.unop (↑(↑ …
      simp only [AlgHom.commutes, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
      -- 🎉 no goals
    · intros
      -- ⊢ MulOpposite.unop (↑(↑(lift R) (MulOpposite.op ∘ ι R)) (MulOpposite.unop (↑(↑ …
      simp only [lift_ι_apply, Function.comp_apply, MulOpposite.unop_op]
      -- 🎉 no goals
    · intros
      -- ⊢ MulOpposite.unop (↑(↑(lift R) (MulOpposite.op ∘ ι R)) (MulOpposite.unop (↑(↑ …
      simp only [*, map_mul, MulOpposite.unop_mul]
      -- 🎉 no goals
    · intros
      -- ⊢ MulOpposite.unop (↑(↑(lift R) (MulOpposite.op ∘ ι R)) (MulOpposite.unop (↑(↑ …
      simp only [*, map_add, MulOpposite.unop_add]
      -- 🎉 no goals
  star_mul a b := by simp only [Function.comp_apply, map_mul, MulOpposite.unop_mul]
                     -- 🎉 no goals
  star_add a b := by simp only [Function.comp_apply, map_add, MulOpposite.unop_add]
                     -- 🎉 no goals

@[simp]
theorem star_ι (x : X) : star (ι R x) = ι R x := by simp [star, Star.star]
                                                    -- 🎉 no goals
#align free_algebra.star_ι FreeAlgebra.star_ι

@[simp]
theorem star_algebraMap (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [star, Star.star]
  -- 🎉 no goals
#align free_algebra.star_algebra_map FreeAlgebra.star_algebraMap

/-- `star` as an `AlgEquiv` -/
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with commutes' := fun r => by simp [star_algebraMap] }
                                                -- 🎉 no goals
#align free_algebra.star_hom FreeAlgebra.starHom

end FreeAlgebra
