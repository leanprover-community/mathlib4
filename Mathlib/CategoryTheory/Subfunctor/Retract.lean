/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Retracts of subfunctors

A retract of type-valued functors that preserves two subfunctors induces a retraction
of their inclusion morphisms.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {F G : C ⥤ Type w}

/-- If a functor `F : C ⥤ Type w` is a retract of `G : C ⥤ Type w`, with maps `i : F ⟶ G`
and `r : G ⟶ F`, and `A ⟶ F` and `B ⟶ G` are subfunctors such that `A ≤ B.preimage i`
and `B ≤ A.preimage r`, then `A ⟶ F` is a retract of `B ⟶ G`. -/
@[simps! i_right r_right]
def retractArrow (A : Subfunctor F) (B : Subfunctor G) (h : Retract F G)
    (hi : A ≤ B.preimage h.i) (hr : B ≤ A.preimage h.r) : RetractArrow A.ι B.ι where
  i := Arrow.homMk (lift (A.ι ≫ h.i) (by rwa [range_comp, range_ι, image_le_iff])) h.i
  r := Arrow.homMk (lift (B.ι ≫ h.r) (by rwa [range_comp, range_ι, image_le_iff])) h.r
  retract := by ext : 1 <;> simp [← cancel_mono A.ι]

end CategoryTheory.Subfunctor
