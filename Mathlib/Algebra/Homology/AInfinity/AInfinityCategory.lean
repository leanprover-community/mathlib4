/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Zhan Shi, Justin Mu, Marco David
-/
module

public import Mathlib.Algebra.Homology.AInfinity.Stasheff

/-!
# A∞-categories

An A∞-category is a graded `R`-linear quiver together with higher compositions
mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ) of degree 2 - n for each n ≥ 1
(i.e. an `AInfinityCategoryStruct`), satisfying the Stasheff identities.

## Main definitions

* `AInfinity.AInfinityCategory β R Obj`: an A∞-category structure whose higher
  compositions satisfy the Stasheff identities.

## Implementation notes

As in [seidel2008], A∞-categories here are non-unital, which means that objects need not have
identity morphisms. The argument order and the Koszul signs of the
Stasheff identities differ from those of [seidel2008], and are described in
`Mathlib/Algebra/Homology/AInfinity/Stasheff.lean`.

## References

* [P. Seidel, *Fukaya categories and Picard-Lefschetz theory*][seidel2008]
-/

@[expose] public section

namespace AInfinity

universe u v w

variable (β : Type v) [AddCommGroup β] [Grading β]
variable (R : Type u) [Semiring R]
variable (Obj : Type w)

/-- An A∞-category is an A∞-category structure whose higher compositions satisfy the
Stasheff identities in every arity. -/
class AInfinityCategory extends AInfinityCategoryStruct β R Obj where
  /-- The higher compositions satisfy the Stasheff identities: in every arity `n ≥ 1`, the
  Stasheff sum of any composable string of morphisms vanishes. -/
  stasheffSum_eq_zero {n : ℕ} [NeZero n] {X : Fin (n + 1) → Obj} {deg : Fin n → β}
    (a : ∀ i : Fin n, GradedLinearQuiver.ComposableHom β R X i (deg i)) {d : β}
    (hd : stasheffTargetDeg deg = d) :
    stasheffSum a d hd = 0

end AInfinity
