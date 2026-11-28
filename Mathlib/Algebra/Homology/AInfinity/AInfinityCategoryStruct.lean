/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Zhan Shi, Justin Mu, Marco David
-/
module

public import Mathlib.Algebra.Homology.AInfinity.GradedLinearQuiver
public import Mathlib.Algebra.Homology.AInfinity.GradedMultilinearMap
public import Mathlib.Algebra.Homology.AInfinity.Grading

/-!
# A∞-category structures

An A∞-category structure on a graded `R`-linear quiver consists of higher compositions
mₙ : Hom(X₀, X₁) ⊗ ⋯ ⊗ Hom(Xₙ₋₁, Xₙ) → Hom(X₀, Xₙ) of degree 2 - n, one for each n ≥ 1.

## Main definitions

* `AInfinity.AInfinityOperation β R X`: the n-ary operations of degree 2 - n on a
  string of objects `X`.
* `AInfinity.AInfinityCategoryStruct β R Obj`: a graded `R`-linear quiver with higher
  compositions mₙ, not yet subject to any relations.

## Implementation notes

The ring of scalars `R` is a semiring and object types can carry several rings of scalars.
It is passed explicitly wherever it cannot be inferred from later arguments: to the hom
spaces `(X →ᵍ[R] Y) i`, to `ComposableHom`, to `AInfinityOperation` and to `homCongr`. The type
of degrees `β` is passed explicitly to `ComposableHom` and to `AInfinityOperation` as well.
-/

@[expose] public section

namespace AInfinity

universe u v w

open GradedLinearQuiver

variable {β : Type v} [AddCommGroup β] [Grading β]
variable {R : Type u} [Semiring R] {Obj : Type w}

variable (β R) [GradedLinearQuiver β R Obj] in
/-- The n-ary A∞ operations for a given string of objects `X` are graded multilinear
maps of degree 2 - n from the hom spaces between consecutive objects to the hom space from the
first object `X 0` to the last object `X (Fin.last n)`. -/
abbrev AInfinityOperation {n : ℕ} (X : Fin (n + 1) → Obj) :=
  GradedMultilinearMap R (ComposableHom β R X) (X 0 →ᵍ[R] X (Fin.last n))
    ((2 - n : ℤ) • degOne)

variable (β R Obj) in
/-- The data of an A∞-category is a graded `R`-linear quiver together with, for each `n ≥ 1`
and each string of objects `X`, an `AInfinityOperation` mₙ. No relations are imposed here,
but `AInfinityCategory` adds the Stasheff identities. -/
class AInfinityCategoryStruct extends GradedLinearQuiver β R Obj where
  /-- The higher compositions mₙ. -/
  m {n : ℕ} [NeZero n] (X : Fin (n + 1) → Obj) : AInfinityOperation β R X

end AInfinity
