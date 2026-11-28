/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Zhan Shi, Marco David
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Graded linear quivers

A graded `R`-linear quiver on a type of objects `Obj` assigns to each pair of objects `X` and
`Y` and each degree `i : β` an `R`-module `Hom R X Y i` of morphisms of degree `i`. It is the
underlying data of an A∞-category, before any compositions are chosen.

## Main definitions

* `AInfinity.GradedLinearQuiver β R Obj`: a graded `R`-linear quiver.
* `AInfinity.GradedLinearQuiver.ComposableHom`: the family of graded hom spaces associated
  to a string of objects.
* `AInfinity.GradedLinearQuiver.homCongr`: transport between graded hom spaces along
  equalities of the source, target and degree.

## Notation

* `X →ᵍ[R] Y`: the graded family `GradedLinearQuiver.Hom R X Y : β → Type*` of morphisms from
  `X` to `Y`, so that `(X →ᵍ[R] Y) i` is the `R`-module of morphisms of degree `i`. The variant
  `X →ᵍ[R, β] Y` allows naming the type of degrees explicitly. Both are scoped to
  `AInfinity.GradedLinearQuiver`.
-/

@[expose] public section

namespace AInfinity

universe u v w w'

/-- A graded `R`-linear quiver: for objects `X` and `Y` and a degree `i`, the morphisms of
degree `i` from `X` to `Y` form an `R`-module `Hom R X Y i`. -/
class GradedLinearQuiver (β : Type v) (R : Type u) [Semiring R] (Obj : Type w) where
  /-- The morphisms of degree `i` from `X` to `Y`. The semiring `R` is an explicit argument so
  that it can be displayed in the notation `X →ᵍ[R] Y`. -/
  Hom (R) : Obj → Obj → β → Type w'
  /-- Each graded piece of a hom space is an abelian group. -/
  homGroup : ∀ X Y i, AddCommGroup (Hom X Y i) := by infer_instance
  /-- Each graded piece of a hom space is an `R`-module. -/
  homModule : ∀ X Y i, Module R (Hom X Y i) := by infer_instance

attribute [instance_reducible, instance] GradedLinearQuiver.homGroup
  GradedLinearQuiver.homModule

namespace GradedLinearQuiver

variable {β : Type v} {R : Type u} [Semiring R] {Obj : Type w} [GradedLinearQuiver β R Obj]
variable {n : ℕ}

/-- `X →ᵍ[R] Y` is the graded family of `R`-modules of morphisms from `X` to `Y` in a graded
`R`-linear quiver, with `(X →ᵍ[R] Y) i` the module of morphisms of degree `i`. -/
scoped notation:25 X " →ᵍ[" R:25 "] " Y:0 => GradedLinearQuiver.Hom R X Y

/-- `X →ᵍ[R, β] Y` is `X →ᵍ[R] Y` with the type of degrees `β` given explicitly, for use when `β`
cannot be inferred from a degree or the expected type. -/
scoped notation:25 X " →ᵍ[" R:25 ", " B "] " Y:0 =>
  GradedLinearQuiver.Hom (β := B) R X Y

variable (β R) in
/-- For a string of objects `X 0`, …, `X n`, this is the family of graded hom spaces between
consecutive objects, sending an index `i : Fin n` to `X i.castSucc →ᵍ[R] X i.succ`. -/
abbrev ComposableHom (X : Fin (n + 1) → Obj) (i : Fin n) : β → Type w' :=
  X i.castSucc →ᵍ[R] X i.succ

variable (R) in
/-- Transport between graded hom spaces along equalities of the source, target and degree.
This is the three-index form of `LinearEquiv.cast`. -/
def homCongr {X X' Y Y' : Obj} {i i' : β} (hX : X = X') (hY : Y = Y') (hi : i = i') :
    (X →ᵍ[R] Y) i ≃ₗ[R] (X' →ᵍ[R] Y') i' := by
  subst hX hY hi
  exact LinearEquiv.refl R _

@[simp]
lemma homCongr_refl (X Y : Obj) (i : β) :
    homCongr R (rfl : X = X) (rfl : Y = Y) (rfl : i = i) = LinearEquiv.refl R _ :=
  rfl

@[simp]
lemma homCongr_symm {X X' Y Y' : Obj} {i i' : β} (hX : X = X') (hY : Y = Y') (hi : i = i') :
    (homCongr R hX hY hi).symm = homCongr R hX.symm hY.symm hi.symm := by
  subst hX hY hi
  rfl

@[simp]
lemma homCongr_trans {X X' X'' Y Y' Y'' : Obj} {i i' i'' : β} (hX : X = X') (hY : Y = Y')
    (hi : i = i') (hX' : X' = X'') (hY' : Y' = Y'') (hi' : i' = i'') :
    (homCongr R hX hY hi).trans (homCongr R hX' hY' hi') =
      homCongr R (hX.trans hX') (hY.trans hY') (hi.trans hi') := by
  subst hX hY hi hX' hY' hi'
  rfl

end GradedLinearQuiver

end AInfinity
