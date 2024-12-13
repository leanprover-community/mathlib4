/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Data.Set.Finite.Basic

/-! # Presentable objects

If `κ` is a regular cardinal, we shall say that a preordered type `J`
is `κ`-directed (`IsCardinalDirected`) if any subset of `J` of
cardinality `< κ` has an upper bound.

A functor `F : C ⥤ D` is `κ`-accessible (`Functor.IsAccessible`)
if it commutes with colimits of shape `J` where `J` is any `κ`-directed preordered type.

An object `X` of a category is `κ`-presentable (`IsPresentable`)
if the functor `Hom(X, _)` (i.e. `coyoneda.obj (op X)`) is `κ`-accessible.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

section

variable (J : Type w) [Preorder J] (κ : Cardinal.{w})

/-- A preorder `J` is `κ`-directed (when `κ` is regular cardinal),
if any subset of `J` of cardinality `< κ` has an upper bound. -/
class IsCardinalDirected [Fact κ.IsRegular] : Prop where
  exists_upper_bound (S : Set J) (hS : Cardinal.mk S < κ) :
    ∃ (j : J), ∀ (s : S), s.1 ≤ j

namespace IsCardinalDirected

variable [hκ : Fact κ.IsRegular] [IsCardinalDirected J κ]

section

variable {J κ} (S : Set J) (hS : Cardinal.mk S < κ)

/-- A choice of upper bound for a subset `S : Set J`
of cardinality `< κ`, when `J` is `κ`-directed. -/
noncomputable def upperBound : J :=
  (IsCardinalDirected.exists_upper_bound S hS).choose

lemma le_upperBound (s : S) : s.1 ≤ upperBound S hS :=
  (IsCardinalDirected.exists_upper_bound S hS).choose_spec s

end

include κ in
lemma isDirected : IsDirected J (· ≤ ·) where
  directed X Y := by
    have : Cardinal.mk ({X, Y} : Set J) < κ := by
      refine lt_of_lt_of_le ?_ hκ.out.aleph0_le
      rw [Cardinal.lt_aleph0_iff_subtype_finite]
      apply Finite.Set.finite_insert
    refine ⟨upperBound _ this,
      le_upperBound _ this ⟨X, by simp⟩, le_upperBound _ this ⟨Y, by simp⟩⟩

include κ in
lemma isFiltered_of_isCardinalDirected :
    IsFiltered J := by
  have : Nonempty J := ⟨upperBound (κ := κ) (∅ : Set J) (by
    refine lt_of_lt_of_le ?_ hκ.out.aleph0_le
    simpa only [Cardinal.mk_eq_zero] using Cardinal.aleph0_pos)⟩
  have := isDirected J κ
  infer_instance

end IsCardinalDirected

end

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A functor is `κ`-accessible (with `κ` a regular cardinal)
if it preserves colimits of shape `J` where `J` is any `κ`-directed preorder. -/
class IsAccessible : Prop where
  preservesColimitOfShape {J : Type w} [Preorder J] [IsCardinalDirected J κ] :
    PreservesColimitsOfShape J F

lemma preservesColimitsOfShape_of_isAccessible [F.IsAccessible κ]
    (J : Type w) [Preorder J] [IsCardinalDirected J κ] :
    PreservesColimitsOfShape J F :=
  IsAccessible.preservesColimitOfShape κ

end Functor

variable (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- An object `X` in a category is `κ`-presentable (for `κ` a regular cardinal)
when the functor `Hom(X, _)` preserves colimits indexed by
`κ`-directed preordered sets. -/
abbrev IsPresentable : Prop := (coyoneda.obj (op X)).IsAccessible κ

lemma preservesColimitsOfShape_of_isPresentable [IsPresentable X κ]
    (J : Type w) [Preorder J] [IsCardinalDirected J κ] :
    PreservesColimitsOfShape J (coyoneda.obj (op X)) :=
  (coyoneda.obj (op X)).preservesColimitsOfShape_of_isAccessible κ J

end CategoryTheory
