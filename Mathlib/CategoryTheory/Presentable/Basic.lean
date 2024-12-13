/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Data.Set.Finite.Basic

/-! # Presentable objects

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

section

variable (J : Type w) [Preorder J]
  (κ : Cardinal.{w})

class IsCardinalDirected [Fact κ.IsRegular] : Prop where
  exists_upper_bound (S : Set J) (hS : Cardinal.mk S < κ) :
    ∃ (j : J), ∀ (s : S), s.1 ≤ j

namespace IsCardinalDirected

variable [hκ : Fact κ.IsRegular] [IsCardinalDirected J κ]

section

variable {J κ} (S : Set J) (hS : Cardinal.mk S < κ)

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

variable {C : Type u} [Category.{v} C]

def coyonedaColimitComparison (X : C) {J : Type u'} [Category.{v'} J] {F : J ⥤ C}
    (c : Cocone F) :
    Types.Quot (F ⋙ coyoneda.obj (op X)) → (X ⟶ c.pt) :=
  Quot.lift (fun ⟨j, f⟩ ↦ f ≫ c.ι.app j) (by
    rintro ⟨j, f⟩ ⟨j', f'⟩ ⟨g, fac⟩
    dsimp at f f' g fac
    subst fac
    simp)

variable (X : C) (κ : Cardinal.{w}) [Fact κ.IsRegular]

class IsPresentable : Prop where
  commutes {J : Type w} [Preorder J] [IsCardinalDirected J κ]
    {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c) :
    Function.Bijective (coyonedaColimitComparison X c)

end CategoryTheory
