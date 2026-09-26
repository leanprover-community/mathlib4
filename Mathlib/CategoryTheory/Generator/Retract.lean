/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# Separators and retracts
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- Separators are invariant under isomorphism. -/
lemma isSeparator_of_iso {C : Type*} [Category C]
    {G H : C} (e : G ≅ H) (hG : IsSeparator G) :
    IsSeparator H := by
  rw [isSeparator_def] at hG ⊢
  exact fun _ _ f g hH ↦ hG f g fun k ↦ by simpa using e.hom ≫= hH (e.inv ≫ k)

/-- If a jointly separating family consists of retracts of `G`, then `G` is a separator. -/
lemma isSeparator_of_retracts_of_hom_ext {C : Type*} [Category C] {I : Type*} (F : I → C) (G : C)
    (hjoint : ∀ {X Y : C} (f g : X ⟶ Y), (∀ i (k : F i ⟶ X), k ≫ f = k ≫ g) → f = g)
    (r : ∀ i, Retract (F i) G) : IsSeparator G := by
  rw [isSeparator_def]
  exact fun _ _ f g hG ↦ hjoint f g fun i k ↦ by simpa using (r i).i ≫= hG ((r i).r ≫ k)

end CategoryTheory
