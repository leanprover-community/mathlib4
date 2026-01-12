/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Properties of objects that are bounded by a cardinal

Given `P : ObjectProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `Subtype P` is `< κ`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

/-- The property that the subtype of objects satisfying a property `P : ObjectProperty C`
is of cardinality `< κ`. -/
protected abbrev HasCardinalLT (P : ObjectProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT (Subtype P) κ

lemma hasCardinalLT_subtype_ofObj
    {ι : Type*} (X : ι → C) {κ : Cardinal.{w}}
    (h : HasCardinalLT ι κ) : (ObjectProperty.ofObj X).HasCardinalLT κ :=
  h.of_surjective (fun i ↦ ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)

lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → ObjectProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ :=
  hasCardinalLT_subtype_iSup _ hι hP

lemma HasCardinalLT.sup
    {P₁ P₂ : ObjectProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ :=
  hasCardinalLT_union hκ h₁ h₂

end ObjectProperty

end CategoryTheory
