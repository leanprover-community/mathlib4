/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of morphisms that are bounded by a cardinal

Given `P : MorphismProperty C` and `κ : Cardinal`, we introduce a predicate
`P.HasCardinalLT κ` saying that the cardinality of `P.toSet` is `< κ`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

/-- The property that the subtype of arrows satisfying a property `P : MorphismProperty C`
is of cardinality `< κ`. -/
protected abbrev HasCardinalLT (P : MorphismProperty C) (κ : Cardinal.{w}) :=
    _root_.HasCardinalLT P.toSet κ

lemma hasCardinalLT_ofHoms {C : Type*} [Category* C]
    {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {κ : Cardinal}
    (h : HasCardinalLT ι κ) : (MorphismProperty.ofHoms f).HasCardinalLT κ :=
  h.of_surjective (fun i ↦ ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff, MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)

lemma HasCardinalLT.iSup
    {ι : Type*} {P : ι → MorphismProperty C} {κ : Cardinal.{w}} [Fact κ.IsRegular]
    (hP : ∀ i, (P i).HasCardinalLT κ) (hι : HasCardinalLT ι κ) :
    (⨆ i, P i).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [toSet_iSup]
  exact hasCardinalLT_iUnion _ hι hP

lemma HasCardinalLT.sup
    {P₁ P₂ : MorphismProperty C} {κ : Cardinal.{w}}
    (h₁ : P₁.HasCardinalLT κ) (h₂ : P₂.HasCardinalLT κ)
    (hκ : Cardinal.aleph0 ≤ κ) :
    (P₁ ⊔ P₂).HasCardinalLT κ := by
  dsimp only [MorphismProperty.HasCardinalLT]
  rw [MorphismProperty.toSet_max]
  exact hasCardinalLT_union hκ h₁ h₂

end MorphismProperty

end CategoryTheory
