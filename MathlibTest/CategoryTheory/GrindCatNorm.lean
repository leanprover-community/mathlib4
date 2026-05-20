import Mathlib.CategoryTheory.Tactic.GrindCatNorm

/-!
# Regression tests for the `grind` category-composition normalizer

The propagator pushes the equality `f ≫ g = (right-associated, identity-free
form)` into grind's e-graph for each composition it sees. With the
permanent `@[grind]` attributes on `Category.assoc` / `id_comp` /
`comp_id` removed, these examples are not solvable by `grind` via
e-matching alone; they only close because the propagator is loaded.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section AssociativityOnly

example {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by grind

example {X Y Z W V : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) :
    ((f ≫ g) ≫ h) ≫ k = f ≫ g ≫ h ≫ k := by grind

example {X Y Z W V : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (k : W ⟶ V) :
    (f ≫ g) ≫ (h ≫ k) = f ≫ (g ≫ h) ≫ k := by grind

example {X₁ X₂ X₃ X₄ X₅ X₆ : C}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) (f₅ : X₅ ⟶ X₆) :
    ((f₁ ≫ f₂) ≫ f₃) ≫ (f₄ ≫ f₅) = f₁ ≫ (f₂ ≫ f₃ ≫ f₄) ≫ f₅ := by grind

end AssociativityOnly

section IdentityRemoval

example {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by grind
example {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by grind
example {X : C} : 𝟙 X ≫ 𝟙 X = 𝟙 X := by grind

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ 𝟙 Y ≫ g = f ≫ g := by grind

example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝟙 X ≫ f) ≫ (g ≫ 𝟙 Z) = f ≫ g := by grind

end IdentityRemoval

section Mixed

example {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    (𝟙 X ≫ (f ≫ g)) ≫ h ≫ 𝟙 W = f ≫ g ≫ h := by grind

example {X₁ X₂ X₃ X₄ X₅ : C}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅) :
    𝟙 X₁ ≫ ((f₁ ≫ 𝟙 X₂) ≫ f₂) ≫ (𝟙 X₃ ≫ f₃ ≫ 𝟙 X₄) ≫ f₄ ≫ 𝟙 X₅ =
      f₁ ≫ f₂ ≫ f₃ ≫ f₄ := by grind

end Mixed

section WithHypotheses

/-- Composition with a hypothesis that needs to flow through the normalizer. -/
example {X Y Z W : C} (f₁ f₂ : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (hfg : f₁ ≫ g = f₂ ≫ g) :
    (f₁ ≫ g) ≫ h = (f₂ ≫ g) ≫ h := by grind

end WithHypotheses

section ReducibleAliases

/-- A reducible alias for the morphism type, even with object arguments
swapped, should still be handled. The propagator reduces the inferred
type until it hits `Quiver.Hom` and extracts the endpoints from there. -/
private def MorAlias (Y X : C) := X ⟶ Y

example {X Y Z W : C} (f : MorAlias Y X) (g : MorAlias Z Y) (h : MorAlias W Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by grind

end ReducibleAliases

section LongChain

-- Performance guard: a 10-morphism left-associated chain should
-- normalize in well under the default heart-beat budget. If this starts
-- failing, the normalizer's per-prefix work has likely regressed.
set_option maxHeartbeats 200000 in
example {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ : C}
    (f₁ : X₀ ⟶ X₁) (f₂ : X₁ ⟶ X₂) (f₃ : X₂ ⟶ X₃) (f₄ : X₃ ⟶ X₄) (f₅ : X₄ ⟶ X₅)
    (f₆ : X₅ ⟶ X₆) (f₇ : X₆ ⟶ X₇) (f₈ : X₇ ⟶ X₈) (f₉ : X₈ ⟶ X₉) (f₁₀ : X₉ ⟶ X₁₀) :
    ((((((((f₁ ≫ f₂) ≫ f₃) ≫ f₄) ≫ f₅) ≫ f₆) ≫ f₇) ≫ f₈) ≫ f₉) ≫ f₁₀ =
      f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ ≫ f₇ ≫ f₈ ≫ f₉ ≫ f₁₀ := by grind

end LongChain
