module
import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.Tactic.CategoryTheory.Coherence

open CategoryTheory

universe w v u

set_option warn.refl_coherence false

section Monoidal
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
open scoped MonoidalCategory

-- Internal tactics

theorem t (X₁ X₂ : C) :
    ((λ_ (𝟙_ C)).inv ⊗ₘ 𝟙 (X₁ ⊗ X₂)) ≫ (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
      (𝟙 (𝟙_ C) ⊗ₘ (α_ (𝟙_ C) X₁ X₂).inv) =
    𝟙 (𝟙_ C) ⊗ₘ ((λ_ X₁).inv ⊗ₘ 𝟙 X₂) := by
  pure_coherence
  -- This is just running:
  -- change projectMap id _ _ (LiftHom.lift (((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫
  --     (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫ (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv))) =
  --   projectMap id _ _ (LiftHom.lift (𝟙 (𝟙_ C) ⊗ ((λ_ X₁).inv ⊗ 𝟙 X₂)))
  -- exact congrArg _ (Subsingleton.elim _ _)

example {Y Z : C} (f : Y ⟶ Z) (g) (w : false) : (λ_ _).hom ≫ f = g := by
  liftable_prefixes
  guard_target = (𝟙 _ ≫ (λ_ _).hom) ≫ f = (𝟙 _) ≫ g
  cases w

-- `coherence`

example (f : 𝟙_ C ⟶ _) : f ≫ (λ_ (𝟙_ C)).hom = f ≫ (ρ_ (𝟙_ C)).hom := by
  coherence

example (f) : (λ_ (𝟙_ C)).hom ≫ f ≫ (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ f ≫ (ρ_ (𝟙_ C)).hom := by
  coherence

example {U : C} (f : U ⟶ 𝟙_ C) : f ≫ (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom = f := by
  coherence

example (W X Y Z : C) (f) :
    ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ₘ (α_ X Y Z).hom) ≫ f ≫
      (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom =
    (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom ≫ f ≫
      ((α_ W X Y).hom ⊗ₘ 𝟙 Z) ≫ (α_ W (X ⊗ Y) Z).hom ≫ (𝟙 W ⊗ₘ (α_ X Y Z).hom) := by
  coherence

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
    f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g := by
  coherence

example : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by coherence
example : (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by coherence
example (X Y Z : C) : (α_ X Y Z).inv ≫ (α_ X Y Z).hom = 𝟙 (X ⊗ Y ⊗ Z) := by coherence
example (X Y Z W : C) :
  (𝟙 X ⊗ₘ (α_ Y Z W).hom) ≫ (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv =
    (α_ X (Y ⊗ Z) W).inv ≫ ((α_ X Y Z).inv ⊗ₘ 𝟙 W) := by
  coherence
example (X Y : C) :
  (𝟙 X ⊗ₘ (λ_ Y).inv) ≫ (α_ X (𝟙_ C) Y).inv = (ρ_ X).inv ⊗ₘ 𝟙 Y := by
  coherence
example (X Y : C) (f : 𝟙_ C ⟶ X) (g : X ⟶ Y) (_w : false) :
  (λ_ (𝟙_ C)).hom ≫ f ≫ 𝟙 X ≫ g = (ρ_ (𝟙_ C)).hom ≫ f ≫ g := by
  coherence

example (X₁ X₂ : C) :
  (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
    (𝟙 (𝟙_ C) ⊗ₘ (α_ (𝟙_ C) X₁ X₂).inv) ≫
      (𝟙 (𝟙_ C) ⊗ₘ (λ_ _).hom ≫ (ρ_ X₁).inv ⊗ₘ 𝟙 X₂) ≫
        (𝟙 (𝟙_ C) ⊗ₘ (α_ X₁ (𝟙_ C) X₂).hom) ≫
          (α_ (𝟙_ C) X₁ (𝟙_ C ⊗ X₂)).inv ≫
            ((λ_ X₁).hom ≫ (ρ_ X₁).inv ⊗ₘ 𝟙 (𝟙_ C ⊗ X₂)) ≫
              (α_ X₁ (𝟙_ C) (𝟙_ C ⊗ X₂)).hom ≫
                (𝟙 X₁ ⊗ₘ 𝟙 (𝟙_ C) ⊗ₘ (λ_ X₂).hom ≫ (ρ_ X₂).inv) ≫
                  (𝟙 X₁ ⊗ₘ (α_ (𝟙_ C) X₂ (𝟙_ C)).inv) ≫
                    (𝟙 X₁ ⊗ₘ (λ_ X₂).hom ≫ (ρ_ X₂).inv ⊗ₘ 𝟙 (𝟙_ C)) ≫
                      (𝟙 X₁ ⊗ₘ (α_ X₂ (𝟙_ C) (𝟙_ C)).hom) ≫
                        (α_ X₁ X₂ (𝟙_ C ⊗ 𝟙_ C)).inv =
  (((λ_ (𝟙_ C)).hom ⊗ₘ 𝟙 (X₁ ⊗ X₂)) ≫ (λ_ (X₁ ⊗ X₂)).hom ≫ (ρ_ (X₁ ⊗ X₂)).inv) ≫
    (𝟙 (X₁ ⊗ X₂) ⊗ₘ (λ_ (𝟙_ C)).inv) := by
  coherence

end Monoidal

section Bicategory

open scoped Bicategory


variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

example {a : B} (f : a ⟶ a) : 𝟙 f ▷ f = 𝟙 (f ≫ f) := by whisker_simps

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by pure_coherence
example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by pure_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).inv ≫ (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) := by
  pure_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  pure_coherence
example (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g := by
  pure_coherence
theorem s : 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (λ_ (𝟙 a)).hom = 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (ρ_ (𝟙 a)).hom := by
  pure_coherence

set_option linter.unusedVariables false in
example (f g : a ⟶ a) (η : 𝟙 a ⟶ f) (θ : f ⟶ g) (w : false) :
  (λ_ (𝟙 a)).hom ≫ η ≫ θ = (ρ_ (𝟙 a)).hom ≫ η ≫ θ := by
  coherence

example (f₁ : a ⟶ b) (f₂ : b ⟶ c) :
  (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
    𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv ≫
      𝟙 a ◁ ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ f₂ ≫
        𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom ≫
          (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
            ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ (𝟙 b ≫ f₂) ≫
              (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                  f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv ≫
                    f₁ ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ▷ 𝟙 c ≫
                      (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
                        (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
  ((λ_ (𝟙 a)).hom ▷ (f₁ ≫ f₂) ≫ (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv) ≫
    (f₁ ≫ f₂) ◁ (λ_ (𝟙 c)).inv := by
  pure_coherence

end Bicategory
