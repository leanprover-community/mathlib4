import Mathlib.CategoryTheory.FiberedCategory.HomLift

universe u₁ v₁ u₂ v₂

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)


/-- Testing simple substitution -/
example {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : f = f := by
  subst_hom_lift p f φ
  rename_i h
  guard_hyp h : p.IsHomLift (p.map φ) φ
  guard_target = p.map φ = p.map φ
  trivial

/-- Test substitution with more complicated expression -/
example {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b) (ψ : b ⟶ c)
    [p.IsHomLift f (φ ≫ ψ)] : f = f := by
  subst_hom_lift p f (φ ≫ ψ)
  rename_i h
  guard_hyp h : p.IsHomLift (p.map (φ ≫ ψ)) (φ ≫ ψ)
  guard_target = p.map (φ ≫ ψ) = p.map (φ ≫ ψ)
  trivial
