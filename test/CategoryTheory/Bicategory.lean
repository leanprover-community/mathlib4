import Mathlib.Tactic.CategoryTheory.Bicategory.Normalize

open CategoryTheory Mathlib.Tactic BicategoryLike
open Bicategory

section

universe w v u

/-- `normalize% η` is the normalization of the 2-morphism `η`.
1. The normalized 2-morphism is of the form `α₀ ≫ η₀ ≫ α₁ ≫ η₁ ≫ ... αₘ ≫ ηₘ ≫ αₘ₊₁` where
  each `αᵢ` is a structural 2-morphism (consisting of associators and unitors),
2. each `ηᵢ` is a non-structural 2-morphism of the form `f₁ ◁ ... ◁ fₘ ◁ θ`, and
3. `θ` is of the form `ι ▷ g₁ ▷ ... ▷ gₗ`
-/
elab "normalize% " t:term:51 : term => do
  let e ← Lean.Elab.Term.elabTerm t none
  let ctx : Bicategory.Context ← mkContext e
  CoherenceM.run ctx do
    return (← BicategoryLike.eval `bicategory (← MkMor₂.ofExpr e)).expr.e


variable {B : Type u} [Bicategory.{w, v} B]

variable {a b c d e : B}

variable {f : a ⟶ b} {g : b ⟶ c} in
#guard_expr normalize% f ◁ 𝟙 g = (whiskerLeftIso f (Iso.refl g)).hom
variable {f : a ⟶ b} {g : b ⟶ c} in
#guard_expr normalize% 𝟙 f ▷ g = (whiskerRightIso (Iso.refl f) g).hom
variable {f : a ⟶ b} {g h i : b ⟶ c} {η : g ⟶ h} {θ : h ⟶ i} in
#guard_expr normalize% f ◁ (η ≫ θ) = _ ≫ f ◁ η ≫ _ ≫ f ◁ θ ≫ _
variable {f g h : a ⟶ b} {i : b ⟶ c} {η : f ⟶ g} {θ : g ⟶ h} in
#guard_expr normalize% (η ≫ θ) ▷ i = _ ≫ η ▷ i ≫ _ ≫ θ ▷ i ≫ _
variable {η : 𝟙 a ⟶ 𝟙 a} in
#guard_expr normalize% 𝟙 a ◁ η = _ ≫ η ≫ _
variable {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} {η : h ⟶ i} in
#guard_expr normalize% (f ≫ g) ◁ η = _ ≫ f ◁ g ◁ η ≫ _
variable {η : 𝟙 a ⟶ 𝟙 a} in
#guard_expr normalize% η ▷ 𝟙 a = _ ≫ η ≫ _
variable {f g : a ⟶ b} {h : b ⟶ c} {i : c ⟶ d} {η : f ⟶ g} in
#guard_expr normalize% η ▷ (h ≫ i) = _ ≫ η ▷ h ▷ i ≫ _
variable {f : a ⟶ b} {g h : b ⟶ c} {i : c ⟶ d} {η : g ⟶ h} in
#guard_expr normalize% (f ◁ η) ▷ i = _ ≫ f ◁ η ▷ i ≫ _
variable {f : a ⟶ b} in
#guard_expr normalize% (λ_ f).hom = (λ_ f).hom
variable {f : a ⟶ b} in
#guard_expr normalize% (λ_ f).inv = ((λ_ f).symm).hom
variable {f : a ⟶ b} in
#guard_expr normalize% (ρ_ f).hom = (ρ_ f).hom
variable {f : a ⟶ b} in
#guard_expr normalize% (ρ_ f).inv = ((ρ_ f).symm).hom
variable {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} in
#guard_expr normalize% (α_ f g h).hom = (α_ _ _ _).hom
variable {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} in
#guard_expr normalize% (α_ f g h).inv = ((α_ f g h).symm).hom
variable {f : a ⟶ b} {g : b ⟶ c} in
#guard_expr normalize% 𝟙 (f ≫ g) = (Iso.refl (f ≫ g)).hom

example {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {i j : a ⟶ d}
    (η : i ⟶ f ≫ (g ≫ h)) (θ : (f ≫ g) ≫ h ⟶ j) :
    η ⊗≫ θ = η ≫ 𝟙 _ ≫ (α_ _ _ _).inv ≫ θ := by
  bicategory

example {f : a ⟶ b} {g : b ⟶ c} {h i : c ⟶ d} (η : h ⟶ i) :
    (f ≫ g) ◁ η = (α_ _ _ _).hom ≫ f ◁ g ◁ η ≫ (α_ _ _ _).inv := by
  bicategory

example {f g h : a ⟶ b} {η : f ⟶ g} {θ : g ⟶ h} : η ≫ θ = η ≫ θ := by
  bicategory

open Mathlib.Tactic.Bicategory

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by bicategory_coherence
example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by bicategory_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).inv ≫ (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) := by
  bicategory_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (f ≫ g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  bicategory_coherence
example (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g := by
  bicategory_coherence

example : 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (λ_ (𝟙 a)).hom = 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (ρ_ (𝟙 a)).hom := by
  bicategory_coherence

set_option linter.unusedVariables false in
example (f g : a ⟶ a) (η : 𝟙 a ⟶ f) (θ : f ⟶ g) (w : false) :
  (λ_ (𝟙 a)).hom ≫ η ≫ θ = (ρ_ (𝟙 a)).hom ≫ η ≫ θ := by
  bicategory

example (f₁ : a ⟶ b) (f₂ : b ⟶ c) :
  (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
    𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv ≫
      𝟙 a ◁ ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ f₂ ⊗≫
        𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom ≫
          (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
            ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ (𝟙 b ≫ f₂) ⊗≫
              (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                  f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv ≫
                    f₁ ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ▷ 𝟙 c ≫
                      (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
                        (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
  ((λ_ (𝟙 a)).hom ▷ (f₁ ≫ f₂) ≫ (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv) ≫
    (f₁ ≫ f₂) ◁ (λ_ (𝟙 c)).inv := by
  bicategory_coherence

end
