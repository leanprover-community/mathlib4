import Mathlib.CategoryTheory.Quotient.Preadditive
import Mathlib.CategoryTheory.Linear.LinearFunctor

namespace CategoryTheory

namespace Quotient

variable {R : Type _} [Ring R] {C : Type _} [Category C] [Preadditive C] [Linear R C]
  (r : HomRel C) [Congruence r]
  (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))

def Linear.smul (X Y : Quotient r) : SMul R (X ⟶ Y) where
  smul a := Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    dsimp
    simp only [compClosure_eq_self] at h₁₂
    erw [functor_map_eq_iff]
    exact hr _ _ _ h₁₂)

lemma Linear.smul_eq (a : R) {X Y : C} (f : X ⟶ Y) :
    letI := smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl

variable [Preadditive (Quotient r)] [(functor r).Additive]

namespace Linear

def module (X Y : Quotient r) : Module R (X ⟶ Y) := by
  letI := smul r hr
  exact
    { one_smul := fun f => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        rw [smul_eq, one_smul, functor_map]
      smul_zero := fun a => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        rw [← (functor r).map_zero X Y, smul_eq, smul_zero]
      zero_smul := fun f => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        rw [smul_eq, zero_smul, Functor.map_zero]
      smul_add := fun a f g => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [← (functor r).map_add, smul_eq, smul_eq, smul_eq, ← (functor r).map_add, smul_add]
      add_smul := fun a b f => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        rw [smul_eq, smul_eq, smul_eq, ← (functor r).map_add, add_smul]
      mul_smul := fun a b f => by
        obtain ⟨X⟩ := X
        obtain ⟨Y⟩ := Y
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        rw [smul_eq, smul_eq, smul_eq, mul_smul] }

end Linear

variable (R)

def linear : Linear R (Quotient r) := by
  letI := Linear.module r hr
  exact
    { smul_comp := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq, ← Functor.map_comp, ← Functor.map_comp,
          Linear.smul_eq, Linear.smul_comp]
      comp_smul := by
        rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f a g
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        obtain ⟨g, rfl⟩ := (functor r).map_surjective g
        rw [Linear.smul_eq, ← Functor.map_comp, ← Functor.map_comp,
          Linear.smul_eq, Linear.comp_smul] }

lemma linear_functor :
    letI := linear R r hr
    Functor.Linear R (functor r) := by
  letI := linear R r hr
  exact
    { map_smul := fun {X Y} f a => by rw [Linear.smul_eq] }

end Quotient

end CategoryTheory
