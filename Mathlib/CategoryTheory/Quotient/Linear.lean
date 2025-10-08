/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# The quotient category is linear

If `r : HomRel C` is a congruence on a preadditive category `C` which satisfies certain
compatibilities, we have already defined a preadditive structure on `Quotient r` in
the file `CategoryTheory.Quotient.Preadditive` such that `functor r : C ⥤ Quotient r` is
an additive functor. In this file, assuming moreover that `C` is a `R`-linear category
and that the relation `r` is compatible with the scalar multiplication by any `a : R`, we
show that `Quotient r` is a `R`-linear category and that `functor r : C ⥤ Quotient r`
is a `R`-linear functor.

-/

namespace CategoryTheory

namespace Quotient

variable {R C : Type*} [Semiring R] [Category C] [Preadditive C] [Linear R C]
  (r : HomRel C) [Congruence r]

namespace Linear

/-- The scalar multiplications on morphisms in `Quotient R`. -/
def smul (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (X Y : Quotient r) : SMul R (X ⟶ Y) where
  smul a := Quot.lift (fun g => Quot.mk _ (a • g)) (fun f₁ f₂ h₁₂ => by
    dsimp
    simp only [compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [compClosure_eq_self]
    exact hr _ _ _ h₁₂)

@[simp]
lemma smul_eq (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    (a : R) {X Y : C} (f : X ⟶ Y) :
    letI := smul r hr
    a • (functor r).map f = (functor r).map (a • f) := rfl


/-- Auxiliary definition for `Quotient.Linear.module`. -/
def module' (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] (X Y : C) :
    Module R ((functor r).obj X ⟶ (functor r).obj Y) :=
  letI smul := smul r hr ((functor r).obj X) ((functor r).obj Y)
  { smul_zero := fun a => by
      rw [← (functor r).map_zero X Y, smul_eq, smul_zero]
    zero_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [zero_smul, Functor.map_zero]
    one_smul := fun f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [one_smul]
    mul_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [mul_smul]
    smul_add := fun a f g => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      obtain ⟨g, rfl⟩ := (functor r).map_surjective g
      dsimp [smul]
      rw [← (functor r).map_add, smul_eq, ← (functor r).map_add, smul_add]
    add_smul := fun a b f => by
      obtain ⟨f, rfl⟩ := (functor r).map_surjective f
      dsimp [smul]
      rw [add_smul, Functor.map_add] }

/-- Auxiliary definition for `Quotient.linear`. -/
def module (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] (X Y : Quotient r) :
    Module R (X ⟶ Y) := module' r hr X.as Y.as

end Linear

variable (R)

/-- Assuming `Quotient r` has already been endowed with a preadditive category structure
such that `functor r : C ⥤ Quotient r` is additive, and that `C` has a `R`-linear category
structure compatible with `r`, this is the induced `R`-linear category structure on
`Quotient r`. -/
def linear (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] : Linear R (Quotient r) := by
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

instance linear_functor
    (hr : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂))
    [Preadditive (Quotient r)] [(functor r).Additive] :
    letI := linear R r hr; Functor.Linear R (functor r) := by
  letI := linear R r hr; exact { }

end Quotient

end CategoryTheory
