/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Quotient.Linear
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The quotient category is monoidal

If `r : HomRel C` is a congruence on a monoidal category `C` which satisfies certain
compatibilities with left and right whiskering, then the quotient category
`Quotient r` is also monoidal.

-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

namespace Quotient

variable {C : Type*} [Category* C] [MonoidalCategory C] (r : HomRel C) [Congruence r]

namespace Monoidal

/-- The left whiskering on morphisms in `Quotient r` when `r` is compatible with left
whiskering. -/
def whiskerLeft
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (W : C) {X Y : Quotient r} (f : X ⟶ Y) :
    (⟨W ⊗ X.as⟩ : Quotient r) ⟶ ⟨W ⊗ Y.as⟩ :=
  Quot.liftOn f (fun g ↦ Quot.mk _ (W ◁ g)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hl W _ _ h₁₂)

/-- The right whiskering on morphisms in `Quotient r` when `r` is compatible with right
whiskering. -/
def whiskerRight
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (W : C) {X Y : Quotient r} (f : X ⟶ Y) :
    (⟨X.as ⊗ W⟩ : Quotient r) ⟶ ⟨Y.as ⊗ W⟩ :=
  Quot.liftOn f (fun g ↦ Quot.mk _ (g ▷ W)) (fun f₁ f₂ h₁₂ => by
    simp only [HomRel.compClosure_eq_self] at h₁₂
    apply Quot.sound
    rw [HomRel.compClosure_eq_self]
    exact hr W _ _ h₁₂)

/-- The tensor product on morphisms in `Quotient r` when `r` is compatible with left and
right whiskering. -/
def tensorHom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    {X₁ Y₁ X₂ Y₂ : Quotient r} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (⟨X₁.as ⊗ X₂.as⟩ : Quotient r) ⟶ ⟨Y₁.as ⊗ Y₂.as⟩ :=
  Quot.liftOn₂ f g (fun f g => Quot.mk _ (f ⊗ₘ g))
    (fun f g₁ g₂ h₁₂ ↦ by
      simp only [HomRel.compClosure_eq_self] at h₁₂
      apply Quot.sound
      rw [HomRel.compClosure_eq_self, tensorHom_def, tensorHom_def]
      exact HomRel.comp_left (f ▷ X₂.as) (hl Y₁.as _ _ h₁₂))
    (fun f₁ f₂ g h₁₂ ↦ by
      simp only [HomRel.compClosure_eq_self] at h₁₂
      apply Quot.sound
      rw [HomRel.compClosure_eq_self, tensorHom_def, tensorHom_def]
      exact HomRel.comp_right (Y₁.as ◁ g) (hr X₂.as _ _ h₁₂))

end Monoidal

/-- The monoidal category structure on `Quotient r` induced by a monoidal category structure
on `C`. -/
@[implicit_reducible]
def monoidalCategoryStruct
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    MonoidalCategoryStruct (Quotient r) where
  tensorObj X Y := ⟨X.as ⊗ Y.as⟩
  whiskerLeft X _ _ f := Monoidal.whiskerLeft r hl X.as f
  whiskerRight f X := Monoidal.whiskerRight r hr X.as f
  tensorHom f g := Monoidal.tensorHom r hl hr f g
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := (functor r).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (functor r).mapIso (λ_ X.as)
  rightUnitor X := (functor r).mapIso (ρ_ X.as)

/-- The monoidal category structure on `Quotient r` induced by a monoidal category structure
on `C`. -/
@[implicit_reducible]
def monoidalCategory
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    MonoidalCategory (Quotient r) := by
  letI := monoidalCategoryStruct r hl hr
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun ⟨_⟩ ⟨_⟩ ↦ congr_arg (functor r).map (id_tensorHom_id _ _))
    (id_tensorHom := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩; exact congr_arg (functor r).map (id_tensorHom _ _))
    (tensorHom_id := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩; exact congr_arg (functor r).map (tensorHom_id _ _))
    (tensorHom_comp_tensorHom := by
      rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (tensorHom_comp_tensorHom _ _ _ _))
    (associator_naturality := by
      rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (associator_naturality _ _ _))
    (leftUnitor_naturality := by
      rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (by
        rw [MonoidalCategory.id_tensorHom]
        exact leftUnitor_naturality _))
    (rightUnitor_naturality := by
      rintro ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (by
        rw [MonoidalCategory.tensorHom_id]
        exact rightUnitor_naturality _))
    (pentagon := by
      rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (by
        rw [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
        exact pentagon _ _ _ _))
    (triangle := by
      rintro ⟨_⟩ ⟨_⟩
      exact congr_arg (functor r).map (by
        rw [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id]
        exact triangle _ _))

@[simp]
lemma functor_map_whiskerLeft
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (W : C) {X Y : C} (f : X ⟶ Y) :
    letI := monoidalCategory r hl hr
    (functor r).obj W ◁ (functor r).map f = (functor r).map (W ◁ f) := rfl

@[simp]
lemma functor_map_whiskerRight
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (W : C) {X Y : C} (f : X ⟶ Y) :
    letI := monoidalCategory r hl hr
    (functor r).map f ▷ (functor r).obj W = (functor r).map (f ▷ W) := rfl

@[simp]
lemma functor_map_tensorHom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    letI := monoidalCategory r hl hr
    (functor r).map f ⊗ₘ (functor r).map g = (functor r).map (f ⊗ₘ g) := rfl

@[simp]
lemma functor_map_associator_hom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (X Y Z : C) :
    letI := monoidalCategory r hl hr
    (α_ ((functor r).obj X) ((functor r).obj Y) ((functor r).obj Z)).hom =
      (functor r).map (α_ X Y Z).hom := rfl

@[simp]
lemma functor_map_leftUnitor_hom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (X : C) :
    letI := monoidalCategory r hl hr
    (λ_ ((functor r).obj X)).hom = (functor r).map (λ_ X).hom := rfl

@[simp]
lemma functor_map_rightUnitor_hom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (X : C) :
    letI := monoidalCategory r hl hr
    (ρ_ ((functor r).obj X)).hom = (functor r).map (ρ_ X).hom := rfl

instance functor_monoidal
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    letI := monoidalCategory r hl hr
    (functor r).Monoidal :=
  letI := monoidalCategory r hl hr
  Functor.CoreMonoidal.toMonoidal (F := functor r)
  { εIso :=
      { hom := (functor r).map (𝟙 _)
        inv := (functor r).map (𝟙 _)
        hom_inv_id := by simp [functor]; rfl
        inv_hom_id := by simp [functor] }
    μIso := fun X Y =>
      { hom := (functor r).map (𝟙 _)
        inv := (functor r).map (𝟙 _)
        hom_inv_id := by simp [functor]; rfl
        inv_hom_id := by simp [functor] }
    μIso_hom_natural_left {X Y} f X' := by
      change (functor r).map ((f ▷ X') ≫ 𝟙 _) = (functor r).map (𝟙 _ ≫ (f ▷ X'))
      simp
    μIso_hom_natural_right {X Y} X' f := by
      change (functor r).map ((X' ◁ f) ≫ 𝟙 _) = (functor r).map (𝟙 _ ≫ (X' ◁ f))
      simp
    associativity X Y Z := by
      change (functor r).map ((𝟙 _ ▷ Z) ≫ 𝟙 _ ≫ (α_ X Y Z).hom) =
        (functor r).map ((α_ X Y Z).hom ≫ X ◁ 𝟙 _ ≫ 𝟙 _)
      simp
    left_unitality X := by
      change (functor r).map (λ_ X).hom = (functor r).map ((𝟙 _ ▷ X) ≫ 𝟙 _ ≫ (λ_ X).hom)
      simp
    right_unitality X := by
      change (functor r).map (ρ_ X).hom = (functor r).map ((X ◁ _) ≫ 𝟙 _ ≫ (ρ_ X).hom)
      simp }

section Braided

variable [BraidedCategory C]

/-- The braided category structure on `Quotient r` induced by a braided category
structure on `C`. -/
@[implicit_reducible]
def braidedCategory
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    letI := monoidalCategory r hl hr
    BraidedCategory (Quotient r) := by
  letI := monoidalCategory r hl hr
  exact
    { braiding := fun X Y => (functor r).mapIso (β_ X.as Y.as)
      braiding_naturality_right _ _ _ f := by
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        exact congr_arg (functor r).map (BraidedCategory.braiding_naturality_right _ f)
      braiding_naturality_left f _ := by
        obtain ⟨f, rfl⟩ := (functor r).map_surjective f
        exact congr_arg (functor r).map (BraidedCategory.braiding_naturality_left f _)
      hexagon_forward _ _ _ := congr_arg (functor r).map (BraidedCategory.hexagon_forward _ _ _)
      hexagon_reverse _ _ _ := congr_arg (functor r).map (BraidedCategory.hexagon_reverse _ _ _) }

@[simp]
lemma functor_map_braiding_hom
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (X Y : C) :
    letI := monoidalCategory r hl hr
    letI := braidedCategory r hl hr
    (β_ ((functor r).obj X) ((functor r).obj Y)).hom = (functor r).map (β_ X Y).hom := rfl

@[simp]
lemma functor_map_braiding_inv
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (X Y : C) :
    letI := monoidalCategory r hl hr
    letI := braidedCategory r hl hr
    (β_ ((functor r).obj X) ((functor r).obj Y)).inv = (functor r).map (β_ X Y).inv := rfl

instance functor_braided
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    letI := monoidalCategory r hl hr
    letI := braidedCategory r hl hr
    (functor r).Braided := by
  letI := monoidalCategory r hl hr
  letI := braidedCategory r hl hr
  letI := functor_monoidal r hl hr
  constructor
  intro _ _
  change (functor r).map (𝟙 _ ≫ (β_ _ _).hom) = (functor r).map ((β_ _ _).hom ≫ 𝟙 _)
  simp

end Braided

section Symmetric

variable [SymmetricCategory C]

/-- The symmetric category structure on `Quotient r` induced by a symmetric category
structure on `C`. -/
@[implicit_reducible]
def symmetricCategory
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W)) :
    letI := monoidalCategory r hl hr
    letI := braidedCategory r hl hr
    SymmetricCategory (Quotient r) := by
  letI := monoidalCategory r hl hr
  letI := braidedCategory r hl hr
  constructor
  intro _ _
  exact congr_arg (functor r).map (SymmetricCategory.symmetry _ _)

end Symmetric

variable [Preadditive C] [MonoidalPreadditive C]

/-- The monoidal preadditive structure on `Quotient r` induced by preadditive and monoidal
structures on `C`. -/
theorem monoidalPreadditive
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (hadd : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂)) :
    letI := preadditive r hadd
    letI := monoidalCategory r hl hr
    MonoidalPreadditive (Quotient r) := by
  letI := preadditive r hadd
  letI := monoidalCategory r hl hr
  constructor
  · intro
    exact congr_arg (functor r).map MonoidalPreadditive.whiskerLeft_zero
  · intro
    exact congr_arg (functor r).map MonoidalPreadditive.zero_whiskerRight
  · intro _ _ _ f g
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    obtain ⟨g, rfl⟩ := (functor r).map_surjective g
    exact congr_arg (functor r).map (MonoidalPreadditive.whiskerLeft_add f g)
  · intro _ _ _ f g
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    obtain ⟨g, rfl⟩ := (functor r).map_surjective g
    exact congr_arg (functor r).map (MonoidalPreadditive.add_whiskerRight f g)

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

/-- The monoidal linear structure on `Quotient r` induced by linear and monoidal structures
on `C`. -/
theorem monoidalLinear
    (hl : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (W ◁ f₁) (W ◁ f₂))
    (hr : ∀ (W : C) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (f₁ ▷ W) (f₂ ▷ W))
    (hadd : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
    (hsmul : ∀ (a : R) ⦃X Y : C⦄ (f₁ f₂ : X ⟶ Y) (_ : r f₁ f₂), r (a • f₁) (a • f₂)) :
    letI := preadditive r hadd
    letI := functor_additive r hadd
    letI := monoidalCategory r hl hr
    letI := linear R r hsmul
    letI := monoidalPreadditive r hl hr hadd
    MonoidalLinear R (Quotient r) := by
  letI := preadditive r hadd
  letI := functor_additive r hadd
  letI := monoidalCategory r hl hr
  letI := linear R r hsmul
  letI := monoidalPreadditive r hl hr hadd
  constructor
  · intro _ _ _ _ f
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congr_arg (functor r).map (MonoidalLinear.whiskerLeft_smul _ _ f)
  · intro _ _ _ f _
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congr_arg (functor r).map (MonoidalLinear.smul_whiskerRight _ f _)

end Quotient

end CategoryTheory
