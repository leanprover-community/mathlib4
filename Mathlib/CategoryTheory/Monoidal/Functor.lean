/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Products.Basic

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms. This is implemented as a typeclass `F.LaxMonoidal`.

Similarly, we define the typeclass `F.OplaxMonoidal`. For these oplax monoidal functors,
we have similar data `η` and `δ`, but with morphisms in the opposite direction.

A monoidal functor (`F.Monoidal`) is defined here as the combination of `F.LaxMonoidal`
and `F.OplaxMonoidal`, with the additional conditions that `ε`/`η` and `μ`/`δ` are
inverse isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean` for monoidal natural
transformations.

We show in `Mathlib.CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/

@[expose] public section


universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

namespace CategoryTheory

open Category Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']

namespace Functor

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A functor `F : C ⥤ D` between monoidal categories is lax monoidal if it is
equipped with morphisms `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences. -/
@[ext]
class LaxMonoidal (F : C ⥤ D) where
  /-- the unit morphism of a lax monoidal functor -/
  ε (F) : 𝟙_ D ⟶ F.obj (𝟙_ C)
  /-- the tensorator of a lax monoidal functor -/
  μ (F) : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)
  μ_natural_left (F) :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ μ Y X' = μ X X' ≫ F.map (f ▷ X') := by
    cat_disch
  μ_natural_right (F) :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ μ X' Y = μ X' X ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity (F) :
    ∀ X Y Z : C,
      μ X Y ▷ F.obj Z ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ Y Z ≫ μ X (Y ⊗ Z) := by
    cat_disch
  -- unitality
  left_unitality (F) :
    ∀ X : C, (λ_ (F.obj X)).hom = ε ▷ F.obj X ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
      cat_disch
  right_unitality (F) :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace LaxMonoidal

attribute [reassoc (attr := simp)] μ_natural_left μ_natural_right
  associativity

attribute [simp, reassoc] right_unitality left_unitality

section

variable (F : C ⥤ D) [F.LaxMonoidal]

@[reassoc (attr := simp)]
theorem μ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ₘ F.map g) ≫ μ F Y Y' = μ F X X' ≫ F.map (f ⊗ₘ g) := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
theorem left_unitality_inv (X : C) :
    (λ_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X = F.map (λ_ X).inv := by
  rw [Iso.inv_comp_eq, left_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]

@[reassoc (attr := simp)]
theorem right_unitality_inv (X : C) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq, right_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]

@[reassoc (attr := simp)]
theorem associativity_inv (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z := by
  rw [Iso.eq_inv_comp, ← associativity_assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, comp_id]

@[reassoc]
lemma ε_tensorHom_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X = 𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom ≫ F.map (λ_ X).inv := by
  simp [tensorHom_def']

@[reassoc]
lemma tensorHom_ε_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) = f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
  simp [tensorHom_def]

@[reassoc]
lemma tensorUnit_whiskerLeft_comp_leftUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom = (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  simp [tensorHom_def']

@[reassoc]
lemma whiskerRight_tensorUnit_comp_rightUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  simp [tensorHom_def]

@[reassoc]
lemma μ_whiskerRight_comp_μ (X Y Z : C) :
    μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv := by
  rw [← associativity_assoc, ← F.map_comp, Iso.hom_inv_id, map_id, Category.comp_id]

@[reassoc]
lemma whiskerLeft_μ_comp_μ (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) = (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom := by
  rw [associativity, Iso.inv_hom_id_assoc]

end

section

variable {F : C ⥤ D}
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (μ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f ⊗ₘ F.map g) ≫ μ Y Y' = μ X X' ≫ F.map (f ⊗ₘ g) := by
      cat_disch)
    /- associativity of the tensorator -/
    (associativity :
      ∀ X Y Z : C,
        (μ X Y ⊗ₘ 𝟙 (F.obj Z)) ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ₘ μ Y Z) ≫ μ X (Y ⊗ Z) := by
      cat_disch)
    /- unitality -/
    (left_unitality :
      ∀ X : C, (λ_ (F.obj X)).hom = (ε ⊗ₘ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
        cat_disch)
    (right_unitality :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ₘ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
        cat_disch)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[implicit_reducible]
def ofTensorHom : F.LaxMonoidal where
  ε := ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity]
  left_unitality := fun X => by
    simp_rw [← tensorHom_id, left_unitality]
  right_unitality := fun X => by
    simp_rw [← id_tensorHom, right_unitality]

end

@[simps]
instance id : (𝟭 C).LaxMonoidal where
  ε := 𝟙 _
  μ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E)

variable [F.LaxMonoidal] [G.LaxMonoidal]

@[simps]
instance comp : (F ⋙ G).LaxMonoidal where
  ε := ε G ≫ G.map (ε F)
  μ X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]
  associativity _ _ _ := by
    dsimp
    simp_rw [comp_whiskerRight, assoc, μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
      assoc, μ_natural_right_assoc, ← associativity_assoc, ← G.map_comp, associativity]

end

end LaxMonoidal

/-- A functor `F : C ⥤ D` between monoidal categories is oplax monoidal if it is
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences. -/
@[ext]
class OplaxMonoidal (F : C ⥤ D) where
  /-- the counit morphism of a lax monoidal functor -/
  η (F) : F.obj (𝟙_ C) ⟶ 𝟙_ D
  /-- the cotensorator of an oplax monoidal functor -/
  δ (F) : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y
  δ_natural_left (F) :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X' := by
    cat_disch
  δ_natural_right (F) :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y := by
    cat_disch
  /-- associativity of the tensorator -/
  oplax_associativity (F) :
    ∀ X Y Z : C,
      δ (X ⊗ Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ F.obj X ◁ δ Y Z := by
    cat_disch
  -- unitality
  oplax_left_unitality (F) :
    ∀ X : C, (λ_ (F.obj X)).inv = F.map (λ_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ F.obj X := by
      cat_disch
  oplax_right_unitality (F) :
    ∀ X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ η := by
      cat_disch

namespace OplaxMonoidal

attribute [reassoc (attr := simp)] δ_natural_left δ_natural_right

@[reassoc (attr := simp)]
alias associativity := oplax_associativity

@[simp, reassoc]
alias left_unitality := oplax_left_unitality

@[simp, reassoc]
alias right_unitality := oplax_right_unitality

section

variable (F : C ⥤ D) [F.OplaxMonoidal]

@[reassoc (attr := simp)]
theorem δ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    δ F X X' ≫ (F.map f ⊗ₘ F.map g) = F.map (f ⊗ₘ g) ≫ δ F Y Y' := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
theorem left_unitality_hom (X : C) :
    δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, left_unitality, ← Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, id_comp]

@[reassoc (attr := simp)]
theorem right_unitality_hom (X : C) :
    δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, right_unitality, ← Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, id_comp]

@[reassoc (attr := simp)]
theorem associativity_inv (X Y Z : C) :
    δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.map (α_ X Y Z).inv ≫ δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, Category.assoc, associativity,
    ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, id_comp]

@[reassoc]
lemma δ_comp_η_tensorHom {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F (𝟙_ C) X ≫ (η F ⊗ₘ f) = F.map (λ_ X).hom ≫ (λ_ (F.obj X)).inv ≫ 𝟙_ D ◁ f := by
  simp [tensorHom_def]

@[reassoc]
lemma δ_comp_tensorHom_η {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F X (𝟙_ C) ≫ (f ⊗ₘ η F) = F.map (ρ_ X).hom ≫ (ρ_ (F.obj X)).inv ≫ f ▷ 𝟙_ D := by
  simp [tensorHom_def']

@[reassoc]
lemma δ_comp_δ_whiskerRight (X Y Z : C) :
    δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z = F.map (α_ X Y Z).hom ≫
      δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  rw [← associativity_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
lemma δ_comp_whiskerLeft_δ (X Y Z : C) :
    δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z = F.map (α_ X Y Z).inv ≫
      δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  rw [associativity, ← F.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

end

@[simps]
instance id : (𝟭 C).OplaxMonoidal where
  η := 𝟙 _
  δ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E) [F.OplaxMonoidal] [G.OplaxMonoidal]

@[simps]
instance comp : (F ⋙ G).OplaxMonoidal where
  η := G.map (η F) ≫ η G
  δ X Y := G.map (δ F X Y) ≫ δ G _ _
  δ_natural_left {X Y} f X' := by
    dsimp
    rw [assoc, δ_natural_left, ← G.map_comp_assoc, δ_natural_left, map_comp, assoc]
  δ_natural_right _ _ := by
    dsimp
    rw [assoc, δ_natural_right, ← G.map_comp_assoc, δ_natural_right, map_comp, assoc]
  oplax_associativity X Y Z := by
    dsimp
    rw [comp_whiskerRight, assoc, assoc, assoc, δ_natural_left_assoc, associativity,
      ← G.map_comp_assoc, ← G.map_comp_assoc, assoc, associativity, map_comp, map_comp,
      assoc, assoc, MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc]

end

end OplaxMonoidal

open LaxMonoidal OplaxMonoidal

/-- A functor between monoidal categories is monoidal if it is lax and oplax monoidals,
and both data give inverse isomorphisms. -/
@[ext]
class Monoidal (F : C ⥤ D) extends F.LaxMonoidal, F.OplaxMonoidal where
  ε_η (F) : ε ≫ η = 𝟙 _ := by cat_disch
  η_ε (F) : η ≫ ε = 𝟙 _ := by cat_disch
  μ_δ (F) (X Y : C) : μ X Y ≫ δ X Y = 𝟙 _ := by cat_disch
  δ_μ (F) (X Y : C) : δ X Y ≫ μ X Y = 𝟙 _ := by cat_disch

namespace Monoidal

attribute [reassoc (attr := simp)] ε_η η_ε μ_δ δ_μ

section

variable (F : C ⥤ D) [F.Monoidal]

/-- The isomorphism `𝟙_ D ≅ F.obj (𝟙_ C)` when `F` is a monoidal functor. -/
@[simps]
def εIso : 𝟙_ D ≅ F.obj (𝟙_ C) where
  hom := ε F
  inv := η F

/-- The isomorphism `F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)` when `F` is a monoidal functor. -/
@[simps]
def μIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) where
  hom := μ F X Y
  inv := δ F X Y

instance : IsIso (ε F) := (εIso F).isIso_hom
instance : IsIso (η F) := (εIso F).isIso_inv
instance (X Y : C) : IsIso (μ F X Y) := (μIso F X Y).isIso_hom
instance (X Y : C) : IsIso (δ F X Y) := (μIso F X Y).isIso_inv

@[reassoc (attr := simp)]
lemma map_ε_η (G : D ⥤ C') : G.map (ε F) ≫ G.map (η F) = 𝟙 _ :=
  (εIso F).map_hom_inv_id G

@[reassoc (attr := simp)]
lemma map_η_ε (G : D ⥤ C') : G.map (η F) ≫ G.map (ε F) = 𝟙 _ :=
  (εIso F).map_inv_hom_id G

@[reassoc (attr := simp)]
lemma map_μ_δ (G : D ⥤ C') (X Y : C) : G.map (μ F X Y) ≫ G.map (δ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_hom_inv_id G

@[reassoc (attr := simp)]
lemma map_δ_μ (G : D ⥤ C') (X Y : C) : G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_inv_hom_id G

@[reassoc (attr := simp)]
lemma whiskerRight_ε_η (T : D) : ε F ▷ T ≫ η F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, ε_η, id_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerRight_η_ε (T : D) : η F ▷ T ≫ ε F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, η_ε, id_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerRight_μ_δ (X Y : C) (T : D) : μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, μ_δ, id_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerRight_δ_μ (X Y : C) (T : D) : δ F X Y ▷ T ≫ μ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, δ_μ, id_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerLeft_ε_η (T : D) : T ◁ ε F ≫ T ◁ η F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, ε_η, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
lemma whiskerLeft_η_ε (T : D) : T ◁ η F ≫ T ◁ ε F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, η_ε, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
lemma whiskerLeft_μ_δ (X Y : C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, μ_δ, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
lemma whiskerLeft_δ_μ (X Y : C) (T : D) : T ◁ δ F X Y ≫ T ◁ μ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, δ_μ, MonoidalCategory.whiskerLeft_id]

@[reassoc]
theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ₘ g) = δ F X X' ≫ (F.map f ⊗ₘ F.map g) ≫ μ F Y Y' := by simp

@[reassoc]
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) = δ F X Y ≫ F.obj X ◁ F.map f ≫ μ F X Z := by simp

@[reassoc]
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) = δ F X Z ≫ F.map f ▷ F.obj Z ≫ μ F Y Z := by simp

@[reassoc]
theorem map_associator (X Y Z : C) :
    F.map (α_ X Y Z).hom =
      δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) := by
  rw [← LaxMonoidal.associativity F, whiskerRight_δ_μ_assoc, δ_μ_assoc]

@[reassoc]
theorem map_associator_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv =
      δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z := by
  rw [← cancel_epi (F.map (α_ X Y Z).hom), Iso.map_hom_inv_id, map_associator,
    assoc, assoc, assoc, assoc, OplaxMonoidal.associativity_inv_assoc,
    whiskerRight_δ_μ_assoc, δ_μ, comp_id, LaxMonoidal.associativity_inv,
    Iso.hom_inv_id_assoc, whiskerRight_δ_μ_assoc, δ_μ]

@[reassoc]
theorem map_associator' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom ≫
        δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z := by
  simp

@[reassoc]
theorem map_associator_inv' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv ≫
        δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom, map_associator']
  simp

@[reassoc]
theorem map_leftUnitor (X : C) :
    F.map (λ_ X).hom = δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by simp

@[reassoc]
theorem map_leftUnitor_inv (X : C) :
    F.map (λ_ X).inv = (λ_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X := by simp

@[reassoc]
theorem map_rightUnitor (X : C) :
    F.map (ρ_ X).hom = δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom := by simp

@[reassoc]
theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv = (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) := by simp

@[simp] lemma inv_η : CategoryTheory.inv (η F) = ε F := by
  rw [← εIso_hom, ← Iso.comp_inv_eq_id, εIso_inv, IsIso.inv_hom_id]

@[simp] lemma inv_ε : CategoryTheory.inv (ε F) = η F := by simp [← inv_η]

@[simp] lemma inv_μ (X Y : C) : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv, ← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]

@[simp] lemma inv_δ (X Y : C) : CategoryTheory.inv (δ F X Y) = μ F X Y := by simp [← inv_μ]

/-- The tensorator as a natural isomorphism. -/
@[simps!]
def μNatIso :
    Functor.prod F F ⋙ tensor D ≅ tensor C ⋙ F :=
  NatIso.ofComponents (fun _ ↦ μIso F _ _)

/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
def commTensorLeft (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F X Y)

/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
def commTensorRight (X : C) :
    F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F Y X)

end

instance : (𝟭 C).Monoidal where

variable (F : C ⥤ D) (G : D ⥤ E)

instance [F.Monoidal] [G.Monoidal] : (F ⋙ G).Monoidal where
  ε_η := by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp

lemma toLaxMonoidal_injective : Function.Injective
    (@Monoidal.toLaxMonoidal _ _ _ _ _ _ _ : F.Monoidal → F.LaxMonoidal) := by
  intro a b eq
  ext1
  · exact congr(($eq).ε)
  · exact congr(($eq).μ)
  · rw [← cancel_epi (εIso _).hom]
    rw [εIso_hom, ε_η, ← @ε_η _ _ _ _ _ _ _ a, ← εIso_hom]
    exact congr(($eq.symm).ε ≫ _)
  · ext
    rw [← cancel_epi (μIso F _ _).hom]
    rw [μIso_hom, μ_δ, ← @μ_δ _ _ _ _ _ _ _ a, ← μIso_hom]
    exact congr(($eq.symm).μ _ _ ≫ _)

lemma toOplaxMonoidal_injective : Function.Injective
    (@Monoidal.toOplaxMonoidal _ _ _ _ _ _ _ : F.Monoidal → F.OplaxMonoidal) := by
  intro a b eq
  ext1
  · rw [← cancel_mono (εIso _).inv]
    rw [εIso_inv, ε_η, ← @ε_η _ _ _ _ _ _ _ a, ← εIso_inv]
    exact congr(_ ≫ ($eq.symm).η)
  · ext
    rw [← cancel_mono (μIso F _ _).inv]
    rw [μIso_inv, μ_δ, ← @μ_δ _ _ _ _ _ _ _ a, ← μIso_inv]
    exact congr(_ ≫ ($eq.symm).δ _ _)
  · exact congr(($eq).η)
  · exact congr(($eq).δ)

end Monoidal

variable (F : C ⥤ D)
/-- Structure which is a helper in order to show that a functor is monoidal. It
consists of isomorphisms `εIso` and `μIso` such that the morphisms `.hom` induced
by these isomorphisms satisfy the axioms of lax monoidal functors. -/
structure CoreMonoidal where
  /-- unit morphism -/
  εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  /-- tensorator -/
  μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  μIso_hom_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X') := by
    cat_disch
  μIso_hom_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
          (μIso X (Y ⊗ Z)).hom := by
    cat_disch
  -- unitality
  left_unitality :
    ∀ X : C, (λ_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by
      cat_disch
  right_unitality :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace CoreMonoidal

attribute [reassoc (attr := simp)] μIso_hom_natural_left
  μIso_hom_natural_right associativity

attribute [reassoc] left_unitality right_unitality

variable {F} (h : F.CoreMonoidal)

/-- The lax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, implicit_reducible]
def toLaxMonoidal : F.LaxMonoidal where
  ε := h.εIso.hom
  μ X Y := (h.μIso X Y).hom
  left_unitality := h.left_unitality
  right_unitality := h.right_unitality

/-- The oplax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, implicit_reducible]
def toOplaxMonoidal : F.OplaxMonoidal where
  η := h.εIso.inv
  δ X Y := (h.μIso X Y).inv
  δ_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_left_assoc, Iso.hom_inv_id, comp_id]
  δ_natural_right _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_right_assoc, Iso.hom_inv_id, comp_id]
  oplax_associativity X Y Z := by
    rw [← cancel_epi (h.μIso (X ⊗ Y) Z).hom, Iso.hom_inv_id_assoc,
      ← cancel_epi ((h.μIso X Y).hom ▷ F.obj Z), hom_inv_whiskerRight_assoc,
      associativity_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv, comp_id]
  oplax_left_unitality _ := by
    rw [← cancel_epi (λ_ _).hom, Iso.hom_inv_id, h.left_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc, hom_inv_whiskerRight]
  oplax_right_unitality _ := by
    rw [← cancel_epi (ρ_ _).hom, Iso.hom_inv_id, h.right_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv]

attribute [local simp] toLaxMonoidal_ε toLaxMonoidal_μ toOplaxMonoidal_η toOplaxMonoidal_δ in
/-- The monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps! toLaxMonoidal toOplaxMonoidal, implicit_reducible]
def toMonoidal : F.Monoidal where
  toLaxMonoidal := h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

variable (F)

/-- The `Functor.CoreMonoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms. -/
noncomputable def ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :
    F.CoreMonoidal where
  εIso := asIso (ε F)
  μIso X Y := asIso (μ F X Y)

/-- The `Functor.CoreMonoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[simps]
noncomputable def ofOplaxMonoidal [F.OplaxMonoidal] [IsIso (η F)] [∀ X Y, IsIso (δ F X Y)] :
    F.CoreMonoidal where
  εIso := (asIso (η F)).symm
  μIso X Y := (asIso (δ F X Y)).symm
  associativity X Y Z := by
    simp [← cancel_epi (δ F X Y ▷ F.obj Z), ← cancel_epi (δ F (X ⊗ Y) Z)]
  left_unitality X := by simp [← cancel_epi (λ_ (F.obj X)).inv]
  right_unitality X := by simp [← cancel_epi (ρ_ (F.obj X)).inv]

end CoreMonoidal

/-- The `Functor.Monoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms. -/
@[implicit_reducible]
noncomputable def Monoidal.ofLaxMonoidal
    [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :=
  (CoreMonoidal.ofLaxMonoidal F).toMonoidal

/-- The `Functor.Monoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[implicit_reducible]
noncomputable def Monoidal.ofOplaxMonoidal
    [F.OplaxMonoidal] [IsIso (η F)] [∀ X Y, IsIso (δ F X Y)] :=
  (CoreMonoidal.ofOplaxMonoidal F).toMonoidal

section Prod

open scoped Prod

variable (F : C ⥤ D) (G : E ⥤ C') [MonoidalCategory C']

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

instance : (prod F G).LaxMonoidal where
  ε := ε F ×ₘ ε G
  μ X Y := μ F _ _ ×ₘ μ G _ _

@[simp] lemma prod_ε_fst : (ε (prod F G)).1 = ε F := rfl
@[simp] lemma prod_ε_snd : (ε (prod F G)).2 = ε G := rfl
@[simp] lemma prod_μ_fst (X Y : C × E) : (μ (prod F G) X Y).1 = μ F _ _ := rfl
@[simp] lemma prod_μ_snd (X Y : C × E) : (μ (prod F G) X Y).2 = μ G _ _ := rfl

end

section

open scoped Prod

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

instance : (prod F G).OplaxMonoidal where
  η := η F ×ₘ η G
  δ X Y := δ F _ _ ×ₘ δ G _ _

@[simp] lemma prod_η_fst : (η (prod F G)).1 = η F := rfl
@[simp] lemma prod_η_snd : (η (prod F G)).2 = η G := rfl
@[simp] lemma prod_δ_fst (X Y : C × E) : (δ (prod F G) X Y).1 = δ F _ _ := rfl
@[simp] lemma prod_δ_snd (X Y : C × E) : (δ (prod F G) X Y).2 = δ G _ _ := rfl

end

instance [F.Monoidal] [G.Monoidal] : (prod F G).Monoidal where
  ε_η := by ext <;> apply Monoidal.ε_η
  η_ε := by ext <;> apply Monoidal.η_ε
  μ_δ _ _ := by ext <;> apply Monoidal.μ_δ
  δ_μ _ _ := by ext <;> apply Monoidal.δ_μ

end Prod

instance : (diag C).Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] lemma diag_ε : ε (diag C) = 𝟙 _ := rfl
@[simp] lemma diag_η : η (diag C) = 𝟙 _ := rfl
@[simp] lemma diag_μ (X Y : C) : μ (diag C) X Y = 𝟙 _ := rfl
@[simp] lemma diag_δ (X Y : C) : δ (diag C) X Y = 𝟙 _ := rfl

section Prod'

variable (F : C ⥤ D) (G : C ⥤ E)

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

/-- The functor `C ⥤ D × E` obtained from two lax monoidal functors is lax monoidal. -/
instance LaxMonoidal.prod' : (prod' F G).LaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).LaxMonoidal

@[simp] lemma prod'_ε_fst : (ε (prod' F G)).1 = ε F := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

@[simp] lemma prod'_ε_snd : (ε (prod' F G)).2 = ε G := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

@[simp] lemma prod'_μ_fst (X Y : C) : (μ (prod' F G) X Y).1 = μ F X Y := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

@[simp] lemma prod'_μ_snd (X Y : C) : (μ (prod' F G) X Y).2 = μ G X Y := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

end

section

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

/-- The functor `C ⥤ D × E` obtained from two oplax monoidal functors is oplax monoidal. -/
instance OplaxMonoidal.prod' : (prod' F G).OplaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

@[simp] lemma prod'_η_fst : (η (prod' F G)).1 = η F := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

@[simp] lemma prod'_η_snd : (η (prod' F G)).2 = η G := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

@[simp] lemma prod'_δ_fst (X Y : C) : (δ (prod' F G) X Y).1 = δ F X Y := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

@[simp] lemma prod'_δ_snd (X Y : C) : (δ (prod' F G) X Y).2 = δ G X Y := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

end

-- TODO: when clearing these deprecations, remove the `CategoryTheory.` in the proof below.

set_option backward.isDefEq.respectTransparency false in
/-- The functor `C ⥤ D × E` obtained from two monoidal functors is monoidal. -/
instance Monoidal.prod' [F.Monoidal] [G.Monoidal] :
    (prod' F G).Monoidal where
  -- automation should work, but it is terribly slow
  ε_η := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, ε_η,
        prodMonoidal_tensorUnit, prod_id]
  η_ε := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, η_ε,
        prod_id, prod'_obj]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, η_ε,
        prod_id, prod'_obj]
  μ_δ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
  δ_μ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, δ_μ,
        prod'_obj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, δ_μ,
        prod'_obj, prod_id]

end Prod'

end Functor

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.OplaxMonoidal Functor.LaxMonoidal

section LaxMonoidal
variable [F.OplaxMonoidal]

set_option backward.isDefEq.respectTransparency false in
/-- The right adjoint of an oplax monoidal functor is lax monoidal. -/
@[simps, implicit_reducible]
def rightAdjointLaxMonoidal : G.LaxMonoidal where
  ε := adj.homEquiv _ _ (η F)
  μ X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y))
  μ_natural_left {X Y} f X' := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp, assoc,
      ← δ_natural_left_assoc F]
    suffices F.map (G.map f) ▷ F.obj (G.obj X') ≫ _ =
      (adj.counit.app X ⊗ₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerRight_app_tensor_app adj.counit adj.counit (f := f) X'
  μ_natural_right {X' Y'} X g := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp,
      assoc, ← δ_natural_right_assoc F]
    suffices F.obj (G.obj X) ◁ F.map (G.map g) ≫ _ =
      (adj.counit.app X ⊗ₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerLeft_app_tensor_app adj.counit adj.counit (f := g) _
  associativity X Y Z := (adj.homEquiv _ _).symm.injective (by
    simp only [homEquiv_unit, comp_obj, map_comp, comp_whiskerRight, assoc, homEquiv_counit,
      counit_naturality, id_obj, counit_naturality_assoc, left_triangle_components_assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [← δ_natural_left_assoc, ← δ_natural_left_assoc, ← δ_natural_left_assoc]
    haveI := @NatTrans.whiskerRight_app_tensor_app_assoc _ _ _ _ _ _ _ _ _ adj.counit adj.counit
    dsimp only [id_obj, comp_obj, Functor.comp_map, Functor.id_map] at this
    rw [this, this, tensorHom_def, assoc, ← comp_whiskerRight_assoc,
      left_triangle_components, id_whiskerRight, id_comp,
      whisker_exchange_assoc, whisker_exchange_assoc, ← tensorHom_def_assoc,
      associator_naturality, OplaxMonoidal.associativity_assoc]
    rw [← δ_natural_right_assoc, ← δ_natural_right_assoc, ← δ_natural_right_assoc]
    nth_rw 4 [tensorHom_def]
    rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, assoc, assoc,
      counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
      MonoidalCategory.whiskerLeft_comp, assoc, tensorHom_def, whisker_exchange])
  left_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit, homEquiv_counit, homEquiv_unit, homEquiv_unit, comp_whiskerRight,
      map_comp, map_comp, map_comp, map_comp, map_comp, map_comp, assoc, assoc, assoc, assoc,
      assoc, counit_naturality, counit_naturality_assoc, counit_naturality_assoc,
      left_triangle_components_assoc, ← δ_natural_left_assoc, ← δ_natural_left_assoc,
      tensorHom_def, assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, assoc, counit_naturality,
      left_triangle_components_assoc, id_whiskerLeft, assoc, assoc, Iso.inv_hom_id, comp_id,
      left_unitality_hom_assoc])
  right_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit, homEquiv_unit, MonoidalCategory.whiskerLeft_comp, homEquiv_unit,
      homEquiv_counit, map_comp, map_comp, map_comp, map_comp, map_comp, map_comp,
      assoc, assoc, assoc, assoc, assoc, counit_naturality, counit_naturality_assoc,
      counit_naturality_assoc, left_triangle_components_assoc, ← δ_natural_right_assoc,
      ← δ_natural_right_assoc, tensorHom_def, assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      assoc, counit_naturality, left_triangle_components_assoc, MonoidalCategory.whiskerRight_id,
      assoc, assoc, Iso.inv_hom_id, comp_id, right_unitality_hom_assoc])

/-- When `adj : F ⊣ G` is an adjunction, with `F` oplax monoidal and `G` lax-monoidal,
this typeclass expresses compatibilities between the adjunction and the (op)lax
monoidal structures. -/
class IsMonoidal [G.LaxMonoidal] : Prop where
  leftAdjoint_ε : ε G = adj.unit.app _ ≫ G.map (η F) := by cat_disch
  leftAdjoint_μ (X Y : D) : μ G X Y =
    adj.unit.app _ ≫ G.map (δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y)) := by cat_disch

instance :
    letI := adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  letI := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

variable [G.LaxMonoidal] [adj.IsMonoidal]

@[reassoc]
lemma unit_app_unit_comp_map_η : adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G :=
  Adjunction.IsMonoidal.leftAdjoint_ε.symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma unit_app_tensor_comp_map_δ (X Y : C) :
    adj.unit.app (X ⊗ Y) ≫ G.map (δ F X Y) = (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _ := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj), ← adj.unit_naturality_assoc,
    ← Functor.map_comp, ← δ_natural_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_ε_comp_counit_app_unit : F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F := by
  simp [IsMonoidal.leftAdjoint_ε (adj := adj)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_μ_comp_counit_app_tensor (X Y : D) :
    F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y) := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj)]

instance : (Adjunction.id (C := C)).IsMonoidal where

instance isMonoidal_comp {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
    [F'.OplaxMonoidal] [G'.LaxMonoidal] [adj'.IsMonoidal] : (adj.comp adj').IsMonoidal where
  leftAdjoint_ε := by
    simp [IsMonoidal.leftAdjoint_ε (adj := adj'), IsMonoidal.leftAdjoint_ε (adj := adj),
      ← map_comp, ← adj'.unit_naturality_assoc]
  leftAdjoint_μ X Y := by
    simp only [comp_obj, comp_μ, IsMonoidal.leftAdjoint_μ (adj := adj), id_obj,
      IsMonoidal.leftAdjoint_μ (adj := adj'), assoc, ← map_comp, comp_unit_app, comp_δ,
      comp_counit_app, ← tensorHom_comp_tensorHom, δ_natural_assoc, Functor.comp_map]
    simp

end LaxMonoidal

section OplaxMonoidal
variable [G.LaxMonoidal]

set_option backward.isDefEq.respectTransparency false in
/-- The left adjoint of a lax monoidal functor is oplax monoidal. -/
@[simps, implicit_reducible]
def leftAdjointOplaxMonoidal : F.OplaxMonoidal where
  η := (adj.homEquiv _ _).symm (ε G)
  δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _)
  δ_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_left]
    simp [← tensorHom_id]
  δ_natural_right _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_right]
    simp [← id_tensorHom]
  oplax_associativity X Y Z := (adj.homEquiv _ _).injective (by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, assoc, assoc]
    conv_lhs =>
      rw [homEquiv_counit, map_comp_assoc, map_comp,
        ← μ_natural_left_assoc, map_comp, map_comp, tensorHom_def'_assoc]
      dsimp
      rw [← comp_whiskerRight_assoc]
    conv_rhs =>
      rw [← μ_natural_right, homEquiv_counit, map_comp_assoc,
        map_comp, tensorHom_def_assoc, ← associator_naturality_left_assoc]
      dsimp
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, map_comp,
        unit_naturality_assoc, MonoidalCategory.whiskerLeft_comp,
        unit_naturality_assoc, right_triangle_components, comp_id, assoc,
        tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc,
        ← associator_naturality_middle_assoc, ← associator_naturality_right_assoc,
        ← associativity G, ← comp_whiskerRight_assoc, ← tensorHom_def,
        ← whisker_exchange_assoc, ← comp_whiskerRight_assoc]
    simp)
  oplax_left_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_left, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def', homEquiv_unit, homEquiv_counit])
  oplax_right_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_right, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def, homEquiv_unit, homEquiv_counit])

set_option backward.isDefEq.respectTransparency false in
instance :
    letI := adj.leftAdjointOplaxMonoidal
    adj.IsMonoidal := by
  letI := adj.leftAdjointOplaxMonoidal
  refine ⟨?_, fun X Y ↦ ?_⟩
  · simp [homEquiv_counit]
  · simp [homEquiv_counit, ← μ_natural]

end OplaxMonoidal

set_option backward.isDefEq.respectTransparency false in
def laxMonoidalOplaxMonoidalEquiv : G.LaxMonoidal ≃ F.OplaxMonoidal where
  toFun _ := leftAdjointOplaxMonoidal adj
  invFun _ := rightAdjointLaxMonoidal adj
  left_inv _ := by
    ext
    · simp
    simp [homEquiv_counit, homEquiv_unit, ← μ_natural]
  right_inv _ := by
    ext
    · simp
    simp [homEquiv_counit, homEquiv_unit, ← δ_natural_assoc]
section Monoidal
variable [F.Monoidal] [G.Monoidal] [adj.IsMonoidal]

@[reassoc]
lemma ε_comp_map_ε : ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C) := by
  simp [← adj.unit_app_unit_comp_map_η]

@[reassoc]
lemma map_η_comp_η : F.map (η G) ≫ η F = adj.counit.app (𝟙_ D) := by
  simp [← adj.map_ε_comp_counit_app_unit]

end Monoidal
end Adjunction

namespace Equivalence

variable (e : C ≌ D)

instance [e.inverse.Monoidal] : e.symm.functor.Monoidal := inferInstanceAs (e.inverse.Monoidal)
instance [e.functor.Monoidal] : e.symm.inverse.Monoidal := inferInstanceAs (e.functor.Monoidal)

set_option backward.isDefEq.respectTransparency false in
/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[implicit_reducible]
noncomputable def inverseMonoidal [e.functor.Monoidal] : e.inverse.Monoidal := by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : ∀ (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y ↦ by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
    infer_instance
  apply Monoidal.ofLaxMonoidal

/-- An equivalence of categories involving monoidal functors is monoidal if the underlying
adjunction satisfies certain compatibilities with respect to the monoidal functor data. -/
abbrev IsMonoidal [e.functor.Monoidal] [e.inverse.Monoidal] : Prop := e.toAdjunction.IsMonoidal

set_option backward.isDefEq.respectTransparency false in
example [e.functor.Monoidal] : letI := e.inverseMonoidal; e.IsMonoidal := inferInstance

variable [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[reassoc]
lemma unitIso_hom_app_comp_inverse_map_η_functor :
    e.unitIso.hom.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
lemma unitIso_hom_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unitIso.hom.app (X ⊗ Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc]
lemma functor_map_ε_inverse_comp_counitIso_hom_app :
    e.functor.map (ε e.inverse) ≫ e.counitIso.hom.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
lemma functor_map_μ_inverse_comp_counitIso_hom_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counitIso.hom.app (X ⊗ Y) =
      δ e.functor _ _ ≫ (e.counitIso.hom.app X ⊗ₘ e.counitIso.hom.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma counitIso_inv_app_comp_functor_map_η_inverse :
    e.counitIso.inv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor), Monoidal.η_ε, ← functor_map_ε_inverse_comp_counitIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal.map_ε_η]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma counitIso_inv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitIso.inv.app (e.functor.obj X ⊗ e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) := by
  rw [← cancel_epi (δ e.functor _ _), Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X ⊗ Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc]
lemma unit_app_comp_inverse_map_η_functor :
    e.unit.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
lemma unit_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unit.app (X ⊗ Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unit.app X ⊗ₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]
lemma functor_map_ε_inverse_comp_counit_app :
    e.functor.map (ε e.inverse) ≫ e.counit.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
lemma functor_map_μ_inverse_comp_counit_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counit.app (X ⊗ Y) =
      δ e.functor _ _ ≫ (e.counit.app X ⊗ₘ e.counit.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma counitInv_app_comp_functor_map_η_inverse :
    e.counitInv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor), Monoidal.η_ε, ← functor_map_ε_inverse_comp_counitIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal.map_ε_η]

@[reassoc]
lemma counitInv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitInv.app (e.functor.obj X ⊗ e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) :=
  counitIso_inv_app_tensor_comp_functor_map_δ_inverse e X Y

@[reassoc (attr := simp)]
lemma ε_comp_map_ε : ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C) :=
  e.toAdjunction.ε_comp_map_ε

@[reassoc (attr := simp)]
lemma map_η_comp_η : e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D) :=
  e.toAdjunction.map_η_comp_η

instance : (refl (C := C)).functor.Monoidal := inferInstanceAs (𝟭 C).Monoidal
instance : (refl (C := C)).inverse.Monoidal := inferInstanceAs (𝟭 C).Monoidal

/-- The obvious auto-equivalence of a monoidal category is monoidal. -/
instance isMonoidal_refl : (Equivalence.refl (C := C)).IsMonoidal :=
  inferInstanceAs (Adjunction.id (C := C)).IsMonoidal

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of a monoidal category equivalence is also a monoidal category equivalence. -/
instance isMonoidal_symm [e.IsMonoidal] : e.symm.IsMonoidal where
  leftAdjoint_ε := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [counitIso_inv_app_comp_functor_map_η_inverse]
  leftAdjoint_μ X Y := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [map_comp, counitIso_inv_app_tensor_comp_functor_map_δ_inverse_assoc]
    simp [← map_comp]

section

variable (e' : D ≌ E)

instance [e'.functor.Monoidal] : (e.trans e').functor.Monoidal :=
  inferInstanceAs (e.functor ⋙ e'.functor).Monoidal

instance [e'.inverse.Monoidal] : (e.trans e').inverse.Monoidal :=
  inferInstanceAs (e'.inverse ⋙ e.inverse).Monoidal

/-- The composition of two monoidal category equivalences is monoidal. -/
instance isMonoidal_trans [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoidal] :
    (e.trans e').IsMonoidal := by
  dsimp [Equivalence.IsMonoidal]
  rw [trans_toAdjunction]
  infer_instance

end

end Equivalence

variable (C D)

/-- Bundled version of lax monoidal functors. This type is equipped with a category
structure in `CategoryTheory.Monoidal.NaturalTransformation`. -/
structure LaxMonoidalFunctor extends C ⥤ D where
  laxMonoidal : toFunctor.LaxMonoidal := by infer_instance

namespace LaxMonoidalFunctor

attribute [instance] laxMonoidal

variable {C D}

/-- Constructor for `LaxMonoidalFunctor C D`. -/
@[simps toFunctor]
def of (F : C ⥤ D) [F.LaxMonoidal] : LaxMonoidalFunctor C D where
  toFunctor := F

end LaxMonoidalFunctor

namespace Functor.Monoidal

variable {C D}

/--
Auxiliary definition for `Functor.Monoidal.transport`
-/
@[simps!]
def coreMonoidalTransport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.CoreMonoidal where
  εIso := εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, μIso_hom, comp_whiskerRight,
      Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [← i.hom.naturality, map_associator_assoc, Functor.OplaxMonoidal.associativity_assoc,
      whiskerLeft_δ_μ_assoc, δ_μ_assoc]
    simp only [← Category.assoc]
    congr 1
    slice_lhs 3 4 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp only [Iso.hom_inv_id_app, Category.id_comp, id_tensorHom]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    simp only [tensor_whiskerLeft, Functor.LaxMonoidal.associativity, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_id, associator_naturality_assoc]
    simp [← id_tensorHom, -tensorHom_id]
  left_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← tensorHom_id, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.comp_id, Category.id_comp]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp
  right_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← id_tensorHom, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp

/--
Transport the structure of a monoidal functor along a natural isomorphism of functors.
-/
@[implicit_reducible]
def transport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.Monoidal :=
  (coreMonoidalTransport i).toMonoidal

@[reassoc]
lemma transport_ε {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
lemma transport_η {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    OplaxMonoidal.η G = i.inv.app (𝟙_ C) ≫ OplaxMonoidal.η F :=
  rfl

@[reassoc]
lemma transport_μ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    LaxMonoidal.μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ LaxMonoidal.μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  rfl

@[reassoc]
lemma transport_δ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    OplaxMonoidal.δ G X Y =
      i.inv.app (X ⊗ Y) ≫ OplaxMonoidal.δ F X Y ≫ (i.hom.app X ⊗ₘ i.hom.app Y) :=
  coreMonoidalTransport_μIso_inv _ _ _

end Functor.Monoidal

namespace Equivalence

variable {C D}

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `e.functor ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[implicit_reducible]
def monoidalOfPrecompFunctor (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.functor ⋙ F ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  letI : (e.functor ⋙ F).Monoidal := .transport i.symm
  .transport (e.invFunIdAssoc F)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `e.inverse ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[implicit_reducible]
def monoidalOfPrecompInverse (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inverse ⋙ F ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPrecompFunctor F i

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `F ⋙ e.inverse`
are monoidal functors, `F` is monoidal as well.
-/
@[implicit_reducible]
def monoidalOfPostcompInverse (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.inverse ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  .transport (Functor.isoWhiskerRight i.symm e.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.counitIso ≪≫ F.rightUnitor)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `F ⋙ e.functor`
are monoidal functors, `F` is monoidal as well.
-/
@[implicit_reducible]
def monoidalOfPostcompFunctor (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.functor ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPostcompInverse _ i

end Equivalence

end CategoryTheory
