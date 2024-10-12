/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Products.Basic

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms. This is implemented as a typeclass `F.LaxMonoidal`.

Similarly, we define the type class `F.OplaxMonoidal`. For these oplax functors,
we have similar data `η` and `δ`, but with morphisms in the opposite direction.

A monoidal functor (`F.Monoidal`) is defined here as the combination of `F.LaxMonoidal`
and `F.OplaxMonoidal`, with the additional conditions that `ε`/`η` and `μ`/`δ` are
inverse isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See `CategoryTheory.Monoidal.NaturalTransformation` for monoidal natural transformations.

We show in `CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/


open CategoryTheory

universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

section

@[ext]
lemma prod_hom_ext {C D : Type*} [Category C] [Category D]
    {X Y : C × D} {f g : X ⟶ Y} (h₁ : f.1 = g.1) (h₂ : f.2 = g.2) : f = g := by
  dsimp
  ext <;> assumption

end

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']
  (F : C ⥤ D) (G : D ⥤ E)

namespace Functor

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A functor `F : C ⥤ D` between monoidal categoires is lax monoidal if it is
equipped with morphisms `ε : 𝟙 _D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences. -/
class LaxMonoidal where
  /-- unit morphism -/
  ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)
  /-- tensorator -/
  μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)
  μ'_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ μ' Y X' = μ' X X' ≫ F.map (f ▷ X') := by
    aesop_cat
  μ'_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      F.obj X' ◁ F.map f ≫ μ' X' Y = μ' X' X ≫ F.map (X' ◁ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity' :
    ∀ X Y Z : C,
      μ' X Y ▷ F.obj Z ≫ μ' (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ' Y Z ≫ μ' X (Y ⊗ Z) := by
    aesop_cat
  -- unitality
  left_unitality' :
    ∀ X : C, (λ_ (F.obj X)).hom = ε' ▷ F.obj X ≫ μ' (𝟙_ C) X ≫ F.map (λ_ X).hom := by
      aesop_cat
  right_unitality' :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε' ≫ μ' X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
    aesop_cat

namespace LaxMonoidal

section

variable [F.LaxMonoidal]

/-- the unit morphism of a lax monoidal functor-/
def ε : 𝟙_ D ⟶ F.obj (𝟙_ C) := ε'

/-- the tensorator of a lax monoidal functor -/
def μ (X Y : C) : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y) := μ' X Y

@[reassoc (attr := simp)]
lemma μ_natural_left {X Y : C} (f : X ⟶ Y) (X' : C) :
      F.map f ▷ F.obj X' ≫ μ F Y X' = μ F X X' ≫ F.map (f ▷ X') := by
  apply μ'_natural_left

@[reassoc (attr := simp)]
lemma μ_natural_right {X Y : C} (X' : C) (f : X ⟶ Y) :
      F.obj X' ◁ F.map f ≫ μ F X' Y = μ F X' X ≫ F.map (X' ◁ f) := by
  apply μ'_natural_right

@[reassoc (attr := simp)]
lemma associativity (X Y Z : C) :
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) := by
  apply associativity'

@[simp, reassoc]
lemma left_unitality (X : C) :
    (λ_ (F.obj X)).hom = ε F ▷ F.obj X ≫ μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  apply left_unitality'

@[simp, reassoc]
lemma right_unitality (X : C) :
    (ρ_ (F.obj X)).hom = F.obj X ◁ ε F ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  apply right_unitality'

@[reassoc (attr := simp)]
theorem μ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
      (F.map f ⊗ F.map g) ≫ μ F Y Y' = μ F X X' ≫ F.map (f ⊗ g) := by
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

end

section

variable {F}
    /- unit morphism -/
    (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (μ'_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f ⊗ F.map g) ≫ μ' Y Y' = μ' X X' ≫ F.map (f ⊗ g) := by
      aesop_cat)
    /- associativity of the tensorator -/
    (associativity' :
      ∀ X Y Z : C,
        (μ' X Y ⊗ 𝟙 (F.obj Z)) ≫ μ' (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ μ' Y Z) ≫ μ' X (Y ⊗ Z) := by
      aesop_cat)
    /- unitality -/
    (left_unitality' :
      ∀ X : C, (λ_ (F.obj X)).hom = (ε' ⊗ 𝟙 (F.obj X)) ≫ μ' (𝟙_ C) X ≫ F.map (λ_ X).hom := by
        aesop_cat)
    (right_unitality' :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ ε') ≫ μ' X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
        aesop_cat)

/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
def ofTensorHom : F.LaxMonoidal where
  ε' := ε'
  μ' := μ'
  μ'_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ'_natural]
  μ'_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ'_natural]
  associativity' := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity']
  left_unitality' := fun X => by
    simp_rw [← tensorHom_id, left_unitality']
  right_unitality' := fun X => by
    simp_rw [← id_tensorHom, right_unitality']

@[simp]
lemma ofTensorHom_ε :
  letI := (ofTensorHom ε' μ' μ'_natural associativity' left_unitality' right_unitality')
  ε F = ε' := rfl

@[simp]
lemma ofTensorHom_μ :
  letI := (ofTensorHom ε' μ' μ'_natural associativity' left_unitality' right_unitality')
  μ F = μ' := rfl

end

instance id : (𝟭 C).LaxMonoidal where
  ε' := 𝟙 _
  μ' _ _ := 𝟙 _

@[simp]
lemma id_ε : ε (𝟭 C) = 𝟙 _ := rfl

@[simp]
lemma id_μ (X Y : C) : μ (𝟭 C) X Y = 𝟙 _ := rfl

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

instance comp : (F ⋙ G).LaxMonoidal where
  ε' := ε G ≫ G.map (ε F)
  μ' X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ'_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ'_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]
  associativity' _ _ _ := by
    dsimp
    simp_rw [comp_whiskerRight, assoc, μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
      assoc, μ_natural_right_assoc, ← associativity_assoc, ← G.map_comp, associativity]
  left_unitality' _ := by
    simp only [comp_obj, left_unitality, μ_natural, implies_true, tensorHom_id, associativity,
      id_tensorHom, right_unitality, ofTensorHom_ε, map_comp, comp_whiskerRight, comp_map, assoc,
      μ_natural_left_assoc]
  right_unitality' _ := by
    simp only [comp_obj, right_unitality, μ_natural, implies_true, tensorHom_id, associativity,
      id_tensorHom, left_unitality, ofTensorHom_ε, map_comp, MonoidalCategory.whiskerLeft_comp,
      comp_map, assoc, μ_natural_right_assoc]

@[simp]
lemma comp_ε : ε (F ⋙ G) = ε G ≫ G.map (ε F) := rfl

@[simp]
lemma comp_μ (X Y : C) : μ (F ⋙ G) X Y = μ G _ _ ≫ G.map (μ F X Y) := rfl

end

end LaxMonoidal

/-- A functor `F : C ⥤ D` between monoidal categories is oplax monoidal if it is
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences. -/
class OplaxMonoidal where
  /-- counit morphism -/
  η' : F.obj (𝟙_ C) ⟶ 𝟙_ D
  /-- cotensorator -/
  δ' : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y
  δ'_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      δ' X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ' Y X' := by
    aesop_cat
  δ'_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      δ' X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ' X' Y := by
    aesop_cat
  /-- associativity of the tensorator -/
  oplax_associativity' :
    ∀ X Y Z : C,
      δ' (X ⊗ Y) Z ≫ δ' X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ δ' X (Y ⊗ Z) ≫ F.obj X ◁ δ' Y Z := by
    aesop_cat
  -- unitality
  oplax_left_unitality' :
    ∀ X : C, (λ_ (F.obj X)).inv = F.map (λ_ X).inv ≫ δ' (𝟙_ C) X ≫ η' ▷ F.obj X := by
      aesop_cat
  oplax_right_unitality' :
    ∀ X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ' X (𝟙_ C) ≫ F.obj X ◁ η' := by
      aesop_cat

namespace OplaxMonoidal

section

variable [F.OplaxMonoidal]

/-- the counit morphism of a lax monoidal functor-/
def η : F.obj (𝟙_ C) ⟶ 𝟙_ D := η'

/-- the cotensorator of an oplax monoidal functor -/
def δ (X Y : C) : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y := δ' X Y

@[reassoc (attr := simp)]
lemma δ_natural_left {X Y : C} (f : X ⟶ Y) (X' : C) :
    δ F X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ F Y X' := by
  apply δ'_natural_left

@[reassoc (attr := simp)]
lemma δ_natural_right {X Y : C} (X' : C) (f : X ⟶ Y) :
    δ F X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ F X' Y := by
  apply δ'_natural_right

@[reassoc (attr := simp)]
lemma associativity (X Y Z : C) :
    δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z := by
  apply oplax_associativity'

@[simp, reassoc]
lemma left_unitality (X : C) :
    (λ_ (F.obj X)).inv = F.map (λ_ X).inv ≫ δ F (𝟙_ C) X ≫ η F ▷ F.obj X := by
  apply oplax_left_unitality'

@[simp, reassoc]
lemma right_unitality (X : C) :
    (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ F X (𝟙_ C) ≫ F.obj X ◁ η F := by
  apply oplax_right_unitality'

@[reassoc (attr := simp)]
theorem δ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
      δ F X X' ≫ (F.map f ⊗ F.map g) = F.map (f ⊗ g) ≫ δ F Y Y' := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
theorem left_unitality_hom  (X : C) :
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

end

instance id : (𝟭 C).OplaxMonoidal where
  η' := 𝟙 _
  δ' _ _ := 𝟙 _

@[simp]
lemma id_η : η (𝟭 C) = 𝟙 _ := rfl

@[simp]
lemma id_δ (X Y : C) : δ (𝟭 C) X Y = 𝟙 _ := rfl

section

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

instance comp : (F ⋙ G).OplaxMonoidal where
  η' := G.map (η F) ≫ η G
  δ' X Y := G.map (δ F X Y) ≫ δ G _ _
  δ'_natural_left {X Y} f X' := by
    dsimp
    rw [assoc, δ_natural_left, ← G.map_comp_assoc, δ_natural_left, map_comp, assoc]
  δ'_natural_right _ _ := by
    dsimp
    rw [assoc, δ_natural_right, ← G.map_comp_assoc, δ_natural_right, map_comp, assoc]
  oplax_associativity' X Y Z := by
    dsimp
    rw [comp_whiskerRight, assoc, assoc, assoc, δ_natural_left_assoc, associativity,
      ← G.map_comp_assoc, ← G.map_comp_assoc, assoc, associativity, map_comp, map_comp,
      assoc, assoc, MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc]

@[simp]
lemma comp_η : η (F ⋙ G) = G.map (η F) ≫ η G := rfl

@[simp]
lemma comp_δ (X Y : C) : δ (F ⋙ G) X Y = G.map (δ F X Y) ≫ δ G _ _ := rfl

end

end OplaxMonoidal

open LaxMonoidal OplaxMonoidal

class Monoidal extends F.LaxMonoidal, F.OplaxMonoidal where
  ε_η : ε F ≫ η F = 𝟙 _ := by aesop_cat
  η_ε : η F ≫ ε F = 𝟙 _ := by aesop_cat
  μ_δ (X Y : C) : μ F X Y ≫ δ F X Y = 𝟙 _ := by aesop_cat
  δ_μ (X Y : C) : δ F X Y ≫ μ F X Y = 𝟙 _ := by aesop_cat

namespace Monoidal

attribute [reassoc (attr := simp)] ε_η η_ε μ_δ δ_μ

section

variable [F.Monoidal]

@[simps]
def εIso : 𝟙_ D ≅ F.obj (𝟙_ C) where
  hom := ε F
  inv := η F

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
lemma whiskerRight_μ_δ (X Y : C) (T : D) : μ F X Y ▷ T ≫ δ F X Y▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, μ_δ, id_whiskerRight]

@[reassoc (attr := simp)]
lemma whiskerRight_δ_μ (X Y : C) (T : D) : δ F X Y ▷ T ≫ μ F X Y▷ T = 𝟙 _ := by
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
    F.map (f ⊗ g) = δ F X X' ≫ (F.map f ⊗ F.map g) ≫ μ F Y Y' := by simp

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
theorem map_leftUnitor (X : C) :
    F.map (λ_ X).hom = δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by simp

@[reassoc]
theorem map_leftUnitor_inv (X : C) :
    F.map (λ_ X).inv = (λ_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X  := by simp

@[reassoc]
theorem map_rightUnitor (X : C) :
    F.map (ρ_ X).hom = δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom := by simp

@[reassoc]
theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv = (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F  ≫ μ F X (𝟙_ C):= by simp

/-- The tensorator as a natural isomorphism. -/
@[simps!]
noncomputable def μNatIso :
    Functor.prod F F ⋙ tensor D ≅ tensor C ⋙ F :=
  NatIso.ofComponents (fun _ ↦ μIso F _ _)

/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
noncomputable def commTensorLeft (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F X Y)

/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
noncomputable def commTensorRight (X : C) :
    F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F Y X)

end

instance : (𝟭 C).Monoidal where

instance [F.Monoidal] [G.Monoidal] : (F ⋙ G).Monoidal where
  ε_η := by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp

end Monoidal

structure CoreMonoidal where
  /-- unit morphism -/
  εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  /-- tensorator -/
  μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  μIso_hom_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X') := by
    aesop_cat
  μIso_hom_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
          (μIso X (Y ⊗ Z)).hom := by
    aesop_cat
  -- unitality
  left_unitality :
    ∀ X : C, (λ_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by
      aesop_cat
  right_unitality :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by
    aesop_cat

namespace CoreMonoidal

attribute [reassoc (attr := simp)] μIso_hom_natural_left
  μIso_hom_natural_right associativity

attribute [reassoc] left_unitality right_unitality

variable {F} (h : F.CoreMonoidal)

def toLaxMonoidal : F.LaxMonoidal where
  ε' := h.εIso.hom
  μ' X Y := (h.μIso X Y).hom
  left_unitality' := h.left_unitality
  right_unitality' := h.right_unitality

@[simp]
lemma toLaxMonoidal_ε :
    letI := h.toLaxMonoidal
    LaxMonoidal.ε F = h.εIso.hom := rfl

@[simp]
lemma toLaxMonoidal_μ (X Y : C) :
    letI := h.toLaxMonoidal
    LaxMonoidal.μ F X Y = (h.μIso X Y).hom := rfl

def toOplaxMonoidal : F.OplaxMonoidal where
  η' := h.εIso.inv
  δ' X Y := (h.μIso X Y).inv
  δ'_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_left_assoc, Iso.hom_inv_id, comp_id]
  δ'_natural_right _ _ := by
    dsimp
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_right_assoc, Iso.hom_inv_id, comp_id]
  oplax_associativity' X Y Z := by
    dsimp
    rw [← cancel_epi (h.μIso (X ⊗ Y) Z).hom, Iso.hom_inv_id_assoc,
      ← cancel_epi ((h.μIso X Y).hom ▷ F.obj Z), hom_inv_whiskerRight_assoc,
      associativity_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv, comp_id]
  oplax_left_unitality' _ := by
    rw [← cancel_epi (λ_ _).hom, Iso.hom_inv_id, h.left_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc,hom_inv_whiskerRight]
  oplax_right_unitality' _ := by
    rw [← cancel_epi (ρ_ _).hom, Iso.hom_inv_id, h.right_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv]

@[simp]
lemma toOplaxMonoidal_η :
    letI := h.toOplaxMonoidal
    OplaxMonoidal.η F = h.εIso.inv := rfl

@[simp]
lemma toOplaxMonoidal_δ  (X Y : C) :
    letI := h.toOplaxMonoidal
    OplaxMonoidal.δ F X Y = (h.μIso X Y).inv := rfl

@[simps! toLaxMonoidal toOplaxMonoidal]
def toMonoidal : F.Monoidal where
  toLaxMonoidal := h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

variable (F)

noncomputable def ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :
    F.CoreMonoidal where
  εIso := asIso (ε F)
  μIso X Y := asIso (μ F X Y)

end CoreMonoidal

noncomputable def Monoidal.ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :=
  (CoreMonoidal.ofLaxMonoidal F).toMonoidal

section Prod

variable (F : C ⥤ D) (G : E ⥤ C') [MonoidalCategory C']

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

set_option maxHeartbeats 400000 in
instance : (prod F G).LaxMonoidal where
  ε' := (ε F, ε G)
  μ' X Y := (μ F _ _, μ G _ _)
  μ'_natural_left _ _ := by dsimp; simp
  μ'_natural_right _ _ := by dsimp; simp
  associativity' _ _ _ := by dsimp; ext <;> simp
  left_unitality' _ := by dsimp; ext <;> simp
  right_unitality' _ := by dsimp; ext <;> simp

@[simp]
lemma prod_ε : ε (prod F G) = (ε F, ε G) := rfl

@[simp]
lemma prod_μ_fst (X Y : C × E) : (μ (prod F G) X Y).1 = μ F _ _ := rfl

@[simp]
lemma prod_μ_snd (X Y : C × E) : (μ (prod F G) X Y).2 = μ G _ _ := rfl

end

section

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

instance : (prod F G).OplaxMonoidal where
  η' := (η F, η G)
  δ' X Y := (δ F _ _, δ G _ _)

@[simp]
lemma prod_η : η (prod F G) = (η F, η G) := rfl

@[simp]
lemma prod_δ_fst (X Y : C × E) : (δ (prod F G) X Y).1 = δ F _ _ := rfl

@[simp]
lemma prod_δ_snd (X Y : C × E) : (δ (prod F G) X Y).2 = δ G _ _ := rfl

end

set_option maxHeartbeats 800000 in
instance [F.Monoidal] [G.Monoidal] : (prod F G).Monoidal where
  ε_η := by dsimp; ext <;> dsimp <;> apply Monoidal.ε_η
  η_ε := by dsimp; ext <;> dsimp <;> apply Monoidal.η_ε
  μ_δ _ _ := by dsimp; ext <;> dsimp <;> apply Monoidal.μ_δ
  δ_μ _ _ := by dsimp; ext <;> dsimp <;> apply Monoidal.δ_μ

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

instance OplaxMonoidal.prod' : (prod' F G).OplaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

@[simp] lemma prod'_η_fst : (η (prod' F G)).1 = η F := by
  change F.map (𝟙 _)  ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

@[simp] lemma prod'_η_snd : (η (prod' F G)).2 = η G := by
  change G.map (𝟙 _)  ≫ _ = _
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

@[simp, reassoc]
lemma prod_comp_fst {C D : Type*} [Category C] [Category D]
    {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp, reassoc]
lemma prod_comp_snd {C D : Type*} [Category C] [Category D]
    {X Y Z : C × D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).2 = f.2 ≫ g.2 := rfl

instance Monoidal.prod' [F.Monoidal] [G.Monoidal] :
    (prod' F G).Monoidal where
  ε_η := by
    ext
    · simp only [prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · sorry
  η_ε := sorry
  μ_δ := sorry
  δ_μ := sorry

end Prod'

end Functor

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.OplaxMonoidal]

open Functor.OplaxMonoidal Functor.LaxMonoidal

def rightAdjointLaxMonoidal : G.LaxMonoidal where
  ε' := adj.homEquiv _ _ (η F)
  μ' X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X ⊗ adj.counit.app Y))
  μ'_natural_left {X Y} f X' := by
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    dsimp
    rw [← δ_natural_left_assoc]
    rw [tensorHom_def]
    simp
    --rw [map_comp,  map_comp, map_comp, map_comp, unit_naturality_assoc, assoc]
    --rw [← map_comp_assoc]
    --have pif := δ_natural_left F (𝟙 sorry)
    sorry
    --Equiv.apply_eq_iff_eq,
    --  assoc, IsIso.eq_inv_comp,
    --  ← F.toLaxMonoidalFunctor.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, tensorHom_def,
    --  ← comp_whiskerRight_assoc, Adjunction.counit_naturality, comp_whiskerRight_assoc,
    --  ← whisker_exchange, ← tensorHom_def_assoc]
  μ'_natural_right := sorry
  associativity' := sorry
  left_unitality' := sorry
  right_unitality' := sorry
--@[simp]
--noncomputable def monoidalAdjoint :
--    LaxMonoidalFunctor D C where
--  toFunctor := G
--  ε := h.homEquiv _ _ (inv F.ε)
--  μ := fun X Y =>
--    h.homEquiv _ _ (inv (F.μ (G.obj X) (G.obj Y)) ≫ (h.counit.app X ⊗ h.counit.app Y))
--  μ_natural_left {X Y} f X' := by
--    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
--      assoc, IsIso.eq_inv_comp,
--      ← F.toLaxMonoidalFunctor.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, tensorHom_def,
--      ← comp_whiskerRight_assoc, Adjunction.counit_naturality, comp_whiskerRight_assoc,
--      ← whisker_exchange, ← tensorHom_def_assoc]
--  μ_natural_right {X Y} X' f := by
--    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
--      assoc, IsIso.eq_inv_comp,
--      ← F.toLaxMonoidalFunctor.μ_natural_right_assoc, IsIso.hom_inv_id_assoc, tensorHom_def',
--      ← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.counit_naturality, whisker_exchange,
--      MonoidalCategory.whiskerLeft_comp, ← tensorHom_def_assoc]
--  associativity X Y Z := by
--    dsimp only
--    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left,
--      ← h.homEquiv_naturality_left, Equiv.apply_eq_iff_eq,
--      ← cancel_epi (F.μ (G.obj X ⊗ G.obj Y) (G.obj Z)),
--      ← cancel_epi (F.μ (G.obj X) (G.obj Y) ▷ (F.obj (G.obj Z)))]
--    simp only [assoc]
--    calc
--      _ = (α_ _ _ _).hom ≫ (h.counit.app X ⊗ h.counit.app Y ⊗ h.counit.app Z) := by
--        rw [← F.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, h.homEquiv_unit,
--          tensorHom_def_assoc (h.counit.app (X ⊗ Y)) (h.counit.app Z)]
--        dsimp only [comp_obj, id_obj]
--        simp_rw [← MonoidalCategory.comp_whiskerRight_assoc]
--        rw [F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc,
--          IsIso.hom_inv_id_assoc, ← tensorHom_def_assoc, associator_naturality]
--      _ = _ := by
--        rw [F.associativity_assoc, ← F.μ_natural_right_assoc, IsIso.hom_inv_id_assoc,
--          h.homEquiv_unit, tensorHom_def (h.counit.app X) (h.counit.app (Y ⊗ Z))]
--        dsimp only [id_obj, comp_obj]
--        rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp, F.map_comp_assoc,
--          h.counit_naturality, h.left_triangle_components_assoc, whisker_exchange_assoc,
--          ← MonoidalCategory.whiskerLeft_comp, ← tensorHom_def, IsIso.hom_inv_id_assoc]
--  left_unitality X := by
--    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
--      h.homEquiv_counit, F.map_leftUnitor_assoc, h.homEquiv_unit, F.map_whiskerRight_assoc, assoc,
--      IsIso.hom_inv_id_assoc, tensorHom_def_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
--      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
--    simp
--  right_unitality X := by
--    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
--      h.homEquiv_counit, F.map_rightUnitor_assoc, h.homEquiv_unit, F.map_whiskerLeft_assoc, assoc,
--      IsIso.hom_inv_id_assoc, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
--      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
--    simp

lemma rightAdjointLaxMonoidal_ε :
    letI := adj.rightAdjointLaxMonoidal
    ε G = adj.homEquiv _ _ (η F) := rfl

lemma rightAdjointLaxMonoidal_μ (X Y : D) :
    letI := adj.rightAdjointLaxMonoidal
    μ G X Y = adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X ⊗ adj.counit.app Y)) := rfl

class IsMonoidal [G.LaxMonoidal] : Prop where
  leftAdjoint_ε : ε G = adj.homEquiv _ _ (η F) := by aesop_cat
  leftAdjoint_μ (X Y : D) :
    μ G X Y = adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X ⊗ adj.counit.app Y)) := by aesop_cat

instance :
    letI := adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  letI := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

end Adjunction

namespace Equivalence

variable (e : C ≌ D) [e.functor.Monoidal]

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
noncomputable def inverseMonoidal : e.inverse.Monoidal := by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    dsimp [Adjunction.rightAdjointLaxMonoidal_ε]
    infer_instance
  have : ∀ (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y ↦ by
    dsimp [Adjunction.rightAdjointLaxMonoidal_μ]
    infer_instance
  apply Monoidal.ofLaxMonoidal

abbrev IsMonoidal [e.inverse.Monoidal] : Prop := e.toAdjunction.IsMonoidal

end Equivalence

end CategoryTheory
