/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Products.Basic

#align_import category_theory.monoidal.functor from "leanprover-community/mathlib"@"3d7987cda72abc473c7cdbbb075170e9ac620042"

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).
satisfying various axioms.

A monoidal functor is a lax monoidal functor for which `ε` and `μ` are isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See also `CategoryTheory.Monoidal.Functorial` for a typeclass decorating an object-level
function with the additional data of a monoidal functor.
This is useful when stating that a pre-existing functor is monoidal.

See `CategoryTheory.Monoidal.NaturalTransformation` for monoidal natural transformations.

We show in `CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## Future work
* Oplax monoidal functors.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/


open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Category

open CategoryTheory.Functor

namespace CategoryTheory

section

open MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  [MonoidalCategory.{v₂} D]

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A lax monoidal functor is a functor `F : C ⥤ D` between monoidal categories,
equipped with morphisms `ε : 𝟙 _D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences. -/
structure LaxMonoidalFunctor extends C ⥤ D where
  /-- unit morphism -/
  ε : 𝟙_ D ⟶ obj (𝟙_ C)
  /-- tensorator -/
  μ : ∀ X Y : C, obj X ⊗ obj Y ⟶ obj (X ⊗ Y)
  μ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      (map f ⊗ 𝟙 (obj X')) ≫ μ Y X' = μ X X' ≫ map (f ⊗ 𝟙 X') := by
    aesop_cat
  μ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      (𝟙 (obj X') ⊗ map f) ≫ μ X' Y = μ X' X ≫ map (𝟙 X' ⊗ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      (μ X Y ⊗ 𝟙 (obj Z)) ≫ μ (X ⊗ Y) Z ≫ map (α_ X Y Z).hom =
        (α_ (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
    aesop_cat
  -- unitality
  left_unitality : ∀ X : C, (λ_ (obj X)).hom = (ε ⊗ 𝟙 (obj X)) ≫ μ (𝟙_ C) X ≫ map (λ_ X).hom :=
    by aesop_cat
  right_unitality : ∀ X : C, (ρ_ (obj X)).hom = (𝟙 (obj X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ map (ρ_ X).hom :=
    by aesop_cat
#align category_theory.lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor

-- Porting note: todo: remove this configuration and use the default configuration.
-- We keep this to be consistent with Lean 3.
-- See also `initialize_simps_projections MonoidalFunctor` below.
-- This may require waiting on https://github.com/leanprover-community/mathlib4/pull/2936
initialize_simps_projections LaxMonoidalFunctor (+toFunctor, -obj, -map)

--Porting note: was `[simp, reassoc.1]`
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_left
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_right

attribute [simp] LaxMonoidalFunctor.left_unitality

attribute [simp] LaxMonoidalFunctor.right_unitality

--Porting note: was `[simp, reassoc.1]`
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.associativity

-- When `rewrite_search` lands, add @[search] attributes to
-- LaxMonoidalFunctor.μ_natural LaxMonoidalFunctor.left_unitality
-- LaxMonoidalFunctor.right_unitality LaxMonoidalFunctor.associativity
section

variable {C D}

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.μ_natural (F : LaxMonoidalFunctor C D) {X Y X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
      (F.map f ⊗ F.map g) ≫ F.μ Y Y' = F.μ X X' ≫ F.map (f ⊗ g) := by
  rw [tensorHom_def, ← id_tensorHom, ← tensorHom_id]
  simp only [assoc, μ_natural_right, μ_natural_left_assoc]
  rw [← F.map_comp, tensor_id_comp_id_tensor]

/-- The tensorator of a lax monoidal functor as a natural transformation. -/
@[simps]
def LaxMonoidalFunctor.μNatTrans (F : LaxMonoidalFunctor C D) :
    .prod F.toFunctor F.toFunctor ⋙ tensor D ⟶ tensor C ⋙ F.toFunctor where
  app XY := F.μ XY.1 XY.2

@[reassoc (attr := simp)]
theorem  LaxMonoidalFunctor.associativity' (F : LaxMonoidalFunctor C D) (X Y Z : C) :
    (F.μ X Y ▷ F.obj Z) ≫ F.μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ ((F.obj X) ◁ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
theorem  LaxMonoidalFunctor.left_unitality' (F : LaxMonoidalFunctor C D) (X : C) :
    (λ_ (F.obj X)).hom = (F.ε ▷ F.obj X) ≫ F.μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc]
theorem  LaxMonoidalFunctor.right_unitality' (F : LaxMonoidalFunctor C D) (X : C) :
    (ρ_ (F.obj X)).hom = (F.obj X ◁ F.ε) ≫ F.μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.μ_natural_left' (F : LaxMonoidalFunctor C D)
    {X Y : C} (f : X ⟶ Y) (X' : C) :
      F.map f ▷ F.obj X' ≫ F.μ Y X' = F.μ X X' ≫ F.map (f ▷ X') := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.μ_natural_right' (F : LaxMonoidalFunctor C D)
    {X Y : C} (X' : C) (f : X ⟶ Y) :
      F.obj X' ◁ F.map f ≫ F.μ X' Y = F.μ X' X ≫ F.map (X' ◁ f) := by
  simp [← id_tensorHom, ← tensorHom_id]

/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[simps]
def LaxMonoidalFunctor.ofTensorHom (F : C ⥤ D)
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (μ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f ⊗ F.map g) ≫ μ Y Y' = μ X X' ≫ F.map (f ⊗ g) := by
      aesop_cat)
    /- associativity of the tensorator -/
    (associativity :
      ∀ X Y Z : C,
        (μ X Y ⊗ 𝟙 (F.obj Z)) ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z) := by
      aesop_cat)
    /- unitality -/
    (left_unitality :
      ∀ X : C, (λ_ (F.obj X)).hom = (ε ⊗ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom :=
        by aesop_cat)
    (right_unitality :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom :=
        by aesop_cat) :
        LaxMonoidalFunctor C D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp
  ε := ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [associativity]
  left_unitality := fun X => by
    simp_rw [left_unitality]
  right_unitality := fun X => by
    simp_rw [right_unitality]

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.left_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (λ_ (F.obj X)).inv ≫ (F.ε ⊗ 𝟙 (F.obj X)) ≫ F.μ (𝟙_ C) X = F.map (λ_ X).inv := by
  rw [Iso.inv_comp_eq, F.left_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.left_unitality_inv CategoryTheory.LaxMonoidalFunctor.left_unitality_inv

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.right_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (ρ_ (F.obj X)).inv ≫ (𝟙 (F.obj X) ⊗ F.ε) ≫ F.μ X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq, F.right_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.right_unitality_inv CategoryTheory.LaxMonoidalFunctor.right_unitality_inv

--Porting note: was `[simp, reassoc.1]`
@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.associativity_inv (F : LaxMonoidalFunctor C D) (X Y Z : C) :
    (𝟙 (F.obj X) ⊗ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (F.μ X Y ⊗ 𝟙 (F.obj Z)) ≫ F.μ (X ⊗ Y) Z := by
  rw [Iso.eq_inv_comp, ← F.associativity_assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, comp_id]
#align category_theory.lax_monoidal_functor.associativity_inv CategoryTheory.LaxMonoidalFunctor.associativity_inv

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.left_unitality_inv' (F : LaxMonoidalFunctor C D) (X : C) :
    (λ_ (F.obj X)).inv ≫ (F.ε ▷ F.obj X) ≫ F.μ (𝟙_ C) X = F.map (λ_ X).inv := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.right_unitality_inv' (F : LaxMonoidalFunctor C D) (X : C) :
    (ρ_ (F.obj X)).inv ≫ (F.obj X ◁ F.ε) ≫ F.μ X (𝟙_ C) = F.map (ρ_ X).inv := by
  simp [← id_tensorHom, ← tensorHom_id]

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.associativity_inv' (F : LaxMonoidalFunctor C D) (X Y Z : C) :
    (F.obj X ◁ F.μ Y Z) ≫ F.μ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ (F.μ X Y ▷ F.obj Z) ≫ F.μ (X ⊗ Y) Z := by
  simp [← id_tensorHom, ← tensorHom_id]

end

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor as isomorphisms.

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/
structure MonoidalFunctor extends LaxMonoidalFunctor.{v₁, v₂} C D where
  private ε_inv : obj (𝟙_ C) ⟶ 𝟙_ D
  private μ_inv : (X Y : C) → obj (X ⊗ Y) ⟶ obj X ⊗ obj Y
  private ε_hom_inv_id : ε ≫ ε_inv = 𝟙 (𝟙_ D) := by aesop_cat
  private ε_inv_hom_id : ε_inv ≫ ε = 𝟙 (obj (𝟙_ C)) := by aesop_cat
  private μ_hom_inv_id : (X Y : C) → μ X Y ≫ μ_inv X Y = 𝟙 (obj X ⊗ obj Y) := by aesop_cat
  private μ_inv_hom_id : (X Y : C) → μ_inv X Y ≫ μ X Y = 𝟙 (obj (X ⊗ Y)) := by aesop_cat
#align category_theory.monoidal_functor CategoryTheory.MonoidalFunctor
-- See porting note on `initialize_simps_projections LaxMonoidalFunctor`
initialize_simps_projections MonoidalFunctor (+toLaxMonoidalFunctor, -obj, -map, -ε, -μ)

variable {C D}

namespace MonoidalFunctor

section projections

variable (F : MonoidalFunctor.{v₁, v₂} C D)

/-- The unit morphism of a (strong) monoidal functor as an isomorphism. -/
@[pp_dot]
def εIso : 𝟙_ D ≅ F.obj (𝟙_ C) :=
  ⟨F.ε, F.ε_inv, F.ε_hom_inv_id, F.ε_inv_hom_id⟩
#align category_theory.monoidal_functor.ε_iso CategoryTheory.MonoidalFunctor.εIso

@[simp] lemma ε_eq_εIso_hom : F.ε = F.εIso.hom := rfl
@[simp] private lemma ε_inv_eq_εIso_inv : F.ε_inv = F.εIso.inv := rfl

/-- The tensorator of a (strong) monoidal functor as a natural isomorphism. -/
@[pp_dot]
def μNatIso : .prod F.toFunctor F.toFunctor ⋙ tensor D ≅ tensor C ⋙ F.toFunctor :=
  NatIso.ofComponents (fun XY => ⟨F.μ XY.1 XY.2, F.μ_inv XY.1 XY.2,
                                  F.μ_hom_inv_id XY.1 XY.2, F.μ_inv_hom_id XY.1 XY.2⟩)
                      (fun f => F.μ_natural f.1 f.2)
#align category_theory.monoidal_functor.μ_nat_iso CategoryTheory.MonoidalFunctor.μNatIso

/-- The tensorator of a (strong) monoidal functor as a pointwise isomorphism.
We set up simp lemmas such that μNatIso and μ appear to be derived from μIso. -/
@[pp_dot]
def μIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) :=
  F.μNatIso.app (X, Y)
#align category_theory.monoidal_functor.μ_iso CategoryTheory.MonoidalFunctor.μIso

@[simp] lemma μ_eq_μIso_hom (X Y : C) : F.μ X Y = (F.μIso X Y).hom := rfl
@[simp] private lemma μ_inv_eq_μIso_inv (X Y : C) : F.μ_inv X Y = (F.μIso X Y).inv := rfl

@[simp] lemma μNatIso_app_eq_μIso (X Y : C) : F.μNatIso.app (X, Y) = F.μIso X Y := rfl
@[simp] lemma μNatTrans_eq_μNatIso_hom : F.μNatTrans = F.μNatIso.hom := rfl

@[simp]
lemma μNatIso_hom_app_eq_μIso_hom (X Y : C) :
    F.μNatIso.hom.app (X, Y) = (F.μIso X Y).hom := rfl

@[simp]
lemma μNatIso_inv_app_eq_μIso_inv (X Y : C) :
    F.μNatIso.inv.app (X, Y) = (F.μIso X Y).inv := rfl

@[reassoc (attr := simp)]
theorem μIso_hom_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ F.map g) ≫ (F.μIso Y Y').hom = (F.μIso X X').hom ≫ F.map (f ⊗ g) :=
  let fg : (X, X') ⟶ (Y, Y') := (f, g)
  F.μNatIso.hom.naturality fg

@[reassoc (attr := simp)]
theorem μIso_inv_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ g) ≫ (F.μIso Y Y').inv = (F.μIso X X').inv ≫ (F.map f ⊗ F.map g) :=
  let fg : (X, X') ⟶ (Y, Y') := (f, g)
  F.μNatIso.inv.naturality fg

@[reassoc (attr := simp)]
lemma μIso_hom_natural_left {X Y} (f : X ⟶ Y) (X' : C) :
    (F.map f ⊗ 𝟙 (F.obj X')) ≫ (F.μIso Y X').hom =
      (F.μIso X X').hom ≫ F.map (f ⊗ 𝟙 X') :=
  F.map_id X' ▸ F.μIso_hom_natural f (𝟙 X')

@[reassoc (attr := simp)]
lemma μIso_hom_natural_right {X Y} (X' : C) (f : X ⟶ Y) :
    (𝟙 (F.obj X') ⊗ F.map f) ≫ (F.μIso X' Y).hom =
      (F.μIso X' X).hom ≫ F.map (𝟙 X' ⊗ f) :=
  F.map_id X' ▸ F.μIso_hom_natural (𝟙 X') f

-- can't be simp bc it follows from `μIso_inv_natural` and `map_id`
@[reassoc]
lemma μIso_inv_natural_left {X Y} (f : X ⟶ Y) (X' : C) :
    F.map (f ⊗ 𝟙 X') ≫ (F.μIso Y X').inv =
      (F.μIso X X').inv ≫ (F.map f ⊗ 𝟙 (F.obj X')) :=
  by simp only [@μIso_inv_natural, @map_id]

@[reassoc]
lemma μIso_inv_natural_right {X Y} (X' : C) (f : X ⟶ Y) :
    F.map (𝟙 X' ⊗ f) ≫ (F.μIso X' Y).inv =
      (F.μIso X' X).inv ≫ (𝟙 (F.obj X') ⊗ F.map f) :=
  F.map_id X' ▸ F.μIso_inv_natural (𝟙 X') f

@[reassoc (attr := simp)]
lemma μIso_hom_natural_left' {X Y} (f : X ⟶ Y) (X' : C) :
    (F.map f ▷ F.obj X') ≫ (F.μIso Y X').hom =
      (F.μIso X X').hom ≫ F.map (f ▷ X') := by
  convert (config := .unfoldSameFun) F.μIso_hom_natural_left f X'
  <;> exact (tensorHom_id _ _).symm

@[reassoc (attr := simp)]
lemma μIso_hom_natural_right' {X Y} (X' : C) (f : X ⟶ Y) :
    (F.obj X' ◁ F.map f) ≫ (F.μIso X' Y).hom =
      (F.μIso X' X).hom ≫ F.map (X' ◁ f) := by
  convert (config := .unfoldSameFun) F.μIso_hom_natural_right X' f
  <;> exact (id_tensorHom _ _).symm

@[reassoc (attr := simp)]
lemma μIso_inv_natural_left' {X Y} (f : X ⟶ Y) (X' : C) :
    F.map (f ▷ X') ≫ (F.μIso Y X').inv =
      (F.μIso X X').inv ≫ (F.map f ▷ F.obj X') := by
  convert (config := .unfoldSameFun) F.μIso_inv_natural_left f X'
  <;> exact (tensorHom_id _ _).symm

@[reassoc (attr := simp)]
lemma μIso_inv_natural_right' {X Y} (X' : C) (f : X ⟶ Y) :
    F.map (X' ◁ f) ≫ (F.μIso X' Y).inv =
      (F.μIso X' X).inv ≫ (F.obj X' ◁ F.map f) := by
  convert (config := .unfoldSameFun) F.μIso_inv_natural_right X' f
  <;> exact (id_tensorHom _ _).symm

@[simp]
theorem associativity_iso (X Y Z : C) :
    (tensorRight (F.obj Z)).mapIso (F.μIso X Y) ≪≫
        F.μIso (X ⊗ Y) Z ≪≫ F.mapIso (α_ X Y Z) =
      α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫
        (tensorLeft (F.obj X)).mapIso (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) :=
  Iso.ext (F.associativity X Y Z)

@[reassoc (attr := simp)]
theorem associativity_μIso_hom (X Y Z : C) :
    ((F.μIso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫ (F.μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ (F.μIso Y Z).hom) ≫
        (F.μIso X (Y ⊗ Z)).hom :=
  congrArg Iso.hom (F.associativity_iso X Y Z)

@[reassoc (attr := simp)]
theorem associativity_μIso_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv ≫ (F.μIso (X ⊗ Y) Z).inv ≫ ((F.μIso X Y).inv ⊗ 𝟙 (F.obj Z)) =
      (F.μIso X (Y ⊗ Z)).inv ≫ (𝟙 (F.obj X) ⊗ (F.μIso Y Z).inv) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  convert congrArg Iso.inv (F.associativity_iso X Y Z) using 1
  <;> exact (assoc _ _ _).symm

@[simp]
theorem associativity'_iso (X Y Z : C) :
    whiskerRightIso (F.μIso X Y) (F.obj Z) ≪≫
        F.μIso (X ⊗ Y) Z ≪≫ F.mapIso (α_ X Y Z) =
      α_ (F.obj X) (F.obj Y) (F.obj Z) ≪≫
        whiskerLeftIso (F.obj X) (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) :=
  Iso.ext (F.associativity' X Y Z)

@[reassoc (attr := simp)]
theorem associativity'_μIso_hom (X Y Z : C) :
    ((F.μIso X Y).hom ▷ F.obj Z) ≫ (F.μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ ((F.obj X) ◁ (F.μIso Y Z).hom) ≫
        (F.μIso X (Y ⊗ Z)).hom :=
  congrArg Iso.hom (F.associativity'_iso X Y Z)

@[reassoc (attr := simp)]
theorem associativity'_μIso_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv ≫ (F.μIso (X ⊗ Y) Z).inv ≫ ((F.μIso X Y).inv ▷ F.obj Z) =
      (F.μIso X (Y ⊗ Z)).inv ≫ ((F.obj X) ◁ (F.μIso Y Z).inv) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  convert congrArg Iso.inv (F.associativity'_iso X Y Z) using 1
  <;> exact (assoc _ _ _).symm

@[simp]
theorem associativity_symm_iso (X Y Z : C) :
    (tensorLeft (F.obj X)).mapIso (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) ≪≫
      F.mapIso (α_ X Y Z).symm =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm ≪≫
      (tensorRight (F.obj Z)).mapIso (F.μIso X Y) ≪≫ F.μIso (X ⊗ Y) Z := by
  exact Iso.ext (F.toLaxMonoidalFunctor.associativity_inv X Y Z)

@[reassoc (attr := simp)]
theorem associativity_inv_μIso_hom (X Y Z : C) :
    (𝟙 (F.obj X) ⊗ (F.μIso Y Z).hom) ≫ (F.μIso X (Y ⊗ Z)).hom ≫
      F.map (α_ X Y Z).inv =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ ((F.μIso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫
      (F.μIso (X ⊗ Y) Z).hom :=
  congrArg Iso.hom (F.associativity_symm_iso X Y Z)

@[reassoc (attr := simp)]
theorem associativity_inv_μIso_inv (X Y Z : C) :
    F.map (α_ X Y Z).hom ≫ (F.μIso X (Y ⊗ Z)).inv ≫
      (𝟙 (F.obj X) ⊗ (F.μIso Y Z).inv) =
    (F.μIso (X ⊗ Y) Z).inv ≫ ((F.μIso X Y).inv ⊗ 𝟙 (F.obj Z)) ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  convert congrArg Iso.inv (F.associativity_symm_iso X Y Z) using 1
  <;> exact (assoc _ _ _).symm

@[simp]
theorem associativity_symm'_iso (X Y Z : C) :
    whiskerLeftIso (F.obj X) (F.μIso Y Z) ≪≫ F.μIso X (Y ⊗ Z) ≪≫
      F.mapIso (α_ X Y Z).symm =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).symm ≪≫
      whiskerRightIso (F.μIso X Y) (F.obj Z) ≪≫ F.μIso (X ⊗ Y) Z := by
  exact Iso.ext (F.toLaxMonoidalFunctor.associativity_inv' X Y Z)

@[reassoc (attr := simp)]
theorem associativity_inv'_μIso_hom (X Y Z : C) :
    (F.obj X ◁ (F.μIso Y Z).hom) ≫ (F.μIso X (Y ⊗ Z)).hom ≫
      F.map (α_ X Y Z).inv =
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ ((F.μIso X Y).hom ▷ F.obj Z) ≫
      (F.μIso (X ⊗ Y) Z).hom :=
  congrArg Iso.hom (F.associativity_symm'_iso X Y Z)

@[reassoc (attr := simp)]
theorem associativity_inv'_μIso_inv (X Y Z : C) :
    F.map (α_ X Y Z).hom ≫ (F.μIso X (Y ⊗ Z)).inv ≫
      (F.obj X ◁ (F.μIso Y Z).inv) =
    (F.μIso (X ⊗ Y) Z).inv ≫ ((F.μIso X Y).inv ▷ F.obj Z) ≫
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  convert congrArg Iso.inv (F.associativity_symm'_iso X Y Z) using 1
  <;> exact (assoc _ _ _).symm

@[simp]
theorem left_unitality_iso (X : C) :
    λ_ (F.obj X) = (tensorRight (F.obj X)).mapIso F.εIso ≪≫ F.μIso (𝟙_ C) X ≪≫
      F.mapIso (λ_ X) := Iso.ext (F.left_unitality X)

@[simp]
theorem right_unitality_iso (X : C) :
    ρ_ (F.obj X) = (tensorLeft (F.obj X)).mapIso F.εIso ≪≫ F.μIso X (𝟙_ C) ≪≫
      F.mapIso (ρ_ X) := Iso.ext (F.right_unitality X)

theorem left_unitality_μIso_inv (X : C) :
    (λ_ (F.obj X)).inv =
      F.map (λ_ X).inv ≫ (F.μIso (𝟙_ C) X).inv ≫ (F.εIso.inv ⊗ 𝟙 (F.obj X)) := by
  convert congrArg Iso.inv (F.left_unitality_iso X) using 1
  exact (assoc _ _ _).symm

theorem right_unitality_μIso_inv (X : C) :
    (ρ_ (F.obj X)).inv =
      F.map (ρ_ X).inv ≫ (F.μIso X (𝟙_ C)).inv ≫ (𝟙 (F.obj X) ⊗ F.εIso.inv) := by
  convert congrArg Iso.inv (F.right_unitality_iso X) using 1
  exact (assoc _ _ _).symm

theorem left_unitality'_iso (X : C) :
    λ_ (F.obj X) = whiskerRightIso F.εIso (F.obj X) ≪≫ F.μIso (𝟙_ C) X ≪≫
      F.mapIso (λ_ X) := Iso.ext (F.left_unitality' X)

theorem right_unitality'_iso (X : C) :
    ρ_ (F.obj X) = whiskerLeftIso (F.obj X) F.εIso ≪≫ F.μIso X (𝟙_ C) ≪≫
      F.mapIso (ρ_ X) := Iso.ext (F.right_unitality' X)

@[reassoc]
theorem left_unitality'_μIso_inv (X : C) :
    (λ_ (F.obj X)).inv =
      F.map (λ_ X).inv ≫ (F.μIso (𝟙_ C) X).inv ≫ (F.εIso.inv ▷ F.obj X) := by
  convert congrArg Iso.inv (F.left_unitality'_iso X) using 1
  exact (assoc _ _ _).symm

@[reassoc]
theorem right_unitality'_μIso_inv (X : C) :
    (ρ_ (F.obj X)).inv =
      F.map (ρ_ X).inv ≫ (F.μIso X (𝟙_ C)).inv ≫ (F.obj X ◁ F.εIso.inv) := by
  convert congrArg Iso.inv (F.right_unitality'_iso X) using 1
  exact (assoc _ _ _).symm

end projections

-- should there be a version which takes μIso as a natural isomorphism?
/-- Make a strong monoidal functor from ε, μ given as isomorphisms. -/
@[simps! toLaxMonoidalFunctor_toFunctor]
def mk' (F : C ⥤ D) (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μIso : (X Y : C) → F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
    (μ_natural_left : ∀ {X Y} (f : X ⟶ Y) (X' : C),
      (F.map f ⊗ 𝟙 (F.obj X')) ≫ (μIso Y X').hom =
        (μIso X X').hom ≫ F.map (f ⊗ 𝟙 X') := by aesop_cat)
    (μ_natural_right : ∀ {X Y} (X' : C) (f : X ⟶ Y),
      (𝟙 (F.obj X') ⊗ F.map f) ≫ (μIso X' Y).hom =
        (μIso X' X).hom ≫ F.map (𝟙 X' ⊗ f) := by aesop_cat)
    (associativity : ∀ X Y Z,
      ((μIso X Y).hom ⊗ 𝟙 (F.obj Z)) ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ (μIso Y Z).hom) ≫
          (μIso X (Y ⊗ Z)).hom := by aesop_cat)
    (left_unitality : ∀ X, (λ_ (F.obj X)).hom =
      (εIso.hom ⊗ 𝟙 (F.obj X)) ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by aesop_cat)
    (right_unitality : ∀ X, (ρ_ (F.obj X)).hom =
      (𝟙 (F.obj X) ⊗ εIso.hom) ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by aesop_cat)
    : MonoidalFunctor C D where
  ε := εIso.hom
  ε_inv := εIso.inv
  μ X Y := (μIso X Y).hom
  μ_inv X Y := (μIso X Y).inv
  __ := F

@[simp] lemma mk'_εIso (F : C ⥤ D) εIso μIso h1 h2 h3 h4 h5 :
    (MonoidalFunctor.mk' F εIso μIso h1 h2 h3 h4 h5).εIso = εIso := rfl

@[simp] lemma mk'_μIso (F : C ⥤ D) εIso μIso h1 h2 h3 h4 h5 :
    (MonoidalFunctor.mk' F εIso μIso h1 h2 h3 h4 h5).μIso = μIso := rfl

@[simp] lemma mk'_obj  (F : C ⥤ D) εIso μIso h1 h2 h3 h4 h5 X:
    (MonoidalFunctor.mk' F εIso μIso h1 h2 h3 h4 h5).obj X = F.obj X := rfl

@[simp] lemma mk'_map  (F : C ⥤ D) εIso μIso h1 h2 h3 h4 h5 {X Y} (f : X ⟶ Y) :
    (MonoidalFunctor.mk' F εIso μIso h1 h2 h3 h4 h5).map f = F.map f := rfl

end MonoidalFunctor

end

open MonoidalCategory

namespace LaxMonoidalFunctor

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- The identity lax monoidal functor. -/
@[simps]
def id : LaxMonoidalFunctor.{v₁, v₁} C C :=
  { 𝟭 C with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }
#align category_theory.lax_monoidal_functor.id CategoryTheory.LaxMonoidalFunctor.id

instance : Inhabited (LaxMonoidalFunctor C C) :=
  ⟨id C⟩

end LaxMonoidalFunctor

namespace MonoidalFunctor

section

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable (F : MonoidalFunctor.{v₁, v₂} C D)

theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ g) = (F.μIso X X').inv ≫ (F.map f ⊗ F.map g) ≫ F.μ Y Y' := by simp
#align category_theory.monoidal_functor.map_tensor CategoryTheory.MonoidalFunctor.map_tensor

-- Note: `𝟙 X ⊗ f` will be replaced by `X ◁ f` in #6307.
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (𝟙 X ⊗ f) = (F.μIso X Y).inv ≫ (𝟙 (F.obj X) ⊗ F.map f) ≫ (F.μIso X Z).hom := by simp

-- Note: `f ⊗ 𝟙 Z` will be replaced by `f ▷ Z` in #6307.
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ⊗ 𝟙 Z) = (F.μIso X Z).inv ≫ (F.map f ⊗ 𝟙 (F.obj Z)) ≫ (F.μIso Y Z).hom := by simp

theorem mapIso_leftUnitor (X : C) :
    F.mapIso (λ_ X) = (F.μIso (𝟙_ C) X).symm ≪≫
      (tensorRight (F.obj X)).mapIso F.εIso.symm ≪≫ λ_ (F.obj X) := by simp

theorem map_leftUnitor_hom (X : C) :
    F.map (λ_ X).hom =
      (F.μIso (𝟙_ C) X).inv ≫ (F.εIso.inv ⊗ 𝟙 (F.obj X)) ≫ (λ_ (F.obj X)).hom :=
  congrArg Iso.hom (F.mapIso_leftUnitor X)
#align category_theory.monoidal_functor.map_left_unitor CategoryTheory.MonoidalFunctor.map_leftUnitor_hom

theorem map_leftUnitor_inv (X : C) :
    F.map (λ_ X).inv =
      (λ_ (F.obj X)).inv ≫ (F.εIso.hom ⊗ 𝟙 (F.obj X)) ≫ (F.μIso (𝟙_ C) X).hom := by
  convert congrArg Iso.inv (F.mapIso_leftUnitor X)
  exact (assoc _ _ _).symm

theorem mapIso_rightUnitor (X : C) :
    F.mapIso (ρ_ X) = (F.μIso X (𝟙_ C)).symm ≪≫
      (tensorLeft (F.obj X)).mapIso F.εIso.symm ≪≫ ρ_ (F.obj X) := by simp

theorem map_rightUnitor_hom (X : C) :
    F.map (ρ_ X).hom =
      (F.μIso X (𝟙_ C)).inv ≫ (𝟙 (F.obj X) ⊗ F.εIso.inv) ≫ (ρ_ (F.obj X)).hom :=
  congrArg Iso.hom (F.mapIso_rightUnitor X)
#align category_theory.monoidal_functor.map_right_unitor CategoryTheory.MonoidalFunctor.map_rightUnitor_hom

theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv =
      (ρ_ (F.obj X)).inv ≫ (𝟙 (F.obj X) ⊗ F.εIso.hom) ≫ (F.μIso X (𝟙_ C)).hom := by
  convert congrArg Iso.inv (F.mapIso_rightUnitor X)
  exact (assoc _ _ _).symm

/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
def commTensorLeft (X : C) :
    F.toFunctor ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso X Y) fun f => F.μ_natural_right X f
#align category_theory.monoidal_functor.comm_tensor_left CategoryTheory.MonoidalFunctor.commTensorLeft

/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
def commTensorRight (X : C) :
    F.toFunctor ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso Y X) fun f => F.μ_natural_left f X
#align category_theory.monoidal_functor.comm_tensor_right CategoryTheory.MonoidalFunctor.commTensorRight

end

section

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- The identity monoidal functor. -/
def id : MonoidalFunctor.{v₁, v₁} C C :=
  .mk' (𝟭 C) (Iso.refl _) (fun _ _ => Iso.refl _)
#align category_theory.monoidal_functor.id CategoryTheory.MonoidalFunctor.id

instance : Inhabited (MonoidalFunctor C C) :=
  ⟨id C⟩

-- is this safe?
@[simp]
lemma id_toLaxMonoidalFunctor_eq_id :
    (id C).toLaxMonoidalFunctor = LaxMonoidalFunctor.id C := rfl

-- can we hook into simps and make this generated automatically?
@[simp] lemma id_εIso : (id C).εIso = Iso.refl (𝟙_ C) := rfl

variable {C}
@[simp] lemma id_μIso (X Y : C) : (id C).μIso X Y = Iso.refl (X ⊗ Y) := rfl

end

end MonoidalFunctor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{v₁, v₂} C D) (G : LaxMonoidalFunctor.{v₂, v₃} D E)

-- The proofs here are horrendous; rewrite_search helps a lot.
/-- The composition of two lax monoidal functors is again lax monoidal. -/
@[simps]
def comp : LaxMonoidalFunctor.{v₁, v₃} C E :=
  { F.toFunctor ⋙ G.toFunctor with
    ε := G.ε ≫ G.map F.ε
    μ := fun X Y => G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y)
    μ_natural_left := by
      intro X Y f X'
      simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
    μ_natural_right := by
      intro X Y f X'
      simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]
    associativity := fun X Y Z => by
      dsimp
      rw [id_tensor_comp]
      slice_rhs 3 4 => rw [← G.map_id, G.μ_natural]
      slice_rhs 1 3 => rw [← G.associativity]
      rw [comp_tensor_id]
      slice_lhs 2 3 => rw [← G.map_id, G.μ_natural]
      rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
          ← G.map_comp, ← G.map_comp, ← G.map_comp, ← G.map_comp, F.associativity] }
#align category_theory.lax_monoidal_functor.comp CategoryTheory.LaxMonoidalFunctor.comp

@[inherit_doc]
infixr:80 " ⊗⋙ " => comp

protected lemma coe_comp_eq_comp_coe :
    (F ⊗⋙ G).toFunctor = (F.toFunctor ⋙ G.toFunctor) := rfl

/-- The isomorphism witnessing that the functor underlying a composition of
lax monoidal functors is the composition of the underlying functors. -/
@[simps!]
def coe_comp_iso_comp_coe :
    (F ⊗⋙ G).toFunctor ≅ (F.toFunctor ⋙ G.toFunctor) := Iso.refl _

end LaxMonoidalFunctor

namespace LaxMonoidalFunctor

universe v₀ u₀

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]

variable (F : LaxMonoidalFunctor.{v₀, v₁} B C) (G : LaxMonoidalFunctor.{v₂, v₃} D E)

attribute [local simp] μ_natural associativity left_unitality right_unitality

/-- The cartesian product of two lax monoidal functors is lax monoidal. -/
@[simps]
def prod : LaxMonoidalFunctor (B × D) (C × E) where
  ε := (ε F, ε G)
  μ := fun X Y => (μ F X.1 Y.1, μ G X.2 Y.2)
  __ := Functor.prod F.toFunctor G.toFunctor
#align category_theory.lax_monoidal_functor.prod CategoryTheory.LaxMonoidalFunctor.prod

end LaxMonoidalFunctor

namespace MonoidalFunctor

variable (C)

/-- The diagonal functor as a monoidal functor. -/
@[simps! toLaxMonoidalFunctor_toFunctor]
def diag : MonoidalFunctor C (C × C) :=
  .mk' (.diag C) (Iso.refl _) (fun _ _ => Iso.refl _)
#align category_theory.monoidal_functor.diag CategoryTheory.MonoidalFunctor.diag

@[simp] lemma diag_εIso : (diag C).εIso = Iso.refl (𝟙_ C, 𝟙_ C) := rfl

variable {C}
@[simp] lemma diag_μIso (X Y : C) : (diag C).μIso X Y = Iso.refl (X ⊗ Y, X ⊗ Y) := rfl

end MonoidalFunctor

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{v₁, v₂} C D) (G : LaxMonoidalFunctor.{v₁, v₃} C E)

/-- The cartesian product of two lax monoidal functors starting from the same monoidal category `C`
    is lax monoidal. -/
def prod' : LaxMonoidalFunctor C (D × E) :=
  (MonoidalFunctor.diag C).toLaxMonoidalFunctor ⊗⋙ F.prod G
#align category_theory.lax_monoidal_functor.prod' CategoryTheory.LaxMonoidalFunctor.prod'

@[simp] theorem coe_prod' :
    (F.prod' G).toFunctor = Functor.prod' F.toFunctor G.toFunctor := rfl
#align category_theory.lax_monoidal_functor.prod'_to_functor CategoryTheory.LaxMonoidalFunctor.coe_prod'

@[simp] theorem prod'_ε : (F.prod' G).ε = (F.ε, G.ε) := by
  dsimp [prod']
  simp
#align category_theory.lax_monoidal_functor.prod'_ε CategoryTheory.LaxMonoidalFunctor.prod'_ε

@[simp]
theorem prod'_μ (X Y : C) : (F.prod' G).μ X Y = (F.μ X Y, G.μ X Y) := by
  dsimp [prod']
  simp
#align category_theory.lax_monoidal_functor.prod'_μ CategoryTheory.LaxMonoidalFunctor.prod'_μ

end LaxMonoidalFunctor

namespace MonoidalFunctor

variable (F : MonoidalFunctor.{v₁, v₂} C D) (G : MonoidalFunctor.{v₂, v₃} D E)

-- we don't use MonoidalFunctor.mk' because proving associativity is annoying
/-- The composition of two monoidal functors is again monoidal. -/
@[simps toLaxMonoidalFunctor]
def comp : MonoidalFunctor.{v₁, v₃} C E where
  ε_inv := G.map F.ε_inv ≫ G.ε_inv
  μ_inv X Y := G.map (F.μ_inv X Y) ≫ G.μ_inv (F.obj X) (F.obj Y)
  ε_hom_inv_id := by simp [← G.map_comp_assoc]
  ε_inv_hom_id := by simp [← G.map_comp]
  μ_hom_inv_id _ _ := by simp [← G.map_comp_assoc]
  μ_inv_hom_id _ _ := by simp [← G.map_comp]
  __ := LaxMonoidalFunctor.comp F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor
  -- MonoidalFunctor.mk' ((F : C ⥤ D) ⋙ (G : D ⥤ E)) (G.εIso ≪≫ G.mapIso F.εIso)
  --   (fun X Y => G.μIso (F.obj X) (F.obj Y) ≪≫ G.mapIso (F.μIso X Y)) H1 H2 H3
#align category_theory.monoidal_functor.comp CategoryTheory.MonoidalFunctor.comp

@[simp] lemma comp_εIso : (F.comp G).εIso = G.εIso ≪≫ G.mapIso F.εIso := rfl
@[simp] lemma comp_μIso (X Y : C) :
    (F.comp G).μIso X Y = G.μIso (F.obj X) (F.obj Y) ≪≫ G.mapIso (F.μIso X Y) := rfl

@[inherit_doc]
infixr:80
  " ⊗⋙ " =>-- We overload notation; potentially dangerous, but it seems to work.
  comp

protected lemma coe_comp_eq_comp_coe :
  (F ⊗⋙ G).toLaxMonoidalFunctor =
    (F.toLaxMonoidalFunctor ⊗⋙ G.toLaxMonoidalFunctor) := rfl

end MonoidalFunctor

namespace MonoidalFunctor

universe v₀ u₀

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]

variable (F : MonoidalFunctor.{v₀, v₁} B C) (G : MonoidalFunctor.{v₂, v₃} D E)

/-- The cartesian product of two monoidal functors is monoidal. -/
def prod : MonoidalFunctor (B × D) (C × E) :=
  MonoidalFunctor.mk' (.prod F.toFunctor G.toFunctor) (.prod F.εIso G.εIso)
                      (fun X Y => .prod (F.μIso X.1 Y.1) (G.μIso X.2 Y.2))
#align category_theory.monoidal_functor.prod CategoryTheory.MonoidalFunctor.prod

@[simp] lemma prod_toLaxMonoidalFunctor :
    (prod F G).toLaxMonoidalFunctor =
      .prod F.toLaxMonoidalFunctor G.toLaxMonoidalFunctor := rfl
@[simp] lemma prod_εIso : (F.prod G).εIso = .prod F.εIso G.εIso := rfl
@[simp] lemma prod_μIso (X Y : B × D) :
    (F.prod G).μIso X Y = .prod (F.μIso X.1 Y.1) (G.μIso X.2 Y.2) := rfl

end MonoidalFunctor

namespace MonoidalFunctor

variable (F : MonoidalFunctor.{v₁, v₂} C D) (G : MonoidalFunctor.{v₁, v₃} C E)

/-- The cartesian product of two monoidal functors starting from the same monoidal category `C`
    is monoidal. -/
def prod' : MonoidalFunctor C (D × E) :=
  diag C ⊗⋙ F.prod G
#align category_theory.monoidal_functor.prod' CategoryTheory.MonoidalFunctor.prod'

@[simp]
theorem prod'_toLaxMonoidalFunctor :
    (F.prod' G).toLaxMonoidalFunctor =
      F.toLaxMonoidalFunctor.prod' G.toLaxMonoidalFunctor := rfl
#align category_theory.monoidal_functor.prod'_to_lax_monoidal_functor CategoryTheory.MonoidalFunctor.prod'_toLaxMonoidalFunctor

@[simp] lemma prod'_εIso : (F.prod' G).εIso = .prod F.εIso G.εIso := by
  dsimp [prod']; exact Eq.trans (congrArg _ (mapIso_refl _ _)) (Iso.trans_refl _)

@[simp] lemma prod'_μIso (X Y : C) :
    (F.prod' G).μIso X Y = .prod (F.μIso X Y) (G.μIso X Y) := by
  dsimp [prod']; exact Eq.trans (congrArg _ (mapIso_refl _ _)) (Iso.trans_refl _)

end MonoidalFunctor

-- TODO: Doctrinal adjunction, double category of (op)lax morphisms of an algebra
/-- If we have a right adjoint functor `G` to a monoidal functor `F`, then `G` has a lax monoidal
structure as well.
-/
@[simps!]
def monoidalAdjoint (F : MonoidalFunctor C D) [IsLeftAdjoint F.toFunctor] :
    LaxMonoidalFunctor D C :=
  let h := IsLeftAdjoint.adj
  let G := IsLeftAdjoint.right F.toFunctor
  LaxMonoidalFunctor.ofTensorHom
  (F := G)
  (ε := h.homEquiv _ _ F.εIso.inv)
  (μ := fun X Y ↦
    h.homEquiv _ (X ⊗ Y) ((F.μIso (G.obj X) (G.obj Y)).inv ≫ (h.counit.app X ⊗ h.counit.app Y)))
  (μ_natural := by
    intro X Y X' Y' f g
    erw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq, assoc,
      Iso.eq_inv_comp, ← F.μIso_hom_natural_assoc, Iso.hom_inv_id_assoc, ←
      tensor_comp, Adjunction.counit_naturality, Adjunction.counit_naturality, tensor_comp])
  (associativity := by
    intro X Y Z
    dsimp only
    erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left,
      ← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left, Equiv.apply_eq_iff_eq,
      ← (F.μIso (G.obj X ⊗ G.obj Y) (G.obj Z)).cancel_iso_hom_left,
      ← ((tensorRight (F.obj (G.obj Z))).mapIso (F.μIso (G.obj X) (G.obj Y))).cancel_iso_hom_left,
      mapIso_hom, tensorRight_map,
      F.associativity_μIso_hom_assoc (G.obj X) (G.obj Y) (G.obj Z),
      ← F.μIso_hom_natural_assoc, assoc, Iso.hom_inv_id_assoc,
      ← F.μIso_hom_natural_assoc, Iso.hom_inv_id_assoc, ← tensor_comp,
      ← tensor_comp, id_comp, Functor.map_id, Functor.map_id, id_comp, ← tensor_comp_assoc,
      ← tensor_comp_assoc, id_comp, id_comp, h.homEquiv_unit, h.homEquiv_unit, Functor.map_comp,
      assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, Functor.map_comp,
      assoc, h.counit_naturality, h.left_triangle_components_assoc]
    simp)
  (left_unitality := by
    intro
    erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_leftUnitor_hom, h.homEquiv_unit, assoc, assoc, assoc,
      F.map_tensor, assoc, assoc, F.μ_eq_μIso_hom, Iso.hom_inv_id_assoc,
      ← tensor_comp_assoc, Functor.map_id, id_comp, Functor.map_comp, assoc,
      h.counit_naturality, h.left_triangle_components_assoc,
      ← leftUnitor_naturality, ← tensor_comp_assoc, id_comp, comp_id]
    rfl)
  (right_unitality := by
    intro
    erw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_rightUnitor_hom, assoc, assoc, ← rightUnitor_naturality,
      ← tensor_comp_assoc, comp_id, id_comp, h.homEquiv_unit, F.map_tensor, assoc, assoc, assoc,
      F.μ_eq_μIso_hom, Iso.hom_inv_id_assoc, Functor.map_comp, Functor.map_id,
      ← tensor_comp_assoc, assoc, h.counit_naturality, h.left_triangle_components_assoc, id_comp]
    simp)
#align category_theory.monoidal_adjoint CategoryTheory.monoidalAdjoint


/-
TODO: Find a better home for this
Maybe also define it as
  .trans (isoEquivOfFullyFaithful e.inverse)
         (Iso.isoCongr_left (e.unitIso.app X).symm)
or in terms of the core groupoid?
-/
@[simps!]
def Equivalence.isoEquiv (e : C ≌ D) (X : C) (Y : D) :
    (e.functor.obj X ≅ Y) ≃ (X ≅ e.inverse.obj Y) where
  toFun f := e.unitIso.app X ≪≫ e.inverse.mapIso f
  invFun f := e.functor.mapIso f ≪≫ e.counitIso.app Y
  left_inv := by aesop_cat
  right_inv := by aesop_cat

lemma Equivalence.mapIso_isoEquiv (e : C ≌ D) {X Y} (f : e.functor.obj X ≅ Y) :
    e.functor.mapIso (e.isoEquiv X Y f) = f ≪≫ (e.counitIso.app Y).symm := by
  aesop_cat

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
def monoidalInverse (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    MonoidalFunctor D C :=
  let A := monoidalAdjoint F
  .mk' A.toFunctor
    (F.asEquivalence.isoEquiv (𝟙_ C) (𝟙_ D) F.εIso.symm)
    (fun X Y => F.asEquivalence.isoEquiv _ _ <|
        (F.μIso (F.inv.obj X) (F.inv.obj Y)).symm ≪≫
        tensorIso (F.asEquivalence.counitIso.app X) (F.asEquivalence.counitIso.app Y))
    A.μ_natural_left A.μ_natural_right A.associativity A.left_unitality A.right_unitality
#align category_theory.monoidal_inverse CategoryTheory.monoidalInverse

@[simp]
lemma monoidalInverse_toLaxMonoidalFunctor (F : MonoidalFunctor C D)
    [IsEquivalence F.toFunctor] :
    (monoidalInverse F).toLaxMonoidalFunctor = monoidalAdjoint F := rfl

@[simp]
lemma monoidalInverse_εIso (F : MonoidalFunctor C D)
    [IsEquivalence F.toFunctor] :
    (monoidalInverse F).εIso =
      F.asEquivalence.isoEquiv (𝟙_ C) (𝟙_ D) F.εIso.symm := rfl

@[simp]
lemma monoidalInverse_μIso (F : MonoidalFunctor C D)
    [IsEquivalence F.toFunctor]  (X Y : D) :
    (monoidalInverse F).μIso X Y =
      (F.asEquivalence.isoEquiv _ _ <|
        (F.μIso (F.inv.obj X) (F.inv.obj Y)).symm ≪≫
        tensorIso (F.asEquivalence.counitIso.app X)
                  (F.asEquivalence.counitIso.app Y)) := rfl

instance (F : MonoidalFunctor C D) [IsEquivalence F.toFunctor] :
    IsEquivalence (monoidalInverse F).toFunctor :=
  inferInstanceAs (IsEquivalence F.inv)

end CategoryTheory
