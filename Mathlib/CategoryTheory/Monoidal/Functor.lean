/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
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
      map f ▷ obj X' ≫ μ Y X' = μ X X' ≫ map (f ▷ X') := by
    aesop_cat
  μ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      obj X' ◁ map f ≫ μ X' Y = μ X' X ≫ map (X' ◁ f) := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      μ X Y ▷ obj Z ≫ μ (X ⊗ Y) Z ≫ map (α_ X Y Z).hom =
        (α_ (obj X) (obj Y) (obj Z)).hom ≫ obj X ◁ μ Y Z ≫ μ X (Y ⊗ Z) := by
    aesop_cat
  -- unitality
  left_unitality : ∀ X : C, (λ_ (obj X)).hom = ε ▷ obj X ≫ μ (𝟙_ C) X ≫ map (λ_ X).hom := by
    aesop_cat
  right_unitality : ∀ X : C, (ρ_ (obj X)).hom = obj X ◁ ε ≫ μ X (𝟙_ C) ≫ map (ρ_ X).hom := by
    aesop_cat
#align category_theory.lax_monoidal_functor CategoryTheory.LaxMonoidalFunctor

-- Porting note (#11215): TODO: remove this configuration and use the default configuration.
-- We keep this to be consistent with Lean 3.
-- See also `initialize_simps_projections MonoidalFunctor` below.
-- This may require waiting on https://github.com/leanprover-community/mathlib4/pull/2936
initialize_simps_projections LaxMonoidalFunctor (+toFunctor, -obj, -map)

attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_left
attribute [reassoc (attr := simp)] LaxMonoidalFunctor.μ_natural_right

attribute [simp] LaxMonoidalFunctor.left_unitality

attribute [simp] LaxMonoidalFunctor.right_unitality

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
  simp [tensorHom_def]

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
      ∀ X : C, (λ_ (F.obj X)).hom = (ε ⊗ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
        aesop_cat)
    (right_unitality :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
        aesop_cat) :
        LaxMonoidalFunctor C D where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp
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

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.left_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (λ_ (F.obj X)).inv ≫ F.ε ▷ F.obj X ≫ F.μ (𝟙_ C) X = F.map (λ_ X).inv := by
  rw [Iso.inv_comp_eq, F.left_unitality, Category.assoc, Category.assoc, ← F.toFunctor.map_comp,
    Iso.hom_inv_id, F.toFunctor.map_id, comp_id]
#align category_theory.lax_monoidal_functor.left_unitality_inv CategoryTheory.LaxMonoidalFunctor.left_unitality_inv

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.right_unitality_inv (F : LaxMonoidalFunctor C D) (X : C) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ F.ε ≫ F.μ X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq, F.right_unitality, Category.assoc, Category.assoc, ← F.toFunctor.map_comp,
    Iso.hom_inv_id, F.toFunctor.map_id, comp_id]
#align category_theory.lax_monoidal_functor.right_unitality_inv CategoryTheory.LaxMonoidalFunctor.right_unitality_inv

@[reassoc (attr := simp)]
theorem LaxMonoidalFunctor.associativity_inv (F : LaxMonoidalFunctor C D) (X Y Z : C) :
    F.obj X ◁ F.μ Y Z ≫ F.μ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ F.μ X Y ▷ F.obj Z ≫ F.μ (X ⊗ Y) Z := by
  rw [Iso.eq_inv_comp, ← F.associativity_assoc, ← F.toFunctor.map_comp, Iso.hom_inv_id,
    F.toFunctor.map_id, comp_id]
#align category_theory.lax_monoidal_functor.associativity_inv CategoryTheory.LaxMonoidalFunctor.associativity_inv

end

/-- A oplax monoidal functor is a functor `F : C ⥤ D` between monoidal categories,
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences. -/
structure OplaxMonoidalFunctor extends C ⥤ D where
  /-- counit morphism -/
  η : obj (𝟙_ C) ⟶ 𝟙_ D
  /-- cotensorator -/
  δ : ∀ X Y : C, obj (X ⊗ Y) ⟶ obj X ⊗ obj Y
  δ_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      δ X X' ≫ map f ▷ obj X' = map (f ▷ X') ≫ δ Y X' := by
    aesop_cat
  δ_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y) ,
      δ X' X ≫ obj X' ◁ map f = map (X' ◁ f) ≫ δ X' Y := by
    aesop_cat
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      δ (X ⊗ Y) Z ≫ δ X Y ▷ obj Z ≫ (α_ (obj X) (obj Y) (obj Z)).hom =
        map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ obj X ◁ δ Y Z := by
    aesop_cat
  -- unitality
  left_unitality : ∀ X : C, (λ_ (obj X)).inv = map (λ_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ obj X := by
    aesop_cat
  right_unitality : ∀ X : C, (ρ_ (obj X)).inv = map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ obj X ◁ η := by
    aesop_cat

initialize_simps_projections OplaxMonoidalFunctor (+toFunctor, -obj, -map)

attribute [reassoc (attr := simp)] OplaxMonoidalFunctor.δ_natural_left
attribute [reassoc (attr := simp)] OplaxMonoidalFunctor.δ_natural_right

attribute [simp] OplaxMonoidalFunctor.left_unitality

attribute [simp] OplaxMonoidalFunctor.right_unitality

attribute [reassoc (attr := simp)] OplaxMonoidalFunctor.associativity

section

variable {C D}

@[reassoc (attr := simp)]
theorem OplaxMonoidalFunctor.δ_natural (F : OplaxMonoidalFunctor C D) {X Y X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') :
      F.δ X X' ≫ (F.map f ⊗ F.map g) = F.map (f ⊗ g) ≫ F.δ Y Y' := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
theorem OplaxMonoidalFunctor.left_unitality_hom (F : OplaxMonoidalFunctor C D) (X : C) :
    F.δ (𝟙_ C) X ≫ F.η ▷ F.obj X ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, F.left_unitality, ← Category.assoc,
    ← F.toFunctor.map_comp, Iso.hom_inv_id, F.toFunctor.map_id, id_comp]

@[reassoc (attr := simp)]
theorem OplaxMonoidalFunctor.right_unitality_hom (F : OplaxMonoidalFunctor C D) (X : C) :
    F.δ X (𝟙_ C) ≫ F.obj X ◁ F.η ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, F.right_unitality, ← Category.assoc,
    ← F.toFunctor.map_comp, Iso.hom_inv_id, F.toFunctor.map_id, id_comp]

@[reassoc (attr := simp)]
theorem OplaxMonoidalFunctor.associativity_inv (F : OplaxMonoidalFunctor C D) (X Y Z : C) :
    F.δ X (Y ⊗ Z) ≫ F.obj X ◁ F.δ Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.map (α_ X Y Z).inv ≫ F.δ (X ⊗ Y) Z ≫ F.δ X Y ▷ F.obj Z := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, Category.assoc, F.associativity,
    ← Category.assoc, ← F.toFunctor.map_comp, Iso.inv_hom_id, F.toFunctor.map_id, id_comp]

end

/--
A monoidal functor is a lax monoidal functor for which the tensorator and unitor are isomorphisms.

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/
structure MonoidalFunctor extends LaxMonoidalFunctor.{v₁, v₂} C D where
  ε_isIso : IsIso ε := by infer_instance
  μ_isIso : ∀ X Y : C, IsIso (μ X Y) := by infer_instance
#align category_theory.monoidal_functor CategoryTheory.MonoidalFunctor

-- See porting note on `initialize_simps_projections LaxMonoidalFunctor`
initialize_simps_projections MonoidalFunctor (+toLaxMonoidalFunctor, -obj, -map, -ε, -μ)

attribute [instance] MonoidalFunctor.ε_isIso MonoidalFunctor.μ_isIso

variable {C D}

/-- The unit morphism of a (strong) monoidal functor as an isomorphism.
-/
noncomputable def MonoidalFunctor.εIso (F : MonoidalFunctor.{v₁, v₂} C D) :
    𝟙_ D ≅ F.obj (𝟙_ C) :=
  asIso F.ε
#align category_theory.monoidal_functor.ε_iso CategoryTheory.MonoidalFunctor.εIso

/-- The tensorator of a (strong) monoidal functor as an isomorphism.
-/
noncomputable def MonoidalFunctor.μIso (F : MonoidalFunctor.{v₁, v₂} C D) (X Y : C) :
    F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) :=
  asIso (F.μ X Y)
#align category_theory.monoidal_functor.μ_iso CategoryTheory.MonoidalFunctor.μIso

/-- The underlying oplax monoidal functor of a (strong) monoidal functor. -/
@[simps]
noncomputable def MonoidalFunctor.toOplaxMonoidalFunctor (F : MonoidalFunctor C D) :
    OplaxMonoidalFunctor C D :=
  { F with
    η := inv F.ε,
    δ := fun X Y => inv (F.μ X Y),
    δ_natural_left := by aesop_cat
    δ_natural_right := by aesop_cat
    associativity := by
      intros X Y Z
      dsimp
      rw [IsIso.inv_comp_eq, ← inv_whiskerRight, IsIso.inv_comp_eq]
      slice_rhs 1 3 =>
        rw [F.associativity]
      simp
    left_unitality := by
      intros X
      dsimp
      apply Iso.inv_ext
      rw [F.left_unitality]
      slice_lhs 3 4 =>
        rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
      simp [inv_whiskerRight]
    right_unitality := by
      intros X
      dsimp
      apply Iso.inv_ext
      rw [F.right_unitality]
      slice_lhs 3 4 =>
        rw [← F.map_comp, Iso.hom_inv_id, F.map_id]
      simp }

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

namespace OplaxMonoidalFunctor

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- The identity lax monoidal functor. -/
@[simps]
def id : OplaxMonoidalFunctor.{v₁, v₁} C C :=
  { 𝟭 C with
    η := 𝟙 _
    δ := fun X Y => 𝟙 _ }

instance : Inhabited (OplaxMonoidalFunctor C C) :=
  ⟨id C⟩

end OplaxMonoidalFunctor

namespace MonoidalFunctor

section

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
variable (F : MonoidalFunctor.{v₁, v₂} C D)

@[reassoc]
theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ g) = inv (F.μ X X') ≫ (F.map f ⊗ F.map g) ≫ F.μ Y Y' := by simp
#align category_theory.monoidal_functor.map_tensor CategoryTheory.MonoidalFunctor.map_tensor

@[reassoc]
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) = inv (F.μ X Y) ≫ F.obj X ◁ F.map f ≫ F.μ X Z := by simp

@[reassoc]
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) = inv (F.μ X Z) ≫ F.map f ▷ F.obj Z ≫ F.μ Y Z := by simp

@[reassoc]
theorem map_leftUnitor (X : C) :
    F.map (λ_ X).hom = inv (F.μ (𝟙_ C) X) ≫ inv F.ε ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by
  simp only [LaxMonoidalFunctor.left_unitality]
  slice_rhs 2 3 =>
    rw [← comp_whiskerRight]
    simp
  simp
#align category_theory.monoidal_functor.map_left_unitor CategoryTheory.MonoidalFunctor.map_leftUnitor

@[reassoc]
theorem map_rightUnitor (X : C) :
    F.map (ρ_ X).hom = inv (F.μ X (𝟙_ C)) ≫ F.obj X ◁ inv F.ε ≫ (ρ_ (F.obj X)).hom := by
  simp only [LaxMonoidalFunctor.right_unitality]
  slice_rhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp]
    simp
  simp
#align category_theory.monoidal_functor.map_right_unitor CategoryTheory.MonoidalFunctor.map_rightUnitor

/-- The tensorator as a natural isomorphism. -/
noncomputable def μNatIso :
    Functor.prod F.toFunctor F.toFunctor ⋙ tensor D ≅ tensor C ⋙ F.toFunctor :=
  NatIso.ofComponents
    (by
      intros
      apply F.μIso)
    (by
      intros
      apply F.toLaxMonoidalFunctor.μ_natural)
#align category_theory.monoidal_functor.μ_nat_iso CategoryTheory.MonoidalFunctor.μNatIso

@[simp]
theorem μIso_hom (X Y : C) : (F.μIso X Y).hom = F.μ X Y :=
  rfl
#align category_theory.monoidal_functor.μ_iso_hom CategoryTheory.MonoidalFunctor.μIso_hom

@[reassoc (attr := simp)]
theorem μ_inv_hom_id (X Y : C) : (F.μIso X Y).inv ≫ F.μ X Y = 𝟙 _ :=
  (F.μIso X Y).inv_hom_id
#align category_theory.monoidal_functor.μ_inv_hom_id CategoryTheory.MonoidalFunctor.μ_inv_hom_id

@[simp]
theorem μ_hom_inv_id (X Y : C) : F.μ X Y ≫ (F.μIso X Y).inv = 𝟙 _ :=
  (F.μIso X Y).hom_inv_id
#align category_theory.monoidal_functor.μ_hom_inv_id CategoryTheory.MonoidalFunctor.μ_hom_inv_id

@[simp]
theorem εIso_hom : F.εIso.hom = F.ε :=
  rfl
#align category_theory.monoidal_functor.ε_iso_hom CategoryTheory.MonoidalFunctor.εIso_hom

@[reassoc (attr := simp)]
theorem ε_inv_hom_id : F.εIso.inv ≫ F.ε = 𝟙 _ :=
  F.εIso.inv_hom_id
#align category_theory.monoidal_functor.ε_inv_hom_id CategoryTheory.MonoidalFunctor.ε_inv_hom_id

@[simp]
theorem ε_hom_inv_id : F.ε ≫ F.εIso.inv = 𝟙 _ :=
  F.εIso.hom_inv_id
#align category_theory.monoidal_functor.ε_hom_inv_id CategoryTheory.MonoidalFunctor.ε_hom_inv_id

/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
noncomputable def commTensorLeft (X : C) :
    F.toFunctor ⋙ tensorLeft (F.toFunctor.obj X) ≅ tensorLeft X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso X Y) fun f => F.μ_natural_right X f
#align category_theory.monoidal_functor.comm_tensor_left CategoryTheory.MonoidalFunctor.commTensorLeft

/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
noncomputable def commTensorRight (X : C) :
    F.toFunctor ⋙ tensorRight (F.toFunctor.obj X) ≅ tensorRight X ⋙ F.toFunctor :=
  NatIso.ofComponents (fun Y => F.μIso Y X) fun f => F.μ_natural_left f X
#align category_theory.monoidal_functor.comm_tensor_right CategoryTheory.MonoidalFunctor.commTensorRight

end

section

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- The identity monoidal functor. -/
@[simps]
def id : MonoidalFunctor.{v₁, v₁} C C :=
  { 𝟭 C with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }
#align category_theory.monoidal_functor.id CategoryTheory.MonoidalFunctor.id

instance : Inhabited (MonoidalFunctor C C) :=
  ⟨id C⟩

end

end MonoidalFunctor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{v₁, v₂} C D) (G : LaxMonoidalFunctor.{v₂, v₃} D E)

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
      simp_rw [comp_whiskerRight, assoc, μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
        assoc, μ_natural_right_assoc]
      slice_rhs 1 3 => rw [← G.associativity]
      simp_rw [Category.assoc, ← G.toFunctor.map_comp, F.associativity] }
#align category_theory.lax_monoidal_functor.comp CategoryTheory.LaxMonoidalFunctor.comp

@[inherit_doc]
infixr:80 " ⊗⋙ " => comp

end LaxMonoidalFunctor

namespace OplaxMonoidalFunctor

variable (F : OplaxMonoidalFunctor.{v₁, v₂} C D) (G : OplaxMonoidalFunctor.{v₂, v₃} D E)

/-- The composition of two oplax monoidal functors is again oplax monoidal. -/
@[simps]
def comp : OplaxMonoidalFunctor.{v₁, v₃} C E :=
  { F.toFunctor ⋙ G.toFunctor with
    η := G.map F.η ≫ G.η
    δ := fun X Y => G.map (F.δ X Y) ≫ G.δ (F.obj X) (F.obj Y)
    δ_natural_left := by
      intro X Y f X'
      simp_rw [comp_obj, Functor.comp_map, ← G.map_comp_assoc, ← F.δ_natural_left, assoc,
        G.δ_natural_left, ← G.map_comp_assoc]
    δ_natural_right := by
      intro X Y f X'
      simp_rw [comp_obj, Functor.comp_map, ← G.map_comp_assoc, ← F.δ_natural_right, assoc,
        G.δ_natural_right, ← G.map_comp_assoc]
    associativity := fun X Y Z => by
      dsimp
      simp_rw [comp_whiskerRight, assoc, δ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
        δ_natural_right_assoc]
      slice_rhs 1 3 =>
        simp only [← G.toFunctor.map_comp]
        rw [← F.associativity]
      rw [G.associativity]
      simp only [G.map_comp, Category.assoc] }

@[inherit_doc]
infixr:80 " ⊗⋙ " => comp

end OplaxMonoidalFunctor

namespace LaxMonoidalFunctor

universe v₀ u₀

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
variable (F : LaxMonoidalFunctor.{v₀, v₁} B C) (G : LaxMonoidalFunctor.{v₂, v₃} D E)

attribute [local simp] μ_natural associativity left_unitality right_unitality

/-- The cartesian product of two lax monoidal functors is lax monoidal. -/
@[simps]
def prod : LaxMonoidalFunctor (B × D) (C × E) :=
  { F.toFunctor.prod G.toFunctor with
    ε := (ε F, ε G)
    μ := fun X Y => (μ F X.1 Y.1, μ G X.2 Y.2) }
#align category_theory.lax_monoidal_functor.prod CategoryTheory.LaxMonoidalFunctor.prod

end LaxMonoidalFunctor

namespace MonoidalFunctor

variable (C)

/-- The diagonal functor as a monoidal functor. -/
@[simps]
def diag : MonoidalFunctor C (C × C) :=
  { Functor.diag C with
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }
#align category_theory.monoidal_functor.diag CategoryTheory.MonoidalFunctor.diag

end MonoidalFunctor

namespace LaxMonoidalFunctor

variable (F : LaxMonoidalFunctor.{v₁, v₂} C D) (G : LaxMonoidalFunctor.{v₁, v₃} C E)

/-- The cartesian product of two lax monoidal functors starting from the same monoidal category `C`
    is lax monoidal. -/
def prod' : LaxMonoidalFunctor C (D × E) :=
  (MonoidalFunctor.diag C).toLaxMonoidalFunctor ⊗⋙ F.prod G
#align category_theory.lax_monoidal_functor.prod' CategoryTheory.LaxMonoidalFunctor.prod'

@[simp]
theorem prod'_toFunctor : (F.prod' G).toFunctor = F.toFunctor.prod' G.toFunctor :=
  rfl
#align category_theory.lax_monoidal_functor.prod'_to_functor CategoryTheory.LaxMonoidalFunctor.prod'_toFunctor

@[simp]
theorem prod'_ε : (F.prod' G).ε = (F.ε, G.ε) := by
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

/-- The composition of two monoidal functors is again monoidal. -/
@[simps]
def comp : MonoidalFunctor.{v₁, v₃} C E :=
  {
    F.toLaxMonoidalFunctor.comp
      G.toLaxMonoidalFunctor with
    ε_isIso := by
      dsimp
      infer_instance
    μ_isIso := by
      dsimp
      infer_instance }
#align category_theory.monoidal_functor.comp CategoryTheory.MonoidalFunctor.comp

@[inherit_doc]
infixr:80
  " ⊗⋙ " =>-- We overload notation; potentially dangerous, but it seems to work.
  comp

end MonoidalFunctor

namespace MonoidalFunctor

universe v₀ u₀

variable {B : Type u₀} [Category.{v₀} B] [MonoidalCategory.{v₀} B]
variable (F : MonoidalFunctor.{v₀, v₁} B C) (G : MonoidalFunctor.{v₂, v₃} D E)

/-- The cartesian product of two monoidal functors is monoidal. -/
@[simps]
def prod : MonoidalFunctor (B × D) (C × E) :=
  {
    F.toLaxMonoidalFunctor.prod
      G.toLaxMonoidalFunctor with
    ε_isIso := (isIso_prod_iff C E).mpr ⟨ε_isIso F, ε_isIso G⟩
    μ_isIso := fun X Y => (isIso_prod_iff C E).mpr ⟨μ_isIso F X.1 Y.1, μ_isIso G X.2 Y.2⟩ }
#align category_theory.monoidal_functor.prod CategoryTheory.MonoidalFunctor.prod

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
    (F.prod' G).toLaxMonoidalFunctor = F.toLaxMonoidalFunctor.prod' G.toLaxMonoidalFunctor :=
  rfl
#align category_theory.monoidal_functor.prod'_to_lax_monoidal_functor CategoryTheory.MonoidalFunctor.prod'_toLaxMonoidalFunctor

end MonoidalFunctor

section

-- TODO: The definitions below would be slightly better phrased if, in addition to
-- `MonoidalFunctor` (which extends `Functor`), we had a data valued type class
-- `Functor.Monoidal` (resp. `Functor.LaxMonoidal`) so that the definitions below
-- could be phrased in terms of `F : C ⥤ D`, `G : D ⥤ D`, `h : F ⊣ G` and `[F.Monoidal]`.
-- Then, in the case of an equivalence (see `monoidalInverse`), we could just take as
-- input an equivalence of categories `e : C ≌ D` and the data `[e.functor.Monoidal]`.

variable (F : MonoidalFunctor C D) {G : D ⥤ C} (h : F.toFunctor ⊣ G)

/-- If we have a right adjoint functor `G` to a monoidal functor `F`, then `G` has a lax monoidal
structure as well.
-/
@[simp]
noncomputable def monoidalAdjoint :
    LaxMonoidalFunctor D C where
  toFunctor := G
  ε := h.homEquiv _ _ (inv F.ε)
  μ := fun X Y =>
    h.homEquiv _ _ (inv (F.μ (G.obj X) (G.obj Y)) ≫ (h.counit.app X ⊗ h.counit.app Y))
  μ_natural_left {X Y} f X' := by
    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
      assoc, IsIso.eq_inv_comp,
      ← F.toLaxMonoidalFunctor.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, tensorHom_def,
      ← comp_whiskerRight_assoc, Adjunction.counit_naturality, comp_whiskerRight_assoc,
      ← whisker_exchange, ← tensorHom_def_assoc]
  μ_natural_right {X Y} X' f := by
    rw [← h.homEquiv_naturality_left, ← h.homEquiv_naturality_right, Equiv.apply_eq_iff_eq,
      assoc, IsIso.eq_inv_comp,
      ← F.toLaxMonoidalFunctor.μ_natural_right_assoc, IsIso.hom_inv_id_assoc, tensorHom_def',
      ← MonoidalCategory.whiskerLeft_comp_assoc, Adjunction.counit_naturality, whisker_exchange,
      MonoidalCategory.whiskerLeft_comp, ← tensorHom_def_assoc]
  associativity X Y Z := by
    dsimp only
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← h.homEquiv_naturality_left,
      ← h.homEquiv_naturality_left, Equiv.apply_eq_iff_eq,
      ← cancel_epi (F.μ (G.obj X ⊗ G.obj Y) (G.obj Z)),
      ← cancel_epi (F.μ (G.obj X) (G.obj Y) ▷ (F.obj (G.obj Z)))]
    simp only [assoc]
    calc
      _ = (α_ _ _ _).hom ≫ (h.counit.app X ⊗ h.counit.app Y ⊗ h.counit.app Z) := by
        rw [← F.μ_natural_left_assoc, IsIso.hom_inv_id_assoc, h.homEquiv_unit,
          tensorHom_def_assoc (h.counit.app (X ⊗ Y)) (h.counit.app Z)]
        dsimp only [comp_obj, id_obj]
        simp_rw [← MonoidalCategory.comp_whiskerRight_assoc]
        rw [F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc,
          IsIso.hom_inv_id_assoc, ← tensorHom_def_assoc, associator_naturality]
      _ = _ := by
        rw [F.associativity_assoc, ← F.μ_natural_right_assoc, IsIso.hom_inv_id_assoc,
          h.homEquiv_unit, tensorHom_def (h.counit.app X) (h.counit.app (Y ⊗ Z))]
        dsimp only [id_obj, comp_obj]
        rw [whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp, F.map_comp_assoc,
          h.counit_naturality, h.left_triangle_components_assoc, whisker_exchange_assoc,
          ← MonoidalCategory.whiskerLeft_comp, ← tensorHom_def, IsIso.hom_inv_id_assoc]
  left_unitality X := by
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_leftUnitor_assoc, h.homEquiv_unit, F.map_whiskerRight_assoc, assoc,
      IsIso.hom_inv_id_assoc, tensorHom_def_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
    simp
  right_unitality X := by
    rw [← h.homEquiv_naturality_right, ← h.homEquiv_naturality_left, ← Equiv.symm_apply_eq,
      h.homEquiv_counit, F.map_rightUnitor_assoc, h.homEquiv_unit, F.map_whiskerLeft_assoc, assoc,
      IsIso.hom_inv_id_assoc, tensorHom_def'_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      F.map_comp_assoc, h.counit_naturality, h.left_triangle_components_assoc]
    simp
#align category_theory.monoidal_adjoint CategoryTheory.monoidalAdjoint

instance [F.IsEquivalence] : IsIso (monoidalAdjoint F h).ε := by
  dsimp
  rw [Adjunction.homEquiv_unit]
  infer_instance

instance (X Y : D) [F.IsEquivalence] : IsIso ((monoidalAdjoint F h).μ X Y) := by
  dsimp
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[simps]
noncomputable def monoidalInverse [F.IsEquivalence] :
    MonoidalFunctor D C where
  toLaxMonoidalFunctor := monoidalAdjoint F h
#align category_theory.monoidal_inverse CategoryTheory.monoidalInverse

end

end CategoryTheory
