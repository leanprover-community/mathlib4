/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.RepresentationTheory.Action.Limits
import Mathlib.RepresentationTheory.Action.Concrete
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Induced monoidal structure on `Action V G`

We show:

* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
-/

universe u v

open CategoryTheory Limits

variable {V : Type (u + 1)} [LargeCategory V] {G : MonCat.{u}}

namespace Action

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

instance instMonoidalCategory : MonoidalCategory (Action V G) :=
  Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]
theorem tensorUnit_v : (𝟙_ (Action V G)).V = 𝟙_ V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_unit_V Action.tensorUnit_v

-- porting note: removed @[simp] as the simpNF linter complains
theorem tensorUnit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_unit_rho Action.tensorUnit_rho

@[simp]
theorem tensor_v {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_V Action.tensor_v

-- porting note: removed @[simp] as the simpNF linter complains
theorem tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_rho Action.tensor_rho

@[simp]
theorem tensor_hom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) : (f ⊗ g).hom = f.hom ⊗ g.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_hom Action.tensor_hom

@[simp]
theorem whiskerLeft_hom (X : Action V G) {Y Z : Action V G} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.V ◁ f.hom :=
  rfl

@[simp]
theorem whiskerRight_hom {X Y : Action V G} (f : X ⟶ Y) (Z : Action V G) :
    (f ▷ Z).hom = f.hom ▷ Z.V :=
  rfl

-- porting note: removed @[simp] as the simpNF linter complains
theorem associator_hom_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.associator_hom_hom Action.associator_hom_hom

-- porting note: removed @[simp] as the simpNF linter complains
theorem associator_inv_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.associator_inv_hom Action.associator_inv_hom

-- porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_hom_hom {X : Action V G} : Hom.hom (λ_ X).hom = (λ_ X.V).hom := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.left_unitor_hom_hom Action.leftUnitor_hom_hom

-- porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_inv_hom {X : Action V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.left_unitor_inv_hom Action.leftUnitor_inv_hom

-- porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_hom_hom {X : Action V G} : Hom.hom (ρ_ X).hom = (ρ_ X.V).hom := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.right_unitor_hom_hom Action.rightUnitor_hom_hom

-- porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_inv_hom {X : Action V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv := by
  dsimp
  simp
set_option linter.uppercaseLean3 false in
#align Action.right_unitor_inv_hom Action.rightUnitor_inv_hom

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f fun _ => by
    simp only [MonoidHom.one_apply, End.one_def, Category.id_comp f.hom, tensorUnit_rho,
      MonCat.oneHom_apply, MonCat.one_of, Category.comp_id]
set_option linter.uppercaseLean3 false in
#align Action.tensor_unit_iso Action.tensorUnitIso

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  .mk' (Action.forget _ _) (Iso.refl _) (fun _ _ => Iso.refl _)
set_option linter.uppercaseLean3 false in
#align Action.forget_monoidal Action.forgetMonoidal

instance forgetMonoidal_faithful : Faithful (forgetMonoidal V G).toFunctor := by
  change Faithful (forget V G); infer_instance
set_option linter.uppercaseLean3 false in
#align Action.forget_monoidal_faithful Action.forgetMonoidal_faithful

variable {V G}

@[simp] lemma forgetMonoidal_obj (X : Action V G) :
    (forgetMonoidal V G).obj X = X.V := rfl
@[simp] lemma forgetMonoidal_map {X Y} (f : X ⟶ Y) :
    (forgetMonoidal V G).map f = f.hom := rfl

@[simp] lemma forgetMonoidal_μIso (X Y : Action V G) :
    (forgetMonoidal V G).μIso X Y = Iso.refl _ := rfl

variable (V G)

@[simp]
lemma forgetMonoidal_εIso : (forgetMonoidal V G).εIso = Iso.refl _ := rfl

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by simp [FunctorCategoryEquivalence.inverse])) (by aesop_cat)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
def forgetBraided : BraidedFunctor (Action V G) V :=
  .mk' (forgetMonoidal V G)
set_option linter.uppercaseLean3 false in
#align Action.forget_braided Action.forgetBraided

instance forgetBraided_faithful : Faithful (forgetBraided V G).toFunctor :=
  inferInstanceAs (Faithful (forget V G))
set_option linter.uppercaseLean3 false in
#align Action.forget_braided_faithful Action.forgetBraided_faithful

variable {V G}

@[simp] lemma forgetBraided_obj (X : Action V G) :
    (forgetBraided V G).obj X = X.V := rfl
@[simp] lemma forgetBraided_map {X Y} (f : X ⟶ Y) :
    (forgetBraided V G).map f = f.hom := rfl

@[simp] lemma forgetBraided_μIso (X Y : Action V G) :
    (forgetBraided V G).μIso X Y = Iso.refl _ := rfl

variable (V G)

@[simp]
lemma forgetBraided_εIso : (forgetBraided V G).εIso = Iso.refl _ := rfl

end

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.tensor_add MonoidalPreadditive.add_tensor

instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (Action V G) where

end

section

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (Action V G) (SingleObj G ⥤ V) :=
  Monoidal.fromTransported (Action.functorCategoryEquivalence _ _).symm
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence Action.functorCategoryMonoidalEquivalence

instance : IsEquivalence (functorCategoryMonoidalEquivalence V G).toFunctor :=
  inferInstanceAs (IsEquivalence (Action.functorCategoryEquivalence _ _).functor)

variable {V G}

@[simp] lemma functorCategoryMonoidalEquivalence_obj (X : Action V G) :
    (functorCategoryMonoidalEquivalence V G).obj X =
      (Action.functorCategoryEquivalence _ _).functor.obj X := rfl
@[simp] lemma functorCategoryMonoidalEquivalence_map {X Y} (f : X ⟶ Y) :
    (functorCategoryMonoidalEquivalence V G).map f =
      (Action.functorCategoryEquivalence _ _).functor.map f := rfl

@[simp] lemma functorCategoryMonoidalEquivalence_μIso (X Y : Action V G) :
    (functorCategoryMonoidalEquivalence V G).μIso X Y = Iso.refl _ := rfl

variable (V G)

@[simp] lemma functorCategoryMonoidalEquivalence_εIso :
    (functorCategoryMonoidalEquivalence V G).εIso = Iso.refl _ := rfl

variable {V G}

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_counit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).inv.adjunction.counit.app A).hom = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.inv_counit_app_hom Action.functorCategoryMonoidalEquivalence.inv_counit_app_hom

@[simp]
theorem functorCategoryMonoidalEquivalence.counit_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).adjunction.counit.app A).app PUnit.unit = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.counit_app Action.functorCategoryMonoidalEquivalence.counit_app

@[simp]
theorem functorCategoryMonoidalEquivalence.inv_unit_app_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalEquivalence _ _).inv.adjunction.unit.app A).app PUnit.unit = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.inv_unit_app_app Action.functorCategoryMonoidalEquivalence.inv_unit_app_app

@[simp]
theorem functorCategoryMonoidalEquivalence.unit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalEquivalence _ _).adjunction.unit.app A).hom = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.unit_app_hom Action.functorCategoryMonoidalEquivalence.unit_app_hom

@[simp]
theorem functorCategoryMonoidalEquivalence.functor_map {A B : Action V G} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).map f = FunctorCategoryEquivalence.functor.map f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.functor_map Action.functorCategoryMonoidalEquivalence.functor_map

@[simp]
theorem functorCategoryMonoidalEquivalence.inverse_map {A B : SingleObj G ⥤ V} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).inv.map f = FunctorCategoryEquivalence.inverse.map f :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.inverse_map Action.functorCategoryMonoidalEquivalence.inverse_map

variable (H : GroupCat.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RightRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change LeftRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryMonoidalEquivalence V _)

variable (X : Action V H)

@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.right_dual_V Action.rightDual_v

@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.left_dual_V Action.leftDual_v

-- -- This lemma was always bad, but the linter only noticed after lean4#2644
-- @[simp, nolint simpNF]
-- theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
--   rw [← SingleObj.inv_as_inv]; rfl
-- set_option linter.uppercaseLean3 false in
-- #align Action.right_dual_ρ Action.rightDual_ρ

-- -- This lemma was always bad, but the linter only noticed after lean4#2644
-- @[simp, nolint simpNF]
-- theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
--   rw [← SingleObj.inv_as_inv]; rfl
-- set_option linter.uppercaseLean3 false in
-- #align Action.left_dual_ρ Action.leftDual_ρ

end

end Monoidal

open MonoidalCategory

/-- Given `X : Action (Type u) (Mon.of G)` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps]
def leftRegularTensorIso (G : Type u) [Group G] (X : Action (Type u) (MonCat.of G)) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ Action.mk X.V 1 where
  hom :=
    { hom := fun g => ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine' Prod.ext rfl _
        change (X.ρ ((g * x₁)⁻¹ : G) * X.ρ g) x₂ = X.ρ _ _
        rw [mul_inv_rev, ← X.ρ.map_mul, inv_mul_cancel_right] }
  inv :=
    { hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine' Prod.ext rfl _
        erw [tensor_rho, tensor_rho]
        dsimp
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [leftRegular_ρ_apply]
        erw [map_mul]
        rfl }
  hom_inv_id := by
    apply Hom.ext
    funext x
    refine' Prod.ext rfl _
    change (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = x.2
    rw [← X.ρ.map_mul, mul_inv_self, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]
  inv_hom_id := by
    apply Hom.ext
    funext x
    refine' Prod.ext rfl _
    change (X.ρ (x.1⁻¹ : G) * X.ρ x.1) x.2 = x.2
    rw [← X.ρ.map_mul, inv_mul_self, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]
set_option linter.uppercaseLean3 false in
#align Action.left_regular_tensor_iso Action.leftRegularTensorIso

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps!]
def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Equiv.piFinSuccAbove _ 0).toIso fun _ => rfl
set_option linter.uppercaseLean3 false in
#align Action.diagonal_succ Action.diagonalSucc

end Action

namespace CategoryTheory.MonoidalFunctor

open Action

variable {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]

/-- A lax monoidal functor induces a lax monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps!]
def mapActionLax (F : LaxMonoidalFunctor V W) (G : MonCat.{u}) :
    LaxMonoidalFunctor (Action V G) (Action W G) := .ofTensorHom
  (F := F.toFunctor.mapAction G)
  (ε :=
    { hom := F.η
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp, F.map_id, Category.comp_id] })
  (μ := fun X Y =>
    { hom := F.μ X.V Y.V
      comm := fun g => F.μ_natural (X.ρ g) (Y.ρ g) })
  -- using `dsimp` before `simp` speeds these up
  (μ_natural := @fun {X Y X' Y'} f g ↦ by ext; dsimp; simp)
  (associativity := fun X Y Z ↦ by ext; dsimp; simp)
  (left_unitality := fun X ↦ by ext; dsimp; simp)
  (right_unitality := fun X ↦ by
    ext
    dsimp
    simp only [MonoidalCategory.rightUnitor_conjugation,
      LaxMonoidalFunctor.right_unitality, Category.id_comp, Category.assoc,
      LaxMonoidalFunctor.right_unitality_inv_assoc, Category.comp_id, Iso.hom_inv_id]
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id])

variable (F : MonoidalFunctor V W) (G : MonCat.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
def mapAction : MonoidalFunctor (Action V G) (Action W G) :=
  let F' := mapActionLax F.toLaxMonoidalFunctor G
  .mk' (F.toFunctor.mapAction G) (mkIso F.εIso F'.η.comm)
    (fun X Y => mkIso (F.μIso X.V Y.V) (F'.μ X Y).comm)
    F'.μ_natural_left F'.μ_natural_right F'.associativity
    F'.left_unitality F'.right_unitality
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal_functor.map_Action CategoryTheory.MonoidalFunctor.mapAction

variable {F}

@[simp] lemma mapAction_obj (X : Action V G) :
    (mapAction F G).obj X = (F.toFunctor.mapAction G).obj X := rfl
@[simp] lemma mapAction_map {X Y} (f : X ⟶ Y) :
    (mapAction F G).map f = (F.toFunctor.mapAction G).map f := rfl

@[simp] lemma mapAction_μIso_hom_hom (X Y : Action V G) :
    ((mapAction F G).μIso X Y).hom.hom = (F.μIso X.V Y.V).hom := rfl

@[simp] lemma mapAction_μIso_inv_hom (X Y : Action V G) :
    ((mapAction F G).μIso X Y).inv.hom = (F.μIso X.V Y.V).inv := rfl

variable (F G)

@[simp]
lemma mapAction_εIso_hom_hom : (mapAction F G).εIso.hom.hom = F.εIso.hom := rfl

@[simp]
lemma mapAction_εIso_inv_hom : (mapAction F G).εIso.inv.hom = F.εIso.inv := rfl

end CategoryTheory.MonoidalFunctor
