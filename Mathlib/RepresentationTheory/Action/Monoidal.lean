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
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
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

-- Porting note: removed @[simp] as the simpNF linter complains
theorem tensorUnit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl

@[simp]
theorem tensor_v {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl

-- Porting note: removed @[simp] as the simpNF linter complains
theorem tensor_rho {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl

@[simp]
theorem tensor_hom {W X Y Z : Action V G} (f : W ⟶ X) (g : Y ⟶ Z) : (f ⊗ g).hom = f.hom ⊗ g.hom :=
  rfl

@[simp]
theorem whiskerLeft_hom (X : Action V G) {Y Z : Action V G} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.V ◁ f.hom :=
  rfl

@[simp]
theorem whiskerRight_hom {X Y : Action V G} (f : X ⟶ Y) (Z : Action V G) :
    (f ▷ Z).hom = f.hom ▷ Z.V :=
  rfl

-- Porting note: removed @[simp] as the simpNF linter complains
theorem associator_hom_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom := by
  dsimp
  simp

-- Porting note: removed @[simp] as the simpNF linter complains
theorem associator_inv_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv := by
  dsimp
  simp

-- Porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_hom_hom {X : Action V G} : Hom.hom (λ_ X).hom = (λ_ X.V).hom := by
  dsimp
  simp

-- Porting note: removed @[simp] as the simpNF linter complains
theorem leftUnitor_inv_hom {X : Action V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv := by
  dsimp
  simp

-- Porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_hom_hom {X : Action V G} : Hom.hom (ρ_ X).hom = (ρ_ X.V).hom := by
  dsimp
  simp

-- Porting note: removed @[simp] as the simpNF linter complains
theorem rightUnitor_inv_hom {X : Action V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv := by
  dsimp
  simp

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f fun _ => by
    simp only [MonoidHom.one_apply, End.one_def, Category.id_comp f.hom, tensorUnit_rho,
      MonCat.oneHom_apply, MonCat.one_of, Category.comp_id]

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  { toFunctor := Action.forget _ _
    ε := 𝟙 _
    μ := fun X Y => 𝟙 _ }

instance forgetMonoidal_faithful : (forgetMonoidal V G).Faithful := by
  change (forget V G).Faithful; infer_instance

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by simp [FunctorCategoryEquivalence.inverse])) (by aesop_cat)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps!]
def forgetBraided : BraidedFunctor (Action V G) V :=
  { forgetMonoidal _ _ with }

instance forgetBraided_faithful : (forgetBraided V G).Faithful := by
  change (forget V G).Faithful; infer_instance

end

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (forgetBraided V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (Action V G) where

end

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (Action V G) (SingleObj G ⥤ V) :=
  Monoidal.fromTransported (Action.functorCategoryEquivalence _ _).symm

/-- Upgrading the functor `(SingleObj G ⥤ V) ⥤ Action V G` to a monoidal functor. -/
def functorCategoryMonoidalEquivalenceInverse : MonoidalFunctor (SingleObj G ⥤ V) (Action V G) :=
  Monoidal.toTransported (Action.functorCategoryEquivalence _ _).symm

/-- The adjunction (which is an equivalence) between the categories
`Action V G` and `(SingleObj G ⥤ V)`. -/
def functorCategoryMonoidalAdjunction :
    (functorCategoryMonoidalEquivalence V G).toFunctor ⊣
      (functorCategoryMonoidalEquivalenceInverse V G).toFunctor :=
  (Action.functorCategoryEquivalence _ _).toAdjunction

instance : (functorCategoryMonoidalEquivalence V G).IsEquivalence := by
  change (Action.functorCategoryEquivalence _ _).functor.IsEquivalence; infer_instance

@[simp]
theorem functorCategoryMonoidalEquivalence.μ_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μ A B).app PUnit.unit = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.μIso_inv_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μIso A B).inv.app PUnit.unit = 𝟙 _ := by
  rw [← NatIso.app_inv, ← IsIso.Iso.inv_hom]
  refine IsIso.inv_eq_of_hom_inv_id ?_
  rw [Category.comp_id, NatIso.app_hom, MonoidalFunctor.μIso_hom,
    functorCategoryMonoidalEquivalence.μ_app]

@[simp]
theorem functorCategoryMonoidalEquivalence.ε_app :
    (functorCategoryMonoidalEquivalence V G).ε.app PUnit.unit = 𝟙 _ := by
  dsimp only [functorCategoryMonoidalEquivalence]
  simp only [Monoidal.fromTransported_toLaxMonoidalFunctor_ε]
  rfl

@[simp]
theorem functorCategoryMonoidalAdjunction.unit_app_hom (A : Action V G) :
    ((functorCategoryMonoidalAdjunction _ _).unit.app A).hom = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalAdjunction.counit_app_app (A : SingleObj G ⥤ V) :
    ((functorCategoryMonoidalAdjunction _ _).counit.app A).app PUnit.unit = 𝟙 _ :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.functor_map {A B : Action V G} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalence _ _).map f = FunctorCategoryEquivalence.functor.map f :=
  rfl

@[simp]
theorem functorCategoryMonoidalEquivalence.inverse_map {A B : SingleObj G ⥤ V} (f : A ⟶ B) :
    (functorCategoryMonoidalEquivalenceInverse _ _).map f =
      FunctorCategoryEquivalence.inverse.map f :=
  rfl

variable (H : Grp.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RightRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalAdjunction V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change LeftRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalAdjunction V _)

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryMonoidalAdjunction V _)

variable {V H}
variable (X : Action V H)

@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl

@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← SingleObj.inv_as_inv]; rfl

end

end Monoidal

open MonoidalCategory

/-- Given `X : Action (Type u) (MonCat.of G)` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps]
noncomputable def leftRegularTensorIso (G : Type u) [Group G] (X : Action (Type u) (MonCat.of G)) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ Action.mk X.V 1 where
  hom :=
    { hom := fun g => ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine Prod.ext rfl ?_
        change (X.ρ ((g * x₁)⁻¹ : G) * X.ρ g) x₂ = X.ρ _ _
        rw [mul_inv_rev, ← X.ρ.map_mul, inv_mul_cancel_right] }
  inv :=
    { hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine Prod.ext rfl ?_
        erw [tensor_rho, tensor_rho]
        dsimp
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [leftRegular_ρ_apply]
        erw [map_mul]
        rfl }
  hom_inv_id := by
    apply Hom.ext
    funext x
    refine Prod.ext rfl ?_
    change (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = x.2
    rw [← X.ρ.map_mul, mul_inv_cancel, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]
  inv_hom_id := by
    apply Hom.ext
    funext x
    refine Prod.ext rfl ?_
    change (X.ρ (x.1⁻¹ : G) * X.ρ x.1) x.2 = x.2
    rw [← X.ρ.map_mul, inv_mul_cancel, X.ρ.map_one, MonCat.one_of, End.one_def, types_id_apply]

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps!]
noncomputable def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

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
    { hom := F.ε
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp, F.map_id, Category.comp_id] })
  (μ := fun X Y =>
    { hom := F.μ X.V Y.V
      comm := fun g => F.μ_natural (X.ρ g) (Y.ρ g) })
  (μ_natural := by intros; ext; simp)
  (associativity := by intros; ext; simp)
  (left_unitality := by intros; ext; simp)
  (right_unitality := by intros; ext; simp)

variable (F : MonoidalFunctor V W) (G : MonCat.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps!]
def mapAction : MonoidalFunctor (Action V G) (Action W G) :=
  { mapActionLax F.toLaxMonoidalFunctor G with
    ε_isIso := by dsimp [mapActionLax]; infer_instance
    μ_isIso := by dsimp [mapActionLax]; infer_instance }

@[simp]
theorem mapAction_ε_inv_hom : (inv (F.mapAction G).ε).hom = inv F.ε := by
  rw [← cancel_mono F.ε, IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_ε_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]

@[simp]
theorem mapAction_μ_inv_hom (X Y : Action V G) :
    (inv ((F.mapAction G).μ X Y)).hom = inv (F.μ X.V Y.V) := by
  rw [← cancel_mono (F.μ X.V Y.V), IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_μ_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]

end CategoryTheory.MonoidalFunctor
