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

universe u v w

open CategoryTheory Limits

variable {V : Type (u + 1)} [LargeCategory V] {G : MonCat.{u}}

namespace Action

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

instance instMonoidalCategory : MonoidalCategory (Action V G) where
  tensorObj := fun X Y => {
    V := X.V ⊗ Y.V
    ρ := {
      toFun := fun g => X.ρ g ⊗ Y.ρ g
      map_one' := sorry
      map_mul' := sorry
    }
  }
  whiskerLeft := fun X Y Z f => {
    hom := X.V ◁ f.hom
    comm := sorry
  }
  whiskerRight := fun f X => {
    hom := f.hom ▷ X.V
    comm := sorry
  }
  tensorHom := fun f g => {
    hom := f.hom ⊗ g.hom
    comm := sorry
  }
  tensorUnit := {
    V := 𝟙_ V
    ρ := {
      toFun := fun g => 𝟙 (𝟙_ V)
      map_one' := sorry
      map_mul' := sorry
    }
  }
  associator := fun X Y Z => Action.mkIso (α_ X.V Y.V Z.V) sorry
  leftUnitor := fun X => Action.mkIso (λ_ X.V) sorry
  rightUnitor := fun X => Action.mkIso (ρ_ X.V) sorry
  tensorHom_def := sorry
  tensor_id := sorry
  tensor_comp := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry
  --Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

--@[simp]
theorem tensorUnit_v : (𝟙_ (Action V G)).V = 𝟙_ V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_unit_V Action.tensorUnit_v

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem tensorUnit_rho {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_unit_rho Action.tensorUnit_rho

--@[simp]
theorem tensor_v {X Y : Action V G} : (X ⊗ Y).V = X.V ⊗ Y.V :=
  rfl
set_option linter.uppercaseLean3 false in
#align Action.tensor_V Action.tensor_v

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
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

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem associator_hom_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).hom = (α_ X.V Y.V Z.V).hom := by
  rfl
  --simp [Monoidal.transportStruct_associator_hom, Category.id_comp (α_ X.V Y.V Z.V).hom]
set_option linter.uppercaseLean3 false in
#align Action.associator_hom_hom Action.associator_hom_hom

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem associator_inv_hom {X Y Z : Action V G} :
    Hom.hom (α_ X Y Z).inv = (α_ X.V Y.V Z.V).inv := by
  rfl
  -- dsimp
  --simp [Monoidal.transportStruct_associator_inv]
set_option linter.uppercaseLean3 false in
#align Action.associator_inv_hom Action.associator_inv_hom

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem leftUnitor_hom_hom {X : Action V G} : Hom.hom (λ_ X).hom = (λ_ X.V).hom := by
  rfl
  --simp [Monoidal.transportStruct_leftUnitor_hom]
  --sorry
set_option linter.uppercaseLean3 false in
#align Action.left_unitor_hom_hom Action.leftUnitor_hom_hom

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem leftUnitor_inv_hom {X : Action V G} : Hom.hom (λ_ X).inv = (λ_ X.V).inv := by
  rfl
  -- dsimp
  --simp [Monoidal.transportStruct_leftUnitor_inv]
set_option linter.uppercaseLean3 false in
#align Action.left_unitor_inv_hom Action.leftUnitor_inv_hom

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem rightUnitor_hom_hom {X : Action V G} : Hom.hom (ρ_ X).hom = (ρ_ X.V).hom := by
  rfl
  -- dsimp
  -- simp [Monoidal.transportStruct_rightUnitor_hom]
set_option linter.uppercaseLean3 false in
#align Action.right_unitor_hom_hom Action.rightUnitor_hom_hom

-- Porting note: removed @[simp] as the simpNF linter complains
@[simp]
theorem rightUnitor_inv_hom {X : Action V G} : Hom.hom (ρ_ X).inv = (ρ_ X.V).inv := by
  rfl
  -- dsimp
  -- simp [Monoidal.transportStruct_rightUnitor_inv]
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
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
{ toFunctor := Action.forget _ _
  ε := 𝟙 _
  μ := fun x y => 𝟙 _
  μ_natural_left := fun f X => by simp
  μ_natural_right := fun X f => by simp
  associativity := fun X Y Z => by simp
  left_unitality := by intros; simp
  right_unitality := by intros; simp
  ε_isIso := by infer_instance
  μ_isIso := by infer_instance }
set_option linter.uppercaseLean3 false in
#align Action.forget_monoidal Action.forgetMonoidal

instance forgetMonoidal_faithful : (forgetMonoidal V G).Faithful := by
  change (forget V G).Faithful; infer_instance
set_option linter.uppercaseLean3 false in
#align Action.forget_monoidal_faithful Action.forgetMonoidal_faithful

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by
      simp
    -- simp [FunctorCategoryEquivalence.inverse]
      )) (by aesop_cat)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
@[simps!]
def forgetBraided : BraidedFunctor (Action V G) V :=
  { forgetMonoidal _ _ with }
set_option linter.uppercaseLean3 false in
#align Action.forget_braided Action.forgetBraided

instance forgetBraided_faithful : (forgetBraided V G).Faithful := by
  change (forget V G).Faithful; infer_instance
set_option linter.uppercaseLean3 false in
#align Action.forget_braided_faithful Action.forgetBraided_faithful

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

/-- Construct a natural transformation between functors `SingleObj M ⥤ C` by
giving a compatible morphism `SingleObj.star M`. -/
@[simp]
def _root_.CategoryTheory.SingleObj.natIso
    {M : Type u} [Monoid M]
    {C : Type v} [Category.{w} C]
    {F G : SingleObj M ⥤ C} (u : F.obj (SingleObj.star M) ≅ G.obj (SingleObj.star M))
    (h : ∀ a : M, F.map a ≫ u.hom = u.hom ≫ G.map a) : F ≅ G :=
  NatIso.ofComponents (fun _ => u) h

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
def functorCategoryMonoidalEquivalence : MonoidalFunctor (Action V G) (SingleObj G ⥤ V) :=
  { toFunctor := (Action.functorCategoryEquivalence V G).functor
    ε := (SingleObj.natIso (Iso.refl _) fun _ => by simp).hom
    μ := fun X Y => (SingleObj.natIso (Iso.refl _) <| fun x => by simp).hom
    μ_natural_left := by aesop_cat
    μ_natural_right := by aesop_cat
    associativity := by aesop_cat
    left_unitality := by aesop_cat
    right_unitality := by aesop_cat
    ε_isIso := by infer_instance
    μ_isIso := by infer_instance }
  --Monoidal.fromTransported (Action.functorCategoryEquivalence _ _).symm
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence Action.functorCategoryMonoidalEquivalence

instance : (functorCategoryMonoidalEquivalence V G).IsEquivalence := by
  change (Action.functorCategoryEquivalence _ _).functor.IsEquivalence; infer_instance

@[simp]
theorem functorCategoryMonoidalEquivalence.μ_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μ A B).app PUnit.unit = 𝟙 _ := by
  dsimp only [functorCategoryMonoidalEquivalence]
  rfl
  --simp only [Monoidal.fromTransported_toLaxMonoidalFunctor_μ, NatTrans.comp_app]
  -- Porting note: Lean3 was able to see through some defeq, as the mathlib3 proof was
  --   show (𝟙 A.V ⊗ 𝟙 B.V) ≫ 𝟙 (A.V ⊗ B.V) ≫ (𝟙 A.V ⊗ 𝟙 B.V) = 𝟙 (A.V ⊗ B.V)
  --   simp only [monoidal_category.tensor_id, category.comp_id]
  --rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.μ_app Action.functorCategoryMonoidalEquivalence.μ_app

@[simp]
theorem functorCategoryMonoidalEquivalence.μIso_inv_app (A B : Action V G) :
    ((functorCategoryMonoidalEquivalence V G).μIso A B).inv.app PUnit.unit = 𝟙 _ := by
  rw [← NatIso.app_inv, ← IsIso.Iso.inv_hom]
  refine' IsIso.inv_eq_of_hom_inv_id _
  rw [Category.comp_id, NatIso.app_hom, MonoidalFunctor.μIso_hom,
    functorCategoryMonoidalEquivalence.μ_app]
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.μ_iso_inv_app Action.functorCategoryMonoidalEquivalence.μIso_inv_app

@[simp]
theorem functorCategoryMonoidalEquivalence.ε_app :
    (functorCategoryMonoidalEquivalence V G).ε.app PUnit.unit = 𝟙 _ := by
  rfl
 -- dsimp only [functorCategoryMonoidalEquivalence]
 -- simp only [Monoidal.fromTransported_toLaxMonoidalFunctor_ε]
 -- rfl
set_option linter.uppercaseLean3 false in
#align Action.functor_category_monoidal_equivalence.ε_app Action.functorCategoryMonoidalEquivalence.ε_app

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

variable {V H}
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

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl
set_option linter.uppercaseLean3 false in
#align Action.right_dual_ρ Action.rightDual_ρ

-- This lemma was always bad, but the linter only noticed after lean4#2644
@[simp, nolint simpNF]
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← SingleObj.inv_as_inv]; rfl
set_option linter.uppercaseLean3 false in
#align Action.left_dual_ρ Action.leftDual_ρ

end

end Monoidal

open MonoidalCategory

/-@[simp 1000]
lemma ugh [MonoidalCategory V] (A B : Action V G) : (A ⊗ B).V = A.V ⊗ B.V := rfl

@[simp]
lemma ffs {G : Type u} [Group G] (A B : Action (Type u) (MonCat.of G)) (g : G) (x : A.V) (y : B.V) :
    (A ⊗ B).ρ g (x, y) = (A.ρ g x, B.ρ g y) := rfl
-/

/-- Given `X : Action (Type u) (Mon.of G)` for `G` a group, then `G × X` (with `G` acting as left
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
        refine' Prod.ext rfl _
        change (X.ρ ((g * x₁)⁻¹ : G) * X.ρ g) x₂ = X.ρ _ _
        rw [mul_inv_rev, ← X.ρ.map_mul, inv_mul_cancel_right] }
  inv :=
    { hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine' Prod.ext rfl _
        simp [End.mul_def (X.ρ g) (X.ρ x₁)]
        /- erw [tensor_rho, tensor_rho]
        dsimp
        -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
        erw [leftRegular_ρ_apply]
        erw [map_mul]
        rfl-/ }
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
noncomputable def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Equiv.piFinSuccAbove _ 0).toIso fun _ => rfl
set_option linter.uppercaseLean3 false in
#align Action.diagonal_succ Action.diagonalSucc

end Action

namespace CategoryTheory.MonoidalFunctor

open Action

variable {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]
open MonoidalCategory
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
        rw [Category.id_comp F.ε, F.map_id MonoidalCategory.tensorUnit, Category.comp_id F.ε]
        -- sorry --rw [Category.id_comp, F.map_id, Category.comp_id]

         })
  (μ := fun X Y =>
    { hom := F.μ X.V Y.V
      comm := fun g => F.μ_natural (X.ρ g) (Y.ρ g) })
  (μ_natural := by intros; ext; simp)
  (associativity := by intros; ext; simp [tensor_v])
  (left_unitality := by intros; ext; simp [tensorUnit_v])
  (right_unitality := by intros; ext; simp [tensorUnit_v])

variable (F : MonoidalFunctor V W) (G : MonCat.{u})

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps!]
def mapAction : MonoidalFunctor (Action V G) (Action W G) :=
  { mapActionLax F.toLaxMonoidalFunctor G with
    ε_isIso := by dsimp [mapActionLax]; infer_instance
    μ_isIso := by dsimp [mapActionLax]; infer_instance }
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal_functor.map_Action CategoryTheory.MonoidalFunctor.mapAction

@[simp]
theorem mapAction_ε_inv_hom : (inv (F.mapAction G).ε).hom = inv F.ε := by
  rw [← cancel_mono F.ε, IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_ε_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal_functor.map_Action_ε_inv_hom CategoryTheory.MonoidalFunctor.mapAction_ε_inv_hom

@[simp]
theorem mapAction_μ_inv_hom (X Y : Action V G) :
    (inv ((F.mapAction G).μ X Y)).hom = inv (F.μ X.V Y.V) := by
  rw [← cancel_mono (F.μ X.V Y.V), IsIso.inv_hom_id, ← F.mapAction_toLaxMonoidalFunctor_μ_hom G,
    ← Action.comp_hom, IsIso.inv_hom_id, Action.id_hom]
set_option linter.uppercaseLean3 false in
#align category_theory.monoidal_functor.map_Action_μ_inv_hom CategoryTheory.MonoidalFunctor.mapAction_μ_inv_hom

end CategoryTheory.MonoidalFunctor
