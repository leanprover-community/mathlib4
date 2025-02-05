/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Limits

/-!
# Induced monoidal structure on `Action V G`

We show:

* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
-/

universe u v

open CategoryTheory Limits MonoidalCategory

variable {V : Type (u + 1)} [LargeCategory V] {G : MonCat.{u}}

namespace Action

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

@[simps! tensorUnit_V tensorObj_V tensorHom_hom whiskerLeft_hom whiskerRight_hom
  associator_hom_hom associator_inv_hom leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom]
instance instMonoidalCategory : MonoidalCategory (Action V G) :=
  Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

/- Adding this solves `simpNF` linter report at `tensorUnit_ρ` -/
@[simp]
theorem tensorUnit_ρ' {g : G} :
    @DFunLike.coe (G →* MonCat.of (End (𝟙_ V))) _ _ _ (𝟙_ (Action V G)).ρ.hom g = 𝟙 (𝟙_ V) := by
  rfl

@[simp]
theorem tensorUnit_ρ {g : G} :
    -- Have to hint `F` here, otherwise `simp` doesn't reduce `↑(MonCat.of (End _))` to `End _`.
    DFunLike.coe (F := _ →* End _)
      -- Have to hint `Y` here for `simpNF` reasons.
      (ConcreteCategory.hom (Y := MonCat.of (End (𝟙_ V))) (𝟙_ (Action V G)).ρ) g = 𝟙 (𝟙_ V) :=
  rfl

/- Adding this solves `simpNF` linter report at `tensor_ρ` -/
@[simp]
theorem tensor_ρ' {X Y : Action V G} {g : G} :
    @DFunLike.coe (G →* MonCat.of (End (X.V ⊗ Y.V))) _ _ _ (X ⊗ Y).ρ.hom g = X.ρ g ⊗ Y.ρ g :=
  rfl

@[simp]
theorem tensor_ρ {X Y : Action V G} {g : G} :
    -- Have to hint `F` here, otherwise `simp` doesn't reduce `↑(MonCat.of (End _))` to `End _`.
    DFunLike.coe (F := _ →* End _)
      -- Have to hint `Y` here for `simpNF` reasons.
      (ConcreteCategory.hom (Y := MonCat.of (End (tensorObj X.V Y.V))) (X ⊗ Y).ρ) g =
    X.ρ g ⊗ Y.ρ g :=
  rfl

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f

variable (V G)

instance : (Action.forget V G).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma forget_ε : ε (Action.forget V G) = 𝟙 _ := rfl
@[simp] lemma forget_η : ε (Action.forget V G) = 𝟙 _ := rfl

variable {V G}

@[simp] lemma forget_μ (X Y : Action V G) : μ (Action.forget V G) X Y = 𝟙 _ := rfl
@[simp] lemma forget_δ (X Y : Action V G) : δ (Action.forget V G) X Y = 𝟙 _ := rfl

variable (V G)

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (Action.forget V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by simp [FunctorCategoryEquivalence.inverse])) (by simp)

/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
instance : (Action.forget V G).Braided where

end

instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  symmetricCategoryOfFaithful (Action.forget V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

instance : MonoidalLinear R (Action V G) where

end

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
instance : (FunctorCategoryEquivalence.functor (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).inverse.Monoidal

instance : (functorCategoryEquivalence V G).functor.Monoidal := by
  dsimp only [functorCategoryEquivalence_functor]; infer_instance

/-- Upgrading the functor `(SingleObj G ⥤ V) ⥤ Action V G` to a monoidal functor. -/
instance : (FunctorCategoryEquivalence.inverse (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).functor.Monoidal

instance : (functorCategoryEquivalence V G).inverse.Monoidal := by
  dsimp only [functorCategoryEquivalence_inverse]; infer_instance

@[simp]
lemma FunctorCategoryEquivalence.functor_ε :
    ε (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
lemma FunctorCategoryEquivalence.functor_η :
    η (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
lemma FunctorCategoryEquivalence.functor_μ (A B : Action V G) :
    μ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl

@[simp]
lemma FunctorCategoryEquivalence.functor_δ (A B : Action V G) :
    δ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl


variable (H : Grp.{u})

instance [RightRigidCategory V] : RightRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RightRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence
    (functorCategoryEquivalence V H).toAdjunction

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change LeftRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

instance [RigidCategory V] : RigidCategory (SingleObj (H : MonCat.{u}) ⥤ V) := by
  change RigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

variable {V H}
variable (X : Action V H)

@[simp]
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl

@[simp]
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl

theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl

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
        rw [mul_inv_rev, ← X.ρ.hom.map_mul, inv_mul_cancel_right] }
  inv :=
    { hom := fun g => ⟨g.1, X.ρ g.1 g.2⟩
      comm := fun (g : G) => by
        funext ⟨(x₁ : G), (x₂ : X.V)⟩
        refine Prod.ext rfl ?_
        dsimp [leftRegular] -- Unfold `leftRegular` so `rw` can see through `(leftRegular V).V = V`
        rw [tensor_ρ, tensor_ρ]
        dsimp
        -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
        erw [leftRegular_ρ_hom_apply]
        rw [map_mul]
        rfl }
  hom_inv_id := by
    apply Hom.ext
    funext x
    refine Prod.ext rfl ?_
    change (X.ρ x.1 * X.ρ (x.1⁻¹ : G)) x.2 = x.2
    rw [← X.ρ.hom.map_mul, mul_inv_cancel, X.ρ.hom.map_one, MonCat.one_of, End.one_def,
      types_id_apply]
  inv_hom_id := by
    apply Hom.ext
    funext x
    refine Prod.ext rfl ?_
    change (X.ρ (x.1⁻¹ : G) * X.ρ x.1) x.2 = x.2
    rw [← X.ρ.hom.map_mul, inv_mul_cancel, X.ρ.hom.map_one, MonCat.one_of, End.one_def,
      types_id_apply]

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps!]
noncomputable def diagonalSucc (G : Type u) [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

end Action

namespace CategoryTheory.Functor

open Action

variable {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]
  (F : V ⥤ W)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

/-- A lax monoidal functor induces a lax monoidal functor between
the categories of `G`-actions within those categories. -/
instance [F.LaxMonoidal] : (F.mapAction G).LaxMonoidal where
  ε' :=
    { hom := ε F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp, F.map_id, Category.comp_id] }
  μ' X Y :=
    { hom := μ F X.V Y.V
      comm := fun g => μ_natural F (X.ρ g) (Y.ρ g) }
  μ'_natural_left _ _ := by ext; simp
  μ'_natural_right _ _ := by ext; simp
  associativity' _ _ _ := by ext; simp
  left_unitality' _ := by ext; simp
  right_unitality' _ := by ext; simp

@[simp]
lemma mapAction_ε_hom [F.LaxMonoidal] : (ε (F.mapAction G)).hom = ε F := rfl

@[simp]
lemma mapAction_μ_hom [F.LaxMonoidal] (X Y : Action V G) :
    (μ (F.mapAction G) X Y).hom = μ F X.V Y.V := rfl

/-- An oplax monoidal functor induces an oplax monoidal functor between
the categories of `G`-actions within those categories. -/
instance [F.OplaxMonoidal] : (F.mapAction G).OplaxMonoidal where
  η' :=
    { hom := η F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [map_id, Category.id_comp, Category.comp_id] }
  δ' X Y :=
    { hom := δ F X.V Y.V
      comm := fun g => (δ_natural F (X.ρ g) (Y.ρ g)).symm }
  δ'_natural_left _ _ := by ext; simp
  δ'_natural_right _ _ := by ext; simp
  oplax_associativity' _ _ _ := by ext; simp
  oplax_left_unitality' _ := by ext; simp
  oplax_right_unitality' _ := by ext; simp

@[simp]
lemma mapAction_η_hom [F.OplaxMonoidal] : (η (F.mapAction G)).hom = η F := rfl

@[simp]
lemma mapAction_δ_hom [F.OplaxMonoidal] (X Y : Action V G) :
    (δ (F.mapAction G) X Y).hom = δ F X.V Y.V := rfl

/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
instance [F.Monoidal] : (F.mapAction G).Monoidal where
  η_ε := by ext; dsimp; rw [η_ε]
  ε_η := by ext; dsimp; rw [ε_η]
  μ_δ _ _ := by ext; dsimp; rw [μ_δ]
  δ_μ _ _ := by ext; dsimp; rw [δ_μ]

end CategoryTheory.Functor
