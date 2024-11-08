/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.RepresentationTheory.Action.Concrete
import Mathlib.RepresentationTheory.Action.Limits

/-!
# Induced monoidal structure on `Action V G`

We show:

* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
-/

universe u v

open CategoryTheory Limits

variable {V : Type (u + 1)} [LargeCategory V] {G : Type u} [Monoid G]

open MonoidalCategory in
theorem CategoryTheory.types_tensorObj {X Y : Type u} : X ⊗ Y = (X × Y) := rfl

@[simp]
theorem CategoryTheory.types_β_hom {X Y : Type u} : (β_ X Y).hom = _root_.Prod.swap := rfl

@[simp]
theorem CategoryTheory.types_β_inv {X Y : Type u} : (β_ X Y).inv = _root_.Prod.swap := rfl

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
    @DFunLike.coe (G →* End (𝟙_ V)) _ _ _ (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) := by
  rfl

@[simp]
theorem tensorUnit_ρ {g : G} : (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl

/- Adding this solves `simpNF` linter report at `tensor_ρ` -/
@[simp]
theorem tensor_ρ' {X Y : Action V G} {g : G} :
    @DFunLike.coe (G →* End (X.V ⊗ Y.V)) _ _ _ (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl

@[simp]
theorem tensor_ρ {X Y : Action V G} {g : G} : (X ⊗ Y).ρ g = X.ρ g ⊗ Y.ρ g :=
  rfl

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f

variable (V G)

/-- When `V` is monoidal the forgetful functor `Action V G` to `V` is monoidal. -/
@[simps]
def forgetMonoidal : MonoidalFunctor (Action V G) V :=
  { toFunctor := Action.forget _ _
    ε := 𝟙 _
    μ := fun _ _ => 𝟙 _ }

instance forgetMonoidal_faithful : (forgetMonoidal V G).Faithful := by
  change (forget V G).Faithful; infer_instance

section

variable [BraidedCategory V]

instance : BraidedCategory (Action V G) :=
  braidedCategoryOfFaithful (forgetMonoidal V G) (fun X Y => mkIso (β_ _ _)
    (fun g => by simp [FunctorCategoryEquivalence.inverse])) (by aesop_cat)

@[simp]
theorem β_hom {X Y : Action V G} : (β_ X Y).hom.hom = (β_ X.V Y.V).hom := rfl

@[simp]
theorem β_inv {X Y : Action V G} : (β_ X Y).inv.hom = (β_ X.V Y.V).inv := rfl

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

variable (H : Type u) [Group H]

instance [RightRigidCategory V] : RightRigidCategory (SingleObj H ⥤ V) := by
  change RightRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence (functorCategoryMonoidalAdjunction V _)

instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj H ⥤ V) := by
  change LeftRigidCategory (SingleObj H ⥤ V); infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryMonoidalAdjunction V _)

instance [RigidCategory V] : RigidCategory (SingleObj H ⥤ V) := by
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

section

open MonoidalCategory

variable (G : Type u)

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps!]
noncomputable def diagonalSuccIsoTensorDiagonal [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

variable [Group G]

/-- Given `X : Action (Type u) G` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
noncomputable abbrev leftRegularTensorIso (X : Action (Type u) G) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ Action.trivial G X.V :=
  Action.mkIso (Equiv.toIso {
    toFun := fun g => ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
    invFun := fun g => ⟨g.1, X.ρ g.1 g.2⟩
    left_inv := fun _ => Prod.ext rfl <| by simp
    right_inv := fun _ => Prod.ext rfl <| by simp }) <| fun _ => by
      ext _
      simp only [instMonoidalCategory_tensorObj_V, tensor_ρ', types_comp_apply, tensor_apply,
        ofMulAction_apply]
      simp

/-- An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).` -/
noncomputable def diagonalSuccIsoTensorTrivial :
    ∀ n : ℕ, diagonal G (n + 1) ≅ leftRegular G ⊗ Action.trivial G (Fin n → G)
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.equivOfUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSuccIsoTensorDiagonal _ _ ≪≫
      tensorIso (Iso.refl _) (diagonalSuccIsoTensorTrivial n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Fin.insertNthEquiv (fun _ => G) 0).toIso fun _ => rfl)

variable {G}

@[simp]
theorem diagonalSuccIsoTensorTrivial_hom_hom {n : ℕ} (f : Fin (n + 1) → G) :
    (diagonalSuccIsoTensorTrivial G n).hom.hom f =
      (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction' n with n hn
  · exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  · refine Prod.ext rfl (funext fun x => ?_)
    induction' x using Fin.cases
    <;> simp_all only [instMonoidalCategory_tensorObj_V, diagonalSuccIsoTensorTrivial,
        Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom, comp_hom,
        instMonoidalCategory_whiskerLeft_hom, mkIso_hom_hom, tensor_ρ', tensor_apply,
        ofMulAction_apply, types_comp_apply, whiskerLeft_apply]
    <;> simp [types_tensorObj, Fin.tail, Fin.castSucc_fin_succ]

@[simp]
theorem diagonalSuccIsoTensorTrivial_inv_hom {n : ℕ} (g : G) (f : Fin n → G) :
    (diagonalSuccIsoTensorTrivial G n).inv.hom (g, f) =
      (g • Fin.partialProd f : Fin (n + 1) → G) := by
  induction' n with n hn generalizing g
  · funext (x : Fin 1)
    simp [diagonalSuccIsoTensorTrivial, diagonalOneIsoLeftRegular, Subsingleton.elim x 0]
  · funext x
    induction' x using Fin.cases
    <;> simp_all only [diagonalSuccIsoTensorTrivial, instMonoidalCategory_tensorObj_V,
        Iso.trans_inv, comp_hom, mkIso_inv_hom, tensor_ρ', tensor_apply, ofMulAction_apply]
    <;> simp_all [types_tensorObj, mul_assoc, Fin.partialProd_succ']

end
end Action

namespace CategoryTheory.MonoidalFunctor

open Action

variable {W : Type (u + 1)} [LargeCategory W] [MonoidalCategory V] [MonoidalCategory W]

/-- A lax monoidal functor induces a lax monoidal functor between
the categories of `G`-actions within those categories. -/
@[simps!]
def mapActionLax (F : LaxMonoidalFunctor V W) (G : Type u) [Monoid G] :
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

variable (F : MonoidalFunctor V W) (G : Type u) [Monoid G]

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
