/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp_

/-!

# `CartesianMonoidalCategory` for `Over X`

We provide a `CartesianMonoidalCategory (Over X)` instance via pullbacks, and provide simp lemmas
for the induced `MonoidalCategory (Over X)` instance.

-/

public noncomputable section

namespace CategoryTheory.Over

open Functor Limits CartesianMonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- A choice of finite products of `Over X` given by `Limits.pullback`. -/
abbrev cartesianMonoidalCategory (X : C) : CartesianMonoidalCategory (Over X) :=
  .ofChosenFiniteProducts
    ⟨asEmptyCone (Over.mk (𝟙 X)), IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    fun Y Z ↦ ⟨pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom),
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor⟩

@[deprecated (since := "2025-05-15")]
noncomputable alias chosenFiniteProducts := cartesianMonoidalCategory

attribute [local instance] cartesianMonoidalCategory

/-- `Over X` is braided w.r.t. the Cartesian monoidal structure given by `Limits.pullback`. -/
abbrev braidedCategory (X : C) : BraidedCategory (Over X) :=
  .ofCartesianMonoidalCategory

attribute [local instance] braidedCategory

open MonoidalCategory

variable {X : C}

@[ext]
lemma tensorObj_ext {R : C} {S T : Over X} (f₁ f₂ : R ⟶ (S ⊗ T).left)
    (e₁ : f₁ ≫ pullback.fst _ _ = f₂ ≫ pullback.fst _ _)
    (e₂ : f₁ ≫ pullback.snd _ _ = f₂ ≫ pullback.snd _ _) : f₁ = f₂ :=
  pullback.hom_ext e₁ e₂

@[simp]
lemma tensorObj_left (R S : Over X) : (R ⊗ S).left = Limits.pullback R.hom S.hom := rfl

@[simp]
lemma tensorObj_hom (R S : Over X) : (R ⊗ S).hom = pullback.fst R.hom S.hom ≫ R.hom := rfl

@[simp]
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl

@[simp]
lemma lift_left {R S T : Over X} (f : R ⟶ S) (g : R ⟶ T) :
    (lift f g).left = pullback.lift f.left g.left (f.w.trans g.w.symm) := rfl

@[simp]
lemma toUnit_left {R : Over X} : (toUnit R).left = R.hom := rfl

@[reassoc (attr := simp)]
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.fst _ (pullback.fst _ _ ≫ _) =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ pullback.snd _ (pullback.fst _ _ ≫ _) ≫ pullback.snd _ _ =
      pullback.snd _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.fst _ _ =
      pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.fst (pullback.fst _ _ ≫ _) _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ :=
  (limit.lift_π_assoc _ _ _).trans (limit.lift_π _ _)

@[reassoc (attr := simp)]
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ pullback.snd (pullback.fst _ _ ≫ _) _ =
      pullback.snd _ _ ≫ pullback.snd _ _ :=
  limit.lift_π _ _

@[simp]
lemma leftUnitor_hom_left (Y : Over X) :
    (λ_ Y).hom.left = pullback.snd _ _ := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_fst (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.fst (𝟙 X) _ = Y.hom :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ pullback.snd (𝟙 X) _ = 𝟙 Y.left :=
  limit.lift_π _ _

@[simp]
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = pullback.fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.fst _ (𝟙 X) = 𝟙 _ :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ pullback.snd _ (𝟙 X) = Y.hom :=
  limit.lift_π _ _

lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullback.map _ _ _ _ (𝟙 _) f.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ pullback.snd _ _ = pullback.snd _ _ ≫ f.left :=
  limit.lift_π _ _

lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullback.map _ _ _ _ f.left (𝟙 _) (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (limit.lift_π _ _).trans (Category.comp_id _)

lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left = pullback.map _ _ _ _ f.left g.left (𝟙 _) (by simp) (by simp) := rfl

@[reassoc (attr := simp)]
lemma tensorHom_left_fst {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.fst fS fU = pullback.fst R.hom T.hom ≫ f.left :=
  limit.lift_π _ _

@[reassoc (attr := simp)]
lemma tensorHom_left_snd {S U : C} {R T : Over X} (fS : S ⟶ X) (fU : U ⟶ X)
    (f : R ⟶ mk fS) (g : T ⟶ mk fU) :
    (f ⊗ₘ g).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left :=
  limit.lift_π _ _

@[simp]
lemma braiding_hom_left {R S : Over X} :
    (β_ R S).hom.left = (pullbackSymmetry _ _).hom := rfl

@[simp]
lemma braiding_inv_left {R S : Over X} :
    (β_ R S).inv.left = (pullbackSymmetry _ _).hom := rfl

variable {A B R S Y Z : C} {f : R ⟶ X} {g : S ⟶ X}

instance : (Over.pullback f).Braided := .ofChosenFiniteProducts _

@[simp]
lemma η_pullback_left : (OplaxMonoidal.η (Over.pullback f)).left = (pullback.snd (𝟙 _) f) := rfl

@[simp]
lemma ε_pullback_left : (LaxMonoidal.ε (Over.pullback f)).left = inv (pullback.snd (𝟙 _) f) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← η_pullback_left, ← Over.comp_left, Monoidal.η_ε, Over.id_left]

lemma μ_pullback_left_fst_fst (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left, ← Over.comp_left_assoc,
    Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, fst]

lemma μ_pullback_left_fst_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫
      pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison, snd]

lemma μ_pullback_left_snd (R S : Over X) :
    (LaxMonoidal.μ (Over.pullback f) R S).left ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Monoidal.μ_of_cartesianMonoidalCategory,
    ← cancel_epi (prodComparisonIso (Over.pullback f) R S).hom.left,
    ← Over.comp_left_assoc, Iso.hom_inv_id]
  simp [CartesianMonoidalCategory.prodComparison]

@[simp]
lemma μ_pullback_left_fst_fst' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.fst g₁ g₂ =
        pullback.fst _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_fst ..

@[simp]
lemma μ_pullback_left_fst_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.fst (pullback.fst g₁ g₂ ≫ g₁) f ≫ pullback.snd g₁ g₂ =
        pullback.snd _ _ ≫ pullback.fst _ _ :=
  μ_pullback_left_fst_snd ..

@[simp]
lemma μ_pullback_left_snd' (g₁ : Y ⟶ X) (g₂ : Z ⟶ X) :
    (LaxMonoidal.μ (Over.pullback f) (.mk g₁) (.mk g₂)).left ≫
      pullback.snd (pullback.fst g₁ g₂ ≫ g₁) f =
        pullback.snd _ _ ≫ pullback.snd _ _ := μ_pullback_left_snd ..

@[simp]
lemma preservesTerminalIso_pullback (f : R ⟶ S) :
    preservesTerminalIso (Over.pullback f) =
      Over.isoMk (asIso (pullback.snd (𝟙 _) f)) (by simp) := by
  ext1; exact toUnit_unique _ _

@[simp]
lemma prodComparisonIso_pullback_inv_left_fst_fst (f : X ⟶ Y) (A B : Over Y) :
    (prodComparisonIso (Over.pullback f) A B).inv.left ≫
      pullback.fst (pullback.fst A.hom B.hom ≫ A.hom) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd A.hom f) (pullback.snd B.hom f) ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) A B).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, fst]

@[simp]
lemma prodComparisonIso_pullback_Spec_inv_left_fst_fst' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.fst _ _ =
        pullback.fst (pullback.snd gA f) (pullback.snd gB f) ≫ pullback.fst _ _ :=
  prodComparisonIso_pullback_inv_left_fst_fst ..

@[simp]
lemma prodComparisonIso_pullback_inv_left_fst_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.fst (pullback.fst gA gB ≫ gA) f ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ pullback.fst _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison, snd]

@[simp]
lemma prodComparisonIso_pullback_inv_left_snd' (f : X ⟶ Y) (gA : A ⟶ Y) (gB : B ⟶ Y) :
    (prodComparisonIso (Over.pullback f) (.mk gA) (.mk gB)).inv.left ≫
      pullback.snd (pullback.fst gA gB ≫ gA) f = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [← cancel_epi (prodComparisonIso (Over.pullback f) _ _).hom.left,
    Over.hom_left_inv_left_assoc]
  simp [CartesianMonoidalCategory.prodComparison]

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
abbrev monObjMkPullbackSnd [MonObj (Over.mk f)] : MonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapMon.obj <| .mk <| .mk f).mon

attribute [local instance] monObjMkPullbackSnd

instance isCommMonObj_mk_pullbackSnd [MonObj (Over.mk f)] [IsCommMonObj (Over.mk f)] :
    IsCommMonObj (Over.mk <| pullback.snd f g) :=
  ((Over.pullback g).mapCommMon.obj <| .mk <| .mk f).comm

/-- The pullback of a monoid object is a monoid object. -/
@[simps! -isSimp mul one]
abbrev grpObjMkPullbackSnd [GrpObj (Over.mk f)] : GrpObj (Over.mk (pullback.snd f g)) :=
  ((Over.pullback g).mapGrp.obj <| .mk <| .mk f).grp

attribute [local simp] monObjMkPullbackSnd_one in
instance isMonHom_pullbackFst_id_right [MonObj (Over.mk f)] :
    IsMonHom <| Over.homMk (U := Over.mk <| pullback.snd f (𝟙 X)) (V := Over.mk f)
      (pullback.fst f (𝟙 X)) (pullback.condition.trans <| by simp) where
  mul_hom := by
    ext
    dsimp [monObjMkPullbackSnd_mul]
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    simp only [← Category.assoc]
    congr 1
    ext <;> simp

end CategoryTheory.Over
