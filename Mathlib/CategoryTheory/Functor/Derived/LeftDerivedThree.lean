/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
import Mathlib.CategoryTheory.Functor.CurryingThree

/-!
# Left derived trifunctors

-/

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ D₁ D₂ D₃ H : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃] [Category H]

@[simps]
def whiskeringLeft₃Equiv {F : D₁ ⥤ D₂ ⥤ D₃ ⥤ H} {G : C₁ ⥤ C₂ ⥤ C₃ ⥤ H}
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} :
    (((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj F ⟶ G) ≃
      (L₁.prod (L₂.prod L₃) ⋙ uncurry₃.obj F ⟶ uncurry₃.obj G) where
  toFun α :=
    { app := fun ⟨X₁, X₂, X₃⟩ ↦ ((α.app X₁).app X₂).app X₃
      naturality X Y f := by
        have h₁ := congr_app (congr_app (α.naturality f.1) X.2.1) X.2.2
        have h₂ := congr_app ((α.app Y.1).naturality f.2.1) X.2.2
        have h₃ := ((α.app Y.1).app Y.2.1).naturality f.2.2
        dsimp at h₁ h₂ h₃ ⊢
        rw [Category.assoc, Category.assoc, Category.assoc, h₃, reassoc_of% h₂, reassoc_of% h₁] }
  invFun β :=
    { app X₁ :=
        { app X₂ :=
            { app X₃ := β.app (X₁, X₂, X₃)
              naturality {X₃ Y₃} f₃ := by
                simpa using β.naturality ((𝟙 X₁, 𝟙 X₂, f₃) : (X₁, X₂, X₃) ⟶ (X₁, X₂, Y₃)) }
          naturality {X₂ Y₂} f₂ := by
            ext X₃
            simpa using β.naturality ((𝟙 X₁, f₂, 𝟙 X₃) : (X₁, X₂, X₃) ⟶ (X₁, Y₂, X₃)) }
      naturality {X₁ Y₁} f₁ := by
        ext X₂ X₃
        simpa using β.naturality ((f₁, 𝟙 X₂, 𝟙 X₃) : (X₁, X₂, X₃) ⟶ (Y₁, X₂, X₃)) }
  left_inv _ := rfl
  right_inv _ := rfl

variable (LF LF' LF'' : D₁ ⥤ D₂ ⥤ D₃ ⥤ H) (F F' F'' : C₁ ⥤ C₂ ⥤ C₃ ⥤ H)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
  (α : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF ⟶ F)
  (α' : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF' ⟶ F')
  (α'₂ : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF' ⟶ F)
  (α'' : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj LF'' ⟶ F'')
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃]

abbrev HasLeftDerivedFunctor₃ := (uncurry₃.obj F).HasLeftDerivedFunctor (W₁.prod (W₂.prod W₃))

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

variable {F F'}

abbrev IsLeftDerivedFunctor₃ : Prop :=
  (uncurry₃.obj LF).IsLeftDerivedFunctor (whiskeringLeft₃Equiv α) (W₁.prod (W₂.prod W₃))

section

variable (F L₁ L₂ L₃) [HasLeftDerivedFunctor₃ F W₁ W₂ W₃]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities] [W₃.ContainsIdentities]

noncomputable def leftDerived₃ : D₁ ⥤ D₂ ⥤ D₃ ⥤ H :=
    curry₃.obj ((uncurry₃.obj F).totalLeftDerived (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃)))

noncomputable def leftDerivedCounit₃ :
    ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj (leftDerived₃ F L₁ L₂ L₃ W₁ W₂ W₃) ⟶ F :=
  whiskeringLeft₃Equiv.symm (whiskerLeft _ (currying₃.counitIso.hom.app _) ≫
    ((uncurry₃.obj F).totalLeftDerivedCounit (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))))

instance : (leftDerived₃ F L₁ L₂ L₃ W₁ W₂ W₃).IsLeftDerivedFunctor₃
    (leftDerivedCounit₃ F L₁ L₂ L₃ W₁ W₂ W₃) W₁ W₂ W₃ := by
  refine (isLeftDerivedFunctor_iff_of_iso _ _
    ((uncurry₃.obj F).totalLeftDerivedCounit (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))) _ _
    (currying₃.counitIso.symm.app
      (((uncurry₃.obj F).totalLeftDerived
      (L₁.prod (L₂.prod L₃)) (W₁.prod (W₂.prod W₃))))) ?_).1 inferInstance
  ext
  simp [leftDerivedCounit₃]

end

section

variable [LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃]
  [LF'.IsLeftDerivedFunctor₃ α' W₁ W₂ W₃]
  [LF''.IsLeftDerivedFunctor₃ α'' W₁ W₂ W₃]
  (G : D₁ ⥤ D₂ ⥤ D₃ ⥤ H)
  (β : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).obj G ⟶ F)

noncomputable def leftDerived₃Lift : G ⟶ LF :=
  fullyFaithfulUncurry₃.preimage
    (leftDerivedLift (LF := uncurry₃.obj LF)
      (whiskeringLeft₃Equiv α) (W₁.prod (W₂.prod W₃)) (uncurry₃.obj G)
      (whiskeringLeft₃Equiv β))

@[reassoc (attr := simp)]
lemma leftDerived₃_fac_app_app (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((leftDerived₃Lift LF α W₁ W₂ W₃ G β).app (L₁.obj X₁)).app (L₂.obj X₂)).app (L₃.obj X₃) ≫
      ((α.app X₁).app X₂).app X₃ = ((β.app X₁).app X₂).app X₃ := by
  simpa [leftDerived₃Lift, fullyFaithfulUncurry₃, Equivalence.fullyFaithfulFunctor] using
    (leftDerived_fac_app (LF := uncurry₃.obj LF)
      (whiskeringLeft₃Equiv α) (W₁.prod (W₂.prod W₃)) (uncurry₃.obj G)
      (whiskeringLeft₃Equiv β)) (X₁, X₂, X₃)

@[reassoc (attr := simp)]
lemma leftDerived₃_fac :
    ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).map
      (leftDerived₃Lift LF α W₁ W₂ W₃ G β) ≫ α = β := by
  aesop

include W₁ W₂ W₃ in
lemma leftDerived₃_ext (G : D₁ ⥤ D₂ ⥤ D₃ ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).map γ₁ ≫ α =
      ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).map γ₂ ≫ α) : γ₁ = γ₂ := by
  apply uncurry₃.map_injective
  apply leftDerived_ext (α := (whiskeringLeft₃Equiv α)) (W := W₁.prod (W₂.prod W₃))
  ext ⟨X₁, X₂, X₃⟩
  exact congr_app (congr_app (congr_app hγ X₁) X₂) X₃

noncomputable def leftDerived₃NatTrans (τ : F ⟶ F') : LF ⟶ LF' :=
  LF'.leftDerived₃Lift α' W₁ W₂ W₃ LF (α ≫ τ)

omit [LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃] in
@[reassoc (attr := simp)]
lemma leftDerived₃NatTrans_fac (τ : F ⟶ F') :
    ((((whiskeringLeft₃ H).obj L₁).obj L₂).obj L₃).map
      (leftDerived₃NatTrans LF LF' α α' W₁ W₂ W₃ τ) ≫ α' =
    α ≫ τ := by
  dsimp only [leftDerived₃NatTrans]
  simp

omit [LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃] in
@[reassoc (attr := simp)]
lemma leftDerived₃NatTrans_app (τ : F ⟶ F') (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) :
    (((leftDerived₃NatTrans LF LF' α α' W₁ W₂ W₃ τ).app (L₁.obj X₁)).app
      (L₂.obj X₂)).app (L₃.obj X₃) ≫ ((α'.app X₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((τ.app X₁).app X₂).app X₃ := by
  dsimp only [leftDerived₃NatTrans]
  simp

@[simp]
lemma leftDerived₃NatTrans_id :
    leftDerived₃NatTrans LF LF α α W₁ W₂ W₃ (𝟙 F) = 𝟙 LF :=
  leftDerived₃_ext LF α W₁ W₂ W₃ _ _ _ (by aesop_cat)

omit [LF.IsLeftDerivedFunctor₃ α W₁ W₂ W₃] in
@[reassoc (attr := simp)]
lemma leftDerived₃NatTrans_comp (τ : F ⟶ F') (τ' : F' ⟶ F'') :
  leftDerived₃NatTrans LF LF' α α' W₁ W₂ W₃ τ ≫
      leftDerived₃NatTrans LF' LF'' α' α'' W₁ W₂ W₃ τ' =
    leftDerived₃NatTrans LF LF'' α α'' W₁ W₂ W₃ (τ ≫ τ') :=
  leftDerived₃_ext LF'' α'' W₁ W₂ W₃ _ _ _ (by aesop_cat)

@[simps]
noncomputable def leftDerived₃NatIso (τ : F ≅ F') :
    LF ≅ LF' where
  hom := leftDerived₃NatTrans LF LF' α α' W₁ W₂ W₃ τ.hom
  inv := leftDerived₃NatTrans LF' LF α' α W₁ W₂ W₃ τ.inv

@[simp]
noncomputable def leftDerivedFunctor₃Unique [LF'.IsLeftDerivedFunctor₃ α'₂ W₁ W₂ W₃] :
    LF ≅ LF' :=
  leftDerived₃NatIso LF LF' α α'₂ W₁ W₂ W₃ (Iso.refl F)

end

end Functor

end CategoryTheory
