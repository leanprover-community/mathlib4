/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Localization.Prod

/-!
# Left derived bifunctors

-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ D₁ D₂ H : Type*} [Category C₁] [Category C₂]
  [Category D₁] [Category D₂] [Category H]

@[simps]
def whiskeringLeft₂Equiv {F : D₁ ⥤ D₂ ⥤ H} {G : C₁ ⥤ C₂ ⥤ H}
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} :
    ((((whiskeringLeft₂ H).obj L₁).obj L₂).obj F ⟶ G) ≃
      (L₁.prod L₂ ⋙ uncurry.obj F ⟶ uncurry.obj G) where
  toFun α :=
    { app := fun ⟨X₁, X₂⟩ ↦ (α.app X₁).app X₂
      naturality := by
        rintro X Y f
        have h₁ := NatTrans.congr_app (α.naturality f.1) X.2
        have h₂ := (α.app Y.1).naturality f.2
        dsimp at h₁ h₂ ⊢
        rw [Category.assoc, h₂, reassoc_of% h₁] }
  invFun β :=
    { app X₁ :=
        { app X₂ := β.app (X₁, X₂)
          naturality {X₂ Y₂} f₂ := by
            simpa using β.naturality ((𝟙 X₁, f₂) : (X₁, X₂) ⟶ (X₁, Y₂)) }
      naturality {X₁ Y₁} f₁ := by
        ext X₂
        simpa using β.naturality ((f₁, 𝟙 X₂) : (X₁, X₂) ⟶ (Y₁, X₂)) }
  left_inv _ := rfl
  right_inv _ := rfl

variable (LF : D₁ ⥤ D₂ ⥤ H) (F : C₁ ⥤ C₂ ⥤ H)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]

abbrev HasLeftDerivedFunctor₂ := (uncurry.obj F).HasLeftDerivedFunctor (W₁.prod W₂)

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

variable {F}

abbrev IsLeftDerivedFunctor₂ : Prop :=
  (uncurry.obj LF).IsLeftDerivedFunctor (whiskeringLeft₂Equiv α) (W₁.prod W₂)

section

variable (F L₁ L₂)
variable [HasLeftDerivedFunctor₂ F W₁ W₂] [W₁.ContainsIdentities] [W₂.ContainsIdentities]

noncomputable def leftDerived₂ : D₁ ⥤ D₂ ⥤ H :=
    curry.obj ((uncurry.obj F).totalLeftDerived (L₁.prod L₂) (W₁.prod W₂))

noncomputable def leftDerivedCounit₂ :
    (((whiskeringLeft₂ H).obj L₁).obj L₂).obj (leftDerived₂ F L₁ L₂ W₁ W₂) ⟶ F :=
  whiskeringLeft₂Equiv.symm (whiskerLeft _ (currying.counitIso.hom.app _) ≫
    ((uncurry.obj F).totalLeftDerivedCounit (L₁.prod L₂) (W₁.prod W₂)))

set_option backward.isDefEq.respectTransparency false in
instance : (leftDerived₂ F L₁ L₂ W₁ W₂).IsLeftDerivedFunctor₂
    (leftDerivedCounit₂ F L₁ L₂ W₁ W₂) W₁ W₂ := by
  refine (isLeftDerivedFunctor_iff_of_iso _ _
    ((uncurry.obj F).totalLeftDerivedCounit (L₁.prod L₂) (W₁.prod W₂)) _ _
    (currying.counitIso.symm.app
      (((uncurry.obj F).totalLeftDerived (L₁.prod L₂) (W₁.prod W₂)))) ?_).1 inferInstance
  ext
  simp [leftDerivedCounit₂]

end

section

variable [LF.IsLeftDerivedFunctor₂ α W₁ W₂]
  (G : D₁ ⥤ D₂ ⥤ H)
  (β : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj G ⟶ F)

noncomputable def leftDerived₂Lift : G ⟶ LF :=
  fullyFaithfulUncurry.preimage
    (leftDerivedLift (LF := uncurry.obj LF)
      (whiskeringLeft₂Equiv α) (W₁.prod W₂) (uncurry.obj G)
      (whiskeringLeft₂Equiv β))

@[reassoc (attr := simp)]
lemma leftDerived₂_fac_app_app (X₁ : C₁) (X₂ : C₂) :
    ((leftDerived₂Lift LF α W₁ W₂ G β).app (L₁.obj X₁)).app (L₂.obj X₂) ≫
      (α.app X₁).app X₂ = (β.app X₁).app X₂ := by
  simpa [leftDerived₂Lift, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
    using leftDerived_fac_app (LF := uncurry.obj LF)
      (whiskeringLeft₂Equiv α) (W₁.prod W₂) (uncurry.obj G)
      (whiskeringLeft₂Equiv β) (X₁, X₂)

@[reassoc (attr := simp)]
lemma leftDerived₂_fac :
    (((whiskeringLeft₂ H).obj L₁).obj L₂).map (leftDerived₂Lift LF α W₁ W₂ G β) ≫ α = β := by
  aesop

include W₁ W₂ in
lemma leftDerived₂_ext (G : D₁ ⥤ D₂ ⥤ H) (γ₁ γ₂ : G ⟶ LF)
    (hγ : (((whiskeringLeft₂ H).obj L₁).obj L₂).map γ₁ ≫ α =
      (((whiskeringLeft₂ H).obj L₁).obj L₂).map γ₂ ≫ α) : γ₁ = γ₂ := by
  apply uncurry.map_injective
  apply leftDerived_ext (α := (whiskeringLeft₂Equiv α)) (W := W₁.prod W₂)
  ext ⟨X₁, X₂⟩
  exact congr_app (congr_app hγ X₁) X₂

end

variable {LF}

def bifunctorCounit₁ (X₁ : C₁) : L₂ ⋙ LF.obj (L₁.obj X₁) ⟶ F.obj X₁ := α.app X₁

@[simp]
lemma bifunctorCounit₁_app (X₁ : C₁) (X₂ : C₂) :
    (bifunctorCounit₁ α X₁).app X₂ = (α.app X₁).app X₂ := rfl

def bifunctorCounit₂ (X₂ : C₂) : L₁ ⋙ LF.flip.obj (L₂.obj X₂) ⟶ F.flip.obj X₂ :=
  ((flipFunctor _ _ _).map α).app X₂

@[simp]
lemma bifunctorCounit₂_app (X₁ : C₁) (X₂ : C₂) :
    (bifunctorCounit₂ α X₂).app X₁ = (α.app X₁).app X₂ := rfl

end Functor

end CategoryTheory
