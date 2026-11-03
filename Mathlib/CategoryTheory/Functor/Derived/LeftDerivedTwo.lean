/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Prod

/-!
# Left derived bifunctors

This files introduces a basic API for left derived bifunctors. In order
to state that a bifunctor `LF : D₁ ⥤ D₂ ⥤ H` is a left derived bifunctor
of `F : C₁ ⥤ C₂ ⥤ H` with respect to localization functors
`L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` for `W₁ : MorphismProperty C₁` and
`W₂ : MorphismProperty C₂` respectively, we translate the situation
into a context involving functors `D₁ × D₂ ⥤ H` and `C₁ × C₂ ⥤ H`
from products categories. This is justified by the fact that if `W₁` and
`W₂` contain identities, then `D₁ × D₂` identifies to the localized
category of `C₁ × C₂` with respect to `W₁.prod W₂ : MorphismProperty (C₁ × C₂)`.

In the `CategoryTheory.Functor` namespace, we introduce `HasLeftDerivedFunctor₂`,
`IsLeftDerivedFunctor₂`, `leftDerived₂` and`leftDerived₂Lift` as `2`-variable versions
of `HasLeftDerivedFunctor`, `IsLeftDerivedFunctor`, `leftDerived` and `leftDerivedLift`.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ H : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* H]
  (LF : D₁ ⥤ D₂ ⥤ H) (F : C₁ ⥤ C₂ ⥤ H)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F)
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]

/-- If `F : C₁ ⥤ C₂ ⥤ H` is a bifunctor, `W₁ : MorphismProperty C₁` and
`W₂ : MorphismProperty C₂`, this is the property that `F` admits a derived functor
in two variables, which is defined by saying that the corresponding uncurried
functor `C₁ × C₂ ⥤ H` admits a left derived functor with respect to `W₁.prod W₂`.
(This should be used only when both `W₁` and `W₂` contain identities.) -/
@[reducible] -- Making this an `abbrev` would create massive slowdowns in downstream code
def HasLeftDerivedFunctor₂ := (uncurry.obj F).HasLeftDerivedFunctor (W₁.prod W₂)

variable {F} [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- If `L₁ : C₁ ⥤ D₁` is localization functor for `W₁`, and
`L₂ : C₂ ⥤ D₂` is localization functor for `W₂`, `F : C₁ ⥤ C₂ ⥤ H`
and `LF : D₁ ⥤ D₂ ⥤ H` are bifunctors related by a natural transformation
`α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F`, we say that `α`
makes `LF` the left derived bifunctor of `F` if it is so for the corresponding
uncurried functors `C₁ × C₂ ⥤ H` and `D₁ × D₂ ⥤ H`. -/
@[reducible]
def IsLeftDerivedFunctor₂ : Prop :=
  (uncurry.obj LF).IsLeftDerivedFunctor (whiskeringLeft₂HomEquiv α) (W₁.prod W₂)

section

variable (F L₁ L₂) [HasLeftDerivedFunctor₂ F W₁ W₂]

/-- When it exists, this is a choice of a left derived bifunctor `D₁ ⥤ D₂ ⥤ H`
of a bifunctor `F : C₁ ⥤ C₂ ⥤ H` with respect to localization functors
`L₁ : C₁ ⥤ D₁` for `W₁ : MorphismProperty C₁` and
`L₂ : C₂ ⥤ D₂` for `W₂ : MorphismProperty C₂`. -/
@[no_expose, local implicit_reducible]
noncomputable def leftDerived₂ : D₁ ⥤ D₂ ⥤ H :=
  curry.obj ((uncurry.obj F).totalLeftDerived (L₁.prod L₂) (W₁.prod W₂))

/-- The natural transformation which exhibits `leftDerived₂ F L₁ L₂ W₁ W₂` as
a left derived bifunctor. -/
@[no_expose]
noncomputable def leftDerivedCounit₂ :
    (((whiskeringLeft₂ H).obj L₁).obj L₂).obj (leftDerived₂ F L₁ L₂ W₁ W₂) ⟶ F :=
  whiskeringLeft₂HomEquiv.symm (whiskerLeft _ (currying.counitIso.hom.app _) ≫
    ((uncurry.obj F).totalLeftDerivedCounit (L₁.prod L₂) (W₁.prod W₂)))

instance : (leftDerived₂ F L₁ L₂ W₁ W₂).IsLeftDerivedFunctor₂
    (leftDerivedCounit₂ F L₁ L₂ W₁ W₂) W₁ W₂ := by
  refine (isLeftDerivedFunctor_iff_of_iso
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

/-- A natural transformation of bifunctors that is constructed as part
of the universal property of left derived bifunctors. -/
@[no_expose]
noncomputable def leftDerived₂Lift : G ⟶ LF :=
  fullyFaithfulUncurry.preimage
    (leftDerivedLift (LF := uncurry.obj LF)
      (whiskeringLeft₂HomEquiv α) (W₁.prod W₂) (uncurry.obj G)
      (whiskeringLeft₂HomEquiv β))

@[reassoc (attr := simp)]
lemma leftDerived₂_fac_app_app (X₁ : C₁) (X₂ : C₂) :
    ((leftDerived₂Lift LF α W₁ W₂ G β).app (L₁.obj X₁)).app (L₂.obj X₂) ≫
      (α.app X₁).app X₂ = (β.app X₁).app X₂ := by
  simpa [leftDerived₂Lift, fullyFaithfulUncurry, Equivalence.fullyFaithfulFunctor]
    using leftDerived_fac_app (LF := uncurry.obj LF)
      (whiskeringLeft₂HomEquiv α) (W₁.prod W₂) (uncurry.obj G)
      (whiskeringLeft₂HomEquiv β) (X₁, X₂)

@[reassoc (attr := simp)]
lemma leftDerived₂_fac :
    (((whiskeringLeft₂ H).obj L₁).obj L₂).map (leftDerived₂Lift LF α W₁ W₂ G β) ≫ α = β := by
  cat_disch

include W₁ W₂ in
lemma leftDerived₂_ext {G : D₁ ⥤ D₂ ⥤ H} {γ₁ γ₂ : G ⟶ LF}
    (hγ : (((whiskeringLeft₂ H).obj L₁).obj L₂).map γ₁ ≫ α =
      (((whiskeringLeft₂ H).obj L₁).obj L₂).map γ₂ ≫ α := by cat_disch) : γ₁ = γ₂ := by
  apply uncurry.map_injective
  apply leftDerived_ext (α := whiskeringLeft₂HomEquiv α) (W := W₁.prod W₂)
  ext ⟨X₁, X₂⟩
  exact congr(($(hγ).app X₁).app X₂)

end

variable {LF}

/-- Given a natural transformation `α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F` of
bifunctors and `X₁ : C₁`, this is the obvious natural transformation of functors
`L₂ ⋙ LF.obj (L₁.obj X₁) ⟶ F.obj X₁`.
(If `α` makes `LF` the left derived bifunctor of `F`, this can be used to state
that the functor `LF.obj (L₁.obj X₁)` may be the left derived functor of `F.obj X₁`.) -/
def bifunctorCounit₁ (X₁ : C₁) : L₂ ⋙ LF.obj (L₁.obj X₁) ⟶ F.obj X₁ := α.app X₁

@[simp]
lemma bifunctorCounit₁_app (X₁ : C₁) (X₂ : C₂) :
    (bifunctorCounit₁ α X₁).app X₂ = (α.app X₁).app X₂ := rfl

/-- Given a natural transformation `α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F` of
bifunctors and `X₂ : C₂`, this is the obvious natural transformation of functors
`L₁ ⋙ LF.flip.obj (L₂.obj X₂) ⟶ F.flip.obj X₂`.
(If `α` makes `LF` the left derived bifunctor of `F`, this can be used to state
that the functor `LF.flip.obj (L₂.obj X₂)` may be the left derived functor of `F.flip.obj X₂`.) -/
def bifunctorCounit₂ (X₂ : C₂) : L₁ ⋙ LF.flip.obj (L₂.obj X₂) ⟶ F.flip.obj X₂ :=
  ((flipFunctor _ _ _).map α).app X₂

@[simp]
lemma bifunctorCounit₂_app (X₁ : C₁) (X₂ : C₂) :
    (bifunctorCounit₂ α X₂).app X₁ = (α.app X₁).app X₂ := rfl

end CategoryTheory.Functor
