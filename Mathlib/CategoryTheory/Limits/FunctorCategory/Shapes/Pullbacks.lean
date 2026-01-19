/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks in functor categories

We prove the isomorphism `(pullback f g).obj d ≅ pullback (f.app d) (g.app d)`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F G H : D ⥤ C}

section Pullback

/-- Given functors `F G H` and natural transformations `f : F ⟶ H` and `g : g : G ⟶ H`, together
with a collection of limiting pullback cones for each cospan `F X ⟶ H X, G X ⟶ H X`, we can stich
them together to give a pullback cone for the cospan formed by `f` and `g`.
`combinePullbackConesIsLimit` shows that this pullback cone is limiting. -/
@[simps!]
def PullbackCone.combine (f : F ⟶ H) (g : G ⟶ H) (c : ∀ X, PullbackCone (f.app X) (g.app X))
    (hc : ∀ X, IsLimit (c X)) : PullbackCone f g :=
  PullbackCone.mk (W := {
    obj X := (c X).pt
    map {X Y} h := (hc Y).lift ⟨_, (c X).π ≫ cospanHomMk (H.map h) (F.map h) (G.map h)⟩
    map_id _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp
    map_comp _ _ := (hc _).hom_ext <| by rintro (_ | _ | _); all_goals simp })
    { app X := (c X).fst }
    { app X := (c X).snd }
    (by ext; simp [(c _).condition])

/--
The pullback cone `combinePullbackCones` is limiting.
-/
def PullbackCone.combineIsLimit (f : F ⟶ H) (g : G ⟶ H)
    (c : ∀ X, PullbackCone (f.app X) (g.app X)) (hc : ∀ X, IsLimit (c X)) :
    IsLimit (combine f g c hc) :=
  evaluationJointlyReflectsLimits _ fun k ↦ by
    refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_ (hc k)
    · exact cospanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · refine Cones.ext (Iso.refl _) ?_
      rintro (_ | _ | _)
      all_goals cat_disch

variable [HasPullbacks C]

/-- Evaluating a pullback amounts to taking the pullback of the evaluations. -/
noncomputable def pullbackObjIso (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullback f g).obj d ≅ pullback (f.app d) (g.app d) :=
  limitObjIsoLimitCompEvaluation (cospan f g) d ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _)

@[reassoc (attr := simp)]
theorem pullbackObjIso_hom_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.fst (f.app d) (g.app d) = (pullback.fst f g).app d := by
  simp [pullbackObjIso]

@[reassoc (attr := simp)]
theorem pullbackObjIso_hom_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).hom ≫ pullback.snd (f.app d) (g.app d) = (pullback.snd f g).app d := by
  simp [pullbackObjIso]

@[reassoc (attr := simp)]
theorem pullbackObjIso_inv_comp_fst (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.fst f g).app d = pullback.fst (f.app d) (g.app d) := by
  simp [pullbackObjIso]

@[reassoc (attr := simp)]
theorem pullbackObjIso_inv_comp_snd (f : F ⟶ H) (g : G ⟶ H) (d : D) :
    (pullbackObjIso f g d).inv ≫ (pullback.snd f g).app d = pullback.snd (f.app d) (g.app d) := by
  simp [pullbackObjIso]

end Pullback

section Pushout

variable [HasPushouts C]

/-- Evaluating a pushout amounts to taking the pushout of the evaluations. -/
noncomputable def pushoutObjIso (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout f g).obj d ≅ pushout (f.app d) (g.app d) :=
  colimitObjIsoColimitCompEvaluation (span f g) d ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

@[reassoc (attr := simp)]
theorem inl_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inl f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inl (f.app d) (g.app d) := by
  simp [pushoutObjIso]

@[reassoc (attr := simp)]
theorem inr_comp_pushoutObjIso_hom (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    (pushout.inr f g).app d ≫ (pushoutObjIso f g d).hom = pushout.inr (f.app d) (g.app d) := by
  simp [pushoutObjIso]

@[reassoc (attr := simp)]
theorem inl_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inl (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inl f g).app d := by
  simp [pushoutObjIso]

@[reassoc (attr := simp)]
theorem inr_comp_pushoutObjIso_inv (f : F ⟶ G) (g : F ⟶ H) (d : D) :
    pushout.inr (f.app d) (g.app d) ≫ (pushoutObjIso f g d).inv = (pushout.inr f g).app d := by
  simp [pushoutObjIso]

end Pushout

end CategoryTheory.Limits
