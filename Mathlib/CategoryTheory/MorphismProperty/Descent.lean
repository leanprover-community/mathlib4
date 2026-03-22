/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!
# Descent of morphism properties

Given morphism properties `P` and `Q` we say that `P` descends along `Q` (`P.DescendsAlong Q`),
if whenever `Q` holds for `X ⟶ Z`, `P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`.
Dually, we define `P.CodescendsAlong Q`.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type*} [Category* C]

variable {P Q W : MorphismProperty C}

/-- `P` descends along `Q` if whenever `Q` holds for `X ⟶ Z`,
`P` holds for `X ×[Z] Y ⟶ X` implies `P` holds for `Y ⟶ Z`. -/
class DescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPullback {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} :
    IsPullback fst snd f g → Q f → P fst → P g

section DescendsAlong

variable {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma of_isPullback_of_descendsAlong [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) (hfst : P fst) : P g :=
  DescendsAlong.of_isPullback h hf hfst

lemma iff_of_isPullback [P.IsStableUnderBaseChange] [P.DescendsAlong Q] (h : IsPullback fst snd f g)
    (hf : Q f) : P fst ↔ P g :=
  ⟨fun hfst ↦ of_isPullback_of_descendsAlong h hf hfst, fun hf ↦ P.of_isPullback h.flip hf⟩

lemma of_pullback_fst_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hf : Q f)
    (hfst : P (pullback.fst f g)) : P g :=
  of_isPullback_of_descendsAlong (.of_hasPullback f g) hf hfst

lemma pullback_fst_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hf : Q f) : P (pullback.fst f g) ↔ P g :=
  iff_of_isPullback (.of_hasPullback f g) hf

lemma of_pullback_snd_of_descendsAlong [P.DescendsAlong Q] [HasPullback f g] (hg : Q g)
    (hsnd : P (pullback.snd f g)) : P f :=
  of_isPullback_of_descendsAlong (IsPullback.of_hasPullback f g).flip hg hsnd

lemma pullback_snd_iff [P.IsStableUnderBaseChange] [P.DescendsAlong Q] [HasPullback f g]
    (hg : Q g) : P (pullback.snd f g) ↔ P f :=
  iff_of_isPullback (IsPullback.of_hasPullback f g).flip hg

instance DescendsAlong.top : (⊤ : MorphismProperty C).DescendsAlong Q where
  of_isPullback _ _ _ := trivial

instance DescendsAlong.inf [P.DescendsAlong Q] [W.DescendsAlong Q] : (P ⊓ W).DescendsAlong Q where
  of_isPullback h hg hfst :=
    ⟨DescendsAlong.of_isPullback h hg hfst.1, DescendsAlong.of_isPullback h hg hfst.2⟩

lemma DescendsAlong.of_le [P.DescendsAlong Q] (hle : W ≤ Q) : P.DescendsAlong W where
  of_isPullback h hg hfst := DescendsAlong.of_isPullback h (hle _ hg) hfst

/-- Alternative constructor for `CodescendsAlong` using `HasPullback`. -/
lemma DescendsAlong.mk' [P.RespectsIso]
    (H : ∀ {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g],
      Q f → P (pullback.fst f g) → P g) :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : HasPullback f g := h.hasPullback
    apply H hf
    rwa [← P.cancel_left_of_respectsIso h.isoPullback.hom, h.isoPullback_hom_fst]

instance [Q.IsStableUnderBaseChange] [P.HasOfPrecompProperty Q] [P.RespectsRight Q] :
    P.DescendsAlong Q where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    apply P.of_precomp (W' := Q) _ _ (Q.of_isPullback h hf)
    rw [← h.1.1]
    exact RespectsRight.postcomp _ hf _ hfst

set_option backward.isDefEq.respectTransparency false in
/-- If `P` descends along `Q`, then `P.diagonal` descends along `Q`. -/
instance [HasPullbacks C] (P Q : MorphismProperty C) [P.DescendsAlong Q] [P.RespectsIso]
    [Q.IsStableUnderBaseChange] :
    DescendsAlong (diagonal P) Q := by
  apply DescendsAlong.mk'
  introv hf hfst
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫
      pullback.diagonal (pullback.fst f g) ≫
      (diagonalObjPullbackFstIso f g).hom := by
    apply pullback.hom_ext
    apply pullback.hom_ext <;> simp [pullback.condition]
    simp [pullback.condition]
  rw [diagonal_iff]
  apply MorphismProperty.of_pullback_fst_of_descendsAlong (P := P) (Q := Q)
      (f := pullback.fst (pullback.snd g g ≫ g) f)
  · exact MorphismProperty.pullback_fst _ _ hf
  · rw [heq]
    iterate 4 rw [cancel_left_of_respectsIso (P := P)]
    rwa [cancel_right_of_respectsIso (P := P)]

lemma eq_of_isomorphisms_descendsAlong [(MorphismProperty.isomorphisms C).DescendsAlong P]
    [P.IsStableUnderBaseChange] [HasEqualizers C]
    [HasPullbacks C] {X Y S T : C} {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s)
    (hg : g ≫ t = s) (v : T ⟶ S) (hv : P v)
    (H :
      pullback.map s v t v f (𝟙 T) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s v t v g (𝟙 T) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  apply (MorphismProperty.isomorphisms C).of_isPullback_of_descendsAlong
    (IsPullback.of_hasPullback _ _).flip (P.pullback_fst s v hv)
  have : pullback.snd (equalizer.ι f g) (pullback.fst s v) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq H

set_option backward.isDefEq.respectTransparency false in
lemma faithful_overPullback_of_isomorphisms_descendAlong
    [(MorphismProperty.isomorphisms C).DescendsAlong P] [P.IsStableUnderBaseChange]
    [HasPullbacks C] [HasEqualizers C] {S T : C} {f : T ⟶ S} (hf : P f) :
    (Over.pullback f).Faithful := by
  refine ⟨fun {X} Y a b hab ↦ ?_⟩
  ext
  apply P.eq_of_isomorphisms_descendsAlong (Over.w a) (Over.w b) f hf
  convert congr($(hab).left) <;> ext <;> simp

end DescendsAlong

/-- `P` codescends along `Q` if whenever `Q` holds for `Z ⟶ X`,
`P` holds for `X ⟶ X ∐[Z] Y` implies `P` holds for `Z ⟶ Y`. -/
class CodescendsAlong (P Q : MorphismProperty C) : Prop where
  of_isPushout {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A} :
    IsPushout f g inl inr → Q f → P inl → P g

section CodescendsAlong

variable {Z X Y A : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ A} {inr : Y ⟶ A}

lemma of_isPushout_of_codescendsAlong [P.CodescendsAlong Q] (h : IsPushout f g inl inr)
    (hf : Q f) (hinl : P inl) : P g :=
  CodescendsAlong.of_isPushout h hf hinl

lemma iff_of_isPushout [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q]
    (h : IsPushout f g inl inr) (hg : Q f) : P inl ↔ P g :=
  ⟨fun hinl ↦ of_isPushout_of_codescendsAlong h hg hinl, fun hf ↦ P.of_isPushout h hf⟩

lemma of_pushout_inl_of_codescendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hf : Q f)
    (hinl : P (pushout.inl f g)) : P g :=
  of_isPushout_of_codescendsAlong (.of_hasPushout f g) hf hinl

lemma pushout_inl_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hf : Q f) : P (pushout.inl f g) ↔ P g :=
  iff_of_isPushout (.of_hasPushout f g) hf

lemma of_pushout_inr_of_descendsAlong [P.CodescendsAlong Q] [HasPushout f g] (hg : Q g)
    (hinr : P (pushout.inr f g)) : P f :=
  of_isPushout_of_codescendsAlong (IsPushout.of_hasPushout f g).flip hg hinr

lemma pushout_inr_iff [P.IsStableUnderCobaseChange] [P.CodescendsAlong Q] [HasPushout f g]
    (hg : Q g) : P (pushout.inr f g) ↔ P f :=
  iff_of_isPushout (IsPushout.of_hasPushout f g).flip hg

lemma CodescendsAlong.of_le [P.CodescendsAlong Q] (hle : W ≤ Q) : P.CodescendsAlong W where
  of_isPushout h hg hinl := CodescendsAlong.of_isPushout h (hle _ hg) hinl

instance CodescendsAlong.top : (⊤ : MorphismProperty C).CodescendsAlong Q where
  of_isPushout _ _ _ := trivial

instance CodescendsAlong.inf [P.CodescendsAlong Q] [W.CodescendsAlong Q] :
    (P ⊓ W).CodescendsAlong Q where
  of_isPushout h hg hfst :=
    ⟨CodescendsAlong.of_isPushout h hg hfst.1, CodescendsAlong.of_isPushout h hg hfst.2⟩

/-- Alternative constructor for `CodescendsAlong` using `HasPushout`. -/
lemma CodescendsAlong.mk' [P.RespectsIso]
    (H : ∀ {X Y Z : C} {f : Z ⟶ X} {g : Z ⟶ Y} [HasPushout f g], Q f → P (pushout.inl f g) → P g) :
    P.CodescendsAlong Q where
  of_isPushout {A X Y Z f g inl inr} h hf hfst := by
    have : HasPushout f g := h.hasPushout
    apply H hf
    rwa [← P.cancel_right_of_respectsIso _ h.isoPushout.inv, h.inl_isoPushout_inv]

instance [Q.IsStableUnderCobaseChange] [P.HasOfPostcompProperty Q] [P.RespectsLeft Q] :
    P.CodescendsAlong Q where
  of_isPushout {X Y Z A f g inl inr} h hf hinl := by
    apply P.of_postcomp (W' := Q) g inr (Q.of_isPushout h.flip hf)
    rw [← h.1.1]
    exact RespectsLeft.precomp _ hf _ hinl

end CodescendsAlong

end CategoryTheory.MorphismProperty
