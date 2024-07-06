/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

#align_import category_theory.limits.shapes.pullbacks from "leanprover-community/mathlib"@"7316286ff2942aa14e540add9058c6b0aa1c8070"

/-!
# Pullbacks and monomorphisms

This file provides some results about interactions between pullbacks and monomorphisms, as well as
the dual statements between pushouts and epimorphisms.

## Main results
* Monomorphisms are stable under pullback. This is available using the `PullbackCone` API as
`mono_fst_of_is_pullback_of_mono` and `mono_snd_of_is_pullback_of_mono`, and using the `pullback`
API as `pullback.fst_of_mono` and `pullback.snd_of_mono`.

* A pullback cone is a limit iff its composition with a monomorphism is a limit. This is available
as `IsLimitOfCompMono` and `pullbackIsPullbackOfCompMono` respectively.

* Monomorphisms admit kernel pairs, this is `has_kernel_pair_of_mono`.

The dual notions for pushouts are also available.
-/

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

open WalkingSpan.Hom WalkingCospan.Hom WidePullbackShape.Hom WidePushoutShape.Hom PullbackCone

variable {C : Type u} [Category.{v} C] {W X Y Z : C}

section Monomorphisms

namespace PullbackCone

variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Monomorphisms are stable under pullback in the first argument. -/
theorem mono_snd_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono f] :
    Mono t.snd := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht ?_ i⟩
  rw [← cancel_mono f, Category.assoc, Category.assoc, condition]
  have := congrArg (· ≫ g) i; dsimp at this
  rwa [Category.assoc, Category.assoc] at this
#align category_theory.limits.pullback_cone.mono_snd_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_snd_of_is_pullback_of_mono

/-- Monomorphisms are stable under pullback in the second argument. -/
theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← condition]
  have := congrArg (· ≫ f) i; dsimp at this
  rwa [Category.assoc, Category.assoc] at this
#align category_theory.limits.pullback_cone.mono_fst_of_is_pullback_of_mono CategoryTheory.Limits.PullbackCone.mono_fst_of_is_pullback_of_mono

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁
#align category_theory.limits.pullback_cone.is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.isLimitMkIdId

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `PullbackCone.is_id_of_mono`.
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩
#align category_theory.limits.pullback_cone.mono_of_is_limit_mk_id_id CategoryTheory.Limits.PullbackCone.mono_of_isLimitMkIdId

/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
    `x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and
    `y`.  -/
def isLimitOfFactors (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Z) [Mono h] (x : X ⟶ W) (y : Y ⟶ W)
    (hxh : x ≫ h = f) (hyh : y ≫ h = g) (s : PullbackCone f g) (hs : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ x = s.snd ≫ y from
          (cancel_mono h).1 <| by simp only [Category.assoc, hxh, hyh, s.condition])) :=
  PullbackCone.isLimitAux' _ fun t =>
    have : fst t ≫ x ≫ h = snd t ≫ y ≫ h := by  -- Porting note: reassoc workaround
      rw [← Category.assoc, ← Category.assoc]
      apply congrArg (· ≫ h) t.condition
    ⟨hs.lift (PullbackCone.mk t.fst t.snd <| by rw [← hxh, ← hyh, this]),
      ⟨hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right, fun hr hr' => by
        apply PullbackCone.IsLimit.hom_ext hs <;>
              simp only [PullbackCone.mk_fst, PullbackCone.mk_snd] at hr hr' ⊢ <;>
            simp only [hr, hr'] <;>
          symm
        exacts [hs.fac _ WalkingCospan.left, hs.fac _ WalkingCospan.right]⟩⟩
#align category_theory.limits.pullback_cone.is_limit_of_factors CategoryTheory.Limits.PullbackCone.isLimitOfFactors

/-- If `W` is the pullback of `f, g`, it is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
def isLimitOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] (s : PullbackCone f g)
    (H : IsLimit s) :
    IsLimit
      (PullbackCone.mk _ _
        (show s.fst ≫ f ≫ i = s.snd ≫ g ≫ i by
          rw [← Category.assoc, ← Category.assoc, s.condition])) := by
  apply PullbackCone.isLimitAux'
  intro s
  rcases PullbackCone.IsLimit.lift' H s.fst s.snd
      ((cancel_mono i).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
#align category_theory.limits.pullback_cone.is_limit_of_comp_mono CategoryTheory.Limits.PullbackCone.isLimitOfCompMono

end PullbackCone

end Monomorphisms

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst : pullback f g ⟶ X) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.fst_of_mono CategoryTheory.Limits.pullback.fst_of_mono

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd : pullback f g ⟶ Y) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)
#align category_theory.limits.pullback.snd_of_mono CategoryTheory.Limits.pullback.snd_of_mono

/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift pullback.fst pullback.snd : pullback f g ⟶ _) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩
#align category_theory.limits.mono_pullback_to_prod CategoryTheory.Limits.mono_pullback_to_prod


/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk pullback.fst pullback.snd
      (show pullback.fst ≫ f ≫ i = pullback.snd ≫ g ≫ i from by -- Porting note: used to be _
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition)) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))
#align category_theory.limits.pullback_is_pullback_of_comp_mono CategoryTheory.Limits.pullbackIsPullbackOfCompMono

instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩
#align category_theory.limits.has_pullback_of_comp_mono CategoryTheory.Limits.hasPullback_of_comp_mono

section

attribute [local instance] hasPullback_of_left_iso

variable (f : X ⟶ Z) (i : Z ⟶ W) [Mono i]

instance hasPullback_of_right_factors_mono : HasPullback i (f ≫ i) := by
  conv =>
    congr
    rw [← Category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_right_factors_mono CategoryTheory.Limits.hasPullback_of_right_factors_mono

instance pullback_snd_iso_of_right_factors_mono :
    IsIso (pullback.snd : pullback i (f ≫ i) ⟶ _) := by
  #adaptation_note /-- nightly-testing 2024-04-01
  this could not be placed directly in the `show from` without `dsimp` -/
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  dsimp only [cospan_right, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    Functor.const_obj_obj, cospan_one] at this
  convert (congrArg IsIso (show _ ≫ pullback.snd = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_right_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_right_factors_mono

attribute [local instance] hasPullback_of_right_iso

instance hasPullback_of_left_factors_mono : HasPullback (f ≫ i) i := by
  conv =>
    congr
    case g => rw [← Category.id_comp i]
  infer_instance
#align category_theory.limits.has_pullback_of_left_factors_mono CategoryTheory.Limits.hasPullback_of_left_factors_mono

instance pullback_snd_iso_of_left_factors_mono :
    IsIso (pullback.fst : pullback (f ≫ i) i ⟶ _) := by
  #adaptation_note /-- nightly-testing 2024-04-01
  this could not be placed directly in the `show from` without `dsimp` -/
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  dsimp only [cospan_left, id_eq, eq_mpr_eq_cast, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    Functor.const_obj_obj, cospan_one] at this
  convert (congrArg IsIso (show _ ≫ pullback.fst = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
#align category_theory.limits.pullback_snd_iso_of_left_factors_mono CategoryTheory.Limits.pullback_snd_iso_of_left_factors_mono

end

section

open WalkingCospan

variable (f : X ⟶ Y)

instance has_kernel_pair_of_mono [Mono f] : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_kernel_pair_of_mono CategoryTheory.Limits.has_kernel_pair_of_mono

theorem fst_eq_snd_of_mono_eq [Mono f] : (pullback.fst : pullback f f ⟶ _) = pullback.snd :=
  ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).cone left).symm.trans
    ((PullbackCone.isLimitMkIdId f).fac (getLimitCone (cospan f f)).cone right : _)
#align category_theory.limits.fst_eq_snd_of_mono_eq CategoryTheory.Limits.fst_eq_snd_of_mono_eq

@[simp]
theorem pullbackSymmetry_hom_of_mono_eq [Mono f] : (pullbackSymmetry f f).hom = 𝟙 _ := by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]
#align category_theory.limits.pullback_symmetry_hom_of_mono_eq CategoryTheory.Limits.pullbackSymmetry_hom_of_mono_eq

instance fst_iso_of_mono_eq [Mono f] : IsIso (pullback.fst : pullback f f ⟶ _) := by
  refine ⟨⟨pullback.lift (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  ext
  · simp
  · simp [fst_eq_snd_of_mono_eq]
#align category_theory.limits.fst_iso_of_mono_eq CategoryTheory.Limits.fst_iso_of_mono_eq

instance snd_iso_of_mono_eq [Mono f] : IsIso (pullback.snd : pullback f f ⟶ _) := by
  rw [← fst_eq_snd_of_mono_eq]
  infer_instance
#align category_theory.limits.snd_iso_of_mono_eq CategoryTheory.Limits.snd_iso_of_mono_eq

end

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩
#align category_theory.limits.pushout_cocone.epi_inr_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inr_of_is_pushout_of_epi

theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩
#align category_theory.limits.pushout_cocone.epi_inl_of_is_pushout_of_epi CategoryTheory.Limits.PushoutCocone.epi_inl_of_is_pushout_of_epi

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_isColimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun s => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁
#align category_theory.limits.pushout_cocone.is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.isColimitMkIdId

/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `PushoutCocone.isColimitMkIdId`.
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩
#align category_theory.limits.pushout_cocone.epi_of_is_colimit_mk_id_id CategoryTheory.Limits.PushoutCocone.epi_of_isColimitMkIdId

/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
    diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
    `x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
    `y`.  -/
def isColimitOfFactors (f : X ⟶ Y) (g : X ⟶ Z) (h : X ⟶ W) [Epi h] (x : W ⟶ Y) (y : W ⟶ Z)
    (hhx : h ≫ x = f) (hhy : h ≫ y = g) (s : PushoutCocone f g) (hs : IsColimit s) :
    have reassoc₁ : h ≫ x ≫ inl s = f ≫ inl s := by  -- Porting note: working around reassoc
      rw [← Category.assoc]; apply congrArg (· ≫ inl s) hhx
    have reassoc₂ : h ≫ y ≫ inr s = g ≫ inr s := by
      rw [← Category.assoc]; apply congrArg (· ≫ inr s) hhy
    IsColimit (PushoutCocone.mk _ _ (show x ≫ s.inl = y ≫ s.inr from
          (cancel_epi h).1 <| by rw [reassoc₁, reassoc₂, s.condition])) :=
  PushoutCocone.isColimitAux' _ fun t => ⟨hs.desc (PushoutCocone.mk t.inl t.inr <| by
    rw [← hhx, ← hhy, Category.assoc, Category.assoc, t.condition]),
      ⟨hs.fac _ WalkingSpan.left, hs.fac _ WalkingSpan.right, fun hr hr' => by
        apply PushoutCocone.IsColimit.hom_ext hs;
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr, hr']
          symm
          exact hs.fac _ WalkingSpan.left
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr, hr']
          symm
          exact hs.fac _ WalkingSpan.right⟩⟩
#align category_theory.limits.pushout_cocone.is_colimit_of_factors CategoryTheory.Limits.PushoutCocone.isColimitOfFactors

/-- If `W` is the pushout of `f, g`,
it is also the pushout of `h ≫ f, h ≫ g` for any epi `h`. -/
def isColimitOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] (s : PushoutCocone f g)
    (H : IsColimit s) :
    IsColimit
      (PushoutCocone.mk _ _
        (show (h ≫ f) ≫ s.inl = (h ≫ g) ≫ s.inr by
          rw [Category.assoc, Category.assoc, s.condition])) := by
  apply PushoutCocone.isColimitAux'
  intro s
  rcases PushoutCocone.IsColimit.desc' H s.inl s.inr
      ((cancel_epi h).mp (by simpa using s.condition)) with
    ⟨l, h₁, h₂⟩
  refine ⟨l, h₁, h₂, ?_⟩
  intro m hm₁ hm₂
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) : _)
#align category_theory.limits.pushout_cocone.is_colimit_of_epi_comp CategoryTheory.Limits.PushoutCocone.isColimitOfEpiComp

end PushoutCocone

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl : Y ⟶ pushout f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inl_of_epi CategoryTheory.Limits.pushout.inl_of_epi

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)
#align category_theory.limits.pushout.inr_of_epi CategoryTheory.Limits.pushout.inr_of_epi

/-- The map `X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc pushout.inl pushout.inr : _ ⟶ pushout f g) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩
#align category_theory.limits.epi_coprod_to_pushout CategoryTheory.Limits.epi_coprod_to_pushout

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk pushout.inl pushout.inr
    (show (h ≫ f) ≫ pushout.inl = (h ≫ g) ≫ pushout.inr from by
    simp only [Category.assoc]; rw [cancel_epi]; exact pushout.condition)) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))
#align category_theory.limits.pushout_is_pushout_of_epi_comp CategoryTheory.Limits.pushoutIsPushoutOfEpiComp

instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩
#align category_theory.limits.has_pushout_of_epi_comp CategoryTheory.Limits.hasPushout_of_epi_comp

section

attribute [local instance] hasPushout_of_left_iso

variable (f : X ⟶ Z) (h : W ⟶ X) [Epi h]

instance hasPushout_of_right_factors_epi : HasPushout h (h ≫ f) := by
  conv =>
    congr
    rw [← Category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_right_factors_epi CategoryTheory.Limits.hasPushout_of_right_factors_epi

instance pushout_inr_iso_of_right_factors_epi :
    IsIso (pushout.inr : _ ⟶ pushout h (h ≫ f)) := by
  convert (congrArg IsIso (show pushout.inr ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩ WalkingSpan.right)).mp
    inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm
#align category_theory.limits.pushout_inr_iso_of_right_factors_epi CategoryTheory.Limits.pushout_inr_iso_of_right_factors_epi

attribute [local instance] hasPushout_of_right_iso

instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  conv =>
    congr
    case g => rw [← Category.comp_id h]
  infer_instance
#align category_theory.limits.has_pushout_of_left_factors_epi CategoryTheory.Limits.hasPushout_of_left_factors_epi

instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl : _ ⟶ pushout (h ≫ f) h) := by
  convert (congrArg IsIso (show pushout.inl ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩ WalkingSpan.left)).mp
        inferInstance;
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm
#align category_theory.limits.pushout_inl_iso_of_left_factors_epi CategoryTheory.Limits.pushout_inl_iso_of_left_factors_epi

end

section

open WalkingSpan

variable (f : X ⟶ Y)

instance has_cokernel_pair_of_epi [Epi f] : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩
#align category_theory.limits.has_cokernel_pair_of_epi CategoryTheory.Limits.has_cokernel_pair_of_epi

theorem inl_eq_inr_of_epi_eq [Epi f] : (pushout.inl : _ ⟶ pushout f f) = pushout.inr :=
  ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).cocone left).symm.trans
    ((PushoutCocone.isColimitMkIdId f).fac (getColimitCocone (span f f)).cocone right : _)
#align category_theory.limits.inl_eq_inr_of_epi_eq CategoryTheory.Limits.inl_eq_inr_of_epi_eq

@[simp]
theorem pullback_symmetry_hom_of_epi_eq [Epi f] : (pushoutSymmetry f f).hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]
#align category_theory.limits.pullback_symmetry_hom_of_epi_eq CategoryTheory.Limits.pullback_symmetry_hom_of_epi_eq

instance inl_iso_of_epi_eq [Epi f] : IsIso (pushout.inl : _ ⟶ pushout f f) := by
  refine ⟨⟨pushout.desc (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply pushout.hom_ext
  · simp
  · simp [inl_eq_inr_of_epi_eq]
#align category_theory.limits.inl_iso_of_epi_eq CategoryTheory.Limits.inl_iso_of_epi_eq

instance inr_iso_of_epi_eq [Epi f] : IsIso (pushout.inr : _ ⟶ pushout f f) := by
  rw [← inl_eq_inr_of_epi_eq]
  infer_instance
#align category_theory.limits.inr_iso_of_epi_eq CategoryTheory.Limits.inr_iso_of_epi_eq

end

end CategoryTheory.Limits
