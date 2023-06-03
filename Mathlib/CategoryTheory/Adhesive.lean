/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module category_theory.adhesive
! leanprover-community/mathlib commit afff1f24a6b68d0077c9d63782a1d093e337758c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Extensive
import Mathbin.CategoryTheory.Limits.Shapes.KernelPair

/-!

# Adhesive categories

## Main definitions
- `category_theory.is_pushout.is_van_kampen`: A convenience formulation for a pushout being
  a van Kampen colimit.
- `category_theory.adhesive`: A category is adhesive if it has pushouts and pullbacks along
  monomorphisms, and such pushouts are van Kampen.

## Main Results
- `category_theory.type.adhesive`: The category of `Type` is adhesive.
- `category_theory.adhesive.is_pullback_of_is_pushout_of_mono_left`: In adhesive categories,
  pushouts along monomorphisms are pullbacks.
- `category_theory.adhesive.mono_of_is_pushout_of_mono_left`: In adhesive categories,
  monomorphisms are stable under pushouts.
- `category_theory.adhesive.to_regular_mono_category`: Monomorphisms in adhesive categories are
  regular (this implies that adhesive categories are balanced).

## TODO

Show that the following are adhesive:
- functor categories into adhesive categories
- the categories of sheaves over a site

## References
- https://ncatlab.org/nlab/show/adhesive+category
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/


namespace CategoryTheory

open Limits

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

-- This only makes sense when the original diagram is a pushout.
/-- A convenience formulation for a pushout being a van Kampen colimit.
See `is_pushout.is_van_kampen_iff` below. -/
@[nolint unused_arguments]
def IsPushout.IsVanKampen (H : IsPushout f g h i) : Prop :=
  ∀ ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (hf : IsPullback f' αW αX f)
    (hg : IsPullback g' αW αY g) (hh : CommSq h' αX αZ h) (hi : CommSq i' αY αZ i)
    (w : CommSq f' g' h' i'), IsPushout f' g' h' i' ↔ IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i
#align category_theory.is_pushout.is_van_kampen CategoryTheory.IsPushout.IsVanKampen

theorem IsPushout.IsVanKampen.flip {H : IsPushout f g h i} (H' : H.IsVanKampen) :
    H.flip.IsVanKampen := by
  introv W' hf hg hh hi w
  simpa only [is_pushout.flip_iff, is_pullback.flip_iff, and_comm'] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip
#align category_theory.is_pushout.is_van_kampen.flip CategoryTheory.IsPushout.IsVanKampen.flip

theorem IsPushout.isVanKampen_iff (H : IsPushout f g h i) :
    H.IsVanKampen ↔ IsVanKampenColimit (PushoutCocone.mk h i H.w) :=
  by
  constructor
  · intro H F' c' α fα eα hα
    refine'
      Iff.trans _
        ((H (F'.map walking_span.hom.fst) (F'.map walking_span.hom.snd) (c'.ι.app _) (c'.ι.app _)
              (α.app _) (α.app _) (α.app _) fα (by convert hα walking_span.hom.fst)
              (by convert hα walking_span.hom.snd) _ _ _).trans
          _)
    · have :
        F'.map walking_span.hom.fst ≫ c'.ι.app walking_span.left =
          F'.map walking_span.hom.snd ≫ c'.ι.app walking_span.right :=
        by simp only [cocone.w]
      rw [(is_colimit.equiv_of_nat_iso_of_iso (diagram_iso_span F') c' (pushout_cocone.mk _ _ this)
            _).nonempty_congr]
      · exact ⟨fun h => ⟨⟨this⟩, h⟩, fun h => h.2⟩
      · refine' cocones.ext (iso.refl c'.X) _;
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [c'.w, category.assoc, category.id_comp, category.comp_id]
    · exact ⟨nat_trans.congr_app eα.symm _⟩
    · exact ⟨nat_trans.congr_app eα.symm _⟩
    · exact ⟨by simp⟩
    constructor
    · rintro ⟨h₁, h₂⟩ (_ | _ | _)
      · rw [← c'.w walking_span.hom.fst]; exact (hα walking_span.hom.fst).paste_horiz h₁
      exacts [h₁, h₂]
    · intro h; exact ⟨h _, h _⟩
  · introv H W' hf hg hh hi w
    refine'
      Iff.trans _ ((H w.cocone ⟨by rintro (_ | _ | _); exacts [αW, αX, αY], _⟩ αZ _ _).trans _)
    rotate_left
    · rintro i _ (_ | _ | _)
      · dsimp; simp only [Functor.map_id, category.comp_id, category.id_comp]
      exacts [hf.w, hg.w]
    · ext (_ | _ | _)
      · dsimp; rw [pushout_cocone.condition_zero]; erw [category.assoc, hh.w, hf.w_assoc]
      exacts [hh.w.symm, hi.w.symm]
    · rintro i _ (_ | _ | _)
      · dsimp; simp_rw [Functor.map_id]
        exact is_pullback.of_horiz_is_iso ⟨by rw [category.comp_id, category.id_comp]⟩
      exacts [hf, hg]
    · constructor
      · intro h; exact ⟨h walking_cospan.left, h walking_cospan.right⟩
      · rintro ⟨h₁, h₂⟩ (_ | _ | _)
        · dsimp; rw [pushout_cocone.condition_zero]; exact hf.paste_horiz h₁
        exacts [h₁, h₂]
    · exact ⟨fun h => h.2, fun h => ⟨_, h⟩⟩
#align category_theory.is_pushout.is_van_kampen_iff CategoryTheory.IsPushout.isVanKampen_iff

theorem is_coprod_iff_isPushout {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y}
    {iY : Y ⟶ YE} {fE : c.pt ⟶ YE} (H : CommSq f c.inl iY fE) :
    Nonempty (IsColimit (BinaryCofan.mk (c.inr ≫ fE) iY)) ↔ IsPushout f c.inl iY fE :=
  by
  constructor
  · rintro ⟨h⟩
    refine' ⟨H, ⟨limits.pushout_cocone.is_colimit_aux' _ _⟩⟩
    intro s
    dsimp
    refine' ⟨h.desc (binary_cofan.mk (c.inr ≫ s.inr) s.inl), h.fac _ ⟨walking_pair.right⟩, _, _⟩
    · apply binary_cofan.is_colimit.hom_ext hc
      · rw [← H.w_assoc]; erw [h.fac _ ⟨walking_pair.right⟩]; exact s.condition
      · rw [← category.assoc]; exact h.fac _ ⟨walking_pair.left⟩
    · intro m e₁ e₂
      apply binary_cofan.is_colimit.hom_ext h
      · dsimp; rw [category.assoc, e₂, eq_comm]; exact h.fac _ ⟨walking_pair.left⟩
      · refine' e₁.trans (Eq.symm _); exact h.fac _ _
  · refine' fun H => ⟨_⟩
    fapply limits.binary_cofan.is_colimit_mk
    ·
      exact fun s =>
        H.is_colimit.desc
          (pushout_cocone.mk s.inr _ <|
            (hc.fac (binary_cofan.mk (f ≫ s.inr) s.inl) ⟨walking_pair.left⟩).symm)
    · intro s
      erw [category.assoc, H.is_colimit.fac _ walking_span.right, hc.fac]; rfl
    · intro s; exact H.is_colimit.fac _ walking_span.left
    · intro s m e₁ e₂
      apply pushout_cocone.is_colimit.hom_ext H.is_colimit
      · symm; exact (H.is_colimit.fac _ walking_span.left).trans e₂.symm
      · erw [H.is_colimit.fac _ walking_span.right]
        apply binary_cofan.is_colimit.hom_ext hc
        · dsimp; erw [hc.fac, ← H.w_assoc, e₂]; rfl
        · refine' ((category.assoc _ _ _).symm.trans e₁).trans _; symm; exact hc.fac _ _
#align category_theory.is_coprod_iff_is_pushout CategoryTheory.is_coprod_iff_isPushout

theorem IsPushout.isVanKampen_inl {W E X Z : C} (c : BinaryCofan W E) [FinitaryExtensive C]
    [HasPullbacks C] (hc : IsColimit c) (f : W ⟶ X) (h : X ⟶ Z) (i : c.pt ⟶ Z)
    (H : IsPushout f c.inl h i) : H.IsVanKampen :=
  by
  obtain ⟨hc₁⟩ := (is_coprod_iff_is_pushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ :=
    ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen c hc)
          (binary_cofan.mk _ pullback.fst) _ _ _ hg.w.symm pullback.condition.symm).mpr
      ⟨hg, is_pullback.of_has_pullback αY c.inr⟩
  refine' (is_coprod_iff_is_pushout _ hc₂ w).symm.trans _
  refine'
    ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen _ hc₁)
          (binary_cofan.mk _ _) pullback.snd _ _ _ hh.w.symm).trans
      _
  · dsimp; rw [← pullback.condition_assoc, category.assoc, hi.w]
  constructor
  · rintro ⟨hc₃, hc₄⟩
    refine' ⟨hc₄, _⟩
    let Y'' := pullback αZ i
    let cmp : Y' ⟶ Y'' := pullback.lift i' αY hi.w
    have e₁ : (g' ≫ cmp) ≫ pullback.snd = αW ≫ c.inl := by
      rw [category.assoc, pullback.lift_snd, hg.w]
    have e₂ : (pullback.fst ≫ cmp : pullback αY c.inr ⟶ _) ≫ pullback.snd = pullback.snd ≫ c.inr :=
      by rw [category.assoc, pullback.lift_snd, pullback.condition]
    obtain ⟨hc₄⟩ :=
      ((binary_cofan.is_van_kampen_iff _).mp (finitary_extensive.van_kampen c hc)
            (binary_cofan.mk _ _) αW _ _ e₁.symm e₂.symm).mpr
        ⟨_, _⟩
    · rw [← category.id_comp αZ, ← show cmp ≫ pullback.snd = αY from pullback.lift_snd _ _ _]
      apply is_pullback.paste_vert _ (is_pullback.of_has_pullback αZ i)
      have : cmp = (hc₂.cocone_point_unique_up_to_iso hc₄).Hom :=
        by
        apply binary_cofan.is_colimit.hom_ext hc₂
        exacts [(hc₂.comp_cocone_point_unique_up_to_iso_hom hc₄ ⟨walking_pair.left⟩).symm,
          (hc₂.comp_cocone_point_unique_up_to_iso_hom hc₄ ⟨walking_pair.right⟩).symm]
      rw [this]
      exact is_pullback.of_vert_is_iso ⟨by rw [← this, category.comp_id, pullback.lift_fst]⟩
    · apply is_pullback.of_right _ e₁ (is_pullback.of_has_pullback _ _)
      rw [category.assoc, pullback.lift_fst, ← H.w, ← w.w]; exact hf.paste_horiz hc₄
    · apply is_pullback.of_right _ e₂ (is_pullback.of_has_pullback _ _)
      rw [category.assoc, pullback.lift_fst]; exact hc₃
  · rintro ⟨hc₃, hc₄⟩
    exact ⟨(is_pullback.of_has_pullback αY c.inr).paste_horiz hc₄, hc₃⟩
#align category_theory.is_pushout.is_van_kampen_inl CategoryTheory.IsPushout.isVanKampen_inl

theorem IsPushout.IsVanKampen.isPullback_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
            (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
        (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip
#align category_theory.is_pushout.is_van_kampen.is_pullback_of_mono_left CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_left

theorem IsPushout.IsVanKampen.isPullback_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
          (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).2
#align category_theory.is_pushout.is_van_kampen.is_pullback_of_mono_right CategoryTheory.IsPushout.IsVanKampen.isPullback_of_mono_right

theorem IsPushout.IsVanKampen.mono_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono i :=
  IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
            (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
        (IsPushout.of_horiz_isIso ⟨by simp⟩)).2
#align category_theory.is_pushout.is_van_kampen.mono_of_mono_left CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_left

theorem IsPushout.IsVanKampen.mono_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono h :=
  IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
            (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
        (IsPushout.of_vert_isIso ⟨by simp⟩)).1
#align category_theory.is_pushout.is_van_kampen.mono_of_mono_right CategoryTheory.IsPushout.IsVanKampen.mono_of_mono_right

/-- A category is adhesive if it has pushouts and pullbacks along monomorphisms,
and such pushouts are van Kampen. -/
class Adhesive (C : Type u) [Category.{v} C] : Prop where
  [hasPullback_of_mono_left : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
  [hasPushout_of_mono_left : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
  van_kampen :
    ∀ {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [Mono f]
      (H : IsPushout f g h i), H.IsVanKampen
#align category_theory.adhesive CategoryTheory.Adhesive

attribute [instance] adhesive.has_pullback_of_mono_left adhesive.has_pushout_of_mono_left

theorem Adhesive.van_kampen' [Adhesive C] [Mono g] (H : IsPushout f g h i) : H.IsVanKampen :=
  (Adhesive.van_kampen H.flip).flip
#align category_theory.adhesive.van_kampen' CategoryTheory.Adhesive.van_kampen'

theorem Adhesive.isPullback_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i)
    [Mono f] : IsPullback f g h i :=
  (Adhesive.van_kampen H).isPullback_of_mono_left
#align category_theory.adhesive.is_pullback_of_is_pushout_of_mono_left CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left

theorem Adhesive.isPullback_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i)
    [Mono g] : IsPullback f g h i :=
  (Adhesive.van_kampen' H).isPullback_of_mono_right
#align category_theory.adhesive.is_pullback_of_is_pushout_of_mono_right CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_right

theorem Adhesive.mono_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i) [Mono f] :
    Mono i :=
  (Adhesive.van_kampen H).mono_of_mono_left
#align category_theory.adhesive.mono_of_is_pushout_of_mono_left CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left

theorem Adhesive.mono_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i) [Mono g] :
    Mono h :=
  (Adhesive.van_kampen' H).mono_of_mono_right
#align category_theory.adhesive.mono_of_is_pushout_of_mono_right CategoryTheory.Adhesive.mono_of_isPushout_of_mono_right

instance Type.adhesive : Adhesive (Type u) :=
  by
  constructor
  intros
  exact (is_pushout.is_van_kampen_inl _ (types.is_coprod_of_mono f) _ _ _ H.flip).flip
#align category_theory.type.adhesive CategoryTheory.Type.adhesive

noncomputable instance (priority := 100) Adhesive.toRegularMonoCategory [Adhesive C] :
    RegularMonoCategory C :=
  ⟨fun X Y f hf =>
    { z := pushout f f
      left := pushout.inl
      right := pushout.inr
      w := pushout.condition
      IsLimit :=
        (adhesive.is_pullback_of_is_pushout_of_mono_left
            (is_pushout.of_has_pushout f f)).isLimitFork }⟩
#align category_theory.adhesive.to_regular_mono_category CategoryTheory.Adhesive.toRegularMonoCategory

-- This then implies that adhesive categories are balanced
example [Adhesive C] : Balanced C :=
  inferInstance

end CategoryTheory

