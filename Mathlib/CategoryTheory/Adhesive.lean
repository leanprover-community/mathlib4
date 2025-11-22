/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!

# Adhesive categories

## Main definitions
- `CategoryTheory.IsPushout.IsVanKampen`: A convenience formulation for a pushout being
  a van Kampen colimit.
- `CategoryTheory.Adhesive`: A category is adhesive if it has pushouts and pullbacks along
  monomorphisms, and such pushouts are van Kampen.

## Main Results
- `CategoryTheory.Type.adhesive`: The category of `Type` is adhesive.
- `CategoryTheory.Adhesive.isPullback_of_isPushout_of_mono_left`: In adhesive categories,
  pushouts along monomorphisms are pullbacks.
- `CategoryTheory.Adhesive.mono_of_isPushout_of_mono_left`: In adhesive categories,
  monomorphisms are stable under pushouts.
- `CategoryTheory.Adhesive.toRegularMonoCategory`: Monomorphisms in adhesive categories are
  regular (this implies that adhesive categories are balanced).
- `CategoryTheory.adhesive_functor`: The category `C ⥤ D` is adhesive if `D`
  has all pullbacks and all pushouts and is adhesive

## References
- https://ncatlab.org/nlab/show/adhesive+category
- [Stephen Lack and Paweł Sobociński, Adhesive Categories][adhesive2004]

-/

@[expose] public section


namespace CategoryTheory

open Limits

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

-- This only makes sense when the original diagram is a pushout.
/-- A convenience formulation for a pushout being a van Kampen colimit.
See `IsPushout.isVanKampen_iff` below. -/
@[nolint unusedArguments]
def IsPushout.IsVanKampen (_ : IsPushout f g h i) : Prop :=
  ∀ ⦃W' X' Y' Z' : C⦄ (f' : W' ⟶ X') (g' : W' ⟶ Y') (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αW : W' ⟶ W)
    (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z) (_ : IsPullback f' αW αX f)
    (_ : IsPullback g' αW αY g) (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i)
    (_ : CommSq f' g' h' i'), IsPushout f' g' h' i' ↔ IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i

/-- An alternative formulation for a pushout being a van Kampen colimit.
See `IsPushout.isVanKampen_iff'` below. -/
@[nolint unusedArguments]
def IsPushout.IsVanKampen' (_ : IsPushout f g h i) : Prop :=
  ∀ ⦃X' Y' Z' : C⦄ (h' : X' ⟶ Z') (i' : Y' ⟶ Z') (αX : X' ⟶ X) (αY : Y' ⟶ Y) (αZ : Z' ⟶ Z)
    (_ : CommSq h' αX αZ h) (_ : CommSq i' αY αZ i) [HasPullback αX f],
    IsPullback h' αX αZ h ∧ IsPullback i' αY αZ i ↔
      ∃ (W' : C) (f' : W' ⟶ X') (g' : W' ⟶ Y') (αW : W' ⟶ W),
    IsPullback f' αW αX f ∧ IsPullback g' αW αY g ∧ IsPushout f' g' h' i'

theorem IsPushout.IsVanKampen.flip {H : IsPushout f g h i} (H' : H.IsVanKampen) :
    H.flip.IsVanKampen := by
  introv W' hf hg hh hi w
  simpa only [IsPushout.flip_iff, IsPullback.flip_iff, and_comm] using
    H' g' f' i' h' αW αY αX αZ hg hf hi hh w.flip

theorem IsPushout.isVanKampen_iff (H : IsPushout f g h i) :
    H.IsVanKampen ↔ IsVanKampenColimit (PushoutCocone.mk h i H.w) := by
  constructor
  · intro H F' c' α fα eα hα
    refine Iff.trans ?_
        ((H (F'.map WalkingSpan.Hom.fst) (F'.map WalkingSpan.Hom.snd) (c'.ι.app _) (c'.ι.app _)
          (α.app _) (α.app _) (α.app _) fα (by convert hα WalkingSpan.Hom.fst)
          (by convert hα WalkingSpan.Hom.snd) ?_ ?_ ?_).trans ?_)
    · have : F'.map WalkingSpan.Hom.fst ≫ c'.ι.app WalkingSpan.left =
          F'.map WalkingSpan.Hom.snd ≫ c'.ι.app WalkingSpan.right := by
        simp only [Cocone.w]
      rw [(IsColimit.equivOfNatIsoOfIso (diagramIsoSpan F') c' (PushoutCocone.mk _ _ this)
            _).nonempty_congr]
      · exact ⟨fun h => ⟨⟨this⟩, h⟩, fun h => h.2⟩
      · refine Cocones.ext (Iso.refl c'.pt) ?_
        rintro (_ | _ | _) <;> dsimp <;>
          simp only [c'.w, Category.id_comp, Category.comp_id]
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨NatTrans.congr_app eα.symm _⟩
    · exact ⟨by simp⟩
    constructor
    · rintro ⟨h₁, h₂⟩ (_ | _ | _)
      · rw [← c'.w WalkingSpan.Hom.fst]; exact (hα WalkingSpan.Hom.fst).paste_horiz h₁
      exacts [h₁, h₂]
    · intro h; exact ⟨h _, h _⟩
  · introv H W' hf hg hh hi w
    refine
      Iff.trans ?_ ((H w.cocone ⟨by rintro (_ | _ | _); exacts [αW, αX, αY], ?_⟩ αZ ?_ ?_).trans ?_)
    rotate_left
    · rintro i _ (_ | _ | _)
      · dsimp; simp only [Functor.map_id, Category.comp_id, Category.id_comp]
      exacts [hf.w, hg.w]
    · ext (_ | _ | _)
      · simp [hh.w, hf.w_assoc]
      exacts [hh.w.symm, hi.w.symm]
    · rintro i _ (_ | _ | _)
      · dsimp; simp_rw [Functor.map_id]
        exact IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Category.id_comp]⟩
      exacts [hf, hg]
    · constructor
      · intro h; exact ⟨h WalkingCospan.left, h WalkingCospan.right⟩
      · rintro ⟨h₁, h₂⟩ (_ | _ | _)
        · dsimp; rw [PushoutCocone.condition_zero]; exact hf.paste_horiz h₁
        exacts [h₁, h₂]
    · exact ⟨fun h => h.2, fun h => ⟨w, h⟩⟩

lemma IsPushout.isVanKampen'_ofIsVanKampen {H : IsPushout f g h i} :
    H.IsVanKampen → H.IsVanKampen' := by
  intro VK X' Y' Z' h' i' αX αY αZ csh csi _
  constructor
  · intro ⟨pbh, pbi⟩
    let l := pbi.lift ((pullback.fst αX f) ≫ h') ((pullback.snd αX f) ≫ g)
        (by simp only [Category.assoc, csh.w, pullback.condition_assoc, ← H.w])
    use (pullback αX f), (pullback.fst αX f), l, (pullback.snd αX f)
    refine ⟨?_, ?_, ?_⟩
    · exact IsPullback.of_hasPullback αX f
    · refine IsPullback.of_right' ?_ pbi
      rw [← H.w]
      refine IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) pbh
    · refine (VK (pullback.fst αX f) l  h' i' (pullback.snd αX f) αX αY αZ
        (IsPullback.of_hasPullback αX f) ?_
          pbh.toCommSq pbi.toCommSq ⟨by simp only [IsPullback.lift_fst, l]⟩).2 ⟨pbh, pbi⟩
      · dsimp [l]
        refine IsPullback.of_right' ?_ pbi
        rw [← H.w]
        refine IsPullback.paste_horiz (IsPullback.of_hasPullback αX f) pbh
  · intro ⟨W', f', g', αW, pbf, pbg, H'⟩
    rwa [← VK f' g' h' i' αW αX αY αZ pbf pbg csh csi H'.toCommSq]

lemma IsPushout.VanKampen_isPullback_isPullback_hom_ext
    {H : IsPushout f g h i} (H' : H.IsVanKampen)
    {X' Y' Z' W : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} [HasPullback αX f] {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z} {f₁ f₂ : Z' ⟶ W}
    (h₁ : IsPullback h' αX αZ h) (h₂ : IsPullback i' αY αZ i)
    (h'_eq : h' ≫ f₁ = h' ≫ f₂) (i'_eq : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ := by
  obtain ⟨W, f', g', αW, h₃, h₄, h₅⟩ :=
    (isVanKampen'_ofIsVanKampen H' h' i' αX αY αZ h₁.toCommSq h₂.toCommSq).1 ⟨h₁, h₂⟩
  exact h₅.hom_ext h'_eq i'_eq

theorem is_coprod_iff_isPushout {X E Y YE : C} (c : BinaryCofan X E) (hc : IsColimit c) {f : X ⟶ Y}
    {iY : Y ⟶ YE} {fE : c.pt ⟶ YE} (H : CommSq f c.inl iY fE) :
    Nonempty (IsColimit (BinaryCofan.mk (c.inr ≫ fE) iY)) ↔ IsPushout f c.inl iY fE := by
  constructor
  · rintro ⟨h⟩
    refine ⟨H, ⟨Limits.PushoutCocone.isColimitAux' _ ?_⟩⟩
    intro s
    dsimp
    refine ⟨h.desc (BinaryCofan.mk (c.inr ≫ s.inr) s.inl), h.fac _ ⟨WalkingPair.right⟩, ?_, ?_⟩
    · apply BinaryCofan.IsColimit.hom_ext hc
      · rw [← H.w_assoc]; erw [h.fac _ ⟨WalkingPair.right⟩]; exact s.condition
      · rw [← Category.assoc]; exact h.fac _ ⟨WalkingPair.left⟩
    · intro m e₁ e₂
      apply BinaryCofan.IsColimit.hom_ext h
      · dsimp
        rw [Category.assoc, e₂, eq_comm]; exact h.fac _ ⟨WalkingPair.left⟩
      · refine e₁.trans (Eq.symm ?_); exact h.fac _ _
  · refine fun H => ⟨?_⟩
    fapply Limits.BinaryCofan.isColimitMk
    · exact fun s => H.isColimit.desc (PushoutCocone.mk s.inr _ <|
        (hc.fac (BinaryCofan.mk (f ≫ s.inr) s.inl) ⟨WalkingPair.left⟩).symm)
    · intro s
      rw [Category.assoc]
      erw [H.isColimit.fac _ WalkingSpan.right]
      erw [hc.fac]
      rfl
    · intro s; exact H.isColimit.fac _ WalkingSpan.left
    · intro s m e₁ e₂
      apply PushoutCocone.IsColimit.hom_ext H.isColimit
      · symm; exact (H.isColimit.fac _ WalkingSpan.left).trans e₂.symm
      · rw [H.isColimit.fac _ WalkingSpan.right]
        apply BinaryCofan.IsColimit.hom_ext hc
        · erw [hc.fac]
          erw [← H.w_assoc]
          rw [e₂]
          rfl
        · refine ((Category.assoc _ _ _).symm.trans e₁).trans ?_; symm; exact hc.fac _ _

theorem IsPushout.isVanKampen_inl {W E X Z : C} (c : BinaryCofan W E) [FinitaryExtensive C]
    [HasPullbacks C] (hc : IsColimit c) (f : W ⟶ X) (h : X ⟶ Z) (i : c.pt ⟶ Z)
    (H : IsPushout f c.inl h i) : H.IsVanKampen := by
  obtain ⟨hc₁⟩ := (is_coprod_iff_isPushout c hc H.1).mpr H
  introv W' hf hg hh hi w
  obtain ⟨hc₂⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
    (BinaryCofan.mk _ (pullback.fst _ _)) _ _ _ hg.w.symm pullback.condition.symm).mpr
    ⟨hg, IsPullback.of_hasPullback αY c.inr⟩
  refine (is_coprod_iff_isPushout _ hc₂ w).symm.trans ?_
  refine ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen _ hc₁)
    (BinaryCofan.mk _ _) (pullback.snd _ _) _ _ ?_ hh.w.symm).trans ?_
  · dsimp; rw [← pullback.condition_assoc, Category.assoc, hi.w]
  constructor
  · rintro ⟨hc₃, hc₄⟩
    refine ⟨hc₄, ?_⟩
    let Y'' := pullback αZ i
    let cmp : Y' ⟶ Y'' := pullback.lift i' αY hi.w
    have e₁ : (g' ≫ cmp) ≫ pullback.snd _ _ = αW ≫ c.inl := by
      rw [Category.assoc, pullback.lift_snd, hg.w]
    have e₂ : (pullback.fst _ _ ≫ cmp : pullback αY c.inr ⟶ _) ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ c.inr := by
      rw [Category.assoc, pullback.lift_snd, pullback.condition]
    obtain ⟨hc₄⟩ := ((BinaryCofan.isVanKampen_iff _).mp (FinitaryExtensive.vanKampen c hc)
      (BinaryCofan.mk _ _) αW _ _ e₁.symm e₂.symm).mpr <| by
        constructor
        · apply IsPullback.of_right _ e₁ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc, pullback.lift_fst, ← H.w, ← w.w]; exact hf.paste_horiz hc₄
        · apply IsPullback.of_right _ e₂ (IsPullback.of_hasPullback _ _)
          rw [Category.assoc, pullback.lift_fst]; exact hc₃
    rw [← Category.id_comp αZ, ← show cmp ≫ pullback.snd _ _ = αY from pullback.lift_snd _ _ _]
    apply IsPullback.paste_vert _ (IsPullback.of_hasPullback αZ i)
    have : cmp = (hc₂.coconePointUniqueUpToIso hc₄).hom := by
      apply BinaryCofan.IsColimit.hom_ext hc₂
      exacts [(hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.left⟩).symm,
        (hc₂.comp_coconePointUniqueUpToIso_hom hc₄ ⟨WalkingPair.right⟩).symm]
    rw [this]
    exact IsPullback.of_vert_isIso ⟨by rw [← this, Category.comp_id, pullback.lift_fst]⟩
  · rintro ⟨hc₃, hc₄⟩
    exact ⟨(IsPullback.of_hasPullback αY c.inr).paste_horiz hc₄, hc₃⟩

theorem IsPushout.IsVanKampen.isPullback_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
      (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
    (IsPushout.of_horiz_isIso ⟨by simp⟩)).1.flip

theorem IsPushout.IsVanKampen.isPullback_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : IsPullback f g h i :=
  ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
      (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
    (IsPushout.of_vert_isIso ⟨by simp⟩)).2

theorem IsPushout.IsVanKampen.mono_of_mono_left [Mono f] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono i :=
  IsKernelPair.mono_of_isIso_fst
    ((H' (𝟙 _) g g (𝟙 Y) (𝟙 _) f (𝟙 _) i (IsKernelPair.id_of_mono f)
        (IsPullback.of_vert_isIso ⟨by simp⟩) H.1.flip ⟨rfl⟩ ⟨by simp⟩).mp
      (IsPushout.of_horiz_isIso ⟨by simp⟩)).2

theorem IsPushout.IsVanKampen.mono_of_mono_right [Mono g] {H : IsPushout f g h i}
    (H' : H.IsVanKampen) : Mono h :=
  IsKernelPair.mono_of_isIso_fst
    ((H' f (𝟙 _) (𝟙 _) f (𝟙 _) (𝟙 _) g h (IsPullback.of_vert_isIso ⟨by simp⟩)
        (IsKernelPair.id_of_mono g) ⟨rfl⟩ H.1 ⟨by simp⟩).mp
      (IsPushout.of_vert_isIso ⟨by simp⟩)).1

/-- A category is adhesive if it has pushouts and pullbacks along monomorphisms,
and such pushouts are van Kampen. -/
class Adhesive (C : Type u) [Category.{v} C] : Prop where
  [hasPullback_of_mono_left : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
  [hasPushout_of_mono_left : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
  van_kampen : ∀ {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} [Mono f]
    (H : IsPushout f g h i), H.IsVanKampen

attribute [instance] Adhesive.hasPullback_of_mono_left Adhesive.hasPushout_of_mono_left
  Limits.hasPullback_symmetry

theorem Adhesive.van_kampen' [Adhesive C] [Mono g] (H : IsPushout f g h i) : H.IsVanKampen :=
  (Adhesive.van_kampen H.flip).flip

theorem Adhesive.isPullback_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i)
    [Mono f] : IsPullback f g h i :=
  (Adhesive.van_kampen H).isPullback_of_mono_left

theorem Adhesive.isPullback_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i)
    [Mono g] : IsPullback f g h i :=
  (Adhesive.van_kampen' H).isPullback_of_mono_right

theorem Adhesive.mono_of_isPushout_of_mono_left [Adhesive C] (H : IsPushout f g h i) [Mono f] :
    Mono i :=
  (Adhesive.van_kampen H).mono_of_mono_left

theorem Adhesive.mono_of_isPushout_of_mono_right [Adhesive C] (H : IsPushout f g h i) [Mono g] :
    Mono h :=
  (Adhesive.van_kampen' H).mono_of_mono_right

lemma Adhesive.isPullback_isPullback_hom_ext [Adhesive C] [Mono f] (H : IsPushout f g h i)
    {X' Y' Z' W : C} {h' : X' ⟶ Z'} {i' : Y' ⟶ Z'}
    {αX : X' ⟶ X} {αY : Y' ⟶ Y} {αZ : Z' ⟶ Z}
    {f₁ f₂ : Z' ⟶ W}
    (h₁ : IsPullback h' αX αZ h) (h₂ : IsPullback i' αY αZ i)
    (h'_eq : h' ≫ f₁ = h' ≫ f₂) (i'_eq : i' ≫ f₁ = i' ≫ f₂) : f₁ = f₂ :=
  IsPushout.VanKampen_isPullback_isPullback_hom_ext (Adhesive.van_kampen H) h₁ h₂ h'_eq i'_eq

open Adhesive IsPullback IsPushout in
instance [Adhesive C] {Z A B : C} {a : A ⟶ Z} {b : B ⟶ Z} [Mono a] [Mono b] :
    Mono (pushout.desc a b pullback.condition) where
  right_cancellation {K} f g eq := by
    let u := pushout.inl (pullback.fst a b) (pullback.snd a b)
    let v := pushout.inr (pullback.fst a b) (pullback.snd a b)

    letI : Mono u :=
      mono_of_isPushout_of_mono_right (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    letI : Mono v :=
      mono_of_isPushout_of_mono_left (of_hasPushout (pullback.fst a b) (pullback.snd a b))
    let f_sq_left := of_hasPullback f u
    let f_sq_right := of_hasPullback f v
    let g_sq_left := of_hasPullback g u
    let g_sq_right := of_hasPullback g v

    let l₁ := pullback.fst f u
    let f₁ := pullback.snd f u
    let l₂ := pullback.fst f v
    let f₂ := pullback.snd f v

    let m₁ := pullback.fst g u
    let g₁ := pullback.snd g u
    let m₂ := pullback.fst g v
    let g₂ := pullback.snd g v

    letI : HasPullback (pullback.snd f u) (pullback.fst a b) := hasPullback_symmetry _ _
    obtain ⟨_, f', _, _, p₁, p₂, h₁⟩ := (isVanKampen'_ofIsVanKampen (van_kampen (of_hasPushout _ _))
      _ _ _ _ _ f_sq_left.toCommSq f_sq_right.toCommSq).1 ⟨f_sq_left, f_sq_right⟩
    letI : Mono f' := by
      rw [← p₁.isoPullback_hom_fst]
      infer_instance

    apply isPullback_isPullback_hom_ext (of_hasPushout _ _) g_sq_left g_sq_right
    · let sq₁₁ := of_hasPullback m₁ l₁
      let sq₁₂ := of_hasPullback m₁ l₂
      apply isPullback_isPullback_hom_ext h₁ sq₁₁ sq₁₂
      · rw [pullback.condition_assoc, f_sq_left.w, g_sq_left.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ u
        letI : Mono (pushout.inl (pullback.fst a b) (pullback.snd a b) ≫
            pushout.desc a b pullback.condition) := by
          rwa [pushout.inl_desc]
        rw [← cancel_mono (pushout.inl _ _ ≫ pushout.desc a b pullback.condition), Category.assoc,
          ← f_sq_left.w_assoc, eq, ← pullback.condition_assoc, Category.assoc, ← g_sq_left.w_assoc]
      · have : (pullback.fst m₁ l₂ ≫ g₁) ≫ a = (pullback.snd m₁ l₂ ≫ f₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition, Category.assoc, ← g_sq_left.w_assoc,
            sq₁₂.w_assoc, ← eq, Category.assoc, pullback.condition_assoc, pushout.inr_desc]
        rw [sq₁₂.w_assoc, f_sq_right.w, ← Category.assoc, ← pullback.lift_snd_assoc _ _ this,
          ← pushout.condition, pullback.lift_fst_assoc _ _ this, Category.assoc, g_sq_left.w]
    · let sq₂₁ := of_hasPullback m₂ l₁
      let sq₂₂ := of_hasPullback m₂ l₂
      apply isPullback_isPullback_hom_ext h₁ sq₂₁ sq₂₂
      · have : (pullback.snd m₂ l₁ ≫ f₁) ≫ a = (pullback.fst m₂ l₁ ≫ g₂) ≫ b := by
          rw [← _ ≫= pushout.inl_desc a b pullback.condition, Category.assoc, ← f_sq_left.w_assoc,
            eq, ← sq₂₁.w_assoc, Category.assoc, g_sq_right.w_assoc, pushout.inr_desc]
        rw [sq₂₁.w_assoc, f_sq_left.w, ← Category.assoc, ← pullback.lift_fst_assoc _ _ this,
          pushout.condition, pullback.lift_snd_assoc _ _ this, g_sq_right.w, Category.assoc]
      · rw [sq₂₂.w_assoc, f_sq_right.w, g_sq_right.w, ← Category.assoc, ← Category.assoc]
        refine ?_ =≫ v
        letI : Mono (pushout.inr (pullback.fst a b) (pullback.snd a b) ≫
            pushout.desc a b pullback.condition) := by
          rwa [pushout.inr_desc]
        rw [← cancel_mono (pushout.inr _ _ ≫ pushout.desc a b pullback.condition), Category.assoc,
          ← f_sq_right.w_assoc, eq, ← pullback.condition_assoc, Category.assoc,
          ← g_sq_right.w_assoc]

instance Type.adhesive : Adhesive (Type u) :=
  ⟨fun {_ _ _ _ f _ _ _ _} H =>
    (IsPushout.isVanKampen_inl _ (Types.isCoprodOfMono f) _ _ _ H.flip).flip⟩

noncomputable instance (priority := 100) Adhesive.toRegularMonoCategory [Adhesive C] :
    IsRegularMonoCategory C :=
  ⟨fun f _ => ⟨{
      Z := pushout f f
      left := pushout.inl _ _
      right := pushout.inr _ _
      w := pushout.condition
      isLimit := (Adhesive.isPullback_of_isPushout_of_mono_left
        (IsPushout.of_hasPushout f f)).isLimitFork }⟩⟩

-- This then implies that adhesive categories are balanced
example [Adhesive C] : Balanced C :=
  inferInstance

section functor

universe v'' u''

variable {D : Type u''} [Category.{v''} D]

instance adhesive_functor [Adhesive C] [HasPullbacks C] [HasPushouts C] :
    Adhesive (D ⥤ C) := by
  constructor
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  apply isVanKampenColimit_of_evaluation
  intro x
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map ((evaluation _ _).obj x))).mp ?_
  apply Adhesive.van_kampen

theorem adhesive_of_preserves_and_reflects (F : C ⥤ D) [Adhesive D]
    [H₁ : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [Mono f], HasPullback f g]
    [H₂ : ∀ {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    [PreservesLimitsOfShape WalkingCospan F]
    [ReflectsLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [ReflectsColimitsOfShape WalkingSpan F] :
    Adhesive C := by
  apply Adhesive.mk (hasPullback_of_mono_left := H₁) (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i hf H
  rw [IsPushout.isVanKampen_iff]
  refine IsVanKampenColimit.of_mapCocone F ?_
  refine (IsVanKampenColimit.precompose_isIso_iff (diagramIsoSpan _).inv).mp ?_
  refine IsVanKampenColimit.of_iso ?_ (PushoutCocone.isoMk _).symm
  refine (IsPushout.isVanKampen_iff (H.map F)).mp ?_
  apply Adhesive.van_kampen

theorem adhesive_of_preserves_and_reflects_isomorphism (F : C ⥤ D)
    [Adhesive D] [HasPullbacks C] [HasPushouts C]
    [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape WalkingSpan F]
    [F.ReflectsIsomorphisms] :
    Adhesive C := by
  haveI : ReflectsLimitsOfShape WalkingCospan F :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  haveI : ReflectsColimitsOfShape WalkingSpan F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact adhesive_of_preserves_and_reflects F

theorem adhesive_of_reflective [HasPullbacks D] [Adhesive C] [HasPullbacks C] [HasPushouts C]
    [H₂ : ∀ {X Y S : D} (f : S ⟶ X) (g : S ⟶ Y) [Mono f], HasPushout f g]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [PreservesLimitsOfShape WalkingCospan Gl] :
    Adhesive D := by
  have := adj.leftAdjoint_preservesColimits
  have := adj.rightAdjoint_preservesLimits
  apply Adhesive.mk (hasPushout_of_mono_left := H₂)
  intro W X Y Z f g h i _ H
  have := Adhesive.van_kampen (IsPushout.of_hasPushout (Gr.map f) (Gr.map g))
  rw [IsPushout.isVanKampen_iff] at this ⊢
  refine (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp ?_
  refine ((this.precompose_isIso (spanCompIso _ _ _).hom).map_reflective adj).of_iso
    (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl ((IsColimit.precomposeHomEquiv _ _).symm <| pushoutIsPushout _ _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm H.isColimit

end functor

end CategoryTheory
