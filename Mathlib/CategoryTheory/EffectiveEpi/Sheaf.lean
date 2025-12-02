module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

namespace CategoryTheory

open Category Functor Limits EffectiveEpiFamily

variable {C D : Type*} [Category C] [Category D]

instance [∀ {F G : D} (f : F ⟶ G) [Epi f], HasPullback f f] [HasPushouts D]
    [IsRegularEpiCategory D] :
    IsRegularEpiCategory (C ⥤ D) where
  regularEpiOfEpi {F G} f := ⟨⟨{
    W := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.pt
    left := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.fst
    right := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.snd
    w := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.condition
    isColimit := by
      apply evaluationJointlyReflectsColimits
      intro k
      have : IsRegularEpi (f.app k) := IsRegularEpiCategory.regularEpiOfEpi (f.app k)
      refine .equivOfNatIsoOfIso ?_ _ _ ?_ (isColimitCoforkOfEffectiveEpi (f.app k)
        (pullback.cone (f.app k) (f.app k))
        (pullback.isLimit (f.app k) (f.app k)))
      · refine NatIso.ofComponents ?_ ?_
        · rintro (_ | _)
          exacts [Iso.refl _, Iso.refl _]
        · rintro (_ | _ | _) (_ | _ | _) (_ | _)
          all_goals cat_disch
      · refine Cocones.ext (Iso.refl _) ?_
        rintro (_ | _ | _)
        · simp only [comp_obj, parallelPair_obj_zero, evaluation_obj_obj, mapCocone_pt,
            Cofork.ofπ_pt, limit.cone_x, PullbackCone.fst_limit_cone, PullbackCone.snd_limit_cone,
            parallelPair_obj_one, Cocones.precompose_obj_pt, const_obj_obj,
            Cocones.precompose_obj_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app, Iso.refl_inv,
            Cofork.ofπ_ι_app, Iso.refl_hom, comp_id, mapCocone_ι_app, evaluation_obj_map]
          erw [id_comp] -- when `D` is `Type*`, `cat_disch` just works and this `erw` is not needed
          cat_disch
        · cat_disch }⟩⟩

universe u

-- TODO: cite Borceux Handbook of Algebra for the proof
def regularEpiCategorySheaf (J : GrothendieckTopology C)
    [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D]
    (h : ∀ {F G : Sheaf J D} (f : F ⟶ G) [Epi f], ∃ (I : Cᵒᵖ ⥤ D) (p : F.val ⟶ I) (i : I ⟶ G.val),
      Epi p ∧ Mono i ∧ p ≫ i = f.val)
    [HasSheafify J D] [Balanced (Sheaf J D)] : IsRegularEpiCategory (Sheaf J D) where
  regularEpiOfEpi {F G} f _ := by
    obtain ⟨I, p, i, hp, hi, hpi⟩ := h f
    -- let p := factorThruImage f.val
    -- let i := image.ι f.val
    -- have hpi : p ≫ i = f.val := by simp [p, i]
    let +nondep hc₁ : IsLimit <| (sheafToPresheaf J D).mapCone (pullback.cone f f) :=
      isLimitOfPreserves _ <| pullback.isLimit f f
    let e := PullbackCone.isoMk ((sheafToPresheaf J D).mapCone (pullback.cone f f))
    let +nondep hc₂ := IsLimit.equivOfNatIsoOfIso _ _ _ e hc₁
    let c : PullbackCone p p := PullbackCone.mk
        (W := (pullback f f).val) (pullback.fst f f).val (pullback.snd f f).val <| by
      simp [← cancel_mono i, hpi, ← Sheaf.comp_val, pullback.condition]
    let +nondep hc₃ : IsLimit c :=
      PullbackCone.isLimitOfFactors f.val f.val i _ _ hpi hpi _ hc₂
    have : IsRegularEpi p := IsRegularEpiCategory.regularEpiOfEpi _
    let +nondep hc₄ := isColimitCoforkOfEffectiveEpi p _ hc₃
    have h₁ : (presheafToSheaf J D).map f.val =
          (sheafificationAdjunction J D).counit.app F ≫ f ≫
          inv ((sheafificationAdjunction J D).counit.app G) := by
        simpa [← Category.assoc] using (sheafificationAdjunction J D).counit_naturality f
    have h₂ : f = inv ((sheafificationAdjunction J D).counit.app F) ≫
        (presheafToSheaf J D).map f.val ≫ (sheafificationAdjunction J D).counit.app G := by
      simp [h₁]
    have : Epi ((presheafToSheaf J D).map f.val) := by
      rw [h₁]
      infer_instance
    have : Epi ((presheafToSheaf J D).map i) := by
      rw [← hpi, Functor.map_comp] at this
      exact epi_of_epi ((presheafToSheaf J D).map p) _
    have : IsIso ((presheafToSheaf J D).map i) :=
      Balanced.isIso_of_mono_of_epi _
    let +nondep hc₅ := isColimitOfPreserves (presheafToSheaf J D) hc₄
    rw [h₂, isRegularEpi_iff_effectiveEpi]
    suffices EffectiveEpi ((presheafToSheaf J D).map f.val) by infer_instance
    rw [← hpi, Functor.map_comp]
    suffices EffectiveEpi ((presheafToSheaf J D).map p) by infer_instance
    rw [← isRegularEpi_iff_effectiveEpi]
    exact ⟨⟨{
      W := (presheafToSheaf J D).obj (pullback f f).val
      left := (presheafToSheaf J D).map (pullback.fst f f).val
      right := (presheafToSheaf J D).map (pullback.snd f f).val
      w := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        rw [← cancel_mono i]
        simp [hpi, ← Sheaf.comp_val, pullback.condition]
      isColimit := by
        refine .equivOfNatIsoOfIso ?_ _ _ ?_ hc₅
        · refine NatIso.ofComponents ?_ ?_
          · rintro (_ | _); exacts [Iso.refl _, Iso.refl _]
          · rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals simp [c]
        · refine Cocones.ext (Iso.refl _) ?_
          rintro (_ | _)
          · simp only [parallelPair_obj_zero, Cofork.ofπ_pt, comp_obj, parallelPair_obj_one,
              Cocones.precompose_obj_pt, mapCocone_pt, const_obj_obj, Cocones.precompose_obj_ι,
              NatTrans.comp_app, NatIso.ofComponents_inv_app, Iso.refl_inv, mapCocone_ι_app,
              Cofork.ofπ_ι_app, map_comp, Iso.refl_hom, comp_id]
            erw [id_comp]
            cat_disch
          · simp }⟩⟩

attribute [local instance] Types.instFunLike Types.instConcreteCategory

-- TODO: pick apart and clean up
instance : HasImages (C ⥤ Type*) where
  has_image {F G} f := {
    exists_image := ⟨{
      F := {
        I := {
          obj X := Set.range <| f.app X
          map g := by
            rintro ⟨x, hx⟩
            refine ⟨G.map g x, ?_⟩
            obtain ⟨y, rfl⟩ := hx
            refine ⟨F.map g y, ?_⟩
            change _ = (f.app _ ≫ G.map g) y
            rw [← NatTrans.naturality]
            rfl
          map_id := by cat_disch
          map_comp := by cat_disch
        }
        m := {
          app X := Subtype.val
          naturality := by cat_disch
        }
        m_mono := by
          rw [NatTrans.mono_iff_mono_app]
          intro X
          simp [mono_iff_injective]
        e := {
          app X := fun x ↦ ⟨f.app _ x, ⟨x, rfl⟩⟩
          naturality := by
            intro X Y g
            ext
            change (F.map g ≫ _) _ = _
            rw [NatTrans.naturality]
            rfl
        }
        fac := rfl
      }
      isImage := {
        lift F' := {
          app X := by
            intro ⟨x, hx⟩
            apply F'.e.app _
            exact hx.choose
          naturality := by
            intro X Y g
            ext a
            simp only [types_comp_apply]
            have hm := F'.m_mono
            rw [NatTrans.mono_iff_mono_app] at hm
            simp_rw [mono_iff_injective] at hm
            apply hm _
            change (F'.e.app _ ≫ _) _ = _
            rw [← NatTrans.comp_app, F'.fac, ]
            change _ = (F'.e.app _ ≫ _ ≫ _) _
            rw [← F'.e.naturality_assoc]
            change _ = (_ ≫ _ ≫ F'.m.app _) _
            rw [← NatTrans.comp_app, F'.fac]
            generalize_proofs h₁ h₂
            rw [h₁.choose_spec]
            rw [f.naturality]
            dsimp
            apply congr_arg
            exact h₂.choose_spec.symm }
        lift_fac F' := by
          ext
          simp only [FunctorToTypes.comp]
          change (F'.e ≫ F'.m).app _ _ = _
          simp only [F'.fac]
          generalize_proofs h
          exact h.choose_spec } }⟩ }

instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨{
    I := image f
    m := image.ι f
    e := factorThruImage f }⟩

instance (J : GrothendieckTopology C) [HasSheafify J (Type u)] :
    IsRegularEpiCategory (Sheaf J (Type u)) := by
  apply regularEpiCategorySheaf J fun f hf ↦
    ⟨image f.val, factorThruImage f.val, image.ι f.val, inferInstance, inferInstance, by simp⟩
  -- intro F G f _
  -- obtain ⟨⟨I, m, e, fac⟩, _⟩ := HasStrongEpiMonoFactorisations.has_fac f.val
  -- refine ⟨I, e, m, inferInstance, inferInstance, fac⟩

instance (J : GrothendieckTopology C) (A : Type*) [Category A] [Abelian A] [HasSheafify J A] :
    IsRegularEpiCategory (Sheaf J A) :=
  regularEpiCategorySheaf J fun f hf ↦
    ⟨image f.val, factorThruImage f.val, image.ι f.val, inferInstance, inferInstance, by simp⟩


end CategoryTheory
