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
public import Mathlib.Condensed.Light.Module
public import Mathlib.Condensed.Module

@[expose] public section

universe u v

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
    isColimit := evaluationJointlyReflectsColimits _ fun k ↦ by
      have := IsRegularEpiCategory.regularEpiOfEpi (f.app k)
      refine .equivOfNatIsoOfIso ?_ _ _ ?_ (isColimitCoforkOfEffectiveEpi (f.app k)
        (pullback.cone (f.app k) (f.app k))
        (pullback.isLimit (f.app k) (f.app k)))
      · refine NatIso.ofComponents (by rintro (_ | _); exacts [Iso.refl _, Iso.refl _]) ?_
        rintro _ _ (_ | _)
        all_goals cat_disch
      · exact Cocones.ext (Iso.refl _) <| by rintro (_ | _ | _); all_goals cat_disch }⟩⟩

-- TODO: cite Borceux Handbook of Algebra for the proof
lemma isRegularEpiCategory_sheaf (J : GrothendieckTopology C)
    [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D]
    (h : ∀ {F G : Sheaf J D} (f : F ⟶ G) [Epi f], ∃ (I : Cᵒᵖ ⥤ D) (p : F.val ⟶ I) (i : I ⟶ G.val),
      Epi p ∧ Mono i ∧ p ≫ i = f.val)
    [HasSheafify J D] [Balanced (Sheaf J D)] : IsRegularEpiCategory (Sheaf J D) where
  regularEpiOfEpi {F G} f _ := by
    -- Factor `f` on the level of presheaves as an epimorphism `p` followed by a monomorphism `i`.
    obtain ⟨I, p, i, hp, hi, hpi⟩ := h f
    -- The sheafification of `f.val` is `f` pre- and postcomposed with isomorphisms.
    have h₁ : (presheafToSheaf J D).map f.val =
          (sheafificationAdjunction J D).counit.app F ≫ f ≫
          inv ((sheafificationAdjunction J D).counit.app G) := by
        simpa [← Category.assoc] using (sheafificationAdjunction J D).counit_naturality f
    have h₂ : f = inv ((sheafificationAdjunction J D).counit.app F) ≫
        (presheafToSheaf J D).map f.val ≫ (sheafificationAdjunction J D).counit.app G := by
      simp [h₁]
    -- The sheafification of `f.val` is still an epimorphism
    have : Epi ((presheafToSheaf J D).map f.val) := by
      rw [h₁]
      infer_instance
    -- The sheafification of `i` is an epimorphism, because the sheafification of `p ≫ i = f.val`
    -- is an epimorphism.
    have : Epi ((presheafToSheaf J D).map i) := by
      rw [← hpi, Functor.map_comp] at this
      exact epi_of_epi ((presheafToSheaf J D).map p) _
    -- Since the sheafification of `i` is both a monomorphism and an epimorphism, it is an
    -- isomorphism.
    have : IsIso ((presheafToSheaf J D).map i) :=
      Balanced.isIso_of_mono_of_epi _
    -- The next five lines show that it suffices to show that the sheafification of `p` is a
    -- regular epimorphism.
    rw [h₂, isRegularEpi_iff_effectiveEpi]
    suffices EffectiveEpi ((presheafToSheaf J D).map f.val) by infer_instance
    rw [← hpi, Functor.map_comp]
    suffices EffectiveEpi ((presheafToSheaf J D).map p) by infer_instance
    rw [← isRegularEpi_iff_effectiveEpi]
    -- The underlying presheaf of the kernel pair of `f` is a kernel pair for `p`, and since
    -- sheafification preserves colimits, `p` exhibits its target `I` as a coequalizer of this
    -- kernel pair. The result follows.
    let c : PullbackCone p p := PullbackCone.mk
        (W := (pullback f f).val) (pullback.fst f f).val (pullback.snd f f).val <| by
      simp [← cancel_mono i, hpi, ← Sheaf.comp_val, pullback.condition]
    have : IsRegularEpi p := IsRegularEpiCategory.regularEpiOfEpi _
    let hc := isColimitOfPreserves (presheafToSheaf J D) <|
      isColimitCoforkOfEffectiveEpi p c (PullbackCone.isLimitOfFactors f.val f.val i _ _ hpi hpi _
        ((isLimitOfPreserves _ <| pullback.isLimit f f).equivOfNatIsoOfIso _ _ _ <|
          PullbackCone.isoMk ((sheafToPresheaf J D).mapCone (pullback.cone f f))))
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
        refine .equivOfNatIsoOfIso ?_ _ _ ?_ hc
        · refine NatIso.ofComponents ?_ ?_
          · rintro (_ | _); exacts [Iso.refl _, Iso.refl _]
          · rintro (_ | _ | _) (_ | _ | _) (_ | _); all_goals simp [c]
        · refine Cocones.ext (Iso.refl _) ?_
          rintro (_ | _)
          all_goals simp [c] }⟩⟩

instance (J : GrothendieckTopology C) [HasPullbacks D] [HasPushouts D] [HasEqualizers D]
    [IsRegularEpiCategory D] [HasImages (Cᵒᵖ ⥤ D)] [HasSheafify J D] [Balanced (Sheaf J D)] :
    IsRegularEpiCategory (Sheaf J D) := isRegularEpiCategory_sheaf J fun f hf ↦
  ⟨image f.val, factorThruImage f.val, image.ι f.val, inferInstance, inferInstance, by simp⟩

@[simps obj map]
def NatTrans.image {F G : C ⥤ Type u} (f : F ⟶ G) : C ⥤ Type u where
  obj X := Set.range <| f.app X
  map g := fun ⟨x, hx⟩ ↦ ⟨G.map g x, by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨F.map g y, FunctorToTypes.naturality F G f g y⟩⟩

attribute [local simp] FunctorToTypes.naturality in
@[simps]
def NatTrans.monoFactorisation {F G : C ⥤ Type u} (f : F ⟶ G) : MonoFactorisation f where
  I := f.image
  m := { app X := Subtype.val }
  m_mono := by
    rw [NatTrans.mono_iff_mono_app]
    intro X
    simp [mono_iff_injective]
  e := { app X := fun x ↦ ⟨f.app _ x, ⟨x, rfl⟩⟩ }

@[simp]
lemma FunctorToTypes.monoFactorisation_fac {F G : C ⥤ Type u} {f : F ⟶ G} {X : C}
    (H : MonoFactorisation f) (x : F.obj X) : H.m.app X (H.e.app X x) = f.app X x := by
  simp [← types_comp_apply, ← NatTrans.comp_app]

noncomputable def NatTrans.monoFactorisationIsImage {F G : C ⥤ Type u} (f : F ⟶ G) :
    IsImage f.monoFactorisation where
  lift H := {
    app X := fun ⟨x, hx⟩ ↦ H.e.app _ hx.choose
    naturality X Y g := by
      ext ⟨⟩
      apply show Function.Injective (H.m.app Y) by rw [← mono_iff_injective]; infer_instance
      simp only [monoFactorisation_I, image_obj, types_comp_apply, image_map,
        FunctorToTypes.monoFactorisation_fac, FunctorToTypes.naturality]
      generalize_proofs h₁ h₂
      rw [h₁.choose_spec, h₂.choose_spec] }
  lift_fac H := by
    ext
    simp only [monoFactorisation_I, image_obj, FunctorToTypes.comp,
      FunctorToTypes.monoFactorisation_fac, monoFactorisation_m_app]
    generalize_proofs h
    exact h.choose_spec

instance : HasImages (C ⥤ Type*) where
  has_image f := { exists_image := ⟨ { F := _, isImage := f.monoFactorisationIsImage } ⟩ }

instance : HasStrongEpiMonoFactorisations (C ⥤ Type*) where
  has_fac {F G} f := ⟨{
    I := image f
    m := image.ι f
    e := factorThruImage f }⟩

example (J : GrothendieckTopology C) [HasSheafify J (Type u)] :
    IsRegularEpiCategory (Sheaf J (Type u)) :=
  inferInstance

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    IsRegularEpiCategory (Sheaf J (Type (max u v))) :=
  inferInstance

example (J : GrothendieckTopology C) (A : Type*) [Category A] [Abelian A] [HasSheafify J A] :
    IsRegularEpiCategory (Sheaf J A) :=
  inferInstance

example (J : GrothendieckTopology C) (R : Type*) [Ring R] [HasSheafify J (ModuleCat.{u} R)] :
    IsRegularEpiCategory (Sheaf J (ModuleCat.{u} R)) :=
  inferInstance

example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type (max u v)) [Ring R] :
    IsRegularEpiCategory (Sheaf J (ModuleCat.{max u v} R)) :=
  inferInstance

end CategoryTheory
