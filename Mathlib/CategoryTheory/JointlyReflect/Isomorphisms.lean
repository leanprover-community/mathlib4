import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Limits.Shapes.CommSq
import Mathlib.CategoryTheory.MorphismProperty

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {I : Type*} {D : I → Type*} [∀ i, Category (D i)]
  (F : ∀ i, C ⥤ D i)

lemma mono_iff_fst_eq_snd {X Y : C} {f : X ⟶ Y} {c : PullbackCone f f} (hc : IsLimit c) :
    Mono f ↔ c.fst = c.snd := by
  constructor
  · intro hf
    rw [← cancel_mono f]
    exact c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hc g g' h
    rw [hf]

lemma mono_iff_isIso_fst {X Y : C} {f : X ⟶ Y} {c : PullbackCone f f} (hc : IsLimit c) :
    Mono f ↔ IsIso c.fst := by
  rw [mono_iff_fst_eq_snd hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    refine' ⟨φ, PullbackCone.IsLimit.hom_ext hc _ _, hφ₁⟩
    · dsimp
      simp only [assoc, hφ₁, id_comp, comp_id]
    · dsimp
      simp only [assoc, hφ₂, id_comp, comp_id, h]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PullbackCone.IsLimit.lift' hc (𝟙 X) (𝟙 X) (by simp)
    have : IsSplitEpi φ := IsSplitEpi.mk ⟨SplitEpi.mk c.fst (by
      rw [← cancel_mono c.fst, assoc, id_comp, hφ₁, comp_id])⟩
    rw [← cancel_epi φ, hφ₁, hφ₂]

lemma mono_iff_isPullback {X Y : C} (f : X ⟶ Y) : Mono f ↔ IsPullback (𝟙 X) (𝟙 X) f f := by
  constructor
  · intro
    exact
      { w := by simp
        isLimit' := ⟨PullbackCone.isLimitMkIdId f⟩ }
  · intro hf
    exact (mono_iff_fst_eq_snd hf.isLimit).2 rfl

lemma epi_iff_inl_eq_inr {X Y : C} {f : X ⟶ Y} {c : PushoutCocone f f} (hc : IsColimit c) :
    Epi f ↔ c.inl = c.inr := by
  constructor
  · intro hf
    rw [← cancel_epi f]
    exact c.condition
  · intro hf
    constructor
    intro Z g g' h
    obtain ⟨φ, rfl, rfl⟩ := PushoutCocone.IsColimit.desc' hc g g' h
    rw [hf]

lemma epi_iff_isIso_inl {X Y : C} {f : X ⟶ Y} {c : PushoutCocone f f} (hc : IsColimit c) :
    Epi f ↔ IsIso c.inl := by
  rw [epi_iff_inl_eq_inr hc]
  constructor
  · intro h
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    refine' ⟨φ, hφ₁, PushoutCocone.IsColimit.hom_ext hc _ _⟩
    · dsimp
      simp only [comp_id, reassoc_of% hφ₁]
    · dsimp
      simp only [comp_id, h, reassoc_of% hφ₂]
  · intro
    obtain ⟨φ, hφ₁, hφ₂⟩ := PushoutCocone.IsColimit.desc' hc (𝟙 Y) (𝟙 Y) (by simp)
    have : IsSplitMono φ := IsSplitMono.mk ⟨SplitMono.mk c.inl (by
      rw [← cancel_epi c.inl, reassoc_of% hφ₁, comp_id])⟩
    rw [← cancel_mono φ, hφ₁, hφ₂]

lemma epi_iff_isPushout {X Y : C} (f : X ⟶ Y) : Epi f ↔ IsPushout f f (𝟙 Y) (𝟙 Y) := by
  constructor
  · intro
    exact
      { w := by simp
        isColimit' := ⟨PushoutCocone.isColimitMkIdId f⟩ }
  · intro hf
    exact (epi_iff_inl_eq_inr hf.isColimit).2 rfl

structure JointlyReflectIsomorphisms : Prop where
  isIso {X Y : C} (f : X ⟶ Y) [∀ i, IsIso ((F i).map f)] : IsIso f

structure JointlyReflectMonomorphisms : Prop where
  mono {X Y : C} (f : X ⟶ Y) [∀ i, Mono ((F i).map f)] : Mono f

structure JointlyReflectEpimorphisms : Prop where
  epi {X Y : C} (f : X ⟶ Y) [∀ i, Epi ((F i).map f)] : Epi f

namespace JointlyReflectIsomorphisms

variable {F} (h : JointlyReflectIsomorphisms F)

lemma isIso_iff {X Y : C} (f : X ⟶ Y) : IsIso f ↔ ∀ i, IsIso ((F i).map f) := by
  constructor
  · intro hf i
    infer_instance
  · intro
    exact h.isIso f

lemma mono {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Mono ((F i).map f)]
    [∀ i,  PreservesLimit (cospan f f) (F i)] [HasPullback f f] : Mono f := by
  have hc := pullbackIsPullback f f
  rw [mono_iff_isIso_fst hc, h.isIso_iff]
  intro i
  exact (mono_iff_isIso_fst ((isLimitMapConePullbackConeEquiv (F i) pullback.condition).1
    (isLimitOfPreserves (F i) hc))).1 (hf i)

lemma jointlyReflectMonomorphisms [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    [HasPullbacks C] :
    JointlyReflectMonomorphisms F where
  mono f _ := h.mono f

lemma epi {X Y : C} (f : X ⟶ Y) [hf : ∀ i, Epi ((F i).map f)]
    [∀ i,  PreservesColimit (span f f) (F i)] [HasPushout f f] : Epi f := by
  have hc := pushoutIsPushout f f
  rw [epi_iff_isIso_inl hc, h.isIso_iff]
  intro i
  exact (epi_iff_isIso_inl ((isColimitMapCoconePushoutCoconeEquiv (F i) pushout.condition).1
    (isColimitOfPreserves (F i) hc))).1 (hf i)

lemma jointlyReflectEpimorphisms [∀ i, PreservesColimitsOfShape WalkingSpan (F i)]
    [HasPushouts C] :
    JointlyReflectEpimorphisms F where
  epi f _ := h.epi f

end JointlyReflectIsomorphisms

namespace JointlyReflectMonomorphisms

variable {F} (h : JointlyReflectMonomorphisms F)

lemma mono_iff [∀ i, (F i).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ i, Mono ((F i).map f) := by
  constructor
  · intros
    infer_instance
  · intro
    exact h.mono f

end JointlyReflectMonomorphisms

namespace JointlyReflectEpimorphisms

variable {F} (h : JointlyReflectEpimorphisms F)

lemma epi_iff [∀ i, (F i).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ ∀ i, Epi ((F i).map f) := by
  constructor
  · intros
    infer_instance
  · intro
    exact h.epi f

end JointlyReflectEpimorphisms

end CategoryTheory
