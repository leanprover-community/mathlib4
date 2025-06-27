/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The category of sheaves of types is balanced

In this file, we obtain that the category of sheaves of types is balanced,
i.e. a morphism that is both a mono and an epi is an isomorphism.

We also obtain the lemmas `Sheaf.mono_iff_injective`,
`Sheaf.isIso_iff_bijective` and `Sheaf.epi_iff_locallySurjective` which
are concrete characterizations of monomorphisms, isomorphisms and epimorphisms
in the category of sheaves of types for a Grothendieck topology `J` on a category `C`.
(The characterization of monomorphisms and isomorphisms apply more generally to
sheaves with values in concrete categories satisfying suitable assumptions.)

-/

universe w v' v u' u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {DD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (DD X) (DD Y)] [ConcreteCategory.{w} D FD]
  {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace Sheaf

section

variable {F G : Sheaf J D} (φ : F ⟶ G)

lemma mono_iff_injective [(forget D).PreservesMonomorphisms]
    [HasLimitsOfShape WalkingCospan D] :
    Mono φ ↔ ∀ (X : Cᵒᵖ), Function.Injective
      (fun (x : (forget _).obj (F.1.obj X)) => φ.1.app _ x) := by
  constructor
  · intro _ X
    apply (CategoryTheory.mono_iff_injective ((sheafToPresheaf J D ⋙
      (evaluation _ _ ).obj X ⋙ forget D).map φ)).1
    infer_instance
  · apply mono_of_injective

lemma isIso_iff_bijective [(forget D).ReflectsIsomorphisms] :
    IsIso φ ↔ ∀ (X : Cᵒᵖ), Function.Bijective
      (fun (x : (forget _).obj (F.1.obj X)) => φ.1.app _ x) := by
  have : IsIso φ ↔ IsIso φ.1 := by
    change _ ↔ IsIso ((sheafToPresheaf _ _).map φ)
    constructor
    · intro
      infer_instance
    · intro
      exact isIso_of_reflects_iso φ (sheafToPresheaf _ _)
  rw [this]
  constructor
  · intro _ X
    rw [← CategoryTheory.isIso_iff_bijective]
    change IsIso ((forget D).map (φ.val.app X))
    infer_instance
  · intro hφ
    have : ∀ (X : Cᵒᵖ), IsIso (φ.1.app X) := fun X => by
      have : IsIso ((forget D).map (φ.val.app X)) := by
        simpa only [CategoryTheory.isIso_iff_bijective] using hφ X
      apply isIso_of_reflects_iso _ (forget D)
    apply NatIso.isIso_of_isIso_app

end

namespace BalancedAux

/-- If a commutative square in the category of types is pushout square, and the top map
is injective, then the square is also a pullback square. -/
noncomputable def isLimit_of_isPushout_of_injective {X Y S : Type w} {f : X ⟶ S} {g : Y ⟶ S}
    (c : PullbackCone f g) (hc : IsPushout c.fst c.snd f g)
    (h₁ : Function.Injective c.fst) :
        IsLimit c := by
  let φ : c.pt ⟶ pullback f g := pullback.lift c.fst c.snd c.condition
  have hφ : IsIso φ := by
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro x₁ x₂ h
      apply h₁
      have : c.fst = φ ≫ pullback.fst _ _ := by simp [φ]
      rw [this, types_comp_apply, types_comp_apply, h]
    · intro t
      obtain ⟨x, hx₁, hx₂⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hc.isColimit h₁
        (@pullback.fst _ _ _ _ _ f g _ t)
        (@pullback.snd _ _ _ _ _ f g _ t)).1 (by
          dsimp
          rw [← types_comp_apply (pullback.fst f g) f,
            ← types_comp_apply (pullback.snd f g) g, pullback.condition])
      refine ⟨x, ?_⟩
      apply (Types.pullbackIsoPullback f g).toEquiv.injective
      ext
      · rw [Iso.toEquiv_fun, Types.pullbackIsoPullback_hom_fst,
          ← types_comp_apply φ (pullback.fst _ _), pullback.lift_fst, hx₁,
          Types.pullbackIsoPullback_hom_fst]
      · rw [Iso.toEquiv_fun, Types.pullbackIsoPullback_hom_snd,
          ← types_comp_apply φ (pullback.snd _ _), pullback.lift_snd, hx₂,
          Types.pullbackIsoPullback_hom_snd]
  exact IsLimit.ofIsoLimit (pullbackIsPullback _ _)
    (Iso.symm (PullbackCone.ext (asIso φ) (by simp [φ]) (by simp [φ])))

end BalancedAux

instance [HasSheafify J (Type w)] : Balanced (Sheaf J (Type w)) where
  isIso_of_mono_of_epi {F G} φ _ _ := by
    -- this is the argument from SGA 4 II 4.2
    let c₁ : PushoutCocone φ.1 φ.1 := PushoutCocone.mk _ _ pushout.condition
    have h₁ : IsColimit c₁ := pushoutIsPushout φ.1 φ.1
    let c₂ := PullbackCone.mk _ _ c₁.condition
    have h₂ : IsLimit c₂ := by
      apply evaluationJointlyReflectsLimits
      intro X
      apply (isLimitMapConePullbackConeEquiv _ _).2
      apply BalancedAux.isLimit_of_isPushout_of_injective
      · exact IsPushout.of_isColimit
          (isColimitPushoutCoconeMapOfIsColimit ((evaluation Cᵒᵖ (Type w)).obj X) _ h₁)
      · exact (mono_iff_injective φ).1 inferInstance X
    have h₁' := isColimitPushoutCoconeMapOfIsColimit (presheafToSheaf J (Type w)) _ h₁
    have h₂' := isLimitPullbackConeMapOfIsLimit (presheafToSheaf J (Type w)) _ h₂
    have e : Arrow.mk φ ≅ ((presheafToSheaf J _).map φ.1) :=
      Arrow.isoOfNatIso (sheafificationNatIso J (Type w)) (Arrow.mk φ)
    have : Epi ((presheafToSheaf J _).map φ.1) :=
      ((MorphismProperty.epimorphisms _).arrow_mk_iso_iff e).1 (by simpa)
    have : IsIso ((presheafToSheaf J _).map φ.1) :=
      (MorphismProperty.isomorphisms _).of_isPullback
        (IsPullback.of_isLimit h₂') ((epi_iff_isIso_inl h₁').1 inferInstance)
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 this

lemma epi_iff_isLocallySurjective
    {F G : Sheaf J (Type w)} (φ : F ⟶ G) [HasSheafify J (Type w)] :
    Epi φ ↔ IsLocallySurjective φ := by
  constructor
  · intro hφ
    have : Epi (Sheaf.imageι φ) :=
      epi_of_epi_fac (Sheaf.toImage_ι φ)
    have : IsIso (Sheaf.imageι φ) := isIso_of_mono_of_epi _
    rw [← Sheaf.toImage_ι φ]
    apply Presheaf.isLocallySurjective_comp
  · intro
    apply epi_of_isLocallySurjective

end Sheaf

end CategoryTheory
