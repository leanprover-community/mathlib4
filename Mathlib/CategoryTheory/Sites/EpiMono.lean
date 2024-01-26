/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.Sites.EpiMonoFactorization
/-!
# Characterization of mono and epi in the category of sheaves of types

In this file, we obtain the lemmas `Sheaf.mono_iff_injective`, `Sheaf.isIso_iff_bijective`
and `Sheaf.epi_iff_locallySurjective` which are concrete characterizations of monomorphisms,
isomorphisms and epimorphisms in a category of sheaves of types for a Grothendieck
topology `J` on a category `C`.

Given a morphism `φ : F ⟶ G` in `Sheaf J (Type _)`, it is easy to show that it is
a mono (resp. an iso) iff for all `X : Cᵒᵖ`, the map `φ.val.app X : F.val.obj X ⟶ G.val.obj X`
is injective (resp. bijective), similarly as for morphisms of presheaves. We also
obtain a characterization of epimorphisms: `φ` is an epimorphism iff if is
locally surjective (see `CategoryTheory.Sites.LocallySurjective`), i.e. any section of
`G` can be *locally* lifted to a section of `F`.

The proof of the characterization of epimorphisms uses an epi/mono factorization of
`φ : F ⟶ G` (see the file `CategoryTheory.Sites.EpiMonoFactorization`) in
order to reduce to the particular case when `φ` is also a monomorphism,
and for this, we show that the category of sheaves of types is balanced:
`φ` is an isomorphism iff it is a mono and an epi. The proof of this last
fact is obtained following the argument in SGA 4 II 4.2.

-/

universe w v u

namespace CategoryTheory

open Opposite Limits

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {F G : Sheaf J (Type w)} (φ : F ⟶ G)

lemma mono_of_injective
    (hφ : ∀ (X : Cᵒᵖ), Function.Injective (fun (x : F.1.obj X) => φ.1.app _ x)) : Mono φ where
  right_cancellation := by
    intro H f₁ f₂ h
    ext Z x
    exact hφ Z (congr_fun (congr_app (congr_arg Sheaf.Hom.val h) Z) x)

lemma mono_iff_injective [HasWeakSheafify J (Type w)] :
    Mono φ ↔ ∀ (X : Cᵒᵖ), Function.Injective (fun (x : F.1.obj X) => φ.1.app _ x) := by
  constructor
  · intro hφ X
    simp only [← CategoryTheory.mono_iff_injective]
    change Mono (((evaluation _ _).obj X).map ((sheafToPresheaf _ _).map φ))
    infer_instance
  · intro hφ
    exact mono_of_injective φ hφ

lemma isIso_iff_bijective :
    IsIso φ ↔ ∀ (X : Cᵒᵖ), Function.Bijective (fun (x : F.1.obj X) => φ.1.app _ x) := by
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
    change IsIso (((evaluation _ _).obj X).map φ.1)
    infer_instance
  · intro hφ
    have : ∀ (X : Cᵒᵖ), IsIso (φ.1.app X) := by
      simpa only [CategoryTheory.isIso_iff_bijective] using hφ
    apply NatIso.isIso_of_isIso_app

namespace BalancedAux

/-- If a commutative square in the category of types is pushout square, and the top map
is injective, then the square is also a pullback square,  -/
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
      have : c.fst = φ ≫ pullback.fst := by simp
      rw [this, types_comp_apply, types_comp_apply, h]
    · intro t
      obtain ⟨x, hx₁, hx₂⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit hc.isColimit h₁
        (@pullback.fst _ _ _ _ _ f g _ t)
        (@pullback.snd _ _ _ _ _ f g _ t)).1 (by
          dsimp
          rw [← types_comp_apply (pullback.fst : pullback f g ⟶ _) f,
            ← types_comp_apply (pullback.snd : pullback f g ⟶ _) g, pullback.condition])
      refine' ⟨x, _⟩
      apply (Types.pullbackIsoPullback f g).toEquiv.injective
      ext
      · rw [Iso.toEquiv_fun, Types.pullbackIsoPullback_hom_fst,
          ← types_comp_apply φ pullback.fst, pullback.lift_fst, hx₁,
          Types.pullbackIsoPullback_hom_fst]
      · rw [Iso.toEquiv_fun, Types.pullbackIsoPullback_hom_snd,
          ← types_comp_apply φ pullback.snd, pullback.lift_snd, hx₂,
          Types.pullbackIsoPullback_hom_snd]
  exact IsLimit.ofIsoLimit (pullbackIsPullback _ _)
    (Iso.symm (PullbackCone.ext (asIso φ) (by simp) (by simp)))

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
      ((MorphismProperty.RespectsIso.epimorphisms _).arrow_mk_iso_iff e).1 (by simpa)
    have : IsIso ((presheafToSheaf J _).map φ.1) :=
      (MorphismProperty.StableUnderBaseChange.isomorphisms (Sheaf J (Type w)))
        (IsPullback.of_isLimit h₂') ((epi_iff_isIso_inl h₁').1 inferInstance)
    exact ((MorphismProperty.RespectsIso.isomorphisms _).arrow_mk_iso_iff e).2 this

lemma epi_iff_locallySurjective [HasSheafify J (Type w)] :
    Epi φ ↔ LocallySurjective φ := by
  constructor
  · intro hφ
    constructor
    have : IsIso (EpiMonoFactorization.ι φ) := isIso_of_mono_of_epi _
    intro X x
    obtain ⟨⟨y, hy⟩, rfl⟩ :=
      ((isIso_iff_bijective (EpiMonoFactorization.ι φ)).1 inferInstance X).2 x
    exact hy
  · intro
    exact epi_of_locallySurjective φ

end Sheaf

end CategoryTheory
