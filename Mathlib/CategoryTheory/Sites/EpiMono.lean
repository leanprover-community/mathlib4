/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.MorphismProperty
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Whiskering
/-!
# Characterization of mono and epi in the category of sheaves of types

In this file, we obtain the lemmas `Sheaf.mono_iff_injective`, `Sheaf.isIso_iff_bijective`
and `Sheaf.epi_iff_locally_surjective` which are concrete characterizations of monomorphisms,
isomorphisms and epimorphisms in a category of sheaves of types for a Grothendieck
topology `J` on a category `C`.

Given a morphism `φ : F ⟶ G` in `Sheaf J (Type _)`, it is easy to show that it is
a mono (resp. an iso) iff for all `X : Cᵒᵖ`, the map `φ.val.app X : F.val.obj X ⟶ G.val.obj X`
is injective (resp. bijective), similarly as for morphisms of presheaves. We also
obtain a characterization of epimorphism : `φ` is an epimorphism iff any section of
`G` can be *locally* lifted to a section of `F`.

The proof of the characterization of epimorphisms uses an epi/mono factorization of
`φ : F ⟶ G` (see `Sheaf.EpiMonoFactorization.π_ι`) in order to reduce to the particular
case when `φ` is also a monomorphism, and for this, we show that the category of
sheaves of types is balanced: `φ` is an isomorphism iff it is a mono and an epi.
The proof of this last fact is obtained following the argument in SGA 4 II 4.2.

-/

universe w v u

namespace CategoryTheory

open Opposite Limits

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

attribute [local instance] ConcreteCategory.hasCoeToSort ConcreteCategory.instFunLike

section

variable {D : Type*} [Category D] [ConcreteCategory D] {F G : Sheaf J D} (φ : F ⟶ G)

structure LocallySurjective : Prop where
  exists_local_lifting {X : Cᵒᵖ} (x : G.1.obj X) :
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
      ∀ {Y : C} (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
        φ.1.app (op Y) y = G.1.map f.op x

namespace LocallySurjective

variable {φ}
variable (h : LocallySurjective φ) {X : Cᵒᵖ} (x : G.1.obj X)

noncomputable def liftingSieve : Sieve X.unop := (h.exists_local_lifting x).choose

lemma liftingSieve_mem : h.liftingSieve x ∈ J X.unop :=
  (h.exists_local_lifting x).choose_spec.choose

noncomputable def lifting {Y : C} (f : Y ⟶ X.unop) (hf : h.liftingSieve x f) :
    F.1.obj (op Y) :=
  ((h.exists_local_lifting x).choose_spec.choose_spec f hf).choose

@[simp]
lemma app_apply_lifting {Y : C} (f : Y ⟶ X.unop) (hf : h.liftingSieve x f) :
    φ.1.app (op Y) (h.lifting x f hf) = G.1.map f.op x :=
  ((h.exists_local_lifting x).choose_spec.choose_spec f hf).choose_spec

lemma epi' {F G : Sheaf J (Type w)} {φ : F ⟶ G} (h : LocallySurjective φ) : Epi φ where
  left_cancellation := by
    intro H f₁ f₂ h₁₂
    ext X x
    apply ((Presieve.isSeparated_of_isSheaf _ _
      ((isSheaf_iff_isSheaf_of_type _ _).1 H.2)) _ (h.liftingSieve_mem x)).ext
    intro Y f hf
    have h₁ := congr_fun (f₁.1.naturality f.op) x
    have h₂ := congr_fun (f₂.1.naturality f.op) x
    dsimp at h₁ h₂
    simp only [← h₁, ← h₂]
    erw [congr_arg (f₁.val.app (op Y)) (h.app_apply_lifting x f hf).symm,
      congr_arg (f₂.val.app (op Y)) (h.app_apply_lifting x f hf).symm]
    exact congr_fun (congr_app (congr_arg Sheaf.Hom.val h₁₂) (op Y)) _

variable [J.HasSheafCompose (forget D)]

lemma sheafCompose_forget : LocallySurjective ((sheafCompose J (forget D)).map φ) where
  exists_local_lifting x := ⟨h.liftingSieve x, h.liftingSieve_mem x, fun f hf =>
    ⟨h.lifting x f hf, h.app_apply_lifting x f hf⟩⟩

instance : Faithful (sheafCompose J (forget D)) where
  map_injective {F G f₁ f₂} h := by
    ext X x
    exact congr_fun (congr_app ((sheafToPresheaf _ _).congr_map h) X) x

lemma epi : Epi φ :=
  (sheafCompose J (forget D)).epi_of_epi_map (h.sheafCompose_forget.epi')

end LocallySurjective

end

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

lemma epi_of_locally_surjective (h : LocallySurjective φ) : Epi φ := h.epi

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

namespace EpiMonoFactorization

/-- The underlying presheaf of the image of a sheaf of sets, which consists of sections
of the target sheaf which can be locally lifted to the source sheaf. -/
@[simps]
def presheafI : Cᵒᵖ ⥤ Type w where
  obj X := { x : G.1.obj X | ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
      φ.1.app _ y = G.1.map f.op x }
  map {X X'} g a := ⟨G.1.map g a.1, by
    obtain ⟨S, hS, h⟩ := a.2
    refine' ⟨S.pullback g.unop, J.pullback_stable _ hS, fun Y f hf => _⟩
    obtain ⟨y, hy⟩ := h (f ≫ g.unop) hf
    exact ⟨y, by simp [hy]⟩⟩

/-- The inclusion of the image of a morphism of sheaves of sets, as a morpshim of presheaves. -/
@[simps]
def presheafι : presheafI φ ⟶ G.1 where
  app _ x := x.1
  naturality _ _ _ := rfl

/-- The image of a morphism of sheaves of sets. -/
@[simps]
def I : Sheaf J (Type w) := ⟨presheafI φ, by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS α hα
  have hS' := (((isSheaf_iff_isSheaf_of_type _ _).1 G.2) _ hS)
  refine' ⟨⟨hS'.amalgamate _
    (hα.compPresheafMap (presheafι φ)), _⟩, _, _⟩
  · let U := fun ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S.arrows f) => (α f hf).2.choose
    have hU : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S.arrows f), U hf ∈ J _:= fun Y f hf =>
        (α f hf).2.choose_spec.choose
    refine' ⟨_, J.bind_covering hS hU, fun Y f hf => _⟩
    obtain ⟨T, a, b, hb, ha : U hb a, fac⟩ := hf
    obtain ⟨y, hy⟩ := (α _ hb).2.choose_spec.choose_spec _ ha
    refine' ⟨y, _⟩
    have hf : S.arrows f := by
      rw [← fac]
      apply S.downward_closed hb
    rw [hy, Presieve.IsSheafFor.valid_glue hS' (hα.compPresheafMap (presheafι φ)) f hf]
    simpa using (hα.compPresheafMap (presheafι φ)) a (𝟙 _) hb hf (by simpa using fac)
  · intro Y f hf
    apply Subtype.ext
    apply Presieve.IsSheafFor.valid_glue hS' (hα.compPresheafMap (presheafι φ))
  · rintro ⟨y, _⟩ hy
    apply Subtype.ext
    apply ((Presieve.isSeparated_of_isSheaf _ _
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.2)) S hS).ext
    intro Y f hf
    dsimp
    replace hy := hy f hf
    rw [Subtype.ext_iff] at hy
    dsimp at hy
    rw [hy]
    symm
    apply Presieve.IsSheafFor.valid_glue⟩

/-- The inclusion of the image of a morphism of sheaves of sets. -/
@[simps]
def ι : I φ ⟶ G := Sheaf.Hom.mk (presheafι φ)

/-- The projection to the image of a morphism of sheaves of sets. -/
@[simps]
def π : F ⟶ I φ where
  val :=
    { app := fun X x => ⟨φ.1.app X x, ⟨⊤, J.top_mem X.unop, fun Y f _ =>
        ⟨F.1.map f.op x, congr_fun (φ.val.naturality f.op) x⟩⟩⟩
      naturality := fun X X' g => by
        ext x
        exact Subtype.ext (congr_fun (φ.val.naturality g) x) }

lemma locallySurjective_π : LocallySurjective (π φ) where
  exists_local_lifting  x := by
    obtain ⟨S, hS, hS'⟩ := x.2
    refine ⟨S, hS, fun f hf => ?_⟩
    obtain ⟨y, hy⟩ := hS' f hf
    exact ⟨y, Subtype.ext hy⟩

instance : Epi (π φ) := (locallySurjective_π φ).epi

instance : Mono (ι φ) := by
  apply mono_of_injective
  intro X x₁ x₂ h
  exact Subtype.ext h

@[reassoc (attr := simp)]
lemma π_ι : π φ ≫ ι φ = φ := rfl

instance [Epi φ] : Epi (ι φ) := epi_of_epi_fac (π_ι φ)

end EpiMonoFactorization

namespace BalancedAux

/-- If a commutative square in the category of sets is pushout square, and the top map
is injective, then the square is also pullback square,  -/
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

lemma epi_iff_locally_surjective [HasSheafify J (Type w)] :
    Epi φ ↔ LocallySurjective φ := by
  constructor
  · intro hφ
    constructor
    have : IsIso (EpiMonoFactorization.ι φ) := isIso_of_mono_of_epi _
    intro X x
    obtain ⟨⟨y, hy⟩, rfl⟩ :=
      ((isIso_iff_bijective (EpiMonoFactorization.ι φ)).1 inferInstance X).2 x
    exact hy
  · intro hφ
    exact epi_of_locally_surjective φ hφ

end Sheaf

end CategoryTheory
