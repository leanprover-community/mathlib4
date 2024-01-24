import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.JointlyReflect.Isomorphisms

universe w v u

namespace CategoryTheory

open Opposite Limits

namespace Limits

variable {J : Type u} [Category J]
  {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

instance [IsLeftAdjoint F] : PreservesColimitsOfShape J F :=
  (Adjunction.ofLeftAdjoint F).leftAdjointPreservesColimits.preservesColimitsOfShape

instance [IsLeftAdjoint F] : PreservesColimits F where

instance [IsRightAdjoint F] : PreservesLimitsOfShape J F :=
  (Adjunction.ofRightAdjoint F).rightAdjointPreservesLimits.preservesLimitsOfShape

instance [IsRightAdjoint F] : PreservesLimits F where

end Limits

namespace Limits

-- to be moved to CategoryTheory.Limits.Shapes.Types
namespace Types

variable {S X₁ X₂ : Type w} (f : S ⟶ X₁) (g : S ⟶ X₂)

variable (T : S → Type w)

inductive pushoutRel (f : S ⟶ X₁) (g : S ⟶ X₂) :
    Sum X₁ X₂ → Sum X₁ X₂ → Prop
  | refl₁ (x₁ : X₁) : pushoutRel f g (Sum.inl x₁) (Sum.inl x₁)
  | refl₂ (x₂ : X₂) : pushoutRel f g (Sum.inr x₂) (Sum.inr x₂)
  | map (s : S) : pushoutRel f g (Sum.inl (f s)) (Sum.inr (g s))
  | map' (s : S) : pushoutRel f g (Sum.inr (g s)) (Sum.inl (f s))

namespace pushoutRel

lemma refl (x : Sum X₁ X₂) : pushoutRel f g x x := by
  obtain (x₁|x₂) := x
  · apply pushoutRel.refl₁
  · apply pushoutRel.refl₂

variable {f g}

lemma symm (x y : Sum X₁ X₂) (h : pushoutRel f g x y) :
    pushoutRel f g y x := by
    cases h
    · apply pushoutRel.refl₁
    · apply pushoutRel.refl₂
    · apply pushoutRel.map'
    · apply pushoutRel.map

end pushoutRel

def pushoutObj : Type w := _root_.Quot (pushoutRel f g)

@[simp]
def pushoutInl : X₁ ⟶ pushoutObj f g := fun x => Quot.mk _ (Sum.inl x)

@[simp]
def pushoutInr : X₂ ⟶ pushoutObj f g := fun x => Quot.mk _ (Sum.inr x)

lemma pushout_condition : f ≫ pushoutInl f g = g ≫ pushoutInr f g := by
  ext x
  exact Quot.sound (pushoutRel.map x)

@[simps!]
def pushoutCocone : PushoutCocone f g :=
    PushoutCocone.mk _ _ (pushout_condition f g)

def isColimitPushoutCocone : IsColimit (pushoutCocone f g) :=
  PushoutCocone.IsColimit.mk _ (fun s => Quot.lift (fun x => match x with
      | Sum.inl x₁ => s.inl x₁
      | Sum.inr x₂ => s.inr x₂) (fun a b h => by
          obtain x₁|x₂|x|x :=  h
          · rfl
          · rfl
          · exact congr_fun s.condition x
          · exact congr_fun s.condition.symm x))
      (fun s => rfl) (fun s => rfl) (fun s m h₁ h₂ => by
        ext ⟨x₁|x₂⟩
        · exact congr_fun h₁ x₁
        · exact congr_fun h₂ x₂)

lemma pushoutRel_inl_inr_iff (x₁ : X₁) (x₂ : X₂) :
    pushoutRel f g (Sum.inl x₁) (Sum.inr x₂) ↔
      ∃ (s : S), f s = x₁ ∧ g s = x₂ := by
  constructor
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨_, rfl, rfl⟩
    apply pushoutRel.map

section

variable [Mono f] [Mono g]

def equivalencePushoutRel :
    _root_.Equivalence (pushoutRel f g) where
  refl := pushoutRel.refl f g
  symm h := h.symm
  trans := by
    rintro (x₁|x₂) (y₁|y₂) (z₁|z₂) hxy hyz
    · cases hxy
      cases hyz
      apply pushoutRel.refl
    · cases hxy
      cases hyz
      apply pushoutRel.map
    · obtain ⟨s, rfl, rfl⟩ := (pushoutRel_inl_inr_iff _ _ _ _ ).1 hxy
      obtain ⟨t, rfl, ht⟩ := (pushoutRel_inl_inr_iff _ _ _ _ ).1 hyz.symm
      obtain rfl : t = s := (mono_iff_injective g).1 inferInstance ht
      apply pushoutRel.refl
    · cases hyz
      exact hxy
    · cases hyz
      exact hxy
    · obtain ⟨s, rfl, rfl⟩ := (pushoutRel_inl_inr_iff _ _ _ _ ).1 hxy.symm
      obtain ⟨t, ht, rfl⟩ := (pushoutRel_inl_inr_iff _ _ _ _ ).1 hyz
      obtain rfl : t = s := (mono_iff_injective f).1 inferInstance ht
      apply pushoutRel.refl
    · cases hxy
      exact hyz
    · cases hyz
      exact hxy

lemma quot_mk_pushoutRel_eq_iff (a b : Sum X₁ X₂) :
    (Quot.mk (pushoutRel f g) a = Quot.mk (pushoutRel f g) b) ↔
        pushoutRel f g a b :=
  (equivalencePushoutRel f g).quot_mk_eq_iff _ _

lemma pushoutInl_eq_pushoutInr_iff (x₁ : X₁) (x₂ : X₂) :
    (pushoutInl f g x₁ = pushoutInr f g x₂) ↔
      ∃ (s : S), f s = x₁ ∧ g s = x₂ := by
  refine' (quot_mk_pushoutRel_eq_iff f g (Sum.inl x₁) (Sum.inr x₂)).trans _
  constructor
  · rintro ⟨⟩
    exact ⟨_, rfl, rfl⟩
  · rintro ⟨s, rfl, rfl⟩
    exact pushoutRel.map s

lemma inl_eq_inr_imp_of_iso
    {S X₁ X₂: Type w} {i₁ : S ⟶ X₁} {i₂ : S ⟶ X₂} (c c' : PushoutCocone i₁ i₂)
    (e : c ≅ c') (x₁ : X₁) (x₂ : X₂) (h : c.inl x₁ = c.inr x₂) :
    c'.inl x₁ = c'.inr x₂ := by
  convert congr_arg e.hom.hom h
  · exact congr_fun (e.hom.w WalkingSpan.left).symm x₁
  · exact congr_fun (e.hom.w WalkingSpan.right).symm x₂

lemma inl_eq_inr_iff_of_iso
    {S X₁ X₂: Type w} {i₁ : S ⟶ X₁} {i₂ : S ⟶ X₂} (c c' : PushoutCocone i₁ i₂)
    (e : c ≅ c') (x₁ : X₁) (x₂ : X₂) :
    c.inl x₁ = c.inr x₂ ↔ c'.inl x₁ = c'.inr x₂ := by
  constructor
  · apply inl_eq_inr_imp_of_iso c c' e
  · apply inl_eq_inr_imp_of_iso c' c e.symm

lemma inl_eq_inr_iff_of_isColimit {S X₁ X₂: Type w} {i₁ : S ⟶ X₁} {i₂ : S ⟶ X₂} (c : PushoutCocone i₁ i₂)
    (hc : IsColimit c) (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    (x₁ : X₁) (x₂ : X₂) :
    c.inl x₁ = c.inr x₂ ↔ ∃ (s : S), i₁ s = x₁ ∧ i₂ s = x₂ := by
  rw [inl_eq_inr_iff_of_iso c (pushoutCocone i₁ i₂)
    (Cocones.ext (IsColimit.coconePointUniqueUpToIso hc (isColimitPushoutCocone i₁ i₂))
    (by aesop_cat))]
  have := (mono_iff_injective i₁).2 h₁
  have := (mono_iff_injective i₂).2 h₂
  apply pushoutInl_eq_pushoutInr_iff

end

end Types

end Limits

namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G : Sheaf J (Type w)} (φ : F ⟶ G)

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

lemma epi_of_locally_surjective (hφ : ∀ (X : Cᵒᵖ) (x : G.1.obj X),
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ (Y : C) (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
    φ.1.app _ y = G.1.map f.op x) : Epi φ where
  left_cancellation := by
    intro H f₁ f₂ h
    ext X x
    obtain ⟨S, hS, hS'⟩ := hφ _ x
    apply ((Presieve.isSeparated_of_isSheaf _ _
      ((isSheaf_iff_isSheaf_of_type _ _).1 H.2)) S hS).ext
    intro Y f hf
    obtain ⟨y, hy⟩ := hS' Y f hf
    have h₁ := congr_fun (f₁.1.naturality f.op) x
    have h₂ := congr_fun (f₂.1.naturality f.op) x
    dsimp at h₁ h₂
    simp only [← h₁, ← h₂, ← hy]
    exact congr_fun (congr_app (congr_arg Sheaf.Hom.val h) (op Y)) y

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

@[simps]
def presheafI : Cᵒᵖ ⥤ Type w where
  obj X := { x : G.1.obj X | ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ (Y : C) (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
      φ.1.app _ y = G.1.map f.op x }
  map {X X'} g a := ⟨G.1.map g a.1, by
    obtain ⟨S, hS, h⟩ := a.2
    refine' ⟨S.pullback g.unop, J.pullback_stable _ hS, fun Y f hf => _⟩
    obtain ⟨y, hy⟩ := h Y (f ≫ g.unop) hf
    exact ⟨y, by simp [hy]⟩⟩

@[simps]
def presheafι : presheafI φ ⟶ G.1 where
  app _ x := x.1
  naturality _ _ _ := rfl

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
    obtain ⟨y, hy⟩ := (α _ hb).2.choose_spec.choose_spec _ a ha
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

@[simps]
def ι : I φ ⟶ G := Sheaf.Hom.mk (presheafι φ)

@[simps]
def π : F ⟶ I φ where
  val :=
    { app := fun X x => ⟨φ.1.app X x, ⟨⊤, J.top_mem X.unop, fun Y f _ =>
        ⟨F.1.map f.op x, congr_fun (φ.val.naturality f.op) x⟩⟩⟩
      naturality := fun X X' g => by
        ext x
        exact Subtype.ext (congr_fun (φ.val.naturality g) x) }

instance : Epi (π φ) := by
  apply epi_of_locally_surjective
  intro X x
  obtain ⟨S, hS, hS'⟩ := x.2
  refine' ⟨S, hS, fun Y f hf => _⟩
  obtain ⟨y, hy⟩ := hS' Y f hf
  exact ⟨y, Subtype.ext hy⟩

instance : Mono (ι φ) := by
  apply mono_of_injective
  intro X x₁ x₂ h
  exact Subtype.ext h

@[reassoc (attr := simp)]
lemma π_ι : π φ ≫ ι φ = φ := rfl

instance [Epi φ] : Epi (ι φ) := epi_of_epi_fac (π_ι φ)

end EpiMonoFactorization

namespace BalancedAux

lemma isLimit_of_isPushout_of_injective {X Y S : Type w} {f : X ⟶ S} {g : Y ⟶ S}
    (c : PullbackCone f g) (hc : IsPushout c.fst c.snd f g)
    (h₁ : Function.Injective c.fst) (h₂ : Function.Injective c.snd) :
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
      obtain ⟨x, hx₁, hx₂⟩ := (Types.inl_eq_inr_iff_of_isColimit _ hc.isColimit h₁ h₂
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
  exact IsLimit.ofIsoLimit (pullbackIsPullback _ _) (Iso.symm (PullbackCone.ext (asIso φ) (by simp) (by simp)))

end BalancedAux

-- SGA 4 II 4.2
instance [HasSheafify J (Type w)] : Balanced (Sheaf J (Type w)) where
  isIso_of_mono_of_epi {F G} φ _ _ := by
    have e : Arrow.mk φ ≅ ((presheafToSheaf J _).map φ.1) :=
      Arrow.isoOfNatIso (sheafificationNatIso J (Type w)) (Arrow.mk φ)
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
      all_goals
        exact (mono_iff_injective φ).1 inferInstance X
    have fac := (presheafToSheaf J _).congr_map c₁.condition
    simp only [Functor.map_comp] at fac
    let c₃ := PushoutCocone.mk _ _ fac
    have h₃ : IsColimit c₃ :=
      isColimitPushoutCoconeMapOfIsColimit (presheafToSheaf J (Type w)) _ h₁
    let c₄ := PullbackCone.mk _ _ fac
    have h₄ : IsLimit c₄ := isLimitPullbackConeMapOfIsLimit (presheafToSheaf J (Type w)) _ h₂
    have : Epi ((presheafToSheaf J _).map φ.1) :=
      ((MorphismProperty.RespectsIso.epimorphisms _).arrow_mk_iso_iff e).1 (by simpa)
    have : IsIso ((presheafToSheaf J _).map φ.1) :=
      (MorphismProperty.StableUnderBaseChange.isomorphisms (Sheaf J (Type w)))
        (IsPullback.of_isLimit h₄) ((epi_iff_isIso_inl h₃).1 inferInstance)
    exact ((MorphismProperty.RespectsIso.isomorphisms _).arrow_mk_iso_iff e).2 this

lemma epi_iff_locally_surjective [HasSheafify J (Type w)] :
    Epi φ ↔ (∀ (X : Cᵒᵖ) (x : G.1.obj X),
    ∃ (S : Sieve X.unop) (_ : S ∈ J X.unop),
    ∀ (Y : C) (f : Y ⟶ X.unop) (_ : S f), ∃ (y : F.1.obj (op Y)),
    φ.1.app _ y = G.1.map f.op x) := by
  constructor
  · intro hφ
    have : IsIso (EpiMonoFactorization.ι φ) := isIso_of_mono_of_epi _
    intro X x
    obtain ⟨⟨y, hy⟩, rfl⟩ :=
      ((isIso_iff_bijective (EpiMonoFactorization.ι φ)).1 inferInstance X).2 x
    exact hy
  · intro hφ
    exact epi_of_locally_surjective φ hφ

end Sheaf

end CategoryTheory
