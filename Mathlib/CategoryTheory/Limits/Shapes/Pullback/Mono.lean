/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

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

@[expose] public section

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
  apply reassoc_of% i

/-- Monomorphisms are stable under pullback in the second argument. -/
theorem mono_fst_of_is_pullback_of_mono {t : PullbackCone f g} (ht : IsLimit t) [Mono g] :
    Mono t.fst := by
  refine ⟨fun {W} h k i => IsLimit.hom_ext ht i ?_⟩
  rw [← cancel_mono g, Category.assoc, Category.assoc, ← condition]
  apply reassoc_of% i

/--
The pullback cone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a limit if `f` is a mono. The converse is
shown in `mono_of_pullback_is_id`.
-/
def isLimitMkIdId (f : X ⟶ Y) [Mono f] : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f) :=
  IsLimit.mk _ (fun s => s.fst) (fun _ => Category.comp_id _)
    (fun s => by rw [← cancel_mono f, Category.comp_id, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/--
`f` is a mono if the pullback cone `(𝟙 X, 𝟙 X)` is a limit for the pair `(f, f)`. The converse is
given in `PullbackCone.is_id_of_mono`.
-/
theorem mono_of_isLimitMkIdId (f : X ⟶ Y) (t : IsLimit (mk (𝟙 X) (𝟙 X) rfl : PullbackCone f f)) :
    Mono f :=
  ⟨fun {Z} g h eq => by
    rcases PullbackCone.IsLimit.lift' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `f` and `g` are two morphisms with a common codomain and `s` is a limit cone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through a monomorphism `h` via
`x` and `y`, respectively.  Then `s` is also a limit cone over the diagram formed by `x` and `y`. -/
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
  exact (PullbackCone.IsLimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PullbackCone

end Monomorphisms

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.fst_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono g] :
    Mono (pullback.fst f g) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (limit.isLimit _)

/-- The pullback of a monomorphism is a monomorphism -/
instance pullback.snd_of_mono {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g] [Mono f] :
    Mono (pullback.snd f g) :=
  PullbackCone.mono_snd_of_is_pullback_of_mono (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The map `X ×[Z] Y ⟶ X × Y` is mono. -/
instance mono_pullback_to_prod {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g] [HasBinaryProduct X Y] :
    Mono (prod.lift (pullback.fst f g) (pullback.snd f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => f ≫ prod.fst) h
    · simpa using congrArg (fun f => f ≫ prod.snd) h⟩

/-- The pullback of `f, g` is also the pullback of `f ≫ i, g ≫ i` for any mono `i`. -/
noncomputable def pullbackIsPullbackOfCompMono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i]
    [HasPullback f g] : IsLimit (PullbackCone.mk (pullback.fst f g) (pullback.snd f g)
      -- Porting note: following used to be _
      (show (pullback.fst f g) ≫ f ≫ i = (pullback.snd f g) ≫ g ≫ i by
        simp only [← Category.assoc]; rw [cancel_mono]; apply pullback.condition)) :=
  PullbackCone.isLimitOfCompMono f g i _ (limit.isLimit (cospan f g))

instance hasPullback_of_comp_mono (f : X ⟶ W) (g : Y ⟶ W) (i : W ⟶ Z) [Mono i] [HasPullback f g] :
    HasPullback (f ≫ i) (g ≫ i) :=
  ⟨⟨⟨_, pullbackIsPullbackOfCompMono f g i⟩⟩⟩

section

attribute [local instance] hasPullback_of_left_iso

variable (f : X ⟶ Z) (i : Z ⟶ W) [Mono i]

instance hasPullback_of_right_factors_mono : HasPullback i (f ≫ i) := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono (𝟙 Z) f i

instance pullback_snd_iso_of_right_factors_mono :
    IsIso (pullback.snd i (f ≫ i)) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono (𝟙 _) f i⟩ WalkingCospan.right
  convert (congrArg IsIso (show _ ≫ pullback.snd (𝟙 Z) f = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

attribute [local instance] hasPullback_of_right_iso

instance hasPullback_of_left_factors_mono : HasPullback (f ≫ i) i := by
  simpa only [Category.id_comp] using hasPullback_of_comp_mono f (𝟙 Z) i

instance pullback_snd_iso_of_left_factors_mono :
    IsIso (pullback.fst (f ≫ i) i) := by
  have := limit.isoLimitCone_hom_π ⟨_, pullbackIsPullbackOfCompMono f (𝟙 _) i⟩ WalkingCospan.left
  convert (congrArg IsIso (show _ ≫ pullback.fst f (𝟙 Z) = _ from this)).mp inferInstance
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm

end

section

open WalkingCospan

variable (f : X ⟶ Y) [Mono f]

instance has_kernel_pair_of_mono : HasPullback f f :=
  ⟨⟨⟨_, PullbackCone.isLimitMkIdId f⟩⟩⟩

theorem PullbackCone.fst_eq_snd_of_mono_eq {f : X ⟶ Y} [Mono f] (t : PullbackCone f f) :
    t.fst = t.snd :=
  (cancel_mono f).1 t.condition

theorem fst_eq_snd_of_mono_eq : pullback.fst f f = pullback.snd f f :=
  PullbackCone.fst_eq_snd_of_mono_eq (getLimitCone (cospan f f)).cone

@[simp]
theorem pullbackSymmetry_hom_of_mono_eq : (pullbackSymmetry f f).hom = 𝟙 _ := by
  ext
  · simp [fst_eq_snd_of_mono_eq]
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
lemma PullbackCone.isIso_fst_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.fst := by
  refine ⟨⟨PullbackCone.IsLimit.lift ht (𝟙 _) (𝟙 _) (by simp), ?_, by simp⟩⟩
  apply PullbackCone.IsLimit.hom_ext ht
  · simp
  · simp [fst_eq_snd_of_mono_eq]

variable {f} in
lemma PullbackCone.isIso_snd_of_mono_of_isLimit {t : PullbackCone f f} (ht : IsLimit t) :
    IsIso t.snd :=
  t.fst_eq_snd_of_mono_eq ▸ t.isIso_fst_of_mono_of_isLimit ht

instance isIso_fst_of_mono : IsIso (pullback.fst f f) :=
  PullbackCone.isIso_fst_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit

instance isIso_snd_of_mono : IsIso (pullback.snd f f) :=
  PullbackCone.isIso_snd_of_mono_of_isLimit (getLimitCone (cospan f f)).isLimit
end

namespace PushoutCocone

variable {f : X ⟶ Y} {g : X ⟶ Z}

theorem epi_inr_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi f] :
    Epi t.inr :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht (by simp [← cancel_epi f, t.condition_assoc, i]) i⟩

theorem epi_inl_of_is_pushout_of_epi {t : PushoutCocone f g} (ht : IsColimit t) [Epi g] :
    Epi t.inl :=
  ⟨fun {W} h k i => IsColimit.hom_ext ht i (by simp [← cancel_epi g, ← t.condition_assoc, i])⟩

/--
The pushout cocone `(𝟙 X, 𝟙 X)` for the pair `(f, f)` is a colimit if `f` is an epi. The converse is
shown in `epi_of_isColimit_mk_id_id`.
-/
def isColimitMkIdId (f : X ⟶ Y) [Epi f] : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f) :=
  IsColimit.mk _ (fun s => s.inl) (fun _ => Category.id_comp _)
    (fun s => by rw [← cancel_epi f, Category.id_comp, s.condition]) fun s m m₁ _ => by
    simpa using m₁

/-- `f` is an epi if the pushout cocone `(𝟙 X, 𝟙 X)` is a colimit for the pair `(f, f)`.
The converse is given in `PushoutCocone.isColimitMkIdId`.
-/
theorem epi_of_isColimitMkIdId (f : X ⟶ Y)
    (t : IsColimit (mk (𝟙 Y) (𝟙 Y) rfl : PushoutCocone f f)) : Epi f :=
  ⟨fun {Z} g h eq => by
    rcases PushoutCocone.IsColimit.desc' t _ _ eq with ⟨_, rfl, rfl⟩
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Suppose `f` and `g` are two morphisms with a common domain and `s` is a colimit cocone over the
diagram formed by `f` and `g`. Suppose `f` and `g` both factor through an epimorphism `h` via
`x` and `y`, respectively. Then `s` is also a colimit cocone over the diagram formed by `x` and
`y`. -/
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
        apply PushoutCocone.IsColimit.hom_ext hs
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr]
          symm
          exact hs.fac _ WalkingSpan.left
        · simp only [PushoutCocone.mk_inl, PushoutCocone.mk_inr] at hr hr' ⊢
          simp only [hr']
          symm
          exact hs.fac _ WalkingSpan.right⟩⟩

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
  exact (PushoutCocone.IsColimit.hom_ext H (hm₁.trans h₁.symm) (hm₂.trans h₂.symm) :)

end PushoutCocone

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inl_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi g] :
    Epi (pushout.inl f g) :=
  PushoutCocone.epi_inl_of_is_pushout_of_epi (colimit.isColimit _)

/-- The pushout of an epimorphism is an epimorphism -/
instance pushout.inr_of_epi {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} [HasPushout f g] [Epi f] :
    Epi (pushout.inr _ _ : Z ⟶ pushout f g) :=
  PushoutCocone.epi_inr_of_is_pushout_of_epi (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/-- The map `X ⨿ Y ⟶ X ⨿[Z] Y` is epi. -/
instance epi_coprod_to_pushout {C : Type*} [Category* C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)
    [HasPushout f g] [HasBinaryCoproduct Y Z] :
    Epi (coprod.desc (pushout.inl f g) (pushout.inr f g)) :=
  ⟨fun {W} i₁ i₂ h => by
    ext
    · simpa using congrArg (fun f => coprod.inl ≫ f) h
    · simpa using congrArg (fun f => coprod.inr ≫ f) h⟩

/-- The pushout of `f, g` is also the pullback of `h ≫ f, h ≫ g` for any epi `h`. -/
noncomputable def pushoutIsPushoutOfEpiComp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h]
    [HasPushout f g] : IsColimit (PushoutCocone.mk (pushout.inl f g) (pushout.inr f g)
    (show (h ≫ f) ≫ pushout.inl f g = (h ≫ g) ≫ pushout.inr f g from by
    simp only [Category.assoc]; rw [cancel_epi]; exact pushout.condition)) :=
  PushoutCocone.isColimitOfEpiComp f g h _ (colimit.isColimit (span f g))

instance hasPushout_of_epi_comp (f : X ⟶ Y) (g : X ⟶ Z) (h : W ⟶ X) [Epi h] [HasPushout f g] :
    HasPushout (h ≫ f) (h ≫ g) :=
  ⟨⟨⟨_, pushoutIsPushoutOfEpiComp f g h⟩⟩⟩

section

attribute [local instance] hasPushout_of_left_iso

variable (f : X ⟶ Z) (h : W ⟶ X) [Epi h]

instance hasPushout_of_right_factors_epi : HasPushout h (h ≫ f) := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp (𝟙 X) f h

set_option backward.isDefEq.respectTransparency false in
instance pushout_inr_iso_of_right_factors_epi :
    IsIso (pushout.inr _ _ : _ ⟶ pushout h (h ≫ f)) := by
  convert (congrArg IsIso (show pushout.inr _ _ ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp (𝟙 _) f h⟩ WalkingSpan.right)).mp
    inferInstance
  · apply (Category.comp_id _).symm
  · apply (Category.comp_id _).symm

attribute [local instance] hasPushout_of_right_iso

instance hasPushout_of_left_factors_epi (f : X ⟶ Y) : HasPushout (h ≫ f) h := by
  simpa only [Category.comp_id] using hasPushout_of_epi_comp f (𝟙 X) h

set_option backward.isDefEq.respectTransparency false in
instance pushout_inl_iso_of_left_factors_epi (f : X ⟶ Y) :
    IsIso (pushout.inl _ _ : _ ⟶ pushout (h ≫ f) h) := by
  convert (congrArg IsIso (show pushout.inl _ _ ≫ _ = _ from colimit.isoColimitCocone_ι_inv
    ⟨_, pushoutIsPushoutOfEpiComp f (𝟙 _) h⟩ WalkingSpan.left)).mp
        inferInstance
  · exact (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

end

section

open WalkingSpan

variable (f : X ⟶ Y) [Epi f]

instance has_cokernel_pair_of_epi : HasPushout f f :=
  ⟨⟨⟨_, PushoutCocone.isColimitMkIdId f⟩⟩⟩

theorem PushoutCocone.inl_eq_inr_of_epi_eq {f : X ⟶ Y} [Epi f] (t : PushoutCocone f f) :
    t.inl = t.inr :=
  (cancel_epi f).1 t.condition

theorem inl_eq_inr_of_epi_eq : pushout.inl f f = pushout.inr f f :=
  PushoutCocone.inl_eq_inr_of_epi_eq (getColimitCocone (span f f)).cocone

@[simp]
theorem pullback_symmetry_hom_of_epi_eq : (pushoutSymmetry f f).hom = 𝟙 _ := by
  ext <;> simp [inl_eq_inr_of_epi_eq]

variable {f} in
lemma PushoutCocone.isIso_inl_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inl := by
  refine ⟨⟨PushoutCocone.IsColimit.desc ht (𝟙 _) (𝟙 _) (by simp), by simp, ?_⟩⟩
  apply PushoutCocone.IsColimit.hom_ext ht
  · simp
  · simp [inl_eq_inr_of_epi_eq]

variable {f} in
lemma PushoutCocone.isIso_inr_of_epi_of_isColimit {t : PushoutCocone f f} (ht : IsColimit t) :
    IsIso t.inr :=
  t.inl_eq_inr_of_epi_eq ▸ t.isIso_inl_of_epi_of_isColimit ht

instance isIso_inl_of_epi : IsIso (pushout.inl f f) :=
  PushoutCocone.isIso_inl_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

instance isIso_inr_of_epi : IsIso (pushout.inr f f) :=
  PushoutCocone.isIso_inr_of_epi_of_isColimit (getColimitCocone (span f f)).isColimit

end

end CategoryTheory.Limits
