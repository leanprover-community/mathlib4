/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Unit

/-!
# Limits and colimits in comma categories

We build limits in the comma category `Comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/


namespace CategoryTheory

open Category Limits

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {J : Type w} [Category.{w'} J]
variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]

namespace Comma

variable {L : A ⥤ T} {R : B ⥤ T}
variable (F : J ⥤ Comma L R)

/-- (Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category. -/
@[simps!]
def limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R) :=
  (Cones.postcompose (whiskerLeft F (Comma.natTrans L R) :)).obj (L.mapCone c₁)

/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
noncomputable def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
    {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : Cone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

/-- Provided that `R` preserves the appropriate limit, then the cone in `coneOfPreserves` is a
limit. -/
noncomputable def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
    (t₁ : IsLimit c₁) {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) :
    IsLimit (coneOfPreserves F c₁ t₂) where
  lift s :=
    { left := t₁.lift ((fst L R).mapCone s)
      right := t₂.lift ((snd L R).mapCone s)
      w :=
        (isLimitOfPreserves R t₂).hom_ext fun j => by
          rw [coneOfPreserves_pt_hom, assoc, assoc, (isLimitOfPreserves R t₂).fac,
            limitAuxiliaryCone_π_app, ← L.map_comp_assoc, t₁.fac, R.mapCone_π_app,
            ← R.map_comp, t₂.fac]
          exact (s.π.app j).w }
  uniq s m w := by
    apply CommaMorphism.ext
    · exact t₁.uniq ((fst L R).mapCone s) _ (fun j => by simp [← w])
    · exact t₂.uniq ((snd L R).mapCone s) _ (fun j => by simp [← w])

/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps!]
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocones.precompose (whiskerLeft F (Comma.natTrans L R) :)).obj (R.mapCocone c₂)

/--
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
noncomputable def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) (c₂ : Cocone (F ⋙ snd L R)) : Cocone F where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality := fun j₁ j₂ t => by
        ext
        · simp [← c₁.w t]
        · simp [← c₂.w t] }

/-- Provided that `L` preserves the appropriate colimit, then the cocone in `coconeOfPreserves` is
a colimit. -/
noncomputable def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L]
    {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit c₂) :
    IsColimit (coconeOfPreserves F t₁ c₂) where
  desc s :=
    { left := t₁.desc ((fst L R).mapCocone s)
      right := t₂.desc ((snd L R).mapCocone s)
      w :=
        (isColimitOfPreserves L t₁).hom_ext fun j => by
          rw [coconeOfPreserves_pt_hom, (isColimitOfPreserves L t₁).fac_assoc,
            colimitAuxiliaryCocone_ι_app, assoc, ← R.map_comp, t₂.fac, L.mapCocone_ι_app, ←
            L.map_comp_assoc, t₁.fac]
          exact (s.ι.app j).w }
  uniq s m w := by
    apply CommaMorphism.ext
    · exact t₁.uniq ((fst L R).mapCocone s) _ (fun j => by simp [← w])
    · exact t₂.uniq ((snd L R).mapCocone s) _ (fun j => by simp [← w])

instance hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩

instance hasLimitsOfShape [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : HasLimitsOfShape J (Comma L R) where

instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
    [PreservesLimitsOfSize.{w, w'} R] : HasLimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩

instance hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩

instance hasColimitsOfShape [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : HasColimitsOfShape J (Comma L R) where

instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
    [PreservesColimitsOfSize.{w, w'} L] : HasColimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩

instance preservesColimitsOfShape_fst [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.fst L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

instance preservesColimitsOfShape_snd [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : PreservesColimitsOfShape J (Comma.snd L R) where
  preservesColimit :=
    preservesColimit_of_preserves_colimit_cocone
      (coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _))
      (colimit.isColimit _)

end Comma

namespace Arrow

instance hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)] :
    HasLimit F := by
  haveI : HasLimit (F ⋙ Comma.fst _ _) := i₁
  haveI : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit

instance hasLimitsOfShape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where

instance hasLimits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩

instance hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
    [i₂ : HasColimit (F ⋙ rightFunc)] : HasColimit F := by
  haveI : HasColimit (F ⋙ Comma.fst _ _) := i₁
  haveI : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit

instance hasColimitsOfShape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where

instance hasColimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩

instance preservesColimitsOfShape_leftFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.leftFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_fst

instance preservesColimitsOfShape_rightFunc [HasColimitsOfShape J T] :
    PreservesColimitsOfShape J (Arrow.rightFunc : _ ⥤ T) := by
  apply Comma.preservesColimitsOfShape_snd

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

instance hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] :
    HasLimit F := by
  haveI : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  haveI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit

instance hasLimitsOfShape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where

instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G] :
    HasLimitsOfSize.{w, w'} (StructuredArrow X G) :=
  ⟨fun J hJ => by infer_instance⟩

noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] :
    CreatesLimit F (proj X G) :=
  letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cones.ext (Iso.refl _) fun _ => (id_comp _).symm }

noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (proj X G) where

noncomputable instance createsLimitsOfSize [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (proj X G :) where

instance mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right :=
  show Mono ((proj X G).map f) from inferInstance

theorem mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right :=
  ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

instance hasTerminal [G.Faithful] [G.Full] {Y : A} :
    HasTerminal (CostructuredArrow G (G.obj Y)) :=
  CostructuredArrow.mkIdTerminal.hasTerminal

instance hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] :
    HasColimit F := by
  haveI : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  haveI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit

instance hasColimitsOfShape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where

instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G] :
    HasColimitsOfSize.{w, w'} (CostructuredArrow G X) :=
  ⟨fun _ _ => inferInstance⟩

noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] :
    CreatesColimit F (proj G X) :=
  letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocones.ext (Iso.refl _) fun _ => comp_id _ }

noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] :
    CreatesColimitsOfShape J (proj G X) where

noncomputable instance createsColimitsOfSize [PreservesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (proj G X :) where

instance epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left :=
  show Epi ((proj G X).map f) from inferInstance

theorem epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left :=
  ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩

end CostructuredArrow

namespace Over

instance {X : T} : HasTerminal (Over X) := CostructuredArrow.hasTerminal

end Over

end CategoryTheory
