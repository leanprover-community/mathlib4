/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Unit

#align_import category_theory.limits.comma from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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
  (Cones.postcompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (L.mapCone c₁)
#align category_theory.comma.limit_auxiliary_cone CategoryTheory.Comma.limitAuxiliaryCone

/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
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
#align category_theory.comma.cone_of_preserves CategoryTheory.Comma.coneOfPreserves

/-- Provided that `R` preserves the appropriate limit, then the cone in `coneOfPreserves` is a
limit. -/
def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
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
#align category_theory.comma.cone_of_preserves_is_limit CategoryTheory.Comma.coneOfPreservesIsLimit

/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps!]
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocones.precompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (R.mapCocone c₂)
#align category_theory.comma.colimit_auxiliary_cocone CategoryTheory.Comma.colimitAuxiliaryCocone

/--
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
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
#align category_theory.comma.cocone_of_preserves CategoryTheory.Comma.coconeOfPreserves

/-- Provided that `L` preserves the appropriate colimit, then the cocone in `coconeOfPreserves` is
a colimit. -/
def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
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
#align category_theory.comma.cocone_of_preserves_is_colimit CategoryTheory.Comma.coconeOfPreservesIsColimit

instance hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩
#align category_theory.comma.has_limit CategoryTheory.Comma.hasLimit

instance hasLimitsOfShape [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : HasLimitsOfShape J (Comma L R) where
#align category_theory.comma.has_limits_of_shape CategoryTheory.Comma.hasLimitsOfShape

instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [HasLimitsOfSize.{w, w'} B]
    [PreservesLimitsOfSize.{w, w'} R] : HasLimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩
#align category_theory.comma.has_limits CategoryTheory.Comma.hasLimitsOfSize

instance hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩
#align category_theory.comma.has_colimit CategoryTheory.Comma.hasColimit

instance hasColimitsOfShape [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : HasColimitsOfShape J (Comma L R) where
#align category_theory.comma.has_colimits_of_shape CategoryTheory.Comma.hasColimitsOfShape

instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [HasColimitsOfSize.{w, w'} B]
    [PreservesColimitsOfSize.{w, w'} L] : HasColimitsOfSize.{w, w'} (Comma L R) :=
  ⟨fun _ _ => inferInstance⟩
#align category_theory.comma.has_colimits CategoryTheory.Comma.hasColimitsOfSize

end Comma

namespace Arrow

instance hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)] :
    HasLimit F := by
  haveI : HasLimit (F ⋙ Comma.fst _ _) := i₁
  haveI : HasLimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasLimit
#align category_theory.arrow.has_limit CategoryTheory.Arrow.hasLimit

instance hasLimitsOfShape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where
#align category_theory.arrow.has_limits_of_shape CategoryTheory.Arrow.hasLimitsOfShape

instance hasLimits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩
#align category_theory.arrow.has_limits CategoryTheory.Arrow.hasLimits

instance hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
    [i₂ : HasColimit (F ⋙ rightFunc)] : HasColimit F := by
  haveI : HasColimit (F ⋙ Comma.fst _ _) := i₁
  haveI : HasColimit (F ⋙ Comma.snd _ _) := i₂
  apply Comma.hasColimit
#align category_theory.arrow.has_colimit CategoryTheory.Arrow.hasColimit

instance hasColimitsOfShape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where
#align category_theory.arrow.has_colimits_of_shape CategoryTheory.Arrow.hasColimitsOfShape

instance hasColimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨fun _ _ => inferInstance⟩
#align category_theory.arrow.has_colimits CategoryTheory.Arrow.hasColimits

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

instance hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] :
    HasLimit F := by
  haveI : HasLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) := i₁
  haveI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) _ := i₂
  apply Comma.hasLimit
#align category_theory.structured_arrow.has_limit CategoryTheory.StructuredArrow.hasLimit

instance hasLimitsOfShape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where
#align category_theory.structured_arrow.has_limits_of_shape CategoryTheory.StructuredArrow.hasLimitsOfShape

instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} A] [PreservesLimitsOfSize.{w, w'} G] :
    HasLimitsOfSize.{w, w'} (StructuredArrow X G) :=
  ⟨fun J hJ => by infer_instance⟩
#align category_theory.structured_arrow.has_limits CategoryTheory.StructuredArrow.hasLimitsOfSize

noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] :
    CreatesLimit F (proj X G) :=
  letI : PreservesLimit (F ⋙ Comma.snd (Functor.fromPUnit X) G) G := i
  createsLimitOfReflectsIso fun _ t =>
    { liftedCone := Comma.coneOfPreserves F punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cones.ext (Iso.refl _) fun _ => (id_comp _).symm }
#align category_theory.structured_arrow.creates_limit CategoryTheory.StructuredArrow.createsLimit

noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (proj X G) where
#align category_theory.structured_arrow.creates_limits_of_shape CategoryTheory.StructuredArrow.createsLimitsOfShape

noncomputable instance createsLimitsOfSize [PreservesLimitsOfSize.{w, w'} G] :
    CreatesLimitsOfSize.{w, w'} (proj X G : _) where
#align category_theory.structured_arrow.creates_limits CategoryTheory.StructuredArrow.createsLimitsOfSize

instance mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right :=
  show Mono ((proj X G).map f) from inferInstance
#align category_theory.structured_arrow.mono_right_of_mono CategoryTheory.StructuredArrow.mono_right_of_mono

theorem mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right :=
  ⟨fun _ => inferInstance, fun _ => mono_of_mono_right f⟩
#align category_theory.structured_arrow.mono_iff_mono_right CategoryTheory.StructuredArrow.mono_iff_mono_right

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

instance hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] :
    HasColimit F := by
  haveI : HasColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) := i₁
  haveI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) _ := i₂
  apply Comma.hasColimit
#align category_theory.costructured_arrow.has_colimit CategoryTheory.CostructuredArrow.hasColimit

instance hasColimitsOfShape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where
#align category_theory.costructured_arrow.has_colimits_of_shape CategoryTheory.CostructuredArrow.hasColimitsOfShape

instance hasColimitsOfSize [HasColimitsOfSize.{w, w'} A] [PreservesColimitsOfSize.{w, w'} G] :
    HasColimitsOfSize.{w, w'} (CostructuredArrow G X) :=
  ⟨fun _ _ => inferInstance⟩
#align category_theory.costructured_arrow.has_colimits CategoryTheory.CostructuredArrow.hasColimitsOfSize

noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] :
    CreatesColimit F (proj G X) :=
  letI : PreservesColimit (F ⋙ Comma.fst G (Functor.fromPUnit X)) G := i
  createsColimitOfReflectsIso fun _ t =>
    { liftedCocone := Comma.coconeOfPreserves F t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocones.ext (Iso.refl _) fun _ => comp_id _ }
#align category_theory.costructured_arrow.creates_colimit CategoryTheory.CostructuredArrow.createsColimit

noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] :
    CreatesColimitsOfShape J (proj G X) where
#align category_theory.costructured_arrow.creates_colimits_of_shape CategoryTheory.CostructuredArrow.createsColimitsOfShape

noncomputable instance createsColimitsOfSize [PreservesColimitsOfSize.{w, w'} G] :
    CreatesColimitsOfSize.{w, w'} (proj G X : _) where
#align category_theory.costructured_arrow.creates_colimits CategoryTheory.CostructuredArrow.createsColimitsOfSize

instance epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left :=
  show Epi ((proj G X).map f) from inferInstance
#align category_theory.costructured_arrow.epi_left_of_epi CategoryTheory.CostructuredArrow.epi_left_of_epi

theorem epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left :=
  ⟨fun _ => inferInstance, fun _ => epi_of_epi_left f⟩
#align category_theory.costructured_arrow.epi_iff_epi_left CategoryTheory.CostructuredArrow.epi_iff_epi_left

end CostructuredArrow

end CategoryTheory
