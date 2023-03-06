/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.shapes.regular_mono
! leanprover-community/mathlib commit 239d882c4fb58361ee8b3b39fb2091320edef10a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

We give the constructions
* `is_split_mono → regular_mono` and
* `regular_mono → mono`
as well as the dual constructions for regular epimorphisms. Additionally, we give the construction
* `regular_epi ⟶ strong_epi`.

We also define classes `regular_mono_category` and `regular_epi_category` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`strong_mono_category`s resp. `strong_epi_category`s.

-/


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class RegularMono (f : X ⟶ Y) where
  z : C
  (left right : Y ⟶ Z)
  w : f ≫ left = f ≫ right
  IsLimit : IsLimit (Fork.ofι f w)
#align category_theory.regular_mono CategoryTheory.RegularMono

attribute [reassoc.1] regular_mono.w

/-- Every regular monomorphism is a monomorphism. -/
instance (priority := 100) RegularMono.mono (f : X ⟶ Y) [RegularMono f] : Mono f :=
  mono_of_isLimit_fork RegularMono.isLimit
#align category_theory.regular_mono.mono CategoryTheory.RegularMono.mono

instance equalizerRegular (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    RegularMono (equalizer.ι g h) where
  z := Y
  left := g
  right := h
  w := equalizer.condition g h
  IsLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w =>
      by
      ext1
      simp [← w]
#align category_theory.equalizer_regular CategoryTheory.equalizerRegular

/-- Every split monomorphism is a regular monomorphism. -/
instance (priority := 100) RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] : RegularMono f
    where
  z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  w := by tidy
  IsLimit := isSplitMonoEqualizes f
#align category_theory.regular_mono.of_is_split_mono CategoryTheory.RegularMono.ofIsSplitMono

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `regular_mono.left` and
    `regular_mono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def RegularMono.lift' {W : C} (f : X ⟶ Y) [RegularMono f] (k : W ⟶ Y)
    (h : k ≫ (RegularMono.left : Y ⟶ @RegularMono.z _ _ _ _ f _) = k ≫ RegularMono.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' RegularMono.isLimit _ h
#align category_theory.regular_mono.lift' CategoryTheory.RegularMono.lift'

/-- The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `pullback.snd_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_fst_of_regular` for the flipped version.
-/
def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hr : RegularMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono g where
  z := hr.z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by rw [← reassoc_of comm, ← reassoc_of comm, hr.w]
  IsLimit := by
    apply fork.is_limit.mk' _ _
    intro s
    have l₁ : (fork.ι s ≫ k) ≫ regular_mono.left = (fork.ι s ≫ k) ≫ regular_mono.right
    rw [category.assoc, s.condition, category.assoc]
    obtain ⟨l, hl⟩ := fork.is_limit.lift' hr.is_limit _ l₁
    obtain ⟨p, hp₁, hp₂⟩ := pullback_cone.is_limit.lift' t _ _ hl
    refine' ⟨p, hp₂, _⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    apply (pullback_cone.mk f g comm).equalizer_ext
    · erw [← cancel_mono h, category.assoc, category.assoc, comm, reassoc_of z]
    · exact z
#align category_theory.regular_of_is_pullback_snd_of_regular CategoryTheory.regularOfIsPullbackSndOfRegular

/-- The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `pullback.fst_of_mono` for the basic monomorphism version, and
`regular_of_is_pullback_snd_of_regular` for the flipped version.
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hr : RegularMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular comm.symm (PullbackCone.flipIsLimit t)
#align category_theory.regular_of_is_pullback_fst_of_regular CategoryTheory.regularOfIsPullbackFstOfRegular

instance (priority := 100) strongMono_of_regularMono (f : X ⟶ Y) [RegularMono f] : StrongMono f :=
  StrongMono.mk'
    (by
      intro A B z hz u v sq
      have : v ≫ (regular_mono.left : Y ⟶ regular_mono.Z f) = v ≫ regular_mono.right :=
        by
        apply (cancel_epi z).1
        simp only [regular_mono.w, ← reassoc_of sq.w]
      obtain ⟨t, ht⟩ := regular_mono.lift' _ _ this
      refine' comm_sq.has_lift.mk' ⟨t, (cancel_mono f).1 _, ht⟩
      simp only [arrow.mk_hom, arrow.hom_mk'_left, category.assoc, ht, sq.w])
#align category_theory.strong_mono_of_regular_mono CategoryTheory.strongMono_of_regularMono

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) [RegularMono f] [e : Epi f] : IsIso f :=
  isIso_of_epi_of_strongMono _
#align category_theory.is_iso_of_regular_mono_of_epi CategoryTheory.isIso_of_regularMono_of_epi

section

variable (C)

/-- A regular mono category is a category in which every monomorphism is regular. -/
class RegularMonoCategory where
  regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], RegularMono f
#align category_theory.regular_mono_category CategoryTheory.RegularMonoCategory

end

/-- In a category in which every monomorphism is regular, we can express every monomorphism as
    an equalizer. This is not an instance because it would create an instance loop. -/
def regularMonoOfMono [RegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  RegularMonoCategory.regularMonoOfMono _
#align category_theory.regular_mono_of_mono CategoryTheory.regularMonoOfMono

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    RegularMonoCategory C
    where regularMonoOfMono _ _ f _ :=
    by
    haveI := is_split_mono_of_mono f
    infer_instance
#align category_theory.regular_mono_category_of_split_mono_category CategoryTheory.regularMonoCategoryOfSplitMonoCategory

instance (priority := 100) strongMonoCategory_of_regularMonoCategory [RegularMonoCategory C] :
    StrongMonoCategory C
    where strongMono_of_mono _ _ f _ :=
    by
    haveI := regular_mono_of_mono f
    infer_instance
#align category_theory.strong_mono_category_of_regular_mono_category CategoryTheory.strongMonoCategory_of_regularMonoCategory

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class RegularEpi (f : X ⟶ Y) where
  w : C
  (left right : W ⟶ X)
  w : left ≫ f = right ≫ f
  IsColimit : IsColimit (Cofork.ofπ f w)
#align category_theory.regular_epi CategoryTheory.RegularEpi

attribute [reassoc.1] regular_epi.w

/-- Every regular epimorphism is an epimorphism. -/
instance (priority := 100) RegularEpi.epi (f : X ⟶ Y) [RegularEpi f] : Epi f :=
  epi_of_isColimit_cofork RegularEpi.isColimit
#align category_theory.regular_epi.epi CategoryTheory.RegularEpi.epi

instance coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    RegularEpi (coequalizer.π g h) where
  w := X
  left := g
  right := h
  w := coequalizer.condition g h
  IsColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w =>
      by
      ext1
      simp [← w]
#align category_theory.coequalizer_regular CategoryTheory.coequalizerRegular

/-- Every split epimorphism is a regular epimorphism. -/
instance (priority := 100) RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f
    where
  w := X
  left := 𝟙 X
  right := f ≫ section_ f
  w := by tidy
  IsColimit := isSplitEpiCoequalizes f
#align category_theory.regular_epi.of_split_epi CategoryTheory.RegularEpi.ofSplitEpi

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `regular_epi.left` and
    `regular_epi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def RegularEpi.desc' {W : C} (f : X ⟶ Y) [RegularEpi f] (k : X ⟶ W)
    (h : (RegularEpi.left : RegularEpi.w f ⟶ X) ≫ k = RegularEpi.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' RegularEpi.isColimit _ h
#align category_theory.regular_epi.desc' CategoryTheory.RegularEpi.desc'

/-- The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `pushout.snd_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_fst_of_regular` for the flipped version.
-/
def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gr : RegularEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi h where
  w := gr.w
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [category.assoc, category.assoc, comm, reassoc_of gr.w]
  IsColimit := by
    apply cofork.is_colimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π
    rw [← category.assoc, ← category.assoc, s.condition]
    obtain ⟨l, hl⟩ := cofork.is_colimit.desc' gr.is_colimit (f ≫ cofork.π s) l₁
    obtain ⟨p, hp₁, hp₂⟩ := pushout_cocone.is_colimit.desc' t _ _ hl.symm
    refine' ⟨p, hp₁, _⟩
    intro m w
    have z := w.trans hp₁.symm
    apply t.hom_ext
    apply (pushout_cocone.mk _ _ comm).coequalizer_ext
    · exact z
    · erw [← cancel_epi g, ← reassoc_of comm, ← reassoc_of comm, z]
      rfl
#align category_theory.regular_of_is_pushout_snd_of_regular CategoryTheory.regularOfIsPushoutSndOfRegular

/-- The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `pushout.fst_of_epi` for the basic epimorphism version, and
`regular_of_is_pushout_snd_of_regular` for the flipped version.
-/
def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [fr : RegularEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular comm.symm (PushoutCocone.flipIsColimit t)
#align category_theory.regular_of_is_pushout_fst_of_regular CategoryTheory.regularOfIsPushoutFstOfRegular

instance (priority := 100) strongEpi_of_regularEpi (f : X ⟶ Y) [RegularEpi f] : StrongEpi f :=
  StrongEpi.mk'
    (by
      intro A B z hz u v sq
      have : (regular_epi.left : regular_epi.W f ⟶ X) ≫ u = regular_epi.right ≫ u :=
        by
        apply (cancel_mono z).1
        simp only [category.assoc, sq.w, regular_epi.w_assoc]
      obtain ⟨t, ht⟩ := regular_epi.desc' f u this
      exact
        comm_sq.has_lift.mk'
          ⟨t, ht,
            (cancel_epi f).1
              (by simp only [← category.assoc, ht, ← sq.w, arrow.mk_hom, arrow.hom_mk'_right])⟩)
#align category_theory.strong_epi_of_regular_epi CategoryTheory.strongEpi_of_regularEpi

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) [RegularEpi f] [m : Mono f] : IsIso f :=
  isIso_of_mono_of_strongEpi _
#align category_theory.is_iso_of_regular_epi_of_mono CategoryTheory.isIso_of_regularEpi_of_mono

section

variable (C)

/-- A regular epi category is a category in which every epimorphism is regular. -/
class RegularEpiCategory where
  regularEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], RegularEpi f
#align category_theory.regular_epi_category CategoryTheory.RegularEpiCategory

end

/-- In a category in which every epimorphism is regular, we can express every epimorphism as
    a coequalizer. This is not an instance because it would create an instance loop. -/
def regularEpiOfEpi [RegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  RegularEpiCategory.regularEpiOfEpi _
#align category_theory.regular_epi_of_epi CategoryTheory.regularEpiOfEpi

instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    RegularEpiCategory C
    where regularEpiOfEpi _ _ f _ :=
    by
    haveI := is_split_epi_of_epi f
    infer_instance
#align category_theory.regular_epi_category_of_split_epi_category CategoryTheory.regularEpiCategoryOfSplitEpiCategory

instance (priority := 100) strongEpiCategory_of_regularEpiCategory [RegularEpiCategory C] :
    StrongEpiCategory C
    where strongEpi_of_epi _ _ f _ :=
    by
    haveI := regular_epi_of_epi f
    infer_instance
#align category_theory.strong_epi_category_of_regular_epi_category CategoryTheory.strongEpiCategory_of_regularEpiCategory

end CategoryTheory

