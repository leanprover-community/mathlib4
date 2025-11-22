/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Definitions and basic properties of regular monomorphisms and epimorphisms.

A regular monomorphism is a morphism that is the equalizer of some parallel pair.

In this file, we give the following definitions.
* `RegularMono f`, which is a class carrying the data that exhibits `f` as a regular monomorphism.
  That is, it carries a fork and data specifying `f` a the equalizer of that fork.
* `IsRegularMono f`, which is a proposition stating that `f` is a regular monomorphism. In
  particular, this doesn't carry any data.
and constructions
* `IsSplitMono f → RegularMono f` and
* `RegularMono f → Mono f`
as well as the dual definitions/constructions for regular epimorphisms.

Additionally, we give the constructions
* `RegularEpi f → EffectiveEpi f`, from which it can be deduced that regular epimorphisms are
  strong.
* `regularEpiOfEffectiveEpi`: constructs a `RegularEpi f` instance from `EffectiveEpi f` and
  `HasPullback f f`.


We also define classes `IsRegularMonoCategory` and `IsRegularEpiCategory` for categories in which
every monomorphism or epimorphism is regular, and deduce that these categories are
`StrongMonoCategory`s resp. `StrongEpiCategory`s.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {X Y : C}

/-- A regular monomorphism is a morphism which is the equalizer of some parallel pair. -/
class RegularMono (f : X ⟶ Y) where
  /-- An object in `C` -/
  Z : C
  /-- A map from the codomain of `f` to `Z` -/
  left : Y ⟶ Z
  /-- Another map from the codomain of `f` to `Z` -/
  right : Y ⟶ Z
  /-- `f` equalizes the two maps -/
  w : f ≫ left = f ≫ right := by cat_disch
  /-- `f` is the equalizer of the two maps -/
  isLimit : IsLimit (Fork.ofι f w)

attribute [reassoc] RegularMono.w

/-- Every regular monomorphism is a monomorphism. -/
instance (priority := 100) RegularMono.mono (f : X ⟶ Y) [RegularMono f] : Mono f :=
  mono_of_isLimit_fork RegularMono.isLimit

/-- Every isomorphism is a regular monomorphism. -/
def RegularMono.ofIso (e : X ≅ Y) : RegularMono e.hom where
  Z := Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ e.inv) (by simp) fun s m w ↦ by
    simp [← w]

/-- Regular monomorphisms are preserved by isomorphisms in the arrow category. -/
def RegularMono.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : RegularMono f] :
    RegularMono g where
  Z := h.Z
  left := e.inv.right ≫ h.left
  right := e.inv.right ≫ h.right
  w := by
    have := Arrow.mk_hom g ▸ Arrow.w_mk_right e.inv
    simp_rw [← reassoc_of% this, h.w]
  isLimit := Fork.isLimitOfIsos _ h.isLimit _
    (Arrow.rightFunc.mapIso e) (Iso.refl _) (Arrow.leftFunc.mapIso e)

/-- `IsRegularMono f` is the assertion that `f` is a regular monomorphism. -/
abbrev IsRegularMono {X Y : C} (f : X ⟶ Y) : Prop := Nonempty (RegularMono f)

variable (C) in
/-- The `MorphismProperty C` satisfied by regular monomorphisms in `C`. -/
def MorphismProperty.regularMono : MorphismProperty C := fun _ _ f => IsRegularMono f

@[simp]
theorem MorphismProperty.regularMono_iff (f : X ⟶ Y) :
    (MorphismProperty.regularMono C) f ↔ IsRegularMono f :=
  Iff.rfl

instance MorphismProperty.regularMono.containsIdentities :
    (MorphismProperty.regularMono C).ContainsIdentities where
  id_mem _ := ⟨RegularMono.ofIso <| Iso.refl _⟩

instance MorphismProperty.regularMono.respectsIso :
    (MorphismProperty.regularMono C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h ↦ ⟨.ofArrowIso e (h := h.some)⟩)

instance isRegularMono_of_regularMono (f : X ⟶ Y) [h : RegularMono f] : IsRegularMono f := ⟨h⟩

/-- Given `IsRegularMono f`, a choice of data for `RegularMono f`. -/
def regularMonoOfIsRegularMono (f : X ⟶ Y) [h : IsRegularMono f] :
    RegularMono f :=
  h.some

instance (priority := low) mono_of_isRegularMono (f : X ⟶ Y) [h : IsRegularMono f] : Mono f :=
  have := regularMonoOfIsRegularMono f
  RegularMono.mono f

instance equalizerRegular (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    RegularMono (equalizer.ι g h) where
  Z := Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]

/-- Every split monomorphism is a regular monomorphism. -/
instance (priority := 100) RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    RegularMono f where
  Z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `RegularMono.left` and
`RegularMono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def RegularMono.lift' {W : C} (f : X ⟶ Y) [RegularMono f] (k : W ⟶ Y)
    (h : k ≫ (RegularMono.left : Y ⟶ @RegularMono.Z _ _ _ _ f _) = k ≫ RegularMono.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' RegularMono.isLimit _ h

/-- The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `Pullback.sndOfMono` for the basic monomorphism version, and
`regularOfIsPullbackFstOfRegular` for the flipped version.
-/
def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [hr : RegularMono h] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono g where
  Z := hr.Z
  left := k ≫ hr.left
  right := k ≫ hr.right
  w := by
    repeat (rw [← Category.assoc, ← eq_whisker comm])
    simp only [Category.assoc, hr.w]
  isLimit := by
    apply Fork.IsLimit.mk' _ _
    intro s
    have l₁ : (Fork.ι s ≫ k) ≫ RegularMono.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Category.assoc, s.condition, Category.assoc]
    obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hr.isLimit _ l₁
    obtain ⟨p, _, hp₂⟩ := PullbackCone.IsLimit.lift' t _ _ hl
    refine ⟨p, hp₂, ?_⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    apply (PullbackCone.mk f g comm).equalizer_ext
    · simp only [PullbackCone.mk_π_app, ← cancel_mono h]
      grind [Fork.ι_ofι]
    · exact z

/-- The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `Pullback.fstOfMono` for the basic monomorphism version, and
`regularOfIsPullbackSndOfRegular` for the flipped version.
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [RegularMono k] (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular comm.symm (PullbackCone.flipIsLimit t)

instance (priority := 100) strongMono_of_regularMono (f : X ⟶ Y) [RegularMono f] : StrongMono f :=
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ (RegularMono.left : Y ⟶ RegularMono.Z f) = v ≫ RegularMono.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
      refine CommSq.HasLift.mk' ⟨t, (cancel_mono f).1 ?_, ht⟩
      simp only [Category.assoc, ht, sq.w])

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) [RegularMono f] [Epi f] : IsIso f :=
  isIso_of_epi_of_strongMono _

section

variable (C)

/-- A regular mono category is a category in which every monomorphism is regular. -/
class IsRegularMonoCategory : Prop where
  /-- Every monomorphism is a regular monomorphism -/
  regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsRegularMono f

end

/-- In a category in which every monomorphism is regular, we can express every monomorphism as
an equalizer. This is not an instance because it would create an instance loop. -/
def regularMonoOfMono [IsRegularMonoCategory C] (f : X ⟶ Y) [Mono f] : RegularMono f :=
  regularMonoOfIsRegularMono f (h := IsRegularMonoCategory.regularMonoOfMono f)

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ := by
    haveI := isSplitMono_of_mono f
    infer_instance

instance (priority := 100) strongMonoCategory_of_regularMonoCategory [IsRegularMonoCategory C] :
    StrongMonoCategory C where
  strongMono_of_mono f _ := by
    haveI := regularMonoOfMono f
    infer_instance

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
class RegularEpi (f : X ⟶ Y) where
  /-- An object from `C` -/
  W : C
  /-- Two maps to the domain of `f` -/
  (left right : W ⟶ X)
  /-- `f` coequalizes the two maps -/
  w : left ≫ f = right ≫ f := by cat_disch
  /-- `f` is the coequalizer -/
  isColimit : IsColimit (Cofork.ofπ f w)

attribute [reassoc] RegularEpi.w

/-- Every regular epimorphism is an epimorphism. -/
instance (priority := 100) RegularEpi.epi (f : X ⟶ Y) [RegularEpi f] : Epi f :=
  epi_of_isColimit_cofork RegularEpi.isColimit

/-- Every isomorphism is a regular epimorphism. -/
def RegularEpi.ofIso (e : X ≅ Y) : RegularEpi e.hom where
  W := X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s ↦ e.inv ≫ s.π) (by simp) fun s m w ↦ by
    simp [← w]

/-- Regular epimorphisms are preserved by isomorphisms in the arrow category. -/
def RegularEpi.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : RegularEpi f] :
    RegularEpi g where
  W := h.W
  left := h.left ≫ e.hom.left
  right := h.right ≫ e.hom.left
  w := by
    simp only [Category.assoc, Arrow.w_mk_right, Arrow.mk_hom]
    rw [reassoc_of% h.w]
  isColimit := Cofork.isColimitOfIsos _ h.isColimit _
    (Iso.refl _) (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)

/-- `IsRegularEpi f` is the assertion that `f` is a regular epimorphism. -/
abbrev IsRegularEpi {X Y : C} (f : X ⟶ Y) : Prop := Nonempty (RegularEpi f)

variable (C) in
/-- The `MorphismProperty C` satisfied by regular epimorphisms in `C`. -/
def MorphismProperty.regularEpi : MorphismProperty C := fun _ _ f => IsRegularEpi f

@[simp]
theorem MorphismProperty.regularEpi_iff (f : X ⟶ Y) :
    (MorphismProperty.regularEpi C) f ↔ IsRegularEpi f :=
  Iff.rfl

instance MorphismProperty.regularEpi.containsIdentities :
    (MorphismProperty.regularEpi C).ContainsIdentities where
  id_mem _ := ⟨RegularEpi.ofIso <| Iso.refl _⟩

instance MorphismProperty.regularEpi.respectsIso :
    (MorphismProperty.regularEpi C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h ↦ ⟨.ofArrowIso e (h := h.some)⟩)

instance isRegularEpi_of_regularEpi (f : X ⟶ Y) [h : RegularEpi f] : IsRegularEpi f := ⟨h⟩

/-- Given `IsRegularEpi f`, a choice of data for `RegularEpi f`. -/
def regularEpiOfIsRegularEpi (f : X ⟶ Y) [h : IsRegularEpi f] :
    RegularEpi f :=
  h.some

instance (priority := low) epi_of_isRegularEpi (f : X ⟶ Y) [h : IsRegularEpi f] : Epi f :=
  have := regularEpiOfIsRegularEpi f
  RegularEpi.epi f

instance coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
    RegularEpi (coequalizer.π g h) where
  W := X
  left := g
  right := h
  w := coequalizer.condition g h
  isColimit :=
    Cofork.IsColimit.mk _ (fun s => colimit.desc _ s) (by simp) fun s m w => by
      apply coequalizer.hom_ext
      simp [← w]

/-- A morphism which is a coequalizer for its kernel pair is a regular epi. -/
noncomputable def regularEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := hc

/-- The data of an `EffectiveEpi` structure on a `RegularEpi`. -/
def effectiveEpiStructOfRegularEpi {B X : C} (f : X ⟶ B) [RegularEpi f] :
    EffectiveEpiStruct f where
  desc _ h := Cofork.IsColimit.desc RegularEpi.isColimit _ (h _ _ RegularEpi.w)
  fac _ _ := Cofork.IsColimit.π_desc' RegularEpi.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext RegularEpi.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

instance {B X : C} (f : X ⟶ B) [RegularEpi f] : EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfRegularEpi f⟩⟩

/-- A morphism which is a coequalizer for its kernel pair is an effective epi. -/
theorem effectiveEpi_of_kernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f :=
  let _ := regularEpiOfKernelPair f hc
  inferInstance

@[deprecated (since := "2025-11-20")] alias effectiveEpiOfKernelPair := effectiveEpi_of_kernelPair

/-- An effective epi which has a kernel pair is a regular epi. -/
noncomputable instance regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := {
    desc := fun s ↦ EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← pullback.lift_snd g₁ g₂ hg, Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
      simp)
    fac := by
      intro s j
      have := EffectiveEpi.fac f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
          simp only [Cofork.app_one_eq_π]
          rw [← pullback.lift_snd g₁ g₂ hg, Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
          simp)
      simp only [Functor.const_obj_obj, Cofork.app_one_eq_π] at this
      cases j with
      | zero => simp [this]
      | one => simp [this]
    uniq := fun _ _ h ↦ EffectiveEpi.uniq f _ _ _ (h WalkingParallelPair.one) }

/-- Every split epimorphism is a regular epimorphism. -/
instance (priority := 100) RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f where
  W := X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `RegularEpi.left` and
`RegularEpi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def RegularEpi.desc' {W : C} (f : X ⟶ Y) [RegularEpi f] (k : X ⟶ W)
    (h : (RegularEpi.left : RegularEpi.W f ⟶ X) ≫ k = RegularEpi.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' RegularEpi.isColimit _ h

/-- The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `Pushout.sndOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutFstOfRegular` for the flipped version.
-/
def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [gr : RegularEpi g] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi h where
  W := gr.W
  left := gr.left ≫ f
  right := gr.right ≫ f
  w := by rw [Category.assoc, Category.assoc, comm]; simp only [← Category.assoc, eq_whisker gr.w]
  isColimit := by
    apply Cofork.IsColimit.mk' _ _
    intro s
    have l₁ : gr.left ≫ f ≫ s.π = gr.right ≫ f ≫ s.π := by
      rw [← Category.assoc, ← Category.assoc, s.condition]
    obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' gr.isColimit (f ≫ Cofork.π s) l₁
    obtain ⟨p, hp₁, _⟩ := PushoutCocone.IsColimit.desc' t _ _ hl.symm
    refine ⟨p, hp₁, ?_⟩
    intro m w
    have z := w.trans hp₁.symm
    apply t.hom_ext
    apply (PushoutCocone.mk _ _ comm).coequalizer_ext
    · exact z
    · erw [← cancel_epi g, ← Category.assoc, ← eq_whisker comm]
      erw [← Category.assoc, ← eq_whisker comm]
      dsimp at z; simp only [Category.assoc, z]

/-- The first leg of a pushout cocone is a regular epimorphism if the left component is too.

See also `Pushout.fstOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutSndOfRegular` for the flipped version.
-/
def regularOfIsPushoutFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    [RegularEpi f] (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular comm.symm (PushoutCocone.flipIsColimit t)

@[deprecated "No replacement" (since := "2025-11-20")]
instance (priority := 100) strongEpi_of_regularEpi (f : X ⟶ Y) [RegularEpi f] : StrongEpi f :=
  inferInstance

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) [RegularEpi f] [Mono f] : IsIso f :=
  isIso_of_mono_of_strongEpi _

section

variable (C)

/-- A regular epi category is a category in which every epimorphism is regular. -/
class IsRegularEpiCategory : Prop where
  /-- Everyone epimorphism is a regular epimorphism -/
  regularEpiOfEpi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsRegularEpi f

end

/-- In a category in which every epimorphism is regular, we can express every epimorphism as
a coequalizer. This is not an instance because it would create an instance loop. -/
def regularEpiOfEpi [IsRegularEpiCategory C] (f : X ⟶ Y) [Epi f] : RegularEpi f :=
  regularEpiOfIsRegularEpi f (h := IsRegularEpiCategory.regularEpiOfEpi f)

instance (priority := 100) regularEpiCategoryOfSplitEpiCategory [SplitEpiCategory C] :
    IsRegularEpiCategory C where
  regularEpiOfEpi f _ := by
    haveI := isSplitEpi_of_epi f
    infer_instance

instance (priority := 100) strongEpiCategory_of_regularEpiCategory [IsRegularEpiCategory C] :
    StrongEpiCategory C where
  strongEpi_of_epi f _ := by
    haveI := regularEpiOfEpi f
    infer_instance

end CategoryTheory
