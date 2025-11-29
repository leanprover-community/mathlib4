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
structure RegularMono (f : X ⟶ Y) where
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
lemma RegularMono.mono {f : X ⟶ Y} (h : RegularMono f) : Mono f :=
  mono_of_isLimit_fork h.isLimit

/-- Every isomorphism is a regular monomorphism. -/
def RegularMono.ofIso (e : X ≅ Y) : RegularMono e.hom where
  Z := Y
  left := 𝟙 Y
  right := 𝟙 Y
  isLimit := Fork.IsLimit.mk _ (fun s ↦ s.ι ≫ e.inv) (by simp) fun s m w ↦ by simp [← w]

/-- Regular monomorphisms are preserved by isomorphisms in the arrow category. -/
def RegularMono.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : RegularMono f) :
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
class IsRegularMono {X Y : C} (f : X ⟶ Y) : Prop where
  regularMono : Nonempty (RegularMono f)

variable (C) in
/-- The `MorphismProperty C` satisfied by regular monomorphisms in `C`. -/
def MorphismProperty.regularMono : MorphismProperty C := fun _ _ f => IsRegularMono f

@[simp]
theorem MorphismProperty.regularMono_iff (f : X ⟶ Y) :
    (MorphismProperty.regularMono C) f ↔ IsRegularMono f :=
  Iff.rfl

instance MorphismProperty.regularMono.containsIdentities :
    (MorphismProperty.regularMono C).ContainsIdentities where
  id_mem _ := ⟨⟨RegularMono.ofIso <| Iso.refl _⟩⟩

instance MorphismProperty.regularMono.respectsIso :
    (MorphismProperty.regularMono C).RespectsIso :=
  RespectsIso.of_respects_arrow_iso _ (fun _ _ e h ↦ ⟨⟨.ofArrowIso e (h := h.regularMono.some)⟩⟩)

lemma isRegularMono_of_regularMono {f : X ⟶ Y} (h : RegularMono f) : IsRegularMono f := ⟨⟨h⟩⟩

/-- Given `IsRegularMono f`, a choice of data for `RegularMono f`. -/
noncomputable def IsRegularMono.get (f : X ⟶ Y) [IsRegularMono f] : RegularMono f :=
  IsRegularMono.regularMono.some

@[deprecated (since := "2025-11-27")] alias regularMonoOfIsRegularMono := IsRegularMono.get

noncomputable section IsRegularMono

variable {X Y : C} (f : X ⟶ Y) [IsRegularMono f]

def IsRegularMono.Z : C := (IsRegularMono.get f).Z

def IsRegularMono.left : Y ⟶ Z f := (IsRegularMono.get f).left

def IsRegularMono.right : Y ⟶ Z f := (IsRegularMono.get f).right

lemma IsRegularMono.w : f ≫ left f = f ≫ right f := (IsRegularMono.get f).w

def IsRegularMono.isLimit : IsLimit <| Fork.ofι _ (w f) := (IsRegularMono.get f).isLimit

def IsRegularMono.lift {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : W ⟶ X :=
  Fork.IsLimit.lift (isLimit f) k h

@[reassoc (attr := simp)]
lemma IsRegularMono.fac {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) : lift f k h ≫ f = k :=
  Fork.IsLimit.lift_ι (isLimit f)

lemma IsRegularMono.uniq {W : C} (f : X ⟶ Y) [IsRegularMono f] (k : W ⟶ Y)
    (h : k ≫ left f = k ≫ right f) (m : W ⟶ X) (hm : m ≫ f = k) : m = lift f k h :=
  Fork.IsLimit.existsUnique (isLimit f) k h |>.unique hm <| by simp


end IsRegularMono

/-- The chosen equalizer of a parallel pair is a regular monomorphism. -/
def RegularMono.equalizer (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    RegularMono (equalizer.ι g h) where
  Z := Y
  left := g
  right := h
  w := equalizer.condition g h
  isLimit :=
    Fork.IsLimit.mk _ (fun s => limit.lift _ s) (by simp) fun s m w => by
      apply equalizer.hom_ext
      simp [← w]

instance (g h : X ⟶ Y) [HasLimit (parallelPair g h)] :
    IsRegularMono (equalizer.ι g h) :=
  isRegularMono_of_regularMono <| RegularMono.equalizer g h

/-- Every split monomorphism is a regular monomorphism. -/
def RegularMono.ofIsSplitMono (f : X ⟶ Y) [IsSplitMono f] :
    RegularMono f where
  Z := Y
  left := 𝟙 Y
  right := retraction f ≫ f
  isLimit := isSplitMonoEqualizes f

instance (priority := 100) (f : X ⟶ Y) [IsSplitMono f] :
    IsRegularMono f :=
  isRegularMono_of_regularMono <| .ofIsSplitMono f

/-- If `f` is a regular mono, then any map `k : W ⟶ Y` equalizing `RegularMono.left` and
`RegularMono.right` induces a morphism `l : W ⟶ X` such that `l ≫ f = k`. -/
def RegularMono.lift' {W : C} {f : X ⟶ Y} (hf : RegularMono f) (k : W ⟶ Y)
    (h : k ≫ hf.left = k ≫ hf.right) :
    { l : W ⟶ X // l ≫ f = k } :=
  Fork.IsLimit.lift' hf.isLimit _ h

/-- The second leg of a pullback cone is a regular monomorphism if the right component is too.

See also `Pullback.sndOfMono` for the basic monomorphism version, and
`regularOfIsPullbackFstOfRegular` for the flipped version.
-/
def regularOfIsPullbackSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hr : RegularMono h) (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
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
    have l₁ : (Fork.ι s ≫ k) ≫ hr.left = (Fork.ι s ≫ k) ≫ hr.right := by
      rw [Category.assoc, s.condition, Category.assoc]
    obtain ⟨l, hl⟩ := Fork.IsLimit.lift' hr.isLimit _ l₁
    obtain ⟨p, _, hp₂⟩ := PullbackCone.IsLimit.lift' t _ _ hl
    refine ⟨p, hp₂, ?_⟩
    intro m w
    have z : m ≫ g = p ≫ g := w.trans hp₂.symm
    apply t.hom_ext
    have := hr.mono
    apply (PullbackCone.mk f g comm).equalizer_ext
    · simp only [PullbackCone.mk_π_app, ← cancel_mono h]
      grind [Fork.ι_ofι]
    · exact z

/-- The first leg of a pullback cone is a regular monomorphism if the left component is too.

See also `Pullback.fstOfMono` for the basic monomorphism version, and
`regularOfIsPullbackSndOfRegular` for the flipped version.
-/
def regularOfIsPullbackFstOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (hk : RegularMono k) (comm : f ≫ h = g ≫ k) (t : IsLimit (PullbackCone.mk _ _ comm)) :
    RegularMono f :=
  regularOfIsPullbackSndOfRegular hk comm.symm (PullbackCone.flipIsLimit t)

/-- Any regular monomorphism is a strong monomorphism. -/
lemma RegularMono.strongMono {f : X ⟶ Y} (h : RegularMono f) : StrongMono f :=
  have := h.mono
  StrongMono.mk' (by
      intro A B z hz u v sq
      have : v ≫ h.left = v ≫ h.right := by
        apply (cancel_epi z).1
        repeat (rw [← Category.assoc, ← eq_whisker sq.w])
        simp only [Category.assoc, RegularMono.w]
      obtain ⟨t, ht⟩ := RegularMono.lift' _ _ this
      refine CommSq.HasLift.mk' ⟨t, (cancel_mono f).1 ?_, ht⟩
      simp only [Category.assoc, ht, sq.w])

instance (priority := 100) (f : X ⟶ Y) [IsRegularMono f] : StrongMono f :=
  RegularMono.strongMono <| IsRegularMono.get f

/-- A regular monomorphism is an isomorphism if it is an epimorphism. -/
theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) (h : RegularMono f) [Epi f] : IsIso f :=
  have := RegularMono.strongMono h
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
  have := IsRegularMonoCategory.regularMonoOfMono f
  IsRegularMono.get f

instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
    IsRegularMonoCategory C where
  regularMonoOfMono f _ :=
    haveI := isSplitMono_of_mono f
    isRegularMono_of_regularMono <| RegularMono.ofIsSplitMono f

instance (priority := 100) strongMonoCategory_of_regularMonoCategory [IsRegularMonoCategory C] :
    StrongMonoCategory C where
  strongMono_of_mono f _ :=
    RegularMono.strongMono <| regularMonoOfMono f

/-- A regular epimorphism is a morphism which is the coequalizer of some parallel pair. -/
structure RegularEpi (f : X ⟶ Y) where
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
lemma RegularEpi.epi (f : X ⟶ Y) (h : RegularEpi f) : Epi f :=
  epi_of_isColimit_cofork h.isColimit

/-- Every isomorphism is a regular epimorphism. -/
def RegularEpi.ofIso (e : X ≅ Y) : RegularEpi e.hom where
  W := X
  left := 𝟙 X
  right := 𝟙 X
  isColimit := Cofork.IsColimit.mk _ (fun s ↦ e.inv ≫ s.π) (by simp) fun s m w ↦ by
    simp [← w]

/-- Regular epimorphisms are preserved by isomorphisms in the arrow category. -/
def RegularEpi.ofArrowIso {X'} {Y'} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) (h : RegularEpi f) :
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

lemma isRegularEpi_of_regularEpi {f : X ⟶ Y} (h : RegularEpi f) : IsRegularEpi f := ⟨h⟩

/-- Given `IsRegularEpi f`, a choice of data for `RegularEpi f`. -/
def regularEpiOfIsRegularEpi (f : X ⟶ Y) [h : IsRegularEpi f] :
    RegularEpi f :=
  h.some

/-- The chosen coequalizer of a parallel pair is a regular epimorphism. -/
def coequalizerRegular (g h : X ⟶ Y) [HasColimit (parallelPair g h)] :
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
def effectiveEpiStructOfRegularEpi {B X : C} {f : X ⟶ B} (hf : RegularEpi f) :
    EffectiveEpiStruct f where
  desc _ h := Cofork.IsColimit.desc hf.isColimit _ (h _ _ hf.w)
  fac _ _ := Cofork.IsColimit.π_desc' hf.isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext hf.isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

lemma RegularEpi.effectiveEpi {B X : C} {f : X ⟶ B} (h : RegularEpi f) : EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfRegularEpi h⟩⟩

instance (priority := 100) {B X : C} {f : X ⟶ B} [h : IsRegularEpi f] : EffectiveEpi f :=
  (regularEpiOfIsRegularEpi f).effectiveEpi

/-- A morphism which is a coequalizer for its kernel pair is an effective epi. -/
theorem effectiveEpi_of_kernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f :=
  RegularEpi.effectiveEpi <| regularEpiOfKernelPair f hc

@[deprecated (since := "2025-11-20")] alias effectiveEpiOfKernelPair := effectiveEpi_of_kernelPair

/--
Given a kernel pair of an effective epimorphism `f : X ⟶ B`, the induced cofork is a coequalizer.
-/
def isColimitCoforkOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f]
    (c : PullbackCone f f) (hc : IsLimit c) :
    IsColimit (Cofork.ofπ f c.condition) where
  desc s := EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg, Category.assoc,
        ← Cofork.app_zero_eq_comp_π_right]
      simp)
  fac s := by
    have := EffectiveEpi.fac f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← PullbackCone.IsLimit.lift_snd hc g₁ g₂ hg,
        Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
      simp)
    rintro (_ | _)
    all_goals simp_all
  uniq _ _ h := EffectiveEpi.uniq f _ _ _ (h WalkingParallelPair.one)

/-- An effective epi which has a kernel pair is a regular epi. -/
noncomputable def regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : RegularEpi f where
  W := pullback f f
  left := pullback.fst f f
  right := pullback.snd f f
  w := pullback.condition
  isColimit := isColimitCoforkOfEffectiveEpi f _ (pullback.isLimit _ _)

noncomputable instance isRegularEpi_of_EffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : IsRegularEpi f :=
  isRegularEpi_of_regularEpi <| regularEpiOfEffectiveEpi f

/-- Every split epimorphism is a regular epimorphism. -/
def RegularEpi.ofSplitEpi (f : X ⟶ Y) [IsSplitEpi f] : RegularEpi f where
  W := X
  left := 𝟙 X
  right := f ≫ section_ f
  isColimit := isSplitEpiCoequalizes f

instance (priority := 100) (f : X ⟶ Y) [IsSplitEpi f] : IsRegularEpi f :=
  isRegularEpi_of_regularEpi <| RegularEpi.ofSplitEpi f

/-- If `f` is a regular epi, then every morphism `k : X ⟶ W` coequalizing `RegularEpi.left` and
`RegularEpi.right` induces `l : Y ⟶ W` such that `f ≫ l = k`. -/
def RegularEpi.desc' {W : C} (f : X ⟶ Y) (hf : RegularEpi f) (k : X ⟶ W)
    (h : hf.left ≫ k = hf.right ≫ k) :
    { l : Y ⟶ W // f ≫ l = k } :=
  Cofork.IsColimit.desc' hf.isColimit _ h

/-- The second leg of a pushout cocone is a regular epimorphism if the right component is too.

See also `Pushout.sndOfEpi` for the basic epimorphism version, and
`regularOfIsPushoutFstOfRegular` for the flipped version.
-/
def regularOfIsPushoutSndOfRegular {P Q R S : C} {f : P ⟶ Q} {g : P ⟶ R} {h : Q ⟶ S} {k : R ⟶ S}
    (gr : RegularEpi g) (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
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
    have := gr.epi
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
    (hf : RegularEpi f) (comm : f ≫ h = g ≫ k) (t : IsColimit (PushoutCocone.mk _ _ comm)) :
    RegularEpi k :=
  regularOfIsPushoutSndOfRegular hf comm.symm (PushoutCocone.flipIsColimit t)

@[deprecated "No replacement" (since := "2025-11-20")]
lemma strongEpi_of_regularEpi (f : X ⟶ Y) (h : RegularEpi f) : StrongEpi f :=
  have := isRegularEpi_of_regularEpi h
  inferInstance

/-- A regular epimorphism is an isomorphism if it is a monomorphism. -/
theorem isIso_of_regularEpi_of_mono (f : X ⟶ Y) (h : RegularEpi f) [Mono f] : IsIso f :=
  have := isRegularEpi_of_regularEpi h
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
    haveI := isRegularEpi_of_regularEpi <| regularEpiOfEpi f
    infer_instance

end CategoryTheory
