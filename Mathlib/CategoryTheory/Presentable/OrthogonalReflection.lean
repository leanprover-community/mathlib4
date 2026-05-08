/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Localization.BousfieldTransfiniteComposition
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration

/-!
# The Orthogonal-reflection construction

Given `W : MorphismProperty C` (which should be small) and assuming the existence
of certain colimits in `C`, we construct a morphism `toSucc W Z : Z ⟶ succ W Z` for
any `Z : C`. This morphism belongs to `W.isLocal.isLocal` and
is an isomorphism iff `Z` belongs to `W.isLocal` (see the lemma `isIso_toSucc_iff`).
The morphism `toSucc W Z : Z ⟶ succ W Z` is defined as a composition
of two morphisms that are roughly described as follows:
* `toStep W Z : Z ⟶ step W Z`: for any morphism `f : X ⟶ Y` satisfying `W`
  and any morphism `X ⟶ Z`, we "attach" a morphism `Y ⟶ step W Z` (using
  coproducts and a pushout in essentially the same way as it is done in
  the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` for the small object
  argument);
* `fromStep W Z : step W Z ⟶ succ W Z`: this morphism coequalizes all pairs
  of morphisms `g₁ g₂ : Y ⟶ step W Z` such that there is a `f : X ⟶ Y`
  satisfying `W` such that `f ≫ g₁ = f ≫ g₂`.

The morphism `toSucc W Z : Z ⟶ succ W Z` is a variant of the (wrong) definition
p. 32 in the book by Adámek and Rosický. In this book, a slightly different object
than `succ W Z` is defined directly as a colimit of an intricate diagram, but
contrary to what is stated on p. 33, it does not satisfy `isIso_toSucc_iff`.
The author of this file was unable to understand the attempt of the authors
to fix this mistake in the errata to this book. This led to the definition
in two steps outlined above.

## Main results

The morphisms described above `toSucc W Z : Z ⟶ succ W Z` for all `Z : C` allow to
define `succStruct W Z₀ : SuccStruct C` for any `Z₀ : C`. By applying
a transfinite iteration to this `SuccStruct`, we obtain the following results
under the assumption that `W : MorphismProperty C` is a `w`-small property
of morphisms in a locally `κ`-presentable category `C` (with `κ : Cardinal.{w}`
a regular cardinal) such that the domains and codomains of the morphisms
satisfying `W` are `κ`-presentable:
* `MorphismProperty.isRightAdjoint_ι_isLocal`: existence of the left adjoint
  of the inclusion `W.isLocal ⥤ C`;
* `MorphismProperty.isLocallyPresentable_isLocal`: the full subcategory
  `W.isLocal` is locally presentable.

This is essentially the implication (i) → (ii) in Theorem 1.39 (and the corollary 1.40)
in the book by Adámek and Rosický (note that according to the
errata to this book, the implication (ii) → (i) is wrong when `κ = ℵ₀`).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe w v' u' v u

namespace CategoryTheory

open Limits Localization Opposite

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

set_option backward.isDefEq.respectTransparency false in
lemma MorphismProperty.isClosedUnderColimitsOfShape_isLocal
    (J : Type u') [Category.{v'} J] [EssentiallySmall.{w} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := fun Z ⟨p⟩ X Y f hf ↦ by
    obtain ⟨_, _⟩ := hW f hf
    refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g₂
      dsimp at h ⊢
      obtain ⟨j₃, u, v, huv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit κ p.isColimit (f ≫ g₁) (f ≫ g₂)
          (by simpa)
      simp only [Category.assoc] at huv
      rw [← p.w u, ← p.w v, reassoc_of% ((p.prop_diag_obj j₃ _ hf).1 huv)]
    · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ p.isColimit g
      obtain ⟨g, rfl⟩ := (p.prop_diag_obj j _ hf).2 g
      exact ⟨g ≫ p.ι.app j, by simp⟩

lemma MorphismProperty.isCardinalAccessible_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits C κ]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
    W.isLocal.ι.IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := W.isClosedUnderColimitsOfShape_isLocal J κ hW
    infer_instance

namespace OrthogonalReflection

variable (Z : C)

/-- Given `W : MorphismProperty C` and `Z : C`, this is the index type
parametrising the data of a morphism `f : X ⟶ Y` satisfying `W`
and a morphism `X ⟶ Z`. -/
def D₁ : Type _ := Σ (f : W.toSet), f.1.left ⟶ Z

instance [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C] :
    Small.{w} (D₁ (W := W) (Z := Z)) := by
  dsimp [D₁]
  infer_instance

lemma D₁.hasCoproductsOfShape [MorphismProperty.IsSmall.{w} W]
    [LocallySmall.{w} C] [HasCoproducts.{w} C] :
    HasCoproductsOfShape (D₁ (W := W) (Z := Z)) C :=
  hasColimitsOfShape_of_equivalence
    (Discrete.equivalence (equivShrink.{w} _).symm)

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `X`. -/
def D₁.obj₁ (d : D₁ W Z) : C := d.1.1.left

variable {W Z} in
/-- If `d : D₁ W Z` corresponds to the data of `f : X ⟶ Y` satisfying `W` and
of a morphism `X ⟶ Z`, this is the object `Y`. -/
def D₁.obj₂ (d : D₁ W Z) : C := d.1.1.right

section

variable [HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]

/-- Considering all diagrams consisting of a morphism `f : X ⟶ Y` satisfying `W`
and of a morphism `d : X ⟶ Z`, this is the morphism from the coproduct of
all these `X` objects to `Z` given by these morphisms `d`. -/
noncomputable abbrev D₁.l : ∐ (obj₁ (W := W) (Z := Z)) ⟶ Z :=
  Sigma.desc (fun d ↦ d.2)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₁`. -/
noncomputable abbrev D₁.ιLeft {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    X ⟶ ∐ obj₁ (W := W) (Z := Z) :=
  Sigma.ι (obj₁ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_l {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.l W Z = g :=
  Sigma.ι_desc _ _

variable [HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]

/-- The coproduct of all the morphisms `f` indexed by all diagrams
consisting of a morphism `f : X ⟶ Y` satisfying `W` and of a morphism `d : X ⟶ Z`. -/
noncomputable abbrev D₁.t : ∐ (obj₁ (W := W) (Z := Z)) ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Limits.Sigma.map (fun d ↦ d.1.1.hom)

variable {W Z} in
/-- The inclusion of a summand in `∐ obj₂`. -/
noncomputable abbrev D₁.ιRight {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    Y ⟶ ∐ (obj₂ (W := W) (Z := Z)) :=
  Sigma.ι (obj₂ (W := W) (Z := Z)) ⟨⟨Arrow.mk f, hf⟩, g⟩

set_option backward.isDefEq.respectTransparency false in -- Needed below
variable {W Z} in
@[reassoc]
lemma D₁.ι_comp_t (d : D₁ W Z) :
    Sigma.ι _ d ≫ D₁.t W Z = d.1.1.hom ≫ Sigma.ι obj₂ d := by
  apply ι_colimMap

variable {W Z} in
@[reassoc]
lemma D₁.ιLeft_comp_t {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    D₁.ιLeft f hf g ≫ D₁.t W Z = f ≫ D₁.ιRight f hf g := by
  apply ι_colimMap

variable [HasPushouts C]

/-- The intermediate object in the definition of the morphism `toSucc W Z : Z ⟶ succ W Z`.
It is the pushout of the following square:
```lean
∐ D₁.obj₁ ⟶ ∐ D₁.obj₂
   |           |
   v           v
   Z      ⟶   step W Z
```
where the coproduct is taken over all the diagram consisting of a morphism `f : X ⟶ Y`
satisfying `W` and a morphism `X ⟶ Z`. The top map is the coproduct of all of these `f`.
-/
noncomputable abbrev step := pushout (D₁.t W Z) (D₁.l W Z)

/-- The canonical map from `Z` to the pushout of `D₁.t W Z` and `D₁.l W Z`. -/
noncomputable abbrev toStep : Z ⟶ step W Z := pushout.inr _ _

/-- The index type parametrising the data of two morphisms `g₁ g₂ : Y ⟶ step W Z`, and
a map `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
def D₂ : Type _ :=
  Σ (f : W.toSet),
    { pq : (f.1.right ⟶ step W Z) × (f.1.right ⟶ step W Z) // f.1.hom ≫ pq.1 = f.1.hom ≫ pq.2 }

/-- The shape of the multicoequalizer of all pairs of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
def D₂.multispanShape : MultispanShape where
  L := D₂ W Z
  R := Unit
  fst _ := .unit
  snd _ := .unit

section

variable [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]

instance : Small.{w} (D₂ (W := W) (Z := Z)) := by
  dsimp [D₂]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance : Small.{w} (D₂.multispanShape W Z).L := by dsimp; infer_instance

attribute [local instance] essentiallySmall_of_small_of_locallySmall in
lemma D₂.hasColimitsOfShape [HasColimitsOfSize.{w, w} C] :
    HasColimitsOfShape (WalkingMultispan (multispanShape W Z)) C :=
  hasColimitsOfShape_of_equivalence (equivSmallModel.{w} _).symm

end

/-- The diagram of the multicoequalizer of all pair of morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
@[simps]
noncomputable def D₂.multispanIndex : MultispanIndex (multispanShape W Z) C where
  left d := d.1.1.right
  right _ := step W Z
  fst d := d.2.1.1
  snd d := d.2.1.2

variable [HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The object `succ W Z` is the multicoequalizer of all pairs of morphisms
 `g₁ g₂ : Y ⟶ step W Z` with a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
noncomputable abbrev succ := multicoequalizer (D₂.multispanIndex W Z)

/-- The projection from `Z` to the multicoequalizer of all morphisms `g₁ g₂ : Y ⟶ step W Z` with
a `f : X ⟶ Y` satisfying `W` such that `f ≫ g₁ = f ≫ g₂`. -/
noncomputable abbrev fromStep : step W Z ⟶ succ W Z :=
  Multicoequalizer.π (D₂.multispanIndex W Z) .unit

variable {W Z} in
@[reassoc]
lemma D₂.condition {X Y : C} (f : X ⟶ Y) (hf : W f)
    {g₁ g₂ : Y ⟶ step W Z} (h : f ≫ g₁ = f ≫ g₂) :
      g₁ ≫ fromStep W Z = g₂ ≫ fromStep W Z :=
  Multicoequalizer.condition (D₂.multispanIndex W Z)
    ⟨⟨Arrow.mk f, hf⟩, ⟨g₁, g₂⟩, h⟩

/-- The morphism `Z ⟶ succ W Z`. -/
noncomputable abbrev toSucc : Z ⟶ succ W Z := toStep W Z ≫ fromStep W Z

variable {W Z} in
lemma toSucc_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f)
    (g₁ g₂ : Y ⟶ Z) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ toSucc W Z = g₂ ≫ toSucc W Z := by
  simpa using D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
    (by simp [reassoc_of% hg])

set_option backward.isDefEq.respectTransparency false in
variable {W Z} in
lemma toSucc_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) (g : X ⟶ Z) :
    ∃ (g' : Y ⟶ succ W Z), f ≫ g' = g ≫ toSucc W Z :=
  ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z, by
    simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isLocal_isLocal_toSucc :
    W.isLocal.isLocal (toSucc W Z) := by
  refine fun T hT ↦ ⟨fun φ₁ φ₂ h ↦ ?_, fun g ↦ ?_⟩
  · ext ⟨⟩
    simp only [Category.assoc] at h
    dsimp
    ext d
    · apply (hT d.1.1.hom d.1.2).1
      simp only [← D₁.ι_comp_t_assoc, pushout.condition_assoc, h]
    · exact h
  · choose f hf using fun (d : D₁ W Z) ↦ (hT d.1.1.hom d.1.2).2 (d.2 ≫ g)
    exact ⟨Multicoequalizer.desc _ _ (fun ⟨⟩ ↦ pushout.desc (Sigma.desc f) g)
      (fun d ↦ (hT d.1.1.hom d.1.2).1 (by simp [reassoc_of% d.2.2])), by simp⟩

@[deprecated (since := "2025-11-20")] alias leftBousfieldW_isLocal_toSucc :=
  isLocal_isLocal_toSucc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isIso_toSucc_iff :
    IsIso (toSucc W Z) ↔ W.isLocal Z := by
  refine ⟨fun _ X Y f hf ↦ ?_, fun hZ ↦ ?_⟩
  · refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
    · simpa [← cancel_mono (toSucc W Z)] using
        D₂.condition f hf (g₁ := g₁ ≫ toStep W Z) (g₂ := g₂ ≫ toStep W Z)
          (by simp [reassoc_of% h])
    · have hZ := IsIso.hom_inv_id (toSucc W Z)
      simp only [Category.assoc] at hZ
      exact ⟨D₁.ιRight f hf g ≫ pushout.inl _ _ ≫ fromStep W Z ≫ inv (toSucc W Z),
        by simp [← D₁.ιLeft_comp_t_assoc, pushout.condition_assoc, hZ]⟩
  · obtain ⟨f, hf⟩ := (isLocal_isLocal_toSucc W Z _ hZ).2 (𝟙 _)
    dsimp at hf
    refine ⟨f, hf, ?_⟩
    ext ⟨⟩
    dsimp
    ext d
    · simp only [Category.assoc] at hf
      simp only [Category.comp_id, ← Category.assoc]
      refine D₂.condition _ d.1.2 ?_
      rw [Category.assoc, Category.assoc, Category.assoc,
        ← D₁.ι_comp_t_assoc, pushout.condition_assoc, reassoc_of% hf,
        ← D₁.ι_comp_t_assoc, pushout.condition]
    · simp [reassoc_of% hf]

end

open SmallObject

variable [HasPushouts C]
  [∀ Z, HasCoproduct (D₁.obj₁ (W := W) (Z := Z))]
  [∀ Z, HasCoproduct (D₁.obj₂ (W := W) (Z := Z))]
  [∀ Z, HasMulticoequalizer (D₂.multispanIndex W Z)]

/-- The successor structure of the orthogonal-reflection construction. -/
noncomputable def succStruct (Z₀ : C) : SuccStruct C where
  X₀ := Z₀
  succ Z := succ W Z
  toSucc Z := toSucc W Z

variable (κ : Cardinal.{w}) [OrderBot κ.ord.ToType]
  [HasIterationOfShape κ.ord.ToType C]

/-- The transfinite iteration of `succStruct W Z` to the power `κ.ord.ToType`. -/
noncomputable def reflectionObj : C := (succStruct W Z).iteration κ.ord.ToType

/-- The map which shall exhibit `reflectionObj W Z κ` as the image of `Z` by
the left adjoint of the inclusion of `W.isLocal`, see `corepresentableBy`. -/
noncomputable def reflection : Z ⟶ reflectionObj W Z κ :=
  (succStruct W Z).ιIteration κ.ord.ToType

/-- The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` is a transfinite
compositions of morphisms in `LeftBousfield.W W.isLocal`. -/
noncomputable def transfiniteCompositionOfShapeReflection :
    W.isLocal.isLocal.TransfiniteCompositionOfShape κ.ord.ToType
      (reflection W Z κ) :=
  ((succStruct W Z).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE (by
    rintro Z₀ _ _ ⟨_⟩
    exact isLocal_isLocal_toSucc W Z₀)

/-- The functor `κ.ord.ToType ⥤ C` that is the diagram of the
transfinite composition `transfiniteCompositionOfShapeReflection`. -/
noncomputable abbrev iteration : κ.ord.ToType ⥤ C :=
  (transfiniteCompositionOfShapeReflection W Z κ).F

section

variable [Fact κ.IsRegular]

/-- `(iteration W Z κ).obj (Order.succ j)` identifies to the image of
`(iteration W Z κ).obj j` by `succ`. -/
noncomputable def iterationObjSuccIso (j : κ.ord.ToType) :
  (iteration W Z κ).obj (Order.succ j) ≅ succ W ((iteration W Z κ).obj j) :=
    (succStruct W Z).iterationFunctorObjSuccIso j (by
      have := Cardinal.noMaxOrder (Fact.elim inferInstance : κ.IsRegular).aleph0_le
      exact not_isMax j)

@[reassoc]
lemma iteration_map_succ (j : κ.ord.ToType) :
    (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      toSucc W _ ≫ (iterationObjSuccIso W Z κ j).inv :=
  (succStruct W Z).iterationFunctor_map_succ _ _

variable {κ W Z} in
lemma iteration_map_succ_injectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g₁ g₂ : Y ⟶ (iteration W Z κ).obj j) (hg : f ≫ g₁ = f ≫ g₂) :
    g₁ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) =
      g₂ ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp [iteration_map_succ, reassoc_of% (toSucc_injectivity f hf _ _ hg)]

variable {κ W Z} in
lemma iteration_map_succ_surjectivity {X Y : C} (f : X ⟶ Y) (hf : W f) {j : κ.ord.ToType}
    (g : X ⟶ (iteration W Z κ).obj j) :
    ∃ (g' : Y ⟶ (iteration W Z κ).obj (Order.succ j)),
      f ≫ g' = g ≫ (iteration W Z κ).map (homOfLE (Order.le_succ j)) := by
  simp only [iteration_map_succ]
  obtain ⟨g', hg'⟩ := toSucc_surjectivity f hf g
  exact ⟨g' ≫ (iterationObjSuccIso W Z κ j).inv, by simp [reassoc_of% hg']⟩

end

lemma isLocal_isLocal_reflection :
     W.isLocal.isLocal (reflection W Z κ) :=
  W.isLocal.isLocal.transfiniteCompositionsOfShape_le κ.ord.ToType _
    ⟨transfiniteCompositionOfShapeReflection W Z κ⟩

variable {W} {κ} [Fact κ.IsRegular]
  (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)

include hW

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isLocal_reflectionObj :
    W.isLocal (reflectionObj W Z κ) := by
  let H := transfiniteCompositionOfShapeReflection W Z κ
  intro X Y f hf
  obtain ⟨_, _⟩ := hW f hf
  refine ⟨fun g₁ g₂ h ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨j, g₁, g₂, rfl, rfl⟩ :
      ∃ (j : κ.ord.ToType) (g₁' g₂' : Y ⟶ H.F.obj j), g₁' ≫ H.incl.app j = g₁ ∧
        g₂' ≫ H.incl.app j = g₂ := by
      obtain ⟨j₁, g₁, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₁
      obtain ⟨j₂, g₂, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g₂
      exact ⟨max j₁ j₂, g₁ ≫ H.F.map (homOfLE (le_max_left _ _)),
        g₂ ≫ H.F.map (homOfLE (le_max_right _ _)), by simp⟩
    dsimp at h
    obtain ⟨k, u, hk⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ H.isColimit
      (f ≫ g₁) (f ≫ g₂) (by simpa)
    have hg := iteration_map_succ_injectivity f hf
      (g₁ ≫ H.F.map u) (g₂ ≫ H.F.map u) (by simpa using hk)
    simp only [homOfLE_leOfHom, Category.assoc] at hg
    have := H.incl.naturality (u ≫ homOfLE (Order.le_succ k))
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    simp only [← this, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hg]
  · obtain ⟨j, g, rfl⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ H.isColimit g
    obtain ⟨g', hg'⟩ := iteration_map_succ_surjectivity f hf g
    exact ⟨g' ≫ H.incl.app (Order.succ j), by simp [reassoc_of% hg']⟩

set_option backward.isDefEq.respectTransparency false in
/-- The morphism `reflection W Z κ : Z ⟶ reflectionObj W Z κ` exhibits `reflectionObj W Z κ`
as the image of `Z` by the left adjoint of the inclusion `W.isLocal.ι`. -/
noncomputable def corepresentableBy :
  (W.isLocal.ι ⋙ coyoneda.obj (op Z)).CorepresentableBy
    ⟨_, isLocal_reflectionObj Z hW⟩ where
  homEquiv {A} :=
    (ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Equiv.ofBijective _ (isLocal_isLocal_reflection W Z κ _ A.2))

variable (W κ)

lemma isRightAdjoint_ι :
    W.isLocal.ι.IsRightAdjoint := by
  rw [Functor.isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top]
  ext Z
  simpa using (corepresentableBy Z hW).isCorepresentable

end OrthogonalReflection

namespace MorphismProperty

open OrthogonalReflection in
lemma isRightAdjoint_ι_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [MorphismProperty.IsSmall.{w} W] [LocallySmall.{w} C]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ)
    [HasColimitsOfSize.{w, w} C] :
    W.isLocal.ι.IsRightAdjoint := by
  have : Nonempty κ.ord.ToType := by simpa using Cardinal.IsRegular.ne_zero Fact.out
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  have := D₁.hasCoproductsOfShape.{w} W
  have := D₂.hasColimitsOfShape.{w} W
  exact isRightAdjoint_ι W κ hW

lemma isLocallyPresentable_isLocal
    (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable C κ]
    [MorphismProperty.IsSmall.{w} W]
    (hW : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f → IsCardinalPresentable X κ ∧ IsCardinalPresentable Y κ) :
  IsCardinalLocallyPresentable W.isLocal.FullSubcategory κ := by
    have := isRightAdjoint_ι_isLocal W κ hW
    have := MorphismProperty.isCardinalAccessible_ι_isLocal W κ hW
    exact (Adjunction.ofIsRightAdjoint W.isLocal.ι).isCardinalLocallyPresentable κ

end MorphismProperty

end CategoryTheory
