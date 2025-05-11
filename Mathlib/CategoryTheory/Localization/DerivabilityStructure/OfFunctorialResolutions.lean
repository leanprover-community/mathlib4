/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# Functorial resolutions gives derivability structures

In this file, we provide a constructor for right derivability structures.
We assume that `Φ : LocalizerMorphism W₁ W₂` is given by
a fully faithful functor `Φ.functor : C₁ ⥤ C₂` and that we have a resolution
functor `ρ : C₂ ⥤ C₁` with a natural transformation `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`
such that `W₂ (i.app X₂)` for any `X₂ : C₂`. Moreover, if we assume
that `W₁` is induced by `W₂`, that `W₂` is multiplicative and has
the two out of three property, then `Φ` is a right derivability structure.

-/

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

section right

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor) (hi : ∀ X₂, W₂ (i.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hi in
lemma hasRightResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasRightResolutions :=
  fun f ↦ ⟨{
    X₁ := Arrow.mk (ρ.map f.hom)
    w := Arrow.homMk (i.app _) (i.app _) ((i.naturality f.hom).symm)
    hw := ⟨hi _, hi _⟩ }⟩

namespace functorialRightResolutions

variable {Φ i}

/-- If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
the inverse image of `W₂` by the functor `Φ.functor` and that we
have functorial right resolutions, then this is a morphism of localizers
in the other direction. -/
@[simps]
def localizerMorphismInv [W₂.HasTwoOutOfThreeProperty] :
    LocalizerMorphism W₂ W₁ where
  functor := ρ
  map := by
    rw [hW₁]
    intro X Y f hf
    have := i.naturality f
    dsimp at this
    simp only [MorphismProperty.inverseImage_iff]
    rw [← W₂.precomp_iff _ _ (hi X), ← this]
    exact W₂.comp_mem _ _ hf (hi Y)

variable [Φ.functor.Full] [Φ.functor.Faithful]

variable (i) in
/-- If `Φ : LocalizerMorphism W₁ W₂` corresponds to a class `W₁` that is
induced by `W₂` via the fully faithful functor `Φ.functor` and that we
have functorial right resolutions given by a functor `ρ : C₂ ⥤ C₁`, then
this is the natural transformation `𝟭 C₁ ⟶ Φ.functor ⋙ ρ` induced
by `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`. -/
noncomputable def i' : 𝟭 C₁ ⟶ Φ.functor ⋙ ρ :=
  ((whiskeringRight C₁ C₁ C₂).obj Φ.functor).preimage (whiskerLeft Φ.functor i)

@[simp]
lemma Φ_functor_map_i'_app (X₁ : C₁) :
    Φ.functor.map ((i' i).app X₁) = i.app (Φ.functor.obj X₁) :=
  NatTrans.congr_app (((whiskeringRight C₁ C₁ C₂).obj Φ.functor).map_preimage
    (X := 𝟭 C₁) (Y := Φ.functor ⋙ ρ) (whiskerLeft Φ.functor i)) X₁

include hW₁ hi in
lemma W₁_i'_app (X₁ : C₁) : W₁ ((i' i).app X₁) := by
  simpa only [hW₁, MorphismProperty.inverseImage_iff, Φ_functor_map_i'_app]
    using hi (Φ.functor.obj X₁)

end functorialRightResolutions

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

open functorialRightResolutions
include hi hW₁

lemma isLocalizedEquivalence_of_functorial_right_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_unit_of_unit (localizerMorphismInv hi hW₁) (i' i) i
    (W₁_i'_app hi hW₁) hi

variable [W₂.IsMultiplicative]

lemma isConnected_rightResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.RightResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have : Nonempty (Φ.RightResolution X₂) := ⟨{ hw := hi X₂, .. }⟩
  have : IsPreconnected (Φ.RightResolution X₂) := zigzag_isPreconnected (fun R₀ R₄ ↦ by
    let R₁ : Φ.RightResolution X₂ := { hw := W₂.comp_mem _ _ R₀.hw (hi _), .. }
    let R₂ : Φ.RightResolution X₂ := { hw := hi X₂, .. }
    let R₃ : Φ.RightResolution X₂ := { hw := W₂.comp_mem _ _ R₄.hw (hi _), .. }
    let f₀ : R₀ ⟶ R₁ := { hf := W₁_i'_app hi hW₁ R₀.X₁, .. }
    let f₁ : R₂ ⟶ R₁ :=
      { f := ρ.map R₀.w
        comm := (i.naturality R₀.w).symm
        hf := (localizerMorphismInv hi hW₁).map _ R₀.hw }
    let f₂ : R₂ ⟶ R₃ :=
      { f := ρ.map R₄.w
        comm := (i.naturality R₄.w).symm
        hf := (localizerMorphismInv hi hW₁).map _ R₄.hw }
    let f₃ : R₄ ⟶ R₃ := { hf := W₁_i'_app hi hW₁ R₄.X₁, .. }
    exact (Zigzag.of_hom f₀).trans ((Zigzag.of_inv f₁).trans
      ((Zigzag.of_hom f₂).trans (Zigzag.of_inv f₃))) )
  constructor

lemma isRightDerivabilityStructure_of_functorial_resolutions :
    Φ.IsRightDerivabilityStructure := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have := Φ.isLocalizedEquivalence_of_functorial_right_resolutions i hi hW₁
  have := Φ.hasRightResolutions_arrow_of_functorial_resolutions i hi
  have := Φ.isConnected_rightResolution_of_functorial_resolutions i hi hW₁
  apply IsRightDerivabilityStructure.mk'

end right

section left

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hp in
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦ ⟨{
    X₁ := Arrow.mk (ρ.map f.hom)
    w := Arrow.homMk (p.app _) (p.app _) ((p.naturality f.hom).symm)
    hw := ⟨hp _, hp _⟩ }⟩

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hp hW₁

lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence := by
  rw [← Φ.isLocalizedEquivalence_op_iff]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  exact Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

lemma isLeftDerivabilityStructure_of_functorial_resolutions [W₂.IsMultiplicative] :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

end left

end LocalizerMorphism

end CategoryTheory
