/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor

/-!
# Functorial resolutions give derivability structures

In this file, we provide a constructor for right derivability structures.
We assume that `Φ : LocalizerMorphism W₁ W₂` is given by
a fully faithful functor `Φ.functor : C₁ ⥤ C₂` and that we have a resolution
functor `ρ : C₂ ⥤ C₁` with a natural transformation `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`
such that `W₂ (i.app X₂)` for any `X₂ : C₂`. If we assume
that `W₁` is induced by `W₂`, that `W₂` is multiplicative and has
the two-out-of-three property, then `Φ` is a right derivability structure.

-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

section right

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor) (hi : ∀ X₂, W₂ (i.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hi in
lemma hasRightResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasRightResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (i.app _) (i.app _) (i.naturality f.hom).symm
       hw := ⟨hi _, hi _⟩ }⟩

namespace functorialRightResolutions
open Functor

variable {Φ i}

set_option backward.isDefEq.respectTransparency false in
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
induced by `W₂` via the fully faithful functor `Φ.functor` and we
have functorial right resolutions given by a functor `ρ : C₂ ⥤ C₁`, then
this is the natural transformation `𝟭 C₁ ⟶ Φ.functor ⋙ ρ` induced
by `i : 𝟭 C₂ ⟶ ρ ⋙ Φ.functor`. -/
noncomputable def ι : 𝟭 C₁ ⟶ Φ.functor ⋙ ρ :=
  ((whiskeringRight C₁ C₁ C₂).obj Φ.functor).preimage (whiskerLeft Φ.functor i)

@[simp]
lemma Φ_functor_map_ι_app (X₁ : C₁) :
    Φ.functor.map ((ι i).app X₁) = i.app (Φ.functor.obj X₁) :=
  NatTrans.congr_app (((whiskeringRight C₁ C₁ C₂).obj Φ.functor).map_preimage
    (X := 𝟭 C₁) (Y := Φ.functor ⋙ ρ) (whiskerLeft Φ.functor i)) X₁

set_option backward.isDefEq.respectTransparency false in
include hW₁ hi in
lemma W₁_ι_app (X₁ : C₁) : W₁ ((ι i).app X₁) := by
  simpa [hW₁] using hi (Φ.functor.obj X₁)

end functorialRightResolutions

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

open functorialRightResolutions

include hi

include hW₁ in
lemma isLocalizedEquivalence_of_functorial_right_resolutions :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_of_unit_of_unit (localizerMorphismInv hi hW₁) (ι i) i
    (W₁_ι_app hi hW₁) hi

set_option backward.isDefEq.respectTransparency false in
lemma isConnected_rightResolution_of_functorial_resolutions (X₂ : C₂) :
    IsConnected (Φ.RightResolution X₂) := by
  have : Nonempty (Φ.RightResolution X₂) := ⟨{ hw := hi X₂, .. }⟩
  have : IsPreconnected (Φ.RightResolution X₂) :=
    zigzag_isPreconnected (fun R₀ R₄ ↦
      calc
        Zigzag R₀ { hw := W₂.comp_mem _ _ R₀.hw (hi _), .. } :=
          Zigzag.of_hom { f := (ι i).app R₀.X₁ }
        Zigzag (J := Φ.RightResolution X₂) _ { hw := hi X₂, .. } :=
          Zigzag.of_inv
            { f := ρ.map R₀.w
              comm := (i.naturality R₀.w).symm }
        Zigzag (J := Φ.RightResolution X₂) _ { hw := W₂.comp_mem _ _ R₄.hw (hi _), .. } :=
          Zigzag.of_hom
            { f := ρ.map R₄.w
              comm := (i.naturality R₄.w).symm }
        Zigzag _ R₄ := Zigzag.of_inv { f := (ι i).app R₄.X₁ })
  constructor

include hW₁ in
lemma isRightDerivabilityStructure_of_functorial_resolutions
    [W₂.ContainsIdentities] :
    Φ.IsRightDerivabilityStructure := by
  have := Φ.isLocalizedEquivalence_of_functorial_right_resolutions i hi hW₁
  have := Φ.hasRightResolutions_arrow_of_functorial_resolutions i hi
  have := Φ.isConnected_rightResolution_of_functorial_resolutions i hi
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

include hp
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    IsConnected (Φ.LeftResolution X₂) := by
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : IsConnected (Φ.op.RightResolution (Opposite.op X₂)) :=
    Φ.op.isConnected_rightResolution_of_functorial_resolutions (ρ := ρ.op)
      (NatTrans.op p) (fun _ ↦ hp _) _
  have := isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂).symm
  exact isConnected_of_isConnected_op

include hW₁ in
lemma isLocalizedEquivalence_of_functorial_left_resolutions [Φ.IsInduced] :
    Φ.IsLocalizedEquivalence := by
  rw [← Φ.isLocalizedEquivalence_op_iff]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  apply Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

include hW₁ in
lemma isLeftDerivabilityStructure_of_functorial_resolutions [W₂.ContainsIdentities]
    [Φ.IsInduced] :
    Φ.IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  have : Φ.op.functor.Full := by dsimp; infer_instance
  have : Φ.op.functor.Faithful := by dsimp; infer_instance
  exact Φ.op.isRightDerivabilityStructure_of_functorial_resolutions (ρ := ρ.op)
    (NatTrans.op p) (fun _ ↦ hp _) (by simp only [hW₁]; rfl)

end left

end LocalizerMorphism

end CategoryTheory
