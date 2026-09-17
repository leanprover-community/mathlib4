/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GuitartExact.Prod
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
public import Mathlib.CategoryTheory.Localization.Prod

/-!
# Product of derivability structures

In this file, we show that the external product of two left/right derivability
structures is also a derivability structure (at least when we assume that
the properties of morphisms that are involved contain identities).

The behavior of derivability structures with respect to products of categories
was not studied in the paper [KahnMaltsiniotis2008]: it was remarked in 2023 by the
author of this file (see also §5.3.4 in [*Formalization of derived categories*][riou-2025]).
This observation was a significant motivation for the formalization of derivability
structures (see the files
`Mathlib/Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean` and
`Mathlib/AlgebraicTopology/ModelCategory/DerivabilityStructureCofibrant.lean` for two examples,
in homological algebra and in homotopical algebra), because it allows not only
to derive functors "in one variable" but also to derive functors in several
variables (e.g. the tensor product as a bifunctor).

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
* [Joël Riou, *Formalization of derived categories in {Lean}/mathlib*][riou-2025]

-/

@[expose] public section

namespace CategoryTheory

open Category Localization

variable {C₁ D₁ C₂ D₂ : Type*} {C₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁ W₁') (Φ₂ : LocalizerMorphism W₂ W₂')

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₁'.ContainsIdentities] [W₂'.ContainsIdentities]

instance [Φ₁.IsRightDerivabilityStructure] [Φ₂.IsRightDerivabilityStructure] :
    (Φ₁.prod Φ₂).IsRightDerivabilityStructure := by
  let e₁ := (Φ₁.catCommSq W₁.Q W₁'.Q).iso
  let e₂ := (Φ₂.catCommSq W₂.Q W₂'.Q).iso
  rw [(Φ₁.prod Φ₂).isRightDerivabilityStructure_iff (W₁.Q.prod W₂.Q) (W₁'.Q.prod W₂'.Q)
    ((Φ₁.localizedFunctor W₁.Q W₁'.Q).prod (Φ₂.localizedFunctor W₂.Q W₂'.Q))
    (NatIso.prod e₁ e₂)]
  change TwoSquare.GuitartExact ((TwoSquare.mk _ _ _ _ e₁.hom).prod (TwoSquare.mk _ _ _ _ e₂.hom))
  infer_instance

-- to be moved
instance {D : Type*} [Category* D] (L : C₁ᵒᵖ × C₂ᵒᵖ ⥤ D)
    [L.IsLocalization (W₁.op.prod W₂.op)] :
    ((prodOpEquiv C₁ C₂).functor ⋙ L).IsLocalization (W₁.prod W₂).op :=
  Functor.IsLocalization.of_equivalence_source L (W₁.op.prod W₂.op) _ (W₁.prod W₂).op
    (prodOpEquiv C₁ C₂).symm (fun _ _ _ h ↦ by
      simp only [Equivalence.symm_functor, MorphismProperty.inverseImage_iff]
      exact MorphismProperty.le_isoClosure _ _ h)
        (fun _ _ _ h ↦ Localization.inverts L (W₁.op.prod W₂.op) _ h) (Iso.refl _)

instance [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure] :
    (Φ₁.prod Φ₂).IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  let L := W₁.op.Q.prod W₂.op.Q
  let L' := W₁'.op.Q.prod W₂'.op.Q
  let F := (Φ₁.op.prod Φ₂.op).functor
  let F' := (Φ₁.op.prod Φ₂.op).localizedFunctor L L'
  let e : F ⋙ L' ≅ L ⋙ F' := ((Φ₁.op.prod Φ₂.op).catCommSq L L').iso
  have he := (Φ₁.op.prod Φ₂.op).guitartExact_of_isRightDerivabilityStructure' _ _ _ e
  let E := prodOpEquiv C₁ C₂
  let E' := prodOpEquiv D₁ D₂
  let w : (Φ₁.prod Φ₂).op.functor ⋙ (prodOpEquiv D₁ D₂).functor ≅ E.functor ⋙ F := Iso.refl _
  rw [isRightDerivabilityStructure_iff (Φ₁.prod Φ₂).op (E.functor ⋙ L)
    (E'.functor ⋙ L') _ (Functor.isoWhiskerLeft E.functor e)]
  have : (Functor.isoWhiskerLeft E.functor e).hom =
    (TwoSquare.vComp (.mk _ _ _ _ w.hom) (.mk _ _ _ _ e.hom)) := by
    ext ⟨X₁, X₂⟩ <;> simp [w, L']
  rw [this]
  infer_instance

end LocalizerMorphism

end CategoryTheory
