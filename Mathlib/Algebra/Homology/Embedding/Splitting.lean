/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Embedding.AreComplementary
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Extension of degreewise splittings

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {ι₁ ι₂ : Type*} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape.Embedding

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  (e : Embedding c₁ c₂) {S : ShortComplex (HomologicalComplex C c₁)}
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

open Classical in
/-- If `S` is a short complex in `HomologicalComplex C c₁` that is degreewise split,
then `S.map (e.extendFunctor C)` also is if `e : Embedding c₁ c₂`. -/
noncomputable def splittingExtend (i₂ : ι₂) :
    ((S.map (e.extendFunctor C)).map (eval _ _ i₂)).Splitting :=
  if hi₂ : ∃ i₁, e.f i₁ = i₂ then
    .ofIso (σ _) (S.mapNatIso (e.extendFunctorCompEvalIso C hi₂.choose_spec).symm)
  else by
    refine .ofIsZero _ ?_ ?_ ?_
    all_goals exact isZero_extend_X _ _ _ (by tauto)

lemma splittingExtend_apply {i₁ : ι₁} {i₂ : ι₂} (h : e.f i₁ = i₂) :
    splittingExtend e σ i₂ =
      .ofIso (σ _) (S.mapNatIso (e.extendFunctorCompEvalIso C h).symm) := by
  have : ∃ i₁, e.f i₁ = i₂ := ⟨_, h⟩
  obtain rfl := e.injective_f (this.choose_spec.trans h.symm)
  apply dite_eq_left

end ComplexShape.Embedding
