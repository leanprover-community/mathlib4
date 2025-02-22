/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.Opposite
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization

/-!
# The Freyd-Mitchell embedding theorem

In this file, we start with an abelian category `C` and construct a full, faithful and exact
functor `C ⥤ ModuleCat.{max u v} (EmbeddingRing C)`.

## Implementation notes

In the literature you will generally only find this theorem stated for small categories `C`. In
Lean, we can work around this limitation by passing from `C` to `AsSmall.{max u v} C`, thereby
enlarging the category of modules that we land in (which should be inconsequential in most
applications) so that our embedding theorem applies to all abelian categories. If `C` was already a
small category, then this does not change anything.
-/

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FreydMitchell

open ZeroObject in
instance : Nonempty (AsSmall.{max u v} C) := ⟨0⟩

variable (C) in
/-- Given an abelian category `C`, this is a ring such that there is a full, faithful and exact
embedding `C ⥤ ModuleCat (EmbeddingRing C)`.

It is probably not a good idea to unfold this. -/
def EmbeddingRing : Type (max u v) :=
  IsGrothendieckAbelian.OppositeModuleEmbedding.EmbeddingRing
    (Ind.yoneda (C := (AsSmall.{max u v} C)ᵒᵖ)).rightOp

noncomputable instance : Ring (EmbeddingRing C) :=
  inferInstanceAs <| Ring <|
    IsGrothendieckAbelian.OppositeModuleEmbedding.EmbeddingRing
      (Ind.yoneda (C := (AsSmall.{max u v} C)ᵒᵖ)).rightOp

variable (C) in
private def F : C ⥤ AsSmall.{max u v} C :=
  AsSmall.equiv.functor

variable (C) in
private noncomputable def G : AsSmall.{max u v} C ⥤ (Ind (AsSmall.{max u v} C)ᵒᵖ)ᵒᵖ :=
  Ind.yoneda.rightOp

variable (C) in
private noncomputable def H :
    (Ind (AsSmall.{max u v} C)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max u v} (EmbeddingRing C) :=
  IsGrothendieckAbelian.OppositeModuleEmbedding.embedding (G C)

variable (C) in
/-- This is the full, faithful and exact embedding `C ⥤ ModuleCat (EmbeddingRing C)`. The fact that
such an functor exists is called the Freyd-Mitchell embedding theorem.

It is probably not a good idea to unfold this. -/
noncomputable def functor : C ⥤ ModuleCat.{max u v} (EmbeddingRing C) :=
  F C ⋙ G C ⋙ H C

instance : (functor C).Faithful := by
  rw [functor]
  have : (F C).Faithful := by rw [F]; infer_instance
  have : (G C).Faithful := by rw [G]; infer_instance
  have : (H C).Faithful := IsGrothendieckAbelian.OppositeModuleEmbedding.faithful_embedding _
  infer_instance

instance : (functor C).Full := by
  rw [functor]
  have : (F C).Full := by rw [F]; infer_instance
  have : (G C).Full := by rw [G]; infer_instance
  have : (G C ⋙ H C).Full := IsGrothendieckAbelian.OppositeModuleEmbedding.full_embedding _
  infer_instance

instance : PreservesFiniteLimits (functor C) := by
  rw [functor]
  have : PreservesFiniteLimits (F C) := by rw [F]; infer_instance
  have : PreservesFiniteLimits (G C) := by rw [G]; apply preservesFiniteLimits_rightOp
  have : PreservesFiniteLimits (H C) :=
    IsGrothendieckAbelian.OppositeModuleEmbedding.preservesFiniteLimits_embedding _
  infer_instance

instance : PreservesFiniteColimits (functor C) := by
  rw [functor]
  have : PreservesFiniteColimits (F C) := by rw [F]; infer_instance
  have : PreservesFiniteColimits (G C) := by rw [G]; apply preservesFiniteColimits_rightOp
  have : PreservesFiniteColimits (H C) :=
    IsGrothendieckAbelian.OppositeModuleEmbedding.preservesFiniteColimits_embedding _
  infer_instance

end FreydMitchell

/-- The Freyd-Mitchell embedding theorem. See also `FreydMitchell.functor` for an unpacked
version of this statement. -/
@[stacks 05PP]
theorem freyd_mitchell (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  ⟨_, _, FreydMitchell.functor C, inferInstance, inferInstance, inferInstance, inferInstance⟩

#print axioms freyd_mitchell

end CategoryTheory.Abelian
