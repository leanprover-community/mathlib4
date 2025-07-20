/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.Opposite
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization

/-!
# The Freyd-Mitchell embedding theorem

Let `C` be an abelian category. We construct a ring `FreydMitchell.EmbeddingRing C` and a functor
`FreydMitchell.embedding : C ⥤ ModuleCat.{max u v} (EmbeddingRing C)` which is full, faithful and
exact.

## Overview over the proof

The usual strategy to prove the Freyd-Mitchell embedding theorem is as follows:

1. Prove that if `D` is a Grothendieck abelian category and `F : C ⥤ Dᵒᵖ` is a functor from a
small category, then there is a functor `G : Dᵒᵖ ⥤ ModuleCat R` for a suitable `R` such that `G`
is faithful and exact and `F ⋙ G` is full.
2. Find a suitable Grothendieck abelian category `D` and a full, faithful and exact functor
`F : C ⥤ Dᵒᵖ`.

To prove (1), we proceed as follows:

1. Using the Special Adjoint Functor Theorem and the duality between subobjects and quotients in
abelian categories, we have that Grothendieck abelian categories have all limits (this is shown in
`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Basic.lean`).
2. Using the small object argument, it is shown that Grothendieck abelian categories have enough
injectives (see `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean`).
3. Putting these two together, it follows that Grothendieck abelian categories have an injective
cogenerator (see `Mathlib/CategoryTheory/Generator/Abelian.lean`).
4. By taking a coproduct of copies of the injective cogenerator, we find a projective separator `G`
in `Dᵒᵖ` such that every object in the image of `F` is a quotient of `G`. Then the additive Hom
functor `Hom(G, ·) : Dᵒᵖ ⥤ Module (End G)ᵐᵒᵖ` is faithful (because `G` is a separator), left exact
(because it is a hom functor), right exact (because `G` is projective) and full (because of a
combination of the aforementioned properties, see `Mathlib/CategoryTheory/Abelian/Yoneda.lean`).
We put this all together in the file
`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/Opposite.lean`.

To prove (2), there are multiple options.

* Some sources (for example Freyd's "Abelian Categories") choose `D := LeftExactFunctor C Ab`. The
  main difficulty with this approach is that it is not obvious that `D` is abelian. This approach
  has a very algebraic flavor and requires a relatively large armount of ad-hoc reasoning.
* In the Stacks project, it is suggested to choose `D := Sheaf J Ab` for a suitable Grothendieck
  topology on `Cᵒᵖ` and there are reasons to believe that this `D` is in fact equivalent to
  `LeftExactFunctor C Ab`. This approach translates many of the interesting properties along the
  sheafification adjunction from a category of `Ab`-valued presheaves, which in turn inherits many
  interesting properties from the category of abelian groups.
* Kashiwara and Schapira choose `D := Ind Cᵒᵖ`, which can be shown to be equivalent to
  `LeftExactFunctor C Ab` (see the file `Mathlib/CategoryTheory/Preadditive/Indization.lean`).
  This approach deduces most interesting properties from the category of types.

When work on this theorem commenced in early 2022, all three approaches were quite out of reach.
By the time the theorem was proved in early 2025, both the `Sheaf` approach and the `Ind` approach
were available in mathlib. The code below uses `D := Ind Cᵒᵖ`.

## Implementation notes

In the literature you will generally only find this theorem stated for small categories `C`. In
Lean, we can work around this limitation by passing from `C` to `AsSmall.{max u v} C`, thereby
enlarging the category of modules that we land in (which should be inconsequential in most
applications) so that our embedding theorem applies to all abelian categories. If `C` was already a
small category, then this does not change anything.

## References

* https://stacks.math.columbia.edu/tag/05PL
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 9.6
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
such a functor exists is called the Freyd-Mitchell embedding theorem.

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

/-- The Freyd-Mitchell embedding theorem. See also `FreydMitchell.functor` for a functor which
has the relevant instances. -/
@[stacks 05PP]
theorem freyd_mitchell (C : Type u) [Category.{v} C] [Abelian C] :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  ⟨_, _, FreydMitchell.functor C, inferInstance, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory.Abelian
