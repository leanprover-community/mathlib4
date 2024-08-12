/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Square
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X₄` is an open subset
of a topological space that is covered by two open subsets `X₂` and `X₃`,
it is known that there is a long exact sequence
`... ⟶ H^q(X₄) ⟶ H^q(X₂) ⊞ H^q(X₃) ⟶ H^q(X₁) ⟶ H^{q+1}(X₄) ⟶ ...`
where `X₁` is the intersection of `X₂` and `X₃`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which extends `Square C`,
and asserts properties which shall imply the existence of long
exact Mayer-Vietoris sequences in sheaf cohomology (TODO).
We require that the map `X₁ ⟶ X₃` is a monomorphism and
that the square in `C` becomes a pushout square in
the category of sheaves after the application of the
functor `yoneda ⋙ presheafToSheaf J _`. Note that in the
standard case of a covering by two open subsets, all
the morphisms in the square would be monomorphisms,
but this dissymetry allows the example of Nisnevich distinguished
squares in the case of the Nisnevich topology on schemes (in which case
`f₂₄ : X₂ ⟶ X₄` shall be an open immersion and
`f₃₄ : X₃ ⟶ X₄` an étale map that is an isomorphism over
the closed (reduced) subscheme `X₄ - X₂`,
and `X₁` shall be the pullback of `f₂₄` and `f₃₄`.).

Given a Mayer-Vietoris square `S` and a presheaf `P` on `C`,
we introduce a sheaf condition `S.SheafCondition P` and show
that it is indeed satisfied by sheaves.

## TODO
* provide constructors for `MayerVietorisSquare`

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₁₃` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare extends Square C where
  mono_f₁₃ : Mono toSquare.f₁₃ := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

namespace MayerVietorisSquare

variable {J}
variable (S : J.MayerVietorisSquare)

/-- The condition that a Mayer-Vietoris square becomes a pullback square
when we evaluate a presheaf on it. --/
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  (S.toSquare.op.map P).IsPullback

lemma sheafCondition_iff_comp_coyoneda {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) :
    S.SheafCondition P ↔ ∀ (X : Aᵒᵖ), S.SheafCondition (P ⋙ coyoneda.obj X) :=
  Square.isPullback_iff_map_coyoneda_isPullback (S.op.map P)

/-- Given a Mayer-Vietoris square `S` and a presheaf of types, this is the
map from `P.obj (op S.X₄)` to the explicit fibre product of
`P.map S.f₁₂.op` and `P.map S.f₁₃.op`. -/
abbrev toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    P.obj (op S.X₄) → Types.PullbackObj (P.map S.f₁₂.op) (P.map S.f₁₃.op) :=
  (S.toSquare.op.map P).pullbackCone.toPullbackObj

lemma sheafCondition_iff_bijective_toPullbackObj (P : Cᵒᵖ ⥤ Type v') :
    S.SheafCondition P ↔ Function.Bijective (S.toPullbackObj P) := by
  have := (S.toSquare.op.map P).pullbackCone.isLimitEquivBijective
  exact ⟨fun h ↦ this h.isLimit, fun h ↦ Square.IsPullback.mk _ (this.symm h)⟩

namespace SheafCondition

variable {S}
variable {P : Cᵒᵖ ⥤ Type v'} (h : S.SheafCondition P)

lemma bijective_toPullbackObj : Function.Bijective (S.toPullbackObj P) := by
  rwa [← sheafCondition_iff_bijective_toPullbackObj]

lemma ext {x y : P.obj (op S.X₄)}
    (h₁ : P.map S.f₂₄.op x = P.map S.f₂₄.op y)
    (h₂ : P.map S.f₃₄.op x = P.map S.f₃₄.op y) : x = y :=
  h.bijective_toPullbackObj.injective (by ext <;> assumption)

variable (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
  (huv : P.map S.f₁₂.op u = P.map S.f₁₃.op v)

/-- If `S` is a Mayer-Vietoris square, and `P` is a presheaf
which satisfies the sheaf condition with respect to `S`, then
elements of `P` over `S.X₂` and `S.X₃` can be glued if the
coincide over `S.X₁`. -/
noncomputable def glue : P.obj (op S.X₄) :=
  (PullbackCone.IsLimit.equivPullbackObj h.isLimit).symm ⟨⟨u, v⟩, huv⟩

@[simp]
lemma map_f₂₄_op_glue : P.map S.f₂₄.op (h.glue u v huv) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit _

@[simp]
lemma map_f₃₄_op_glue : P.map S.f₃₄.op (h.glue u v huv) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit _

end SheafCondition

private lemma sheafCondition_of_sheaf' (F : Sheaf J (Type v)) :
    S.SheafCondition F.val := by
  refine (S.isPushout.op.map (yoneda.obj F)).of_equiv
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv) ?_ ?_ ?_ ?_
  all_goals
    ext x
    dsimp
    rw [yonedaEquiv_naturality]
    erw [Adjunction.homEquiv_naturality_left]
    rfl

lemma sheafCondition_of_sheaf {A : Type u'} [Category.{v} A]
    (F : Sheaf J A) : S.SheafCondition F.val := by
  rw [sheafCondition_iff_comp_coyoneda]
  intro X
  exact S.sheafCondition_of_sheaf'
    ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 (F.cond X.unop)⟩

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
