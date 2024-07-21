/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
<<<<<<< HEAD
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
=======
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
import Mathlib.CategoryTheory.Limits.Shapes.Types
>>>>>>> origin/mayer-vietoris-square-basic
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X₄` is an open subset
of a topological space that is covered by two open subsets `X₂` and `X₃`,
it is known that there is a long exact sequence
`... ⟶ H^q(X₄) ⟶ H^q(X₂) ⊞ H^q(X₃) ⟶ H^q(X₁) ⟶ H^{q+1}(X₄) ⟶ ...`
when `X₁` is the intersection of `X₂` and `X₃`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which extends `Squace C`,
and asserts properties which shall imply the existence of long
exact Mayer-Vietoris sequences in sheaf cohomology (TODO).
We require that the map `X₂ ⟶ X₄` is a monomorphism and
that the square in `C` becomes a pushout square in
the category of sheaves after the application of the
functor `yoneda ⋙ presheafToSheaf J _`. Note that in the
standard case of a covering by two open subsets, the morphism
`f₃₄ : X₃ ⟶ X₄` would also be a monomophism, but this dissymetry
allows the example of Nisnevich distinguished squares in the
case of the Nisnevich topology on schemes (in which case
`f₂₄ : X₂ ⟶ X₄` shall be an open immersion and
`f₃₄ : X₃ ⟶ X₄` an étale map that is an isomorphism over
the closed (reduced) subscheme `X₄ - X₂`,
and `X₁` is the the pullback of `f₂₄` and `f₃₄`.).

Given `S : J.MayerVietorisSquare`, we show that if `F` is a sheaf
of types, then the types of sections of `F` over `S.X`, `S.U`,
`S.V`, `S.W` form a pullback square.

## TODO
* provide constructors for `MayerVietorisSquare`

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe v u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) [HasWeakSheafify J (Type v)]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `f₁₂ ≫ f₂₄ = f₁₃ ≫ f₃₄` in `C`
such that `f₂₄` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare extends Square C where
  mono_f₂₄ : Mono toSquare.f₂₄ := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isPushout : (toSquare.map (yoneda ⋙ presheafToSheaf J _)).IsPushout

namespace MayerVietorisSquare

variable {J}
variable (S : J.MayerVietorisSquare)

lemma isPushout :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) where
  w := by simp only [← Functor.map_comp, S.fac]
  isColimit' := ⟨S.isColimit⟩

/-- The condition that a Mayer-Vietoris square becomes a pullback square
when we evaluate a presheaf on it. --/
def SheafCondition {A : Type u'} [Category.{v'} A] (P : Cᵒᵖ ⥤ A) : Prop :=
  IsPullback (P.map S.i.op) (P.map S.j.op) (P.map S.p.op) (P.map S.q.op)

section

variable (F : Sheaf J (Type v))

/-- Given `S : J.MayerVietoris Square` and `F : Sheaf J (Type _)`,
this is the pullback cone corresponding to the (pullback) square
obtained by evaluating `F` on the square `S`. -/
@[simps!]
def pullbackConeOfSheaf :
    PullbackCone (F.val.map S.p.op) (F.val.map S.q.op) :=
  PullbackCone.mk (F.val.map S.i.op) (F.val.map S.j.op) (by
    simp only [← Functor.map_comp, ← op_comp, S.fac])

/-- Given `S : J.MayerVietoris Square` and `F : Sheaf J (Type _)`, this is
the map from  -/
abbrev toPullbackSections :
    F.val.obj (op S.X) → Types.PullbackObj (F.val.map S.p.op) (F.val.map S.q.op) :=
  (S.pullbackConeOfSheaf F).toPullbackObj

namespace bijective_toPullbackSections

@[simps!]
noncomputable def pullbackCone :
    PullbackCone
      ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.p).op)
      ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.q).op) :=
  PullbackCone.mk ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.i).op)
    ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.j).op) (by
      dsimp
      simp only [← Functor.map_comp, ← op_comp, S.fac])

noncomputable def isLimitPullbackCone : IsLimit (pullbackCone S F) :=
  isLimitPullbackConeMapOfIsLimit (yoneda.obj F) (by
    simp only [← Functor.map_comp, ← op_comp, S.fac])
    ((PushoutCocone.isColimitEquivIsLimitOp _ S.isPushout.isColimit).ofIsoLimit
      (PullbackCone.ext (Iso.refl _)))

noncomputable def pullbackObjEquiv :
  Types.PullbackObj
    ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.p).op)
    ((yoneda.obj F).map ((yoneda ⋙ presheafToSheaf J _).map S.q).op) ≃
    Types.PullbackObj (F.val.map S.p.op) (F.val.map S.q.op) :=
  Types.pullbackMapEquiv _ _ _ _
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv)
    (fun x ↦ by
      dsimp
      rw [yonedaEquiv_naturality]
      erw [Adjunction.homEquiv_naturality_left]
      rfl)
    (fun x ↦ by
      dsimp
      rw [yonedaEquiv_naturality]
      erw [Adjunction.homEquiv_naturality_left]
      rfl)

lemma pullbackObjEquiv_comm :
    (S.pullbackConeOfSheaf F).toPullbackObj ∘
      ((sheafificationAdjunction J (Type v)).homEquiv _ _).trans yonedaEquiv =
        pullbackObjEquiv S F ∘ (pullbackCone S F).toPullbackObj := by
  ext x
  all_goals
    dsimp [pullbackObjEquiv, Types.pullbackMapEquiv]
    rw [yonedaEquiv_naturality]
    erw [Adjunction.homEquiv_naturality_left]
    rfl

end bijective_toPullbackSections

open bijective_toPullbackSections in
lemma bijective_toPullbackSections :
    Function.Bijective (S.pullbackConeOfSheaf F).toPullbackObj := by
  suffices Function.Bijective (pullbackObjEquiv S F ∘ (pullbackCone S F).toPullbackObj) by
    rw [← pullbackObjEquiv_comm, Function.Bijective.of_comp_iff _
      (by apply Equiv.bijective)] at this
    exact this
  rw [Function.Bijective.of_comp_iff' (by apply Equiv.bijective)]
  exact (PullbackCone.isLimitEquivBijective _).1
    (isLimitPullbackCone S F)

lemma isPullback_of_sheaf :
    IsPullback (F.val.map S.i.op) (F.val.map S.j.op)
      (F.val.map S.p.op) (F.val.map S.q.op) where
  w := by simp only [← Functor.map_comp, ← op_comp, S.fac]
  isLimit' := ⟨(PullbackCone.isLimitEquivBijective _).2
    (S.bijective_toPullbackSections F)⟩

lemma ext {x y : F.val.obj (op S.X)} (h₁ : F.val.map S.i.op x = F.val.map S.i.op y)
    (h₂ : F.val.map S.j.op x = F.val.map S.j.op y) : x = y :=
  PullbackCone.IsLimit.type_ext (S.isPullback_of_sheaf F).isLimit h₁ h₂

section

variable (u : F.val.obj (op S.U)) (v : F.val.obj (op S.V))
  (h : F.val.map S.p.op u = F.val.map S.q.op v)

/-- If `S` is a Mayer-Vietoris square, a section of a sheaf
on `S.X` can be constructed by gluing sections over `S.U` and `S.V`
which coincide on `S.W`. -/
noncomputable def glue : F.val.obj (op S.X) :=
  (PullbackCone.IsLimit.equivPullbackObj (S.isPullback_of_sheaf F).isLimit).symm
    ⟨⟨u, v⟩, h⟩

lemma map_i_op_glue : F.val.map S.i.op (S.glue F u v h) = u :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst
    (S.isPullback_of_sheaf F).isLimit _

lemma map_j_op_glue : F.val.map S.j.op (S.glue F u v h) = v :=
  PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd
    (S.isPullback_of_sheaf F).isLimit _

end

end

end MayerVietorisSquare

end GrothendieckTopology

end CategoryTheory
