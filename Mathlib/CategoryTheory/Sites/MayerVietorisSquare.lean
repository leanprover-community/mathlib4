/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.OneHypercover
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Types

/-!
# Mayer-Vietoris squares

The purpose of this file is to allow the formalization of long exact
Mayer-Vietoris sequences in sheaf cohomology. If `X` is an open subset
of a topological space that is covered by two open subsets `U` and `V`,
it is known that there is a long exact sequence
`... ⟶ H^q(X) ⟶ H^q(U) ⊞ H^q(V) ⟶ H^q(W) ⟶ H^{q+1}(X) ⟶ ...`
when `W` is the intersection of `U` and `V`, and `H^q` are the
cohomology groups with values in an abelian sheaf.

In this file, we introduce a structure
`GrothendieckTopology.MayerVietorisSquare` which contains the data
of a commutative square in a category `C` equipped with a Grothendieck
topology `J`, which share some properties with the square formed by
the open subsets `W`, `U`, `V`, `X` in the example above.
In particular, we require that the square become a pushout square
when it is understood as a square in the category of sheaves of sets.
We also require that `U ⟶ X` is a monomorphism. The morphism `V ⟶ X`
does not have to be a monomorphism, which shall allow the example
of Nisnevich distinguished squares in the case of the Nisnevich
topology on schemes (in which case `i : U ⟶ X` shall be an open
immersion and `j : V ⟶ X` an étale map that is an
isomorphism over the closed (reduced) subscheme `X - U`,
and `W` is the fibre product of `i` and `j`.).

Given `S : J.MayerVietorisSquare`, we show that if `F` is a sheaf
of types, then the types of sections of `F` over `S.X`, `S.U`,
`S.V`, `S.W` form a pullback square.

## TODO
* provide constructors for `MayerVietorisSquare`

## References
* https://stacks.math.columbia.edu/tag/08GL

-/
universe w v u

namespace CategoryTheory

open Limits Opposite

namespace Limits

namespace PullbackCone

variable {X Y Z }

end PullbackCone

end Limits

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrp.{v}]

/-- A Mayer-Vietoris square in a category `C` equipped with a Grothendieck
topology consists of a commutative square `p ≫ i = q ≫ j` in `C`
such that `i` is a monomorphism and that the square becomes a
pushout square in the category of sheaves of sets. -/
structure MayerVietorisSquare where
  /-- the object that is covered -/
  X : C
  /-- the first object of the covering -/
  U : C
  /-- the second object of the covering -/
  V : C
  /-- the top-left corner of the square -/
  W : C
  /-- the inclusion of `U` in `X` -/
  i : U ⟶ X
  /-- the morphism from `V` to `X` -/
  j : V ⟶ X
  /-- the morphism from `W` to `U` -/
  p : W ⟶ U
  /-- the morphism from `W` to `V` -/
  q : W ⟶ V
  fac : p ≫ i = q ≫ j
  hi : Mono i := by infer_instance
  /-- the square becomes a pushout square in the category of sheaves of types -/
  isColimit :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsColimit (PushoutCocone.mk
      (f := F.map p) (g := F.map q) (F.map i) (F.map j) (by
        simp only [← Functor.map_comp, fac]))

initialize_simps_projections MayerVietorisSquare (-isColimit)

namespace MayerVietorisSquare

variable {J}
variable (S : J.MayerVietorisSquare)

lemma isPushout :
    letI F := yoneda ⋙ presheafToSheaf J _
    IsPushout (F.map S.p) (F.map S.q) (F.map S.i) (F.map S.j) where
  w := by simp only [← Functor.map_comp, S.fac]
  isColimit' := ⟨S.isColimit⟩

section

variable (F : Sheaf J (Type v))

@[simps!]
def pullbackConeOfSheaf :
    PullbackCone (F.val.map S.p.op) (F.val.map S.q.op) :=
  PullbackCone.mk (F.val.map S.i.op) (F.val.map S.j.op) (by
    simp only [← Functor.map_comp, ← op_comp, S.fac])

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
