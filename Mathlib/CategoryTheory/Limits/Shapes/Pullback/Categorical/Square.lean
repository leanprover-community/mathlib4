/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-! # Categorical pullback squares

In this file, given a `CatCommSq T L R B`, we provide the basic definition
of a typeclass `CatPullbackSquare` that bundles the data of a (chosen, adjoint)
inverse to the canonical functor from the top left corner to `R ⊡ B`, the
categorical pullback of `R` and `B`.

We show that for such squares, we have a universal property characterizing
functors with values in the top left corner of the square, much like it is
the case for `CategoricalPullback`.

-/


universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Limits
open scoped CategoricalPullback

section

open CategoricalPullback CatCommSqOver in
/-- A `CatPullbackSquare T L R B` asserts that a `CatCommSq T L R B` is a
categorical pullback square. This is realized as the data of a chosen
(adjoint) inverse to the canonical functor `C₁ ⥤ R ⊡ B` induced by
the square. The field of this struct are not intended to be accessed directly.
Instead one should use the corresponding fields of
`CatPullbackSquare.equivalence`. -/
class CatPullbackSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
    [CatCommSq T L R B] where
  /-- a chosen (adjoint) inverse to the canonical functor `C₁ ⥤ R ⊡ B`. -/
  inverse (T) (L) (R) (B) : R ⊡ B ⥤ C₁
  /-- the unit isomorphism for the equivalence -/
  unitIso (T) (L) (R) (B) :
    𝟭 C₁ ≅
    (toFunctorToCategoricalPullback _ _ _).obj (.ofSquare T L R B) ⋙ inverse
  /-- the counit isomorphism for the equivalence -/
  counitIso (T) (L) (R) (B) :
    inverse ⋙ (toFunctorToCategoricalPullback _ _ _).obj
      (.ofSquare T L R B) ≅
    𝟭 (R ⊡ B)
  /-- the left triangle identity -/
  functorEquiv_inverse_obj_unitIso_comp (T) (L) (R) (B) (X : C₁) :
    ((toFunctorToCategoricalPullback _ _ _).obj (.ofSquare T L R B)).map
      (unitIso.hom.app X) ≫
      counitIso.hom.app
        (functorEquiv _ _ _|>.inverse.obj (.ofSquare T L R B)|>.obj X) =
    𝟙 _ := by aesop_cat

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace CatPullbackSquare
open CategoricalPullback

variable [CatCommSq T L R B] [CatPullbackSquare T L R B]

instance (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₂) :
    CatPullbackSquare
      (CategoricalPullback.π₁ F G) (CategoricalPullback.π₂ F G) F G where
  inverse := 𝟭 _
  unitIso := .refl _
  counitIso := .refl _

/-- The canonical equivalence `C₁ ≌ R ⊡ B` bundled by the fields of
`CatPullbackSquare T L R B`. It is advised to avoid working with it,
instead, one should prefer working with `functorEquiv`. -/
@[simps functor]
def equivalence : C₁ ≌ R ⊡ B where
  functor :=
    (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj (.ofSquare T L R B)
  inverse := inverse T L R B
  unitIso := unitIso T L R B
  counitIso := counitIso T L R B
  functor_unitIso_comp := functorEquiv_inverse_obj_unitIso_comp T L R B

instance :
    ((CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
      (.ofSquare T L R B)).IsEquivalence :=
  inferInstanceAs (equivalence T L R B).functor.IsEquivalence

instance : (inverse T L R B).IsEquivalence :=
  inferInstanceAs (equivalence T L R B).inverse.IsEquivalence

/-- An isomorphism of `catCommSqOver` which bundles the natural ismorphisms
`(equivalence T L R B).inverse ⋙ T ≅ π₁ R B`,
`(equivalence T L R B).inverse ⋙ L ≅ π₂ R B` as well as the coherence conditions
they satisfy. -/
@[simps!]
def precomposeEquivalenceInverseIsoDefault :
    (CatCommSqOver.precompose R B (equivalence T L R B).inverse).obj
      (.ofSquare T L R B) ≅
    default :=
  mkIso (Iso.inverseCompIso (.refl _)) (Iso.inverseCompIso (.refl _))
    (by ext; simp)

variable (X : Type u₅) [Category.{v₅} X]

/-- The canonical equivalence between functors to the top left corner of the
square and `CatCommSqOver R B X`.

Note that the component at `S` of the counit of this equivalence
bundles an equivalence between

(Impl. details) This is *not* tagged `@[simps!]` intentionally! This equivalence
should be treated as a primitive when working with categorical pullback squares.
Only its forward direction admits some level of characterization. The idea being
that once this equivalence is obtained, any reference to `R ⊡ B` should be
avoided. -/
def functorEquiv : (X ⥤ C₁) ≌ CatCommSqOver R B X :=
  (equivalence T L R B).congrRight.trans <|
    CategoricalPullback.functorEquiv R B X

@[simp]
lemma functoEquiv_obj_fst (F : X ⥤ C₁) :
    ((functorEquiv T L R B X).functor.obj F).fst = F ⋙ T :=
  rfl

@[simp]
lemma functoEquiv_obj_snd (F : X ⥤ C₁) :
    ((functorEquiv T L R B X).functor.obj F).snd = F ⋙ L :=
  rfl

@[simp]
lemma functoEquiv_obj_iso (F : X ⥤ C₁) :
    ((functorEquiv T L R B X).functor.obj F).iso =
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso T L R B) ≪≫
      (Functor.associator _ _ _).symm :=
  rfl

end CatPullbackSquare

/-- A `Prop-valued` version of `CatPullbackSquare`, that merely asserts the
existence of a `CatPullbackSquare` structure. -/
class IsCatPullbackSquare
    {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
    [CatCommSq T L R B] : Prop where
  nonempty_catPullbackSquare (T) (L) (R) (B) :
    Nonempty (CatPullbackSquare T L R B)

open CategoricalPullback CatCommSqOver in
lemma isCatPullbackSquare_iff_isEquivalence_toFunctorToCategoricalPullback
    [CatCommSq T L R B] :
    IsCatPullbackSquare T L R B ↔
      ((toFunctorToCategoricalPullback R B _).obj
        (.ofSquare T L R B)).IsEquivalence := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · letI S : CatPullbackSquare T L R B :=
    (IsCatPullbackSquare.nonempty_catPullbackSquare T L R B).some
    infer_instance
  · exact
      ⟨⟨{ inverse :=
            ((toFunctorToCategoricalPullback R B C₁).obj
              (ofSquare T L R B)).asEquivalence.inverse
          unitIso :=
            ((toFunctorToCategoricalPullback R B C₁).obj
              (ofSquare T L R B)).asEquivalence.unitIso
          counitIso :=
            ((toFunctorToCategoricalPullback R B C₁).obj
              (ofSquare T L R B)).asEquivalence.counitIso
          functorEquiv_inverse_obj_unitIso_comp :=
            ((toFunctorToCategoricalPullback R B C₁).obj
              (ofSquare T L R B)).asEquivalence.functor_unitIso_comp }⟩⟩

namespace IsCatPullbackSquare

variable [CatCommSq T L R B]

noncomputable def catPullbackSquare [IsCatPullbackSquare T L R B] :
    CatPullbackSquare T L R B :=
  nonempty_catPullbackSquare T L R B|>.some

end IsCatPullbackSquare

end

end CategoryTheory.Limits
