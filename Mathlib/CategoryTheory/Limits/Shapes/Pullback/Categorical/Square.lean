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
`CatPullbackSquare.functorEquiv`, which bundles this into the expected
universal property. -/
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

/- We set up the equivalence `functorEquiv : (X ⥤ C₁) ≌ CatCommSqOver R B X`
which realizes the universal property of the square. It could be defined
directly as
```
(equivalence T L R B).congrRight.trans <| CategoricalPullback.functorEquiv R B X
```
but this leads to unsatisfying unfoldings in practice, especially
when using `@[simps!]`: terms that mention `R ⊡ B`
keep appearing with this approach, while you don’t want to work with a
categorical pullback square by constantly going through a generic model of the
categorical pullback.
Instead, we split the equivalence over several definitions to create a stronger
abstraction barrier, and mark `local irreducible` all of its "non-canonical"
(i.e the ones that might refer to `R ⊡ B`) components when building the API,
so that the API is completely blind to the existence of a default
categorical pullback. -/

namespace functorEquiv

/-- The forward direction of FunctorEquiv. -/
@[simps]
def functor : (X ⥤ C₁) ⥤ CatCommSqOver R B X where
  obj F :=
    { fst := F ⋙ T
      snd := F ⋙ L
      iso :=
        Functor.associator F T R ≪≫
          Functor.isoWhiskerLeft F (CatCommSq.iso T L R B) ≪≫
          (Functor.associator F L B).symm}
  map f :=
    { fst := Functor.whiskerRight f T
      snd := Functor.whiskerRight f L }

/-- (impl.) The inverse direction of `FunctorEquiv`. -/
def inverse : CatCommSqOver R B X ⥤ (X ⥤ C₁) :=
  (equivalence T L R B|>.congrRight.trans <|
    CategoricalPullback.functorEquiv R B X).inverse

/-- (impl.) The unit isomorphism of `functorEquiv`. -/
def unitIso :
    𝟭 (X ⥤ C₁) ≅ functor T L R B X ⋙ inverse T L R B X :=
  (equivalence T L R B|>.congrRight.trans <|
    CategoricalPullback.functorEquiv R B X).unitIso

/-- (impl.) The first component of the counit isomorphism of `functorEquiv`. -/
def counitIsoAppFst
    (S : CatCommSqOver R B X) :
    (inverse T L R B X|>.obj S) ⋙ T ≅ S.fst :=
  CatCommSqOver.fstFunctor _ _ _|>.mapIso <|
    (equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S

/-- (impl.) The second component of the counit isomorphism of `functorEquiv`. -/
def counitIsoAppSnd
    (S : CatCommSqOver R B X) :
    ((inverse T L R B X).obj S) ⋙ L ≅ S.snd :=
  CatCommSqOver.sndFunctor _ _ _|>.mapIso <|
    (equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S

private lemma counitCoherence_hom_app' (S : CatCommSqOver R B X) (x : X) :
    R.map ((counitIsoAppFst T L R B X S).hom.app x) ≫
      S.iso.hom.app x =
    (CatCommSq.iso T L R B).hom.app
      (((inverse T L R B X).obj S).obj x) ≫
      B.map ((counitIsoAppSnd T L R B X S).hom.app x) := by
  simpa [counitIsoAppFst, counitIsoAppSnd, inverse] using
    congr_app ((equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S).hom.w x

end functorEquiv

/-- The equivalence of categories `(X ⥤ C₁) ≌ CatCommSqOver R B X` when
`C₁` is the top left corner of a categorical pullback square. The forward
direction of this equivalence is the "canonical" functor while the inverse
should be treated as mostly "opaque".
This equivalence of categories realizes the universal property of categorical
pullbacks, and should be the main object to work with.

### Implementation note:
When building general definitions using this equivalence, one should be
very cautious about the usage of `@[simps!]`, and should always carefully
check that it does not generate lemmas that unfold the inverse or
the co/unit isomorphisms of this equivalence. A good hint that it did
is the appearance of terms containing `CatPullbackSquare.equivalence` in the
generated lemmas.
If they do appear, one should locally `seal` the relevant declarations by doing
```
seal functorEquiv.inverse functorEquiv.counitIsoAppFst
functorEquiv.counitIsoAppSnd functorEquiv.unitIso
```
-/
@[simps! functor_obj_fst functor_obj_snd functor_obj_iso
functor_map_fst functor_map_snd]
def functorEquiv : (X ⥤ C₁) ≌ CatCommSqOver R B X where
  functor := functorEquiv.functor T L R B X
  inverse := functorEquiv.inverse T L R B X
  counitIso := NatIso.ofComponents
    (fun S ↦ CategoricalPullback.mkIso
      (functorEquiv.counitIsoAppFst T L R B X S)
      (functorEquiv.counitIsoAppSnd T L R B X S)
      (by
        ext x
        simp [functorEquiv.counitCoherence_hom_app']))
    (fun {x y} f ↦
      ((equivalence T L R B).congrRight.trans <|
          CategoricalPullback.functorEquiv R B X).counitIso.hom.naturality f)
  unitIso := functorEquiv.unitIso T L R B X
  functor_unitIso_comp x :=
    ((equivalence T L R B).congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).functor_unitIso_comp x

/-- The forward direction of `functorEquiv` maps the identity functor
to the `CatCommSqOver` represented by the square itself. -/
@[simps!]
def functorEquivFunctorIdIso :
    (functorEquiv T L R B C₁).functor.obj (𝟭 C₁) ≅ .ofSquare T L R B :=
  CategoricalPullback.mkIso (Functor.leftUnitor _) (Functor.leftUnitor _)

/-- The inverse direction of `functorEquiv` maps (the `CatCommSqOver`
represented by) the categorical pullback square to the identity functor. -/
@[simps!]
def functorEquivInverseOfSquareIso :
    (functorEquiv T L R B C₁).inverse.obj (.ofSquare T L R B) ≅ (𝟭 C₁) :=
    (functorEquiv T L R B C₁).inverse.mapIso
      (functorEquivFunctorIdIso T L R B).symm ≪≫
      (functorEquiv T L R B C₁).unitIso.symm.app _

@[simp, reassoc]
lemma functorEquivInverse_map_app_fst {S₁ S₂ : CatCommSqOver R B X}
      (f : S₁ ⟶ S₂) (x : X) :
    T.map (((functorEquiv T L R B X).inverse.map f).app x) =
    ((functorEquiv T L R B X).counitIso.hom.app S₁).fst.app x ≫
      f.fst.app x
      ≫ ((functorEquiv T L R B X).counitIso.inv.app S₂).fst.app x := by
  haveI := congr_arg (fun t ↦ t.fst.app x) <|
    (functorEquiv T L R B X).counitIso.hom.naturality f
  dsimp at this
  rw [← reassoc_of% this]
  simp [← NatTrans.comp_app, ← comp_fst]

@[simp, reassoc]
lemma functorEquivInverse_map_app_snd {S₁ S₂ : CatCommSqOver R B X}
      (f : S₁ ⟶ S₂) (x : X) :
    L.map (((functorEquiv T L R B X).inverse.map f).app x) =
    ((functorEquiv T L R B X).counitIso.hom.app S₁).snd.app x ≫
      f.snd.app x
      ≫ ((functorEquiv T L R B X).counitIso.inv.app S₂).snd.app x := by
  haveI := congr_arg (fun t ↦ t.snd.app x) <|
    (functorEquiv T L R B X).counitIso.hom.naturality f
  dsimp at this
  rw [← reassoc_of% this]
  simp [← NatTrans.comp_app, ← comp_snd]

@[reassoc (attr := simp)]
lemma functorEquiv_functor_UnitIso_comp_fst_app (F : X ⥤ C₁) (x : X) :
    T.map (functorEquiv T L R B X|>.unitIso.hom.app F|>.app x) ≫
      (functorEquiv T L R B X|>.counitIso.hom.app <|
        (functorEquiv.functor T L R B X).obj F).fst.app x =
    𝟙 (T.obj <| F.obj x) :=
  congr_arg (fun t ↦ t.fst.app x) <|
    (functorEquiv T L R B X).functor_unitIso_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_functor_UnitIso_comp_snd_app (F : X ⥤ C₁) (x : X) :
    L.map (functorEquiv T L R B X|>.unitIso.hom.app F|>.app x) ≫
      (functorEquiv T L R B X|>.counitIso.hom.app <|
        (functorEquiv.functor T L R B X).obj F).snd.app x =
    𝟙 (L.obj <| F.obj x) :=
  congr_arg (fun t ↦ t.snd.app x) <|
    (functorEquiv T L R B X).functor_unitIso_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_counitInv_functor_comp_fst_app (F : X ⥤ C₁) (x : X) :
    (functorEquiv T L R B X|>.counitInv.app <|
        functorEquiv.functor T L R B X|>.obj F).fst.app x ≫
      T.map (functorEquiv T L R B X|>.unitInv.app F|>.app x) =
    𝟙 (T.obj <| F.obj x) :=
  congrArg (fun t ↦ t.fst.app x) <|
    (functorEquiv T L R B X).counitInv_functor_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_counitInv_functor_comp_snd_app (F : X ⥤ C₁) (x : X) :
    (functorEquiv T L R B X|>.counitInv.app <|
        (functorEquiv.functor T L R B X).obj F).snd.app x ≫
      L.map (functorEquiv T L R B X|>.unitInv.app F|>.app x) =
    𝟙 (L.obj <| F.obj x) :=
  congrArg (fun t ↦ t.snd.app x) <|
    (functorEquiv T L R B X).counitInv_functor_comp F

/-- The canonical isomorphism between the first projection
`CatCommSqOver.sndFunctor R B X ⥤ (X ⥤ C₂) ` and composition with `T` through
`functorEquiv`. -/
@[simps!]
def functorEquivInverseWhiskeringIsoFst :
    (functorEquiv T L R B X).inverse ⋙
      (Functor.whiskeringRight X _ _|>.obj <| T) ≅
    CatCommSqOver.fstFunctor R B X :=
  Iso.inverseCompIso (.refl _)

/-- The canonical isomorphism between the second projection
`CatCommSqOver.sndFunctor R B X ⥤ (X ⥤ C₃) ` and composition with `L` through
`functorEquiv`. -/
@[simps!]
def functorEquivInverseWhiskeringIsoSnd :
    (functorEquiv T L R B X).inverse ⋙
      (Functor.whiskeringRight X _ _|>.obj <| L) ≅
    CatCommSqOver.sndFunctor R B X :=
  Iso.inverseCompIso (.refl _)

end CatPullbackSquare

/-- A `Prop`-valued version of `CatPullbackSquare` that merely asserts the
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

/-- Noncomputably get a `CatPullbackSquare` from a `CategoryTheory.CatCommSq`
with an `IsCatPullbackSquare` instance. -/
noncomputable def catPullbackSquare [IsCatPullbackSquare T L R B] :
    CatPullbackSquare T L R B :=
  nonempty_catPullbackSquare T L R B|>.some

end IsCatPullbackSquare

end

end CategoryTheory.Limits
