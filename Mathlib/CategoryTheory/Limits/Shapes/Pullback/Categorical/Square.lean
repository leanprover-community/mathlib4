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

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ v₁₀ v₁₁ v₁₂ v₁₃ v₁₄ v₁₅ v₁₆
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂ u₁₃ u₁₄ u₁₅ u₁₆

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
    (CatCommSqOver.precompose R B|>.obj (equivalence T L R B).inverse).obj
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
but this leads to unsatisfying unfoldings in practice: terms that mention `R ⊡ B`
keep appearing with this approach, while you don’t want to work with a
categorical pullback square by constantly going through an model of the
categorical pullback.
Instead, we split the equivalence over several definitions to create a stronger
abstraction barrier, and mark irreducible all of its "non-canonical" components,
i.e the ones that might refer to `R ⊡ B`, so that the API is completely
blind to the existence of a default categorical pullback. -/

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
private def inverse : CatCommSqOver R B X ⥤ (X ⥤ C₁) :=
  (equivalence T L R B|>.congrRight.trans <|
    CategoricalPullback.functorEquiv R B X).inverse

/-- (impl.) The unit isomorphism of `functorEquiv`. -/
private def unitIso :
    𝟭 (X ⥤ C₁) ≅ functor T L R B X ⋙ inverse T L R B X :=
  (equivalence T L R B|>.congrRight.trans <|
    CategoricalPullback.functorEquiv R B X).unitIso

/-- (impl.) The first component of the counit isomorphism of `functorEquiv`. -/
private def counitIsoAppFst
    (S : CatCommSqOver R B X) :
    (inverse T L R B X|>.obj S) ⋙ T ≅ S.fst :=
  CatCommSqOver.fstFunctor _ _ _|>.mapIso <|
    (equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S

/-- (impl.) The second component of the counit isomorphism of `functorEquiv`. -/
private def counitIsoAppSnd
    (S : CatCommSqOver R B X) :
    ((inverse T L R B X).obj S) ⋙ L ≅ S.snd :=
  CatCommSqOver.sndFunctor _ _ _|>.mapIso <|
    (equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S

@[reassoc]
private lemma counitCoherence_hom_app' (S : CatCommSqOver R B X) (x : X) :
    R.map ((counitIsoAppFst T L R B X S).hom.app x) ≫
      S.iso.hom.app x =
    (CatCommSq.iso T L R B).hom.app
      (((inverse T L R B X).obj S).obj x) ≫
      B.map ((counitIsoAppSnd T L R B X S).hom.app x) := by
  simpa [counitIsoAppFst, counitIsoAppSnd, inverse] using
    congr_app ((equivalence T L R B|>.congrRight.trans <|
      CategoricalPullback.functorEquiv R B X).counitIso.app S).hom.w x

attribute [irreducible] inverse counitIsoAppFst counitIsoAppSnd

/-- (impl.) The component of the counit isomorphism of `functorEquiv`. -/
private def counitIsoApp (S : CatCommSqOver R B X) :
    (functor T L R B X).obj (inverse T L R B X|>.obj S) ≅ S :=
  CategoricalPullback.mkIso
    (counitIsoAppFst T L R B X S)
    (counitIsoAppSnd T L R B X S)
    (by
      ext x
      simp [counitCoherence_hom_app'])

end functorEquiv

unseal functorEquiv.inverse functorEquiv.counitIsoAppFst
functorEquiv.counitIsoAppSnd in
/-- The equivalence of categories `(X ⥤ C₁) ≌ CatCommSqOver R B X` when
`C₁` is the top left corner of a categorical pullback square. The forward
direction of this equivalence is the "canonical" functor while the inverse
should be treated as mostly "opaque".
This equivalence of categories realizes the universal property of categorical
pullbacks, and should be the main object to work with. -/
@[simps! functor_obj_fst functor_obj_snd functor_obj_iso
functor_map_fst functor_map_snd]
def functorEquiv : (X ⥤ C₁) ≌ CatCommSqOver R B X where
  functor := functorEquiv.functor T L R B X
  inverse := functorEquiv.inverse T L R B X
  counitIso := NatIso.ofComponents
    (functorEquiv.counitIsoApp T L R B X ·)
    (fun {x y} f ↦ by
      dsimp
      have e :
        (functorEquiv.counitIsoApp T L R B X y) =
          ((equivalence T L R B).congrRight.trans <|
            CategoricalPullback.functorEquiv R B X).counitIso.app y := rfl
      have e' :
        (functorEquiv.counitIsoApp T L R B X x) =
          ((equivalence T L R B).congrRight.trans <|
            CategoricalPullback.functorEquiv R B X).counitIso.app x := rfl
      rw [e, e']
      exact
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
        (functorEquiv T L R B X).functor.obj F).fst.app x =
    𝟙 (T.obj <| F.obj x) :=
  congr_arg (fun t ↦ t.fst.app x) <|
    (functorEquiv T L R B X).functor_unitIso_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_functor_UnitIso_comp_snd_app (F : X ⥤ C₁) (x : X) :
    L.map (functorEquiv T L R B X|>.unitIso.hom.app F|>.app x) ≫
      (functorEquiv T L R B X|>.counitIso.hom.app <|
        (functorEquiv T L R B X).functor.obj F).snd.app x =
    𝟙 (L.obj <| F.obj x) :=
  congr_arg (fun t ↦ t.snd.app x) <|
    (functorEquiv T L R B X).functor_unitIso_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_counitInv_functor_comp_fst_app (F : X ⥤ C₁) (x : X) :
    (functorEquiv T L R B X|>.counitInv.app <|
        functorEquiv T L R B X|>.functor.obj F).fst.app x ≫
      T.map (functorEquiv T L R B X|>.unitInv.app F|>.app x) =
    𝟙 (T.obj <| F.obj x) :=
  congrArg (fun t ↦ t.fst.app x) <|
    (functorEquiv T L R B X).counitInv_functor_comp F

@[reassoc (attr := simp)]
lemma functorEquiv_counitInv_functor_comp_snd_app (F : X ⥤ C₁) (x : X) :
    (functorEquiv T L R B X|>.counitInv.app <|
        (functorEquiv T L R B X).functor.obj F).snd.app x ≫
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

section Pseudofunctoriality

open CatCommSqOver

/-- The equivalence `functorEquiv` identifies the functoriality
in `X` of `X ⥤ C₁` and `CatCommSqOver R B X`. -/
instance whiskeringLeftFunctorEquivFunctorSquare
    {X : Type u₅} {Y : Type u₆} [Category.{v₅} X] [Category.{v₆} Y]
    (U : X ⥤ Y) :
    CatCommSq
      ((Functor.whiskeringLeft X Y C₁).obj U)
      (functorEquiv T L R B Y).functor
      (functorEquiv T L R B X).functor
      (precompose R B|>.obj U) where
  iso :=
    NatIso.ofComponents (fun _ =>
      CategoricalPullback.mkIso
        (Functor.associator _ _ _)
        (Functor.associator _ _ _))

/-- The equivalence `functorEquiv` identifies the functoriality
on `X` of `X ⥤ C₁` and `CatCommSqOver F G X` (inverse direction). -/
instance precomposeToFunctorToCategoricalPullbackSquare
    {X : Type u₅} {Y : Type u₆} [Category.{v₅} X] [Category.{v₆} Y]
    (U : X ⥤ Y) :
    CatCommSq
      (precompose R B|>.obj U)
      (functorEquiv T L R B Y).inverse
      (functorEquiv T L R B X).inverse
      (Functor.whiskeringLeft X Y C₁|>.obj U) :=
  CatCommSq.vInv _ _ _ _
    (whiskeringLeftFunctorEquivFunctorSquare T L R B _)

variable {D₁ : Type u₅} {D₂ : Type u₆} {D₃ : Type u₇} {D₄ : Type u₈}
  [Category.{v₅} D₁] [Category.{v₆} D₂] [Category.{v₇} D₃] [Category.{v₈} D₄]
  (T' : D₁ ⥤ D₂) (L' : D₁ ⥤ D₃) (R' : D₂ ⥤ D₄) (B' : D₃ ⥤ D₄)
  [CatCommSq T' L' R' B'] [CatPullbackSquare T' L' R' B']

variable {R B} {R' B'}

/-- Given a (not-necessarily pullback) `CatCommSq T L R B`, a
`CatCospanTransform ψ R B R' B'` and a `CatPullbackSquare T' L' R' B'`,
there is an induced functor between the top left corners of the squares. -/
def functorOfTransform :
    (CatCospanTransform R B R' B') ⥤ (C₁ ⥤ D₁) where
  obj ψ := functorEquiv T' L' R' B' C₁|>.inverse.obj <|
    CatCommSqOver.transform _|>.obj ψ|>.obj (.ofSquare T L R B)
  map α := functorEquiv T' L' R' B' C₁|>.inverse.map <|
    transform _|>.map α|>.app <| .ofSquare T L R B

instance functorOfTransformObjFstSquare (ψ : CatCospanTransform R B R' B') :
    CatCommSq T (functorOfTransform T L T' L'|>.obj ψ) ψ.left T' where
  iso := (CatCommSqOver.fstFunctor _ _ _|>.mapIso <|
    functorEquiv T' L' R' B' C₁|>.counitIso.app <|
      CatCommSqOver.transform _|>.obj ψ|>.obj <| .ofSquare T L R B).symm

omit [CatPullbackSquare T L R B] in
lemma functorOfTransform_obj_map_fst
    (ψ : CatCospanTransform R B R' B')
    {x y : C₁} (f : x ⟶ y) :
    T'.map (functorOfTransform T L T' L'|>.obj ψ |>.map f) =
    (CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ)
      ψ.left T').inv.app _ ≫
      ψ.left.map (T.map f) ≫
      (CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ)
        ψ.left T').hom.app _ := by
  simp

instance functorOfTransformObjSndSquare (ψ : CatCospanTransform R B R' B') :
    CatCommSq L (functorOfTransform T L T' L'|>.obj ψ) ψ.right L' where
  iso := (CatCommSqOver.sndFunctor _ _ _|>.mapIso <|
    functorEquiv T' L' R' B' C₁|>.counitIso.app <|
      CatCommSqOver.transform _|>.obj ψ|>.obj <| .ofSquare T L R B).symm

omit [CatPullbackSquare T L R B] in
lemma functorOfTransform_obj_map_snd
    (ψ : CatCospanTransform R B R' B')
    {x y : C₁} (f : x ⟶ y) :
    L'.map (functorOfTransform T L T' L'|>.obj ψ |>.map f) =
    (CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ)
      ψ.right L').inv.app x ≫
      ψ.right.map (L.map f) ≫
      (CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ)
        ψ.right L').hom.app y := by
  simp

/-- The canonical square that expresses that `functorEquiv` maps
(postcomposition by) `functorOfTransform` to `CatCommSqOver.transform`. -/
@[simps!]
instance functorEquivFunctorWhiskeringFunctorOfTransformObjSquare
    (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform R B R' B') :
    CatCommSq
      (functorEquiv T L R B X).functor
      (Functor.whiskeringRight X C₁ D₁|>.obj <|
        (functorOfTransform T L T' L').obj ψ)
      (transform X|>.obj ψ)
      (functorEquiv T' L' R' B' X).functor where
  iso :=
    NatIso.ofComponents
      (fun J => CategoricalPullback.mkIso
        (Functor.associator _ _ _ ≪≫
          (Functor.isoWhiskerLeft _ (CatCommSq.iso _ _ _ _)) ≪≫
          (Functor.associator _ _ _).symm)
        (Functor.associator _ _ _ ≪≫
          (Functor.isoWhiskerLeft _ (CatCommSq.iso _ _ _ _)) ≪≫
          (Functor.associator _ _ _).symm)
        (by
          ext x
          haveI :=
            R'.map (functorEquiv T' L' R' B' C₁|>.counitIso.inv.app
              (transform C₁|>.obj ψ|>.obj <|ofSquare T L R B)|>.fst.app <|
                J.obj x) ≫=
              (congr_app (functorEquiv T' L' R' B' C₁|>.counitIso.hom.app <|
                CatCommSqOver.transform _|>.obj ψ|>.obj <|
                    .ofSquare T L R B).w <| J.obj x) =≫
              B'.map (functorEquiv T' L' R' B' C₁|>.counitIso.inv.app
                (transform C₁|>.obj ψ|>.obj <| ofSquare T L R B)|>.snd.app <|
                  J.obj x)
          dsimp at this
          simp only [Category.comp_id, Category.id_comp, Category.assoc] at this
          simp only [← Functor.map_comp_assoc, ← Functor.map_comp] at this
          simp only [← NatTrans.comp_app, ← comp_fst, ← comp_snd,
            Iso.inv_hom_id, Iso.hom_inv_id] at this
          simpa using this.symm ))
      (fun {_ _} f ↦ by ext x <;> simp)

/-- The horizontal inverse of
`functorEquivFunctorWhiskeringFunctorOfTransformObjSquare`. -/
@[simps! -isSimp]
instance functorEquivInverseTransformObjSquare
    (X : Type u₁₀) [Category.{v₁₀} X]
    (ψ : CatCospanTransform R B R' B') :
    CatCommSq
      (functorEquiv T L R B X).inverse
      (transform X|>.obj ψ)
      (Functor.whiskeringRight X C₁ D₁|>.obj
        (functorOfTransform T L T' L'|>.obj ψ))
      (functorEquiv T' L' R' B' X).inverse :=
  CatCommSq.hInv (functorEquiv T L R B X) _ _ (functorEquiv T' L' R' B' X)
    (functorEquivFunctorWhiskeringFunctorOfTransformObjSquare _ _ _ _ _ _)

section functorOfTransform_map
omit [CatPullbackSquare T L R B]

@[reassoc]
lemma functorOfTransform_map_app_fst {ψ ψ' : CatCospanTransform R B R' B'}
    (α : ψ ⟶ ψ') (x : C₁) :
    (T'.map <| (functorOfTransform T L T' L'|>.map α).app x) =
    (CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ)
      ψ.left T').inv.app x ≫
      α.left.app (T.obj x) ≫
      (CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ')
        ψ'.left T').hom.app x := by
  simp [functorOfTransform, functorOfTransformObjFstSquare]

@[reassoc]
lemma functorOfTransform_map_app_snd {ψ ψ' : CatCospanTransform R B R' B'}
    (α : ψ ⟶ ψ') (x : C₁) :
    (L'.map ((functorOfTransform T L T' L'|>.map α).app x)) =
    (CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ)
      ψ.right L').inv.app x ≫
      α.right.app (L.obj x) ≫
      (CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ')
        ψ'.right L').hom.app x := by
  simp [functorOfTransform, functorOfTransformObjSndSquare]

end functorOfTransform_map

variable (R B) in
/-- `functorOfTransform` repects identities up to isomorphism. -/
@[simps!]
def functorOfTransformObjId :
    (functorOfTransform T L T L).obj (.id R B) ≅ 𝟭 C₁ :=
  (functorEquiv T L R B C₁|>.inverse.mapIso <|
    (transformObjId C₁ R B).app (.ofSquare T L R B)) ≪≫
    (functorEquivInverseOfSquareIso T L R B)

variable
  {E₁ : Type u₉} {E₂ : Type u₁₀} {E₃ : Type u₁₁} {E₄ : Type u₁₂}
  [Category.{v₉} E₁] [Category.{v₁₀} E₂] [Category.{v₁₁} E₃] [Category.{v₁₂} E₄]
  (T'' : E₁ ⥤ E₂) (L'' : E₁ ⥤ E₃) {R'' : E₂ ⥤ E₄} {B'' : E₃ ⥤ E₄}
  [CatCommSq T'' L'' R'' B''] [CatPullbackSquare T'' L'' R'' B'']

/-- `functorOfTransform` repects compositions up to isomorphism. -/
def functorOfTransformObjComp
    (ψ : CatCospanTransform R B R' B') (ψ' : CatCospanTransform R' B' R'' B'') :
    (functorOfTransform T L T'' L'' ).obj (ψ.comp ψ') ≅
    (functorOfTransform T L T' L').obj ψ ⋙
      (functorOfTransform T' L' T'' L'').obj ψ' :=
  (functorEquiv T'' L'' R'' B'' C₁|>.inverse.mapIso <|
    transformObjComp _ ψ ψ'|>.app <| .ofSquare T L R B) ≪≫
    (functorEquivInverseTransformObjSquare _ _ _ _ _ ψ').iso.symm.app
      (transform _|>.obj ψ|>.obj <| .ofSquare T L R B)

section functorOfTransformObjComp
omit [CatPullbackSquare T L R B]

lemma functorOfTransformObjComp_hom_app_fst (ψ : CatCospanTransform R B R' B')
    (ψ' : CatCospanTransform R' B' R'' B'') (x : C₁) :
    T''.map (functorOfTransformObjComp T L T' L' T'' L'' ψ ψ'|>.hom.app x) =
    (CatCommSq.iso T (functorOfTransform T L T'' L''|>.obj <| ψ.comp ψ')
        (ψ.comp ψ').left T'').inv.app x ≫
      ψ'.left.map ((CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ)
        ψ.left T').hom.app x) ≫
      (CatCommSq.iso T' (functorOfTransform T' L' T'' L''|>.obj ψ')
        ψ'.left T'').hom.app
          (functorOfTransform T L T' L'|>.obj ψ|>.obj x) := by
  simp [functorOfTransformObjComp, CatCommSq.iso, functorOfTransform]

lemma functorOfTransformObjComp_hom_app_snd (ψ : CatCospanTransform R B R' B')
    (ψ' : CatCospanTransform R' B' R'' B'') (x : C₁) :
    L''.map ((functorOfTransformObjComp T L T' L' T'' L'' ψ ψ').hom.app x) =
    (CatCommSq.iso L (functorOfTransform T L T'' L''|>.obj <| ψ.comp ψ')
        (ψ.comp ψ').right L'').inv.app x ≫
      ψ'.right.map ((CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ)
        ψ.right L').hom.app x) ≫
      (CatCommSq.iso L' (functorOfTransform T' L' T'' L''|>.obj ψ')
        ψ'.right L'').hom.app
          (functorOfTransform T L T' L'|>.obj ψ|>.obj x) := by
  simp [functorOfTransformObjComp, CatCommSq.iso, functorOfTransform]

lemma functorOfTransformObjComp_inv_app_fst (ψ : CatCospanTransform R B R' B')
    (ψ' : CatCospanTransform R' B' R'' B'') (x : C₁) :
    T''.map ((functorOfTransformObjComp T L T' L' T'' L'' ψ ψ').inv.app x) =
    (CatCommSq.iso T' (functorOfTransform T' L' T'' L''|>.obj ψ')
        ψ'.left T'').inv.app (functorOfTransform T L T' L'|>.obj ψ|>.obj x) ≫
      ψ'.left.map ((CatCommSq.iso T (functorOfTransform T L T' L'|>.obj ψ)
        ψ.left T').inv.app x) ≫
      (CatCommSq.iso T (functorOfTransform T L T'' L''|>.obj <| ψ.comp ψ')
        (ψ.comp ψ').left T'').hom.app x := by
  simpa [← Functor.map_inv, -IsIso.comp_inv_eq, -IsIso.eq_comp_inv,
    -IsIso.eq_inv_comp, ← Iso.app_hom] using
      IsIso.inv_eq_inv.mpr <|
        functorOfTransformObjComp_hom_app_fst T L T' L' T'' L'' ψ ψ' x

lemma functorOfTransformObjComp_inv_app_snd (ψ : CatCospanTransform R B R' B')
    (ψ' : CatCospanTransform R' B' R'' B'') (x : C₁) :
    L''.map ((functorOfTransformObjComp T L T' L' T'' L'' ψ ψ').inv.app x) =
    (CatCommSq.iso L' (functorOfTransform T' L' T'' L''|>.obj ψ')
        ψ'.right L'').inv.app ((functorOfTransform T L T' L'|>.obj ψ).obj x) ≫
      ψ'.right.map ((CatCommSq.iso L (functorOfTransform T L T' L'|>.obj ψ)
        ψ.right L').inv.app x) ≫
      (CatCommSq.iso L (functorOfTransform T L T'' L''|>.obj <| ψ.comp ψ')
        (ψ.comp ψ').right L'').hom.app x := by
  simpa [← Functor.map_inv, -IsIso.comp_inv_eq, -IsIso.eq_comp_inv,
    -IsIso.eq_inv_comp, ← Iso.app_hom] using
      IsIso.inv_eq_inv.mpr <|
        functorOfTransformObjComp_hom_app_snd T L T' L' T'' L'' ψ ψ' x

end functorOfTransformObjComp

section

open scoped CatCospanTransform
open Functor

@[reassoc]
lemma functorOfTransform_map_leftUnitor
    (ψ : CatCospanTransform R B R' B') :
    (functorOfTransform T L T' L').map (λ_ ψ).hom =
    (functorOfTransformObjComp T L T L T' L' (.id R B) ψ).hom ≫
      whiskerRight (functorOfTransformObjId T L R B).hom
        (functorOfTransform T L T' L'|>.obj ψ) ≫
      (functorOfTransform T L T' L'|>.obj ψ).leftUnitor.hom := by
  apply functorEquiv T' L' R' B' C₁|>.functor.map_injective
  ext x
  · dsimp
    simp only [functorOfTransform_map_app_fst, comp_obj,
      CatCospanTransform.comp_left, CatCospanTransform.id_left, id_obj,
      CatCommSq.iso, π₁_obj, transform_obj_obj_fst, ofSquare_fst, Iso.symm_inv,
      mapIso_hom, Iso.app_hom, π₁_map,
      CatCospanTransform.leftUnitor_hom_left_app, Iso.symm_hom, mapIso_inv,
      Iso.app_inv, Category.id_comp, map_comp, Category.comp_id,
      functorOfTransformObjComp_hom_app_fst, functorOfTransform_obj_map_fst,
      functorEquivInverse_map_app_fst, transformObjId_hom_app_fst_app,
      Category.assoc, functorEquivFunctorIdIso_inv_fst_app,
      Iso.inv_hom_id_app_fst_app_assoc]
    simp [← Functor.map_comp_assoc]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj,
      CatCospanTransform.comp_right, CatCospanTransform.id_right, id_obj,
      CatCommSq.iso, π₂_obj, transform_obj_obj_snd, ofSquare_snd, Iso.symm_inv,
      mapIso_hom, Iso.app_hom, π₂_map,
      CatCospanTransform.leftUnitor_hom_right_app, Iso.symm_hom,
      mapIso_inv, Iso.app_inv, Category.id_comp, map_comp, Category.comp_id,
      functorOfTransformObjComp_hom_app_snd, functorOfTransform_obj_map_snd,
      functorEquivInverse_map_app_snd, transformObjId_hom_app_snd_app,
      Category.assoc, functorEquivFunctorIdIso_inv_snd_app,
      Iso.inv_hom_id_app_snd_app_assoc]
    simp [← Functor.map_comp_assoc]

@[reassoc]
lemma functorOfTransform_map_leftUnitor_inv
    (ψ : CatCospanTransform R B R' B') :
    (functorOfTransform T L T' L').map (λ_ ψ).inv =
    (functorOfTransform T L T' L'|>.obj ψ).leftUnitor.inv ≫
      whiskerRight (functorOfTransformObjId T L R B).inv
        (functorOfTransform T L T' L'|>.obj ψ) ≫
      (functorOfTransformObjComp T L T L T' L' (.id R B) ψ).inv := by
  simpa [← Functor.map_inv, -IsIso.comp_inv_eq, -IsIso.eq_comp_inv,
    -IsIso.eq_inv_comp, ← Iso.app_hom] using
      IsIso.inv_eq_inv.mpr <| functorOfTransform_map_leftUnitor T L T' L' ψ

omit [CatPullbackSquare T L R B]

@[reassoc]
lemma functorOfTransform_map_rightUnitor
    (ψ : CatCospanTransform R B R' B') :
    (functorOfTransform T L T' L').map (ρ_ ψ).hom =
    (functorOfTransformObjComp T L T' L' T' L' ψ (.id R' B')).hom ≫
      whiskerLeft (functorOfTransform T L T' L'|>.obj ψ)
        (functorOfTransformObjId T' L' R' B').hom ≫
      (functorOfTransform T L T' L'|>.obj ψ).rightUnitor.hom := by
  apply functorEquiv T' L' R' B' C₁|>.functor.map_injective
  ext x
  · simp [functorOfTransformObjComp_hom_app_fst,
      CatCommSq.iso, functorOfTransform_map_app_fst]
  · simp [functorOfTransformObjComp_hom_app_snd,
      CatCommSq.iso, functorOfTransform_map_app_snd]

@[reassoc]
lemma functorOfTransform_map_rightUnitor_inv
    (ψ : CatCospanTransform R B R' B') :
    (functorOfTransform T L T' L').map (ρ_ ψ).inv =
    (functorOfTransform T L T' L'|>.obj ψ).rightUnitor.inv ≫
      whiskerLeft (functorOfTransform T L T' L'|>.obj ψ)
        (functorOfTransformObjId T' L' R' B').inv ≫
      (functorOfTransformObjComp T L T' L' T' L' ψ (.id R' B')).inv := by
  simpa [← Functor.map_inv, -IsIso.comp_inv_eq, -IsIso.eq_comp_inv,
    -IsIso.eq_inv_comp, ← Iso.app_hom] using
      IsIso.inv_eq_inv.mpr <| functorOfTransform_map_rightUnitor T L T' L' ψ

@[reassoc]
lemma functorOfTransform_map_whiskerLeft
    (ψ : CatCospanTransform R B R' B')
    {φ φ' : CatCospanTransform R' B' R'' B''} (α : φ ⟶ φ') :
    (functorOfTransform T L T'' L'').map (ψ ◁ α) =
    (functorOfTransformObjComp T L T' L' T'' L'' ψ φ).hom ≫
      whiskerLeft (functorOfTransform T L T' L'|>.obj ψ)
        (functorOfTransform T' L' T'' L''|>.map α) ≫
      (functorOfTransformObjComp T L T' L' T'' L'' ψ φ').inv := by
  apply functorEquiv T'' L'' R'' B'' C₁|>.functor.map_injective
  ext x
  · dsimp
    simp only [functorOfTransform_map_app_fst, comp_obj,
      CatCospanTransform.comp_left, CatCospanTransformMorphism.whiskerLeft_left,
      whiskerLeft_app, map_comp, functorOfTransformObjComp_hom_app_fst,
      functorOfTransformObjComp_inv_app_fst, Category.assoc,
      Iso.hom_inv_id_app_assoc, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp [← Functor.map_comp_assoc ]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj,
      CatCospanTransform.comp_right,
      CatCospanTransformMorphism.whiskerLeft_right, whiskerLeft_app, map_comp,
      functorOfTransformObjComp_hom_app_snd, functorOfTransformObjComp_inv_app_snd,
      Category.assoc, Iso.hom_inv_id_app_assoc, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp [← Functor.map_comp_assoc]

@[reassoc]
lemma functorOfTransform_map_whiskerRight
    {ψ ψ' : CatCospanTransform R B R' B'} (α : ψ ⟶ ψ')
    (φ : CatCospanTransform R' B' R'' B'') :
    (functorOfTransform T L T'' L'').map (α ▷ φ) =
    (functorOfTransformObjComp T L T' L' T'' L'' ψ φ).hom ≫
      whiskerRight (functorOfTransform T L T' L'|>.map α)
        (functorOfTransform T' L' T'' L''|>.obj φ) ≫
      (functorOfTransformObjComp T L T' L' T'' L'' ψ' φ).inv := by
  apply functorEquiv T'' L'' R'' B'' C₁|>.functor.map_injective
  ext x
  · dsimp
    simp only [functorOfTransform_map_app_fst, comp_obj,
      CatCospanTransform.comp_left,
      CatCospanTransformMorphism.whiskerRight_left, whiskerRight_app, map_comp,
      functorOfTransformObjComp_hom_app_fst, functorOfTransformObjComp_inv_app_fst,
      CatCommSq.iso_inv_naturality_assoc, Category.assoc,
      Iso.hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    -- needs to be squeezed to avoid infinite recursion
    simp only [← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
      comp_obj, Category.comp_id]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj,
      CatCospanTransform.comp_right,
      CatCospanTransformMorphism.whiskerRight_right, whiskerRight_app, map_comp,
      functorOfTransformObjComp_hom_app_snd, functorOfTransformObjComp_inv_app_snd,
      CatCommSq.iso_inv_naturality_assoc, Category.assoc,
      Iso.hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    -- needs to be squeezed to avoid infinite recursion
    simp only [← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc,
      comp_obj, Category.comp_id]

@[reassoc]
lemma functorOfTransform_map_associator
    {F₁ : Type u₁₃} {F₂ : Type u₁₄} {F₃ : Type u₁₅} {F₄ : Type u₁₆}
    [Category.{v₁₃} F₁] [Category.{v₁₄} F₂]
    [Category.{v₁₅} F₃] [Category.{v₁₆} F₄]
    (T''' : F₁ ⥤ F₂) (L''' : F₁ ⥤ F₃) {R''' : F₂ ⥤ F₄} {B''' : F₃ ⥤ F₄}
    (ψ : CatCospanTransform R B R' B') (φ : CatCospanTransform R' B' R'' B'')
    (τ : CatCospanTransform R'' B'' R''' B''')
    [CatCommSq T''' L''' R''' B'''] [CatPullbackSquare T''' L''' R''' B'''] :
    (functorOfTransform T L T''' L''').map (α_ ψ φ τ).hom =
    (functorOfTransformObjComp T L T'' L'' T''' L''' (ψ.comp φ) τ).hom ≫
      whiskerRight (functorOfTransformObjComp T L T' L' T'' L'' ψ φ).hom
        (functorOfTransform T'' L'' T''' L'''|>.obj τ) ≫
      ((functorOfTransform T L T' L'|>.obj ψ).associator
        (functorOfTransform T' L' T'' L''|>.obj φ)
          (functorOfTransform T'' L'' T''' L'''|>.obj τ)).hom ≫
      whiskerLeft (functorOfTransform T L T' L'|>.obj ψ)
        (functorOfTransformObjComp T' L' T'' L'' T''' L''' φ τ).inv ≫
      (functorOfTransformObjComp T L T' L' T''' L''' ψ (φ.comp τ)).inv := by
  apply functorEquiv T''' L''' R''' B''' C₁|>.functor.map_injective
  ext x
  · dsimp
    simp only [functorOfTransform_map_app_fst, comp_obj,
      CatCospanTransform.comp_left, CatCospanTransform.associator_hom_left_app,
      Category.id_comp, map_comp, functorOfTransformObjComp_hom_app_fst,
      functorOfTransformObjComp_inv_app_fst, Functor.comp_map, Category.assoc,
      Iso.hom_inv_id_app_assoc, CatCommSq.iso_inv_naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj,
      CatCospanTransform.comp_right,
      CatCospanTransform.associator_hom_right_app, Category.id_comp, map_comp,
      functorOfTransformObjComp_hom_app_snd, functorOfTransformObjComp_inv_app_snd,
      Functor.comp_map, Category.assoc, Iso.hom_inv_id_app_assoc,
      CatCommSq.iso_inv_naturality_assoc, NatIso.cancel_natIso_inv_left]
    simp [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp, Iso.hom_inv_id_app]

@[reassoc]
lemma functorOfTransform_map_associator_inv
    {F₁ : Type u₁₃} {F₂ : Type u₁₄} {F₃ : Type u₁₅} {F₄ : Type u₁₆}
    [Category.{v₁₃} F₁] [Category.{v₁₄} F₂]
    [Category.{v₁₅} F₃] [Category.{v₁₆} F₄]
    (T''' : F₁ ⥤ F₂) (L''' : F₁ ⥤ F₃) {R''' : F₂ ⥤ F₄} {B''' : F₃ ⥤ F₄}
    (ψ : CatCospanTransform R B R' B') (φ : CatCospanTransform R' B' R'' B'')
    (τ : CatCospanTransform R'' B'' R''' B''')
    [CatCommSq T''' L''' R''' B'''] [CatPullbackSquare T''' L''' R''' B'''] :
    (functorOfTransform T L T''' L''').map (α_ ψ φ τ).inv =
    (functorOfTransformObjComp T L T' L' T''' L''' ψ (φ.comp τ)).hom ≫
      whiskerLeft (functorOfTransform T L T' L'|>.obj ψ)
        (functorOfTransformObjComp T' L' T'' L'' T''' L''' φ τ).hom ≫
      ((functorOfTransform T L T' L'|>.obj ψ).associator
        (functorOfTransform T' L' T'' L''|>.obj φ)
          (functorOfTransform T'' L'' T''' L'''|>.obj τ)).inv ≫
      whiskerRight (functorOfTransformObjComp T L T' L' T'' L'' ψ φ).inv
        (functorOfTransform T'' L'' T''' L'''|>.obj τ) ≫
      (functorOfTransformObjComp T L T'' L'' T''' L''' (ψ.comp φ) τ).inv := by
  simpa [← Functor.map_inv, -IsIso.comp_inv_eq, -IsIso.eq_comp_inv,
    -IsIso.eq_inv_comp, ← Iso.app_hom] using
      IsIso.inv_eq_inv.mpr <|
        functorOfTransform_map_associator T L T' L' T'' L'' T''' L''' ψ φ τ

end

/-- An adjunction of categorical cospans induce an adjunction between the
functors induced on the categorical pullbacks -/
@[simps]
def adjunctionOfCatCospanAdjunction (𝔄 : CatCospanAdjunction R B R' B') :
    (functorOfTransform T L T' L').obj 𝔄.leftAdjoint ⊣
    (functorOfTransform T' L' T L).obj 𝔄.rightAdjoint where
  unit :=
    (functorOfTransformObjId T L R B).inv ≫
      (functorOfTransform T L T L).map 𝔄.unit ≫
      (functorOfTransformObjComp T L T' L' T L _ _).hom
  counit :=
    (functorOfTransformObjComp T' L' T L T' L' _ _).inv ≫
      (functorOfTransform T' L' T' L').map 𝔄.counit ≫
      (functorOfTransformObjId T' L' _ _).hom
  left_triangle_components x := by
    have := congr_app
      ((Functor.whiskerRight (functorOfTransformObjId T L R B).inv
        (functorOfTransform T L T' L'|>.obj 𝔄.leftAdjoint) ≫
        (functorOfTransformObjComp T L T L T' L'
          (CatCospanTransform.id R B) 𝔄.leftAdjoint).inv) ≫=
        congr_arg (fun t ↦ functorOfTransform T L T' L'|>.map t)
          𝔄.left_triangle =≫
        (functorOfTransformObjComp T L T' L' T' L'
          𝔄.leftAdjoint (CatCospanTransform.id R' B')).hom ≫
        (functorOfTransform T L T' L'|>.obj 𝔄.leftAdjoint).whiskerLeft
          (functorOfTransformObjId T' L' R' B').hom) x
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp,
      functorOfTransform_map_whiskerRight_assoc T L T L _ _
        𝔄.unit 𝔄.leftAdjoint,
      functorOfTransform_map_whiskerLeft T L T' L' _ _ 𝔄.leftAdjoint 𝔄.counit,
      functorOfTransform_map_associator T L T' L' T L _ _
        𝔄.leftAdjoint 𝔄.rightAdjoint 𝔄.leftAdjoint,
      functorOfTransform_map_leftUnitor T L T' L' 𝔄.leftAdjoint,
      functorOfTransform_map_rightUnitor_inv T L T' L' 𝔄.leftAdjoint,
      ← Functor.whiskerLeft_comp_assoc, ← Functor.whiskerRight_comp_assoc,
      ← Functor.whiskerLeft_comp, Functor.whiskerRight_id',
      Functor.whiskerLeft_id'] at this
    dsimp [-functorOfTransformObjId_hom_app] at this
    simp only [Category.id_comp] at this
    exact this
  right_triangle_components x := by
    have := congr_app
      (((functorOfTransform T' L' T L|>.obj 𝔄.rightAdjoint).whiskerLeft
          (functorOfTransformObjId T L R B).inv ≫
        (functorOfTransformObjComp T' L' T L T L
          𝔄.rightAdjoint (.id R B)).inv) ≫=
        congr_arg (fun t ↦ functorOfTransform T' L' T L|>.map t)
          𝔄.right_triangle =≫
        ((functorOfTransformObjComp T' L' T' L' T L
          (.id R' B') 𝔄.rightAdjoint).hom) ≫
          Functor.whiskerRight (functorOfTransformObjId T' L' R' B').hom
            (functorOfTransform T' L' T L|>.obj 𝔄.rightAdjoint)) x
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp,
      functorOfTransform_map_whiskerRight T' L' T' L' _ _
        𝔄.counit 𝔄.rightAdjoint,
      functorOfTransform_map_whiskerLeft T' L' T L _ _ 𝔄.rightAdjoint 𝔄.unit,
      functorOfTransform_map_associator_inv T' L' T L T' L' _ _
        𝔄.rightAdjoint 𝔄.leftAdjoint 𝔄.rightAdjoint,
      functorOfTransform_map_leftUnitor_inv T' L' T L 𝔄.rightAdjoint,
      functorOfTransform_map_rightUnitor T' L' T L 𝔄.rightAdjoint,
      ← Functor.whiskerLeft_comp_assoc, ← Functor.whiskerRight_comp_assoc,
      ← Functor.whiskerRight_comp, Functor.whiskerRight_id',
      Functor.whiskerLeft_id'] at this
    dsimp [-functorOfTransformObjId_hom_app] at this
    simp only [Category.id_comp] at this
    exact this

/-- A `CatCospanEquivalence` induces an equivalence between the top left corners
of categorical pullback squares.
This fully realizes the fact that the notion of categorical pullback respects
equivalences of categories in all of its arguments.
Note that the corresponding fact is *not* true for the strict pullback of
categories (i.e the pullback in the `1`-category `Cat`) and is the principal
motivation behind using categorical pullbacks as a replacement for the strict
pullback. -/
@[simps]
def equivalenceOfCatCospanEquivalence (E : CatCospanEquivalence R B R' B') :
    C₁ ≌ D₁ where
  functor := functorOfTransform T L T' L'|>.obj E.transform
  inverse := functorOfTransform T' L' T L|>.obj E.inverse
  unitIso :=
    (functorOfTransformObjId _ _ _ _).symm ≪≫
      (functorOfTransform _ _ _ _|>.mapIso E.unitIso) ≪≫
      (functorOfTransformObjComp _ _ _ _ _ _ _ _)
  counitIso :=
    (functorOfTransformObjComp _ _ _ _ _ _ _ _).symm ≪≫
      (functorOfTransform _ _ _ _).mapIso E.counitIso ≪≫
      (functorOfTransformObjId _ _ _ _)
  functor_unitIso_comp :=
    (adjunctionOfCatCospanAdjunction _ _ _ _
      E.toCatCospanAdjunction).left_triangle_components

end Pseudofunctoriality

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
