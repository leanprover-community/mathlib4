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

@[simps]
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

@[simp]
lemma CategoricalPullback.inverse_def :
    (equivalence (π₁ R B) (π₂ R B) R B).inverse = 𝟭 _ := rfl

@[simp]
lemma CategoricalPullback.unitIso_def :
    (equivalence (π₁ R B) (π₂ R B) R B).unitIso = .refl _ := rfl

@[simp]
lemma CategoricalPullback.counitIso_def :
    (equivalence (π₁ R B) (π₂ R B) R B).counitIso = .refl _ := rfl

open CatCommSqOver in
/-- An alternative constructor for categorical pullback squares:
to exhibit a square as a `CatPullbackSquare`, it suffices to provide an
equivalence with the default categorical pullback, as well as a
natural isomorphism between the forward direction of the equivalence and
the canonical functor. -/
def mkOfEquivalence
    {D₁ : Type u₅} {D₂ : Type u₆} {D₃ : Type u₇} {D₄ : Type u₈}
    [Category.{v₅} D₁] [Category.{v₆} D₂] [Category.{v₇} D₃] [Category.{v₈} D₄]
    (T' : D₁ ⥤ D₂) (L' : D₁ ⥤ D₃) (R' : D₂ ⥤ D₄) (B' : D₃ ⥤ D₄)
    [CatCommSq T' L' R' B'] (e : D₁ ≌ R' ⊡ B')
    (η : e.functor ≅
      (toFunctorToCategoricalPullback _ _ _).obj (.ofSquare T' L' R' B')) :
    CatPullbackSquare T' L' R' B' where
  inverse := e.inverse
  unitIso := (e.changeFunctor η).unitIso
  counitIso := (e.changeFunctor η).counitIso

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

lemma equivalence_map_fst {X Y : R ⊡ B} (f : X ⟶ Y) :
    T.map ((equivalence T L R B).inverse.map f) =
    ((equivalence T L R B).counitIso.hom.app X).fst ≫ f.fst ≫
      ((equivalence T L R B).counitIso.inv.app Y).fst := by
  have := (precomposeEquivalenceInverseIsoDefault T L R B).hom.fst.naturality f =≫
    ((equivalence T L R B).counitIso.inv.app Y).fst
  dsimp at this
  simp only [precomposeEquivalenceInverseIsoDefault_hom_fst_app, Category.assoc,
    ← comp_fst, Iso.hom_inv_id_app, Functor.comp_obj, id_fst,
    CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_fst,
    CatCommSqOver.ofSquare_fst,
    Category.comp_id] at this
  simpa

lemma equivalence_map_snd {X Y : R ⊡ B} (f : X ⟶ Y) :
    L.map ((equivalence T L R B).inverse.map f) =
    ((equivalence T L R B).counitIso.hom.app X).snd ≫ f.snd ≫
      ((equivalence T L R B).counitIso.inv.app Y).snd := by
  have := (precomposeEquivalenceInverseIsoDefault T L R B).hom.snd.naturality f =≫
    ((equivalence T L R B).counitIso.inv.app Y).snd
  dsimp at this
  simp only [precomposeEquivalenceInverseIsoDefault_hom_snd_app, Category.assoc,
    ← comp_snd, Iso.hom_inv_id_app, Functor.comp_obj, id_snd,
    CatCommSqOver.toFunctorToCategoricalPullback_obj_obj_snd,
    CatCommSqOver.ofSquare_snd,
    Category.comp_id] at this
  simpa

@[reassoc (attr := simp)]
lemma functor_unitIso_comp_fst (x : C₁) :
    T.map ((equivalence T L R B).unitIso.hom.app x) ≫
    (equivalence T L R B|>.counitIso.hom.app <|
      (CatCommSqOver.toFunctorToCategoricalPullback R B C₁|>.obj <|
          CatCommSqOver.ofSquare T L R B).obj x).fst =
  𝟙 (T.obj x) := by
  simpa using congr_arg (fun t ↦ t.fst) <|  (equivalence T L R B).functor_unitIso_comp x

@[reassoc (attr := simp)]
lemma functor_unitIso_comp_snd (x : C₁) :
    L.map ((equivalence T L R B).unitIso.hom.app x) ≫
    (equivalence T L R B|>.counitIso.hom.app <|
      (CatCommSqOver.toFunctorToCategoricalPullback R B C₁|>.obj <|
          CatCommSqOver.ofSquare T L R B).obj x).snd =
  𝟙 (L.obj x) := by
  simpa using congr_arg (fun t ↦ t.snd) <|  (equivalence T L R B).functor_unitIso_comp x

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
      (Functor.whiskeringRight X _ _|>.obj T) ≅
    CatCommSqOver.fstFunctor R B X :=
  Iso.inverseCompIso (.refl _)

/-- The canonical isomorphism between the second projection
`CatCommSqOver.sndFunctor R B X ⥤ (X ⥤ C₃) ` and composition with `L` through
`functorEquiv`. -/
@[simps!]
def functorEquivInverseWhiskeringIsoSnd :
    (functorEquiv T L R B X).inverse ⋙
      (Functor.whiskeringRight X _ _|>.obj L) ≅
    CatCommSqOver.sndFunctor R B X :=
  Iso.inverseCompIso (.refl _)

variable {R B X}

@[reassoc]
lemma counitCoherence_hom_app (S : CatCommSqOver R B X) (x : X) :
    R.map (((functorEquiv T L R B X).counitIso.hom.app S).fst.app x) ≫
      S.iso.hom.app x =
    (CatCommSq.iso T L R B).hom.app
      (((functorEquiv T L R B X).inverse.obj S).obj x) ≫
      B.map (((functorEquiv T L R B X).counitIso.hom.app S).snd.app x) := by
  simp

@[reassoc (attr := simp)]
lemma counitCoherence_inv_app (S : CatCommSqOver R B X) (x : X) :
    R.map (((functorEquiv T L R B X).counitIso.inv.app S).fst.app x) ≫
      (CatCommSq.iso T L R B).hom.app
        (((functorEquiv T L R B X).inverse.obj S).obj x) =
    S.iso.hom.app x ≫
      B.map (((functorEquiv T L R B X).counitIso.inv.app S).snd.app x) := by
  rw [← cancel_epi (R.map <|
      functorEquiv T L R B X|>.counitIso.hom.app S|>.fst.app x),
    ← cancel_mono (CatCommSq.iso T L R B|>.inv.app <|
      functorEquiv T L R B X|>.inverse.obj S|>.obj x)]
  simp only [Functor.comp_obj, functorEquiv_functor_obj_fst,
    Functor.id_obj, Category.assoc, ← NatTrans.comp_app,
    Iso.hom_inv_id, NatTrans.id_app, Category.comp_id,
    ← Functor.map_comp, ← comp_fst, id_fst, Functor.map_id,
    Functor.whiskeringRight_obj_obj, functorEquiv_functor_obj_snd,
    CatCommSqOver.w_app_assoc, functorEquiv_functor_obj_iso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, ← comp_snd, id_snd]
  simp

variable (R B X)

/-- Applying the inverse of `functorEquiv` to the canonical
`CatCommSqOver R B (R ⊡ B)` (definitionally) gives back the inverse of the
structural equivalence `C₁ ≌ R ⊡ B`. -/
def functorEquivInverseDefault :
    (functorEquiv T L R B (R ⊡ B)).inverse.obj default ≅
    (equivalence T L R B).inverse :=
  .refl _

open Functor in
/-- A constructor for natural isomorphisms of functors `X ⥤ C₁` derived from
the universal property: to produce such a natural isomorphism, it suffices to
construct isomorphisms between the postcompositions with the projections in
a way that is compatible with the structural `CatCommSq`. -/
def mkNatIso {J K : X ⥤ C₁} (e₁ : J ⋙ T ≅ K ⋙ T) (e₂ : J ⋙ L ≅ K ⋙ L)
    (coh :
      whiskerRight e₁.hom R ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso T L R B).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso T L R B).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom B := by aesop_cat) :
    J ≅ K :=
  (functorEquiv T L R B X).fullyFaithfulFunctor.preimageIso
    (CategoricalPullback.mkIso e₁ e₂
      (by simpa [functorEquiv, toCatCommSqOver] using coh))


@[deprecated (since := "2025-07-29")] alias
  __root__.CategoryTheory.Limits.CategoricalPullback.mkNatIso := mkNatIso

section mkNatIso
open Functor

variable {J K : X ⥤ C₁} (e₁ : J ⋙ T ≅ K ⋙ T) (e₂ : J ⋙ L ≅ K ⋙ L)
    (coh :
      whiskerRight e₁.hom R ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso T L R B).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso T L R B).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom B := by aesop_cat)

@[simp]
lemma mkNatIso_hom_app_fst (x : X) :
    T.map ((mkNatIso T L R B X e₁ e₂ coh).hom.app x) = e₁.hom.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_inv_app_fst (x : X) :
    T.map ((mkNatIso T L R B X e₁ e₂ coh).inv.app x) = e₁.inv.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_hom_app_snd (x : X) :
    L.map ((mkNatIso T L R B X e₁ e₂ coh).hom.app x) = e₂.hom.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_inv_app_snd (x : X) :
    L.map ((mkNatIso T L R B X e₁ e₂ coh).inv.app x) = e₂.inv.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[deprecated (since := "2025-07-29")]
alias __root__.CategoryTheory.Limits.CategoricalPullback.mkNatIso_hom_app_fst :=
  mkNatIso_hom_app_fst
@[deprecated (since := "2025-07-29")]
alias __root__.CategoryTheory.Limits.CategoricalPullback.mkNatIso_inv_app_fst :=
  mkNatIso_inv_app_fst
@[deprecated (since := "2025-07-29")]
alias __root__.CategoryTheory.Limits.CategoricalPullback.mkNatIso_hom_app_snd :=
  mkNatIso_hom_app_snd
@[deprecated (since := "2025-07-29")]
alias __root__.CategoryTheory.Limits.CategoricalPullback.mkNatIso_inv_app_snd :=
  mkNatIso_inv_app_snd

end mkNatIso

section Pseudofunctoriality

seal functorEquiv.inverse functorEquiv.counitIsoAppFst functorEquiv.counitIsoAppSnd

open CatCommSqOver

/-- The equivalence `functorEquiv` identifies the functoriality
in `X` of `X ⥤ C₁` and `CatCommSqOver R B X`. -/
@[simps!]
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
@[simps! -isSimp]
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

@[simps!]
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
  simp [functorOfTransform]

@[simps!]
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
  simp [functorOfTransform]

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
          simp only [Category.comp_id, Category.id_comp, Category.assoc,
            ← Functor.map_comp_assoc, ← Functor.map_comp, ← NatTrans.comp_app,
            ← comp_fst, ← comp_snd, Iso.inv_hom_id, Iso.hom_inv_id] at this
          simpa [-counitCoherence_inv_app,
            -counitCoherence_inv_app_assoc] using this.symm ))
      (fun {_ _} f ↦ by ext x <;> simp [functorOfTransform])

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
  simpa [functorOfTransform, ← Functor.map_inv, -IsIso.comp_inv_eq,
    -IsIso.eq_comp_inv, -IsIso.eq_inv_comp, ← Iso.app_hom] using
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
  simpa [functorOfTransform, ← Functor.map_inv, -IsIso.comp_inv_eq,
    -IsIso.eq_comp_inv, -IsIso.eq_inv_comp, ← Iso.app_hom] using
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
      mapIso_hom, Iso.app_hom, π₁_map, functorOfTransformObjId,
      CatCospanTransform.leftUnitor_hom_left_app, Iso.symm_hom, mapIso_inv,
      Iso.app_inv, Category.id_comp, map_comp, Category.comp_id,
      functorOfTransformObjComp_hom_app_fst, functorOfTransform_obj_map_fst,
      Category.assoc, Iso.inv_hom_id_app_fst_app_assoc]
    simp [← Functor.map_comp_assoc]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj, functorOfTransformObjId,
      CatCospanTransform.comp_right, CatCospanTransform.id_right, id_obj,
      CatCommSq.iso, π₂_obj, transform_obj_obj_snd, ofSquare_snd, Iso.symm_inv,
      mapIso_hom, Iso.app_hom, π₂_map, functorOfTransformObjId,
      CatCospanTransform.leftUnitor_hom_right_app, Iso.symm_hom,
      mapIso_inv, Iso.app_inv, Category.id_comp, map_comp, Category.comp_id,
      functorOfTransformObjComp_hom_app_snd, functorOfTransform_obj_map_snd,
      Category.assoc, Iso.inv_hom_id_app_snd_app_assoc]
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
  · simp [functorOfTransformObjComp_hom_app_fst, functorOfTransformObjId,
      CatCommSq.iso, functorOfTransform_map_app_fst]
  · simp [functorOfTransformObjComp_hom_app_snd, functorOfTransformObjId,
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
      functorOfTransformObjComp_hom_app_snd,
      functorOfTransformObjComp_inv_app_snd,
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
      functorOfTransformObjComp_hom_app_fst,
      functorOfTransformObjComp_inv_app_fst,
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
      functorOfTransformObjComp_hom_app_snd,
      functorOfTransformObjComp_inv_app_snd,
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
    simp [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  · dsimp
    simp only [functorOfTransform_map_app_snd, comp_obj,
      CatCospanTransform.comp_right,
      CatCospanTransform.associator_hom_right_app, Category.id_comp, map_comp,
      functorOfTransformObjComp_hom_app_snd,
      functorOfTransformObjComp_inv_app_snd,
      Functor.comp_map, Category.assoc, Iso.hom_inv_id_app_assoc,
      CatCommSq.iso_inv_naturality_assoc, NatIso.cancel_natIso_inv_left]
    simp [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]

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
    dsimp at this
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
    dsimp at this
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

namespace CategoricalPullback

/-- An abstract isomorphism between the general
`CatPullbackSquare.functorEquiv` and `CategoricalPullback.functorEquiv`.
Under the hood, this is `Iso.refl _`. If you need to use this isomorphism,
you should consider using `CatPullbackSquare.functorEquiv` instead of
`CategoricalPullback.functorEquiv` in the first place. -/
@[simps!]
def functorEquivInverseIso :
    (functorEquiv (π₁ R B) (π₂ R B) R B X).inverse ≅
    (CategoricalPullback.functorEquiv R B X).inverse := .refl _

@[simp]
lemma functorEquivInverse_obj_obj_fst (S : CatCommSqOver R B X) (x : X) :
  (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.obj S).obj x).fst =
  S.fst.obj x := rfl

@[simp]
lemma functorEquivInverse_obj_obj_snd (S : CatCommSqOver R B X) (x : X) :
  (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.obj S).obj x).snd =
  S.snd.obj x := rfl

@[simp]
lemma functorEquivInverse_obj_obj_iso_hom (S : CatCommSqOver R B X) (x : X) :
  (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.obj S).obj x).iso.hom =
  S.iso.hom.app x := rfl

@[simp]
lemma functorEquivInverse_obj_obj_iso_inv (S : CatCommSqOver R B X) (x : X) :
  (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.obj S).obj x).iso.inv =
  S.iso.inv.app x := rfl

@[simp]
lemma functorEquivCounitIso_hom_app_fst_app (S : CatCommSqOver R B X) (x : X) :
    ((functorEquiv (π₁ R B) (π₂ R B) R B X).counitIso.hom.app S).fst.app x =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.counitIsoAppFst, equivalence,
    functorEquiv.inverse]

@[simp]
lemma functorEquivCounitIso_inv_app_fst_app (S : CatCommSqOver R B X) (x : X) :
    ((functorEquiv (π₁ R B) (π₂ R B) R B X).counitIso.inv.app S).fst.app x =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.counitIsoAppFst, equivalence,
    functorEquiv.inverse]

@[simp]
lemma functorEquivCounitIso_hom_app_snd_app (S : CatCommSqOver R B X) (x : X) :
    ((functorEquiv (π₁ R B) (π₂ R B) R B X).counitIso.hom.app S).snd.app x =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.counitIsoAppSnd, equivalence,
    functorEquiv.inverse]

@[simp]
lemma functorEquivCounitIso_inv_app_snd_app (S : CatCommSqOver R B X) (x : X) :
    ((functorEquiv (π₁ R B) (π₂ R B) R B X).counitIso.inv.app S).snd.app x =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.counitIsoAppSnd, equivalence,
    functorEquiv.inverse]

@[simp]
lemma functorEquivUnitIso_hom_app_app_fst (F : X ⥤ R ⊡ B) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).unitIso.hom.app F).app x).fst =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.unitIso, equivalence, functorEquiv.inverse]

@[simp]
lemma functorEquivUnitIso_hom_app_app_snd (F : X ⥤ R ⊡ B) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).unitIso.hom.app F).app x).snd =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.unitIso, equivalence, functorEquiv.inverse]

@[simp]
lemma functorEquivUnitIso_inv_app_app_fst (F : X ⥤ R ⊡ B) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).unitIso.inv.app F).app x).fst =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.unitIso, equivalence, functorEquiv.inverse]

@[simp]
lemma functorEquivUnitIso_inv_app_app_snd (F : X ⥤ R ⊡ B) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).unitIso.inv.app F).app x).snd =
    𝟙 _ := by
  simp [functorEquiv, functorEquiv.unitIso, equivalence, functorEquiv.inverse]

@[simp]
lemma functorEquivInverse_map_app_fst
    {S₁ S₂ : CatCommSqOver R B X} (f : S₁ ⟶ S₂) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.map f).app x).fst =
    f.fst.app x := by
  simpa using CatPullbackSquare.functorEquivInverse_map_app_fst (π₁ R B) (π₂ R B) R B X f x

@[simp]
lemma functorEquivInverse_map_app_snd
    {S₁ S₂ : CatCommSqOver R B X} (f : S₁ ⟶ S₂) (x : X) :
    (((functorEquiv (π₁ R B) (π₂ R B) R B X).inverse.map f).app x).snd =
    f.snd.app x := by
  simpa using CatPullbackSquare.functorEquivInverse_map_app_snd (π₁ R B) (π₂ R B) R B X f x

section

variable {D₂ : Type u₆} {D₃ : Type u₇} {D₄ : Type u₈}
  [Category.{v₆} D₂] [Category.{v₇} D₃] [Category.{v₈} D₄]
  (R' : D₂ ⥤ D₄) (B' : D₃ ⥤ D₄)
  {X : Type u₉} [Category.{v₉} X]

omit [CatPullbackSquare T L R B]

@[simp]
lemma functorOfTransform_obj_obj_fst (ψ : CatCospanTransform R B R' B')
    (x : C₁) :
    (functorOfTransform T L (π₁ R' B') (π₂ R' B')|>.obj ψ|>.obj x).fst =
    ψ.left.obj (T.obj x) :=
  rfl

@[simp]
lemma functorOfTransform_obj_obj_snd (ψ : CatCospanTransform R B R' B')
    (x : C₁) :
    (functorOfTransform T L (π₁ R' B') (π₂ R' B')|>.obj ψ|>.obj x).snd =
    ψ.right.obj (L.obj x) :=
  rfl

@[simp]
lemma functorOfTransform_obj_obj_iso_hom (ψ : CatCospanTransform R B R' B')
    (x : C₁) :
    (functorOfTransform T L (π₁ R' B') (π₂ R' B')|>.obj ψ|>.obj x).iso =
    ((ψ.squareLeft.iso.app (T.obj x)).symm ≪≫
      ψ.base.mapIso ((CatCommSq.iso T L R B).app x) ≪≫
      (ψ.squareRight.iso.app (L.obj x))) := by
  ext
  simp [functorOfTransform]

@[simp]
lemma functorOfTransform_map_app_fst {ψ ψ' : CatCospanTransform R B R' B'}
    (α : ψ ⟶ ψ') (x : C₁) :
    (functorOfTransform T L (π₁ R' B') (π₂ R' B')|>.map α|>.app x).fst =
    α.left.app (T.obj x) :=
  rfl

@[simp]
lemma functorOfTransform_map_app_snd {ψ ψ' : CatCospanTransform R B R' B'}
    (α : ψ ⟶ ψ') (x : C₁) :
    (functorOfTransform T L (π₁ R' B') (π₂ R' B')|>.map α|>.app x).snd =
    α.right.app (L.obj x) :=
  rfl

end

section mkNatIso

open Functor

variable {J K : X ⥤ R ⊡ B}
    (e₁ : J ⋙ (π₁ R B) ≅ K ⋙ (π₁ R B))
    (e₂ : J ⋙ (π₂ R B) ≅ K ⋙ (π₂ R B))
    (coh :
      whiskerRight e₁.hom R ≫ (associator _ _ _).hom ≫
        whiskerLeft K (CatCommSq.iso (π₁ R B) (π₂ R B) R B).hom ≫
        (associator _ _ _).inv =
      (associator _ _ _).hom ≫
        whiskerLeft J (CatCommSq.iso (π₁ R B) (π₂ R B) R B).hom ≫
        (associator _ _ _).inv ≫
        whiskerRight e₂.hom B := by aesop_cat)

@[simp]
lemma mkNatIso_hom_app_fst (x : X) :
    ((mkNatIso (π₁ R B) (π₂ R B) R B X e₁ e₂ coh).hom.app x).fst =
    e₁.hom.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_inv_app_fst (x : X) :
    ((mkNatIso (π₁ R B) (π₂ R B) R B X e₁ e₂ coh).inv.app x).fst =
    e₁.inv.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_hom_app_snd (x : X) :
    ((mkNatIso (π₁ R B) (π₂ R B) R B X e₁ e₂ coh).hom.app x).snd =
    e₂.hom.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

@[simp]
lemma mkNatIso_inv_app_snd (x : X) :
    ((mkNatIso (π₁ R B) (π₂ R B) R B X e₁ e₂ coh).inv.app x).snd =
    e₂.inv.app x := by
  simp [mkNatIso, Equivalence.fullyFaithfulFunctor]

end mkNatIso

end CategoricalPullback

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

instance [CatCommSq T L R B] [CatPullbackSquare T L R B] :
    IsCatPullbackSquare T L R B :=
  ⟨⟨inferInstance⟩⟩

namespace IsCatPullbackSquare

variable [CatCommSq T L R B]

/-- Noncomputably get a `CatPullbackSquare` from a `CategoryTheory.CatCommSq`
with an `IsCatPullbackSquare` instance. -/
noncomputable def catPullbackSquare [IsCatPullbackSquare T L R B] :
    CatPullbackSquare T L R B :=
  nonempty_catPullbackSquare T L R B|>.some

open CatPullbackSquare in
/-- To check equality of two natural transformations of functors to the top
left corner of a `CatCommSq T L R B` such that `IsCatPullbackSquare T L R B`,
it suffices to do so after whiskering with the projections. -/
@[ext (iff := false)]
lemma natTrans_ext {X : Type u₅} [Category.{v₅} X] [IsCatPullbackSquare T L R B]
    {J K : X ⥤ C₁} {α β : J ⟶ K}
    (e₁ : Functor.whiskerRight α T = Functor.whiskerRight β T)
    (e₂ : Functor.whiskerRight α L = Functor.whiskerRight β L) :
    α = β := by
  ext x
  letI : CatPullbackSquare T L R B := catPullbackSquare T L R B
  apply (equivalence T L R B).fullyFaithfulFunctor.map_injective
  ext
  · simpa using congrArg (fun t ↦ t.app x) e₁
  · simpa using congrArg (fun t ↦ t.app x) e₂

@[deprecated (since := "2025-07-29")]
alias __root__.CategoryTheory.Limits.CategoricalPullback.natTrans_ext :=
  natTrans_ext

end IsCatPullbackSquare

end

end CategoryTheory.Limits
