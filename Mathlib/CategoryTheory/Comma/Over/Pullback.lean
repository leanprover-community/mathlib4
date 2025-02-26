/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Monad.Products
import Mathlib.CategoryTheory.Equivalence

/-!
# Adjunctions related to the over category

In a category with pullbacks, for any morphism `f : X ⟶ Y`, the functor
`Over.map f : Over X ⥤ Over Y` has a right adjoint `Over.pullback f`.

In a category with binary products, for any object `X` the functor
`Over.forget X : Over X ⥤ C` has a right adjoint `Over.star X`.

## Main declarations

- `Over.pullback f : Over Y ⥤ Over X` is the functor induced by a morphism `f : X ⟶ Y`.
- `Over.mapPullbackAdj` is the adjunction `Over.map f ⊣ Over.pullback f`.
- `star : C ⥤ Over X` is the functor induced by an object `X`. When `X` is the terminal object,
  this functor is isomorphic to `Functor.toOverTerminal C` which maps `Y : C` to `terminal.from Y`.
- `forgetAdjStar` is the adjunction  `forget X ⊣ star X`.
- `Reindex` is the reindexing of `Z : Over X` along `Y : Over X`. It is a syntactic sugar for
  `(Over.pullback Y.hom).obj Z`.

## Notation

- `μ X Y` : is notation for `fstProj : (Sigma Y (Reindex Y Z)) ⟶ Z`
- `π X Y` : is notation for `sndProj : (Sigma Y (Reindex Y Z)) ⟶ Y`

## Main results

- `Over.mapPulbackNatIsoTensorLeft` constructs a natural isomorphism between the composition
  `(pullback Y.hom) ⋙ (map Y.hom)` and the left tensor product functor `tensorLeft Y`.

- `mapStarIso` constructs a natural isomorphism between the functors `star X` and
  `star Y ⋙ pullback f` for any morphism `f : X ⟶ Y`.

- `starIteratedSliceForwardIsoPullback` relates `Over.pullback f` and `star (Over.mk f)`.
  In particular, it constructs a natural isomorphism between the functors
  `star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward` and `pullback f`. We shall use the
  mate conjugate of this isomorphic to construct the right adjoint of `Over.pullback f` in locally
  cartesian closed categories.

-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u₁} [Category.{v₁} C]

namespace Over

open Limits

/-- In a category with pullbacks, a morphism `f : X ⟶ Y` induces a functor `Over Y ⥤ Over X`,
by pulling back a morphism along `f`. -/
@[simps! (config := { simpRhs := true}) obj_left obj_hom map_left]
def pullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd g.hom f)
  map := fun g {h} {k} =>
    Over.homMk (pullback.lift (pullback.fst _ _ ≫ k.left) (pullback.snd _ _)
      (by simp [pullback.condition]))

@[deprecated (since := "2024-05-15")]
noncomputable alias Limits.baseChange := Over.pullback

@[deprecated (since := "2024-07-08")]
noncomputable alias baseChange := pullback

/-- `Over.map f` is left adjoint to `Over.pullback f`. -/
@[simps! unit_app counit_app]
def mapPullbackAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over.map f ⊣ pullback f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun x y =>
        { toFun := fun u =>
            Over.homMk (pullback.lift u.left x.hom <| by simp)
          invFun := fun v => Over.homMk (v.left ≫ pullback.fst _ _) <| by
            simp [← Over.w v, pullback.condition]
          left_inv := by aesop_cat
          right_inv := fun v => by
            ext
            dsimp
            ext
            · simp
            · simpa using (Over.w v).symm } }

@[deprecated (since := "2024-07-08")]
noncomputable alias mapAdjunction := mapPullbackAdj

/-- pullback (𝟙 X) : Over X ⥤ Over X is the identity functor. -/
def pullbackId {X : C} [HasPullbacks C] : pullback (𝟙 X) ≅ 𝟭 _ :=
  conjugateIsoEquiv (mapPullbackAdj (𝟙 _)) (Adjunction.id (C := Over _)) (Over.mapId _).symm

/-- pullback commutes with composition (up to natural isomorphism). -/
def pullbackComp [HasPullbacks C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  conjugateIsoEquiv (mapPullbackAdj _) ((mapPullbackAdj _).comp (mapPullbackAdj _))
    (Over.mapComp _ _).symm

instance pullbackIsRightAdjoint [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    (pullback f).IsRightAdjoint  :=
  ⟨_, ⟨mapPullbackAdj f⟩⟩

/-- The reindexing of `Z : Over X` along `Y : Over X`, defined by pulling back `Z` along
`Y.hom : Y.left ⟶ X`. -/
abbrev Reindex [HasPullbacks C] {X : C} (Y : Over X) (Z : Over X) : Over Y.left :=
  (Over.pullback Y.hom).obj Z

namespace Reindex

open Sigma

variable [HasPullbacks C] {X : C}

lemma hom {Y : Over X} {Z : Over X} :
    (Reindex Y Z).hom = pullback.snd Z.hom Y.hom := by
  rfl

/-- `Reindex` is symmetric in its first and second arguments up to an isomorphism. -/
def symmetryObjIso (Y Z : Over X) :
    (Reindex Y Z).left ≅ (Reindex Z Y).left := pullbackSymmetry _ _

/-- The reindexed sum of `Z` along `Y` is isomorphic to the reindexed sum of `Y` along `Z` in the
category `Over X`. -/
@[simps!]
def sigmaSymmetryIso (Y Z : Over X) :
  Sigma Y (Reindex Y Z) ≅ Sigma Z (Reindex Z Y) := by
  apply Over.isoMk _ _
  · exact pullbackSymmetry ..
  · simp [pullback.condition]

lemma symmetry_hom {Y Z : Over X} :
    (pullback.snd Z.hom Y.hom) ≫ Y.hom =
    (pullbackSymmetry _ _).hom ≫ (pullback.snd Y.hom Z.hom) ≫ Z.hom  := by
  simp [← pullback.condition]

/-- The first projection out of the reindexed sigma object. -/
def fstProj (Y Z : Over X) : Sigma Y (Reindex Y Z) ⟶ Y :=
  Over.homMk (pullback.snd Z.hom Y.hom) (by simp)

lemma fstProj_sigma_fst (Y Z : Over X) : fstProj Y Z = Sigma.fst (Reindex Y Z) := by rfl

/-- The second projection out of the reindexed sigma object. -/
def sndProj (Y Z : Over X) : Sigma Y (Reindex Y Z) ⟶ Z :=
  Over.homMk (pullback.fst Z.hom Y.hom) (by simp [pullback.condition])

/-- The notation for the first projection of the reindexed sigma object. -/
scoped notation " π_ " => fstProj

/-- The notation for the second projection of the reindexed sigma object. -/
scoped notation " μ_ " => sndProj

lemma counit_app_pullback_fst {Y Z : Over X} :
    μ_ Y Z = (mapPullbackAdj Y.hom).counit.app Z := by
  simp [mapPullbackAdj_counit_app]
  rfl

lemma counit_app_pullback_snd {Y Z : Over X} :
    π_ Y Z = (sigmaSymmetryIso Y Z).hom ≫ (mapPullbackAdj Z.hom).counit.app Y := by
  aesop

@[simp]
lemma counit_app_pullback_snd_eq_homMk {Y Z : Over X} :
    π_ Y Z = (homMk (Reindex Y Z).hom : (Sigma Y (Reindex Y Z)) ⟶ Y) :=
  OverMorphism.ext (by aesop)

end Reindex

section BinaryProduct

open ChosenFiniteProducts Sigma Reindex

variable [HasFiniteWidePullbacks C] {X : C}

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
def isBinaryProductSigmaReindex (Y Z : Over X) :
    IsLimit <| BinaryFan.mk (P:= Sigma Y (Reindex Y Z)) (π_ Y Z) (μ_ Y Z) := by
  refine IsLimit.mk (?lift) ?fac ?uniq
  · intro s
    fapply Over.homMk
    · exact pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop)
    · aesop
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;> simp [Reindex.sndProj]
  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
    · exact congr_arg CommaMorphism.left (h ⟨ .right⟩)
    · exact congr_arg CommaMorphism.left (h ⟨ .left ⟩)

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

/-- The object `(Sigma Y) (Reindex Y Z)` is isomorphic to the binary product `Y × Z`
in `Over X`. -/
@[simps!]
def sigmaReindexIsoProd (Y Z : Over X) :
    (Sigma Y) (Reindex Y Z) ≅ Limits.prod Y Z := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProductSigmaReindex Y Z) (prodIsProd Y Z)

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the `(map f).obj ((pullback f).obj Y)`
is isomorphic to the binary product of `(Over.mk f)` and `Y`. -/
def sigmaReindexIsoProdMk {Y : C} (f : Y ⟶ X) (Z : Over X) :
    (map f).obj ((pullback f).obj Z) ≅ Limits.prod (Over.mk f) Z :=
  sigmaReindexIsoProd (Over.mk f) _

lemma sigmaReindexIsoProd_hom_comp_fst {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ (fst Y Z) = (π_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.left⟩

lemma sigmaReindexIsoProd_hom_comp_snd {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ (snd Y Z) = (μ_ Y Z) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.right⟩

end BinaryProduct

end Over

section TensorLeft

open MonoidalCategory Over Functor ChosenFiniteProducts

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts
attribute [local instance] monoidalOfChosenFiniteProducts

variable [HasFiniteWidePullbacks C] {X : C}

/-- The pull-push composition `(Over.pullback Y.hom) ⋙ (Over.map Y.hom)` is naturally isomorphic
to the left tensor product functor `Y × _` in `Over X`-/
def Over.sigmaReindexNatIsoTensorLeft (Y : Over X) :
    (pullback Y.hom) ⋙ (map Y.hom) ≅ tensorLeft Y := by
  fapply NatIso.ofComponents
  · intro Z
    simp only [const_obj_obj, Functor.id_obj, comp_obj, tensorLeft_obj, tensorObj, Over.pullback]
    exact sigmaReindexIsoProd Y Z
  · intro Z Z' f
    simp
    ext1 <;> simp_rw [assoc]
    · simp_rw [whiskerLeft_fst]
      iterate rw [sigmaReindexIsoProd_hom_comp_fst]
      ext
      simp
    · simp_rw [whiskerLeft_snd]
      iterate rw [sigmaReindexIsoProd_hom_comp_snd, ← assoc, sigmaReindexIsoProd_hom_comp_snd]
      ext
      simp [Reindex.sndProj]

lemma Over.sigmaReindexNatIsoTensorLeft_hom_app
    {Y : Over X} (Z : Over X) :
    (Over.sigmaReindexNatIsoTensorLeft Y).hom.app Z = (sigmaReindexIsoProd Y Z).hom := by
  aesop

end TensorLeft

variable (C)

/-- The functor from `C` to `Over (⊤_ C)` which sends `X : C` to `terminal.from X`. -/
@[simps! obj_left obj_hom map_left]
def Functor.toOverTerminal [HasTerminal C] : C ⥤ Over (⊤_ C) where
  obj X := Over.mk (terminal.from X)
  map {X Y} f := Over.homMk f

/-- The slice category over the terminal object is equivalent to the original category. -/
def equivOverTerminal [HasTerminal C] : Over (⊤_ C) ≌ C :=
  CategoryTheory.Equivalence.mk (Over.forget _) (Functor.toOverTerminal C)
    (NatIso.ofComponents (fun X => Over.isoMk (Iso.refl _)))
    (NatIso.ofComponents (fun X => Iso.refl _))

namespace Over

variable {C}

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star [HasBinaryProducts C] (X : C) : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X

lemma star_map [HasBinaryProducts C] {X : C} {Y Z : C} (f : Y ⟶ Z) :
    (star X).map f = Over.homMk (prod.map (𝟙 X) f) (by aesop) := by
  simp [star]

variable (X : C)

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.
Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar [HasBinaryProducts C] : forget X ⊣ star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : (forget X).IsLeftAdjoint  :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

namespace forgetAdjStar

variable [HasBinaryProducts C]

theorem unit_app {I : C} (X : Over I): (Over.forgetAdjStar I).unit.app X =
    Over.homMk (prod.lift X.hom (𝟙 X.left)) := by
  ext
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

theorem counit_app {I : C} (X : C) :
    ((Over.forgetAdjStar I).counit.app X) = prod.snd := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

theorem homEquiv {I : C} (X : Over I) (A : C) (f : X.left ⟶ A) :
    ((Over.forgetAdjStar I).homEquiv X A) f =
    Over.homMk (prod.lift X.hom f) := by
  rw [Adjunction.homEquiv_unit, unit_app]
  ext
  simp

theorem homEquiv_symm {I : C} (X : Over I) (A : C) (f : X ⟶ (Over.star I).obj A) :
     ((Over.forgetAdjStar I).homEquiv X A).symm f = f.left ≫ prod.snd := by
   rw [Adjunction.homEquiv_counit, counit_app]
   simp

end forgetAdjStar

end Over

namespace Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A right adjoint to the forward functor of an equivalence is naturally isomorphic to the
inverse functor of the equivalence. -/
def equivalenceRightAdjointIsoInverse (e : D ≌ C) (R : C ⥤ D) (adj : e.functor ⊣ R) :
    R ≅ e.inverse :=
  conjugateIsoEquiv adj (e.toAdjunction) (Iso.refl _)

end Adjunction

namespace Over

/-- `star (⊤_ C) : C ⥤ Over (⊤_ C)` is naturally isomorphic to `Functor.toOverTerminal C`. -/
def starIsoToOverTerminal [HasTerminal C] [HasBinaryProducts C] :
    star (⊤_ C) ≅ Functor.toOverTerminal C := by
  apply Adjunction.equivalenceRightAdjointIsoInverse
    (equivOverTerminal C) (star (⊤_ C)) (forgetAdjStar (⊤_ C))

variable {C}

/-- A natural isomorphism between the functors `star X` and `star Y ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
def starPullbackIsoStar [HasBinaryProducts C] [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    star Y ⋙ pullback f ≅ star X :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjStar Y)) (forgetAdjStar X) (mapForget f)

/-- The functor `Over.pullback f : Over Y ⥤ Over X` is naturally isomorphic to
`Over.star : Over Y ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over X`. -/
def starIteratedSliceForwardIsoPullback [HasFiniteWidePullbacks C]
    {X Y : C} (f : X ⟶ Y) : star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjStar _))
  (mapPullbackAdj f) (eqToIso (iteratedSliceBackward_forget (Over.mk f)))

end Over

@[deprecated (since := "2024-05-18")] noncomputable alias star := Over.star

@[deprecated (since := "2024-05-18")] noncomputable alias forgetAdjStar := Over.forgetAdjStar

namespace Under

variable {C} [HasPushouts C]

/-- When `C` has pushouts, a morphism `f : X ⟶ Y` induces a functor `Under X ⥤ Under Y`,
by pushing a morphism forward along `f`. -/
@[simps]
def pushout {X Y : C} (f : X ⟶ Y) : Under X ⥤ Under Y where
  obj x := Under.mk (pushout.inr x.hom f)
  map := fun x {x'} {u} =>
    Under.homMk (pushout.desc (u.right ≫ pushout.inl _ _) (pushout.inr _ _)
      (by simp [← pushout.condition]))

/-- `Under.pushout f` is left adjoint to `Under.map f`. -/
@[simps! unit_app counit_app]
def mapPushoutAdj {X Y : C} (f : X ⟶ Y) : pushout f ⊣ map f :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun x y => {
      toFun := fun u => Under.homMk (pushout.inl _ _ ≫ u.right) <| by
        simp only [map_obj_hom]
        rw [← Under.w u]
        simp only [Functor.const_obj_obj, map_obj_right, Functor.id_obj, pushout_obj, mk_right,
          mk_hom]
        rw [← assoc, ← assoc, pushout.condition]
      invFun := fun v => Under.homMk (pushout.desc v.right y.hom <| by simp)
      left_inv := fun u => by
        ext
        dsimp
        ext
        · simp
        · simpa using (Under.w u).symm
      right_inv := by aesop_cat
    }
  }

/-- pushout (𝟙 X) : Under X ⥤ Under X is the identity functor. -/
def pushoutId {X : C} : pushout (𝟙 X) ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := Under _)) (mapPushoutAdj (𝟙 _)) ).symm
    (Under.mapId X).symm

/-- pushout commutes with composition (up to natural isomorphism). -/
def pullbackComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : pushout (f ≫ g) ≅ pushout f ⋙ pushout g :=
  (conjugateIsoEquiv ((mapPushoutAdj _).comp (mapPushoutAdj _)) (mapPushoutAdj _) ).symm
    (mapComp f g).symm

instance pushoutIsLeftAdjoint {X Y : C} (f : X ⟶ Y) : (pushout f).IsLeftAdjoint  :=
  ⟨_, ⟨mapPushoutAdj f⟩⟩

/-- If `X : C` is initial, then the under category of `X` is equivalent to `C`. -/
def equivalenceOfIsInitial {C : Type*} [Category C] {X : C} (hX : IsInitial X) :
    Under X ≌ C where
  functor := Under.forget X
  inverse := { obj Y := Under.mk (hX.to Y), map f := Under.homMk f }
  unitIso := NatIso.ofComponents (fun Y ↦ Under.isoMk (Iso.refl _) (hX.hom_ext _ _))
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _)

end Under

end CategoryTheory
