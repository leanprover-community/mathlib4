/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Equivalence

/-!
# Preliminaries for the theory of locally cartesian closed categories

# Main declarations

- `Sigma Y Z` is the object in `Over X` obtained by applying the functor `Over.map Y.hom`
  to `Z : Over (Y.left)`. This is the category-theoretic analogue of `Sigma` for types.
  If `Y : Over X` is given by `Y.left ⟶ X` and `Z : Over (Y.left)` is given by
  `Z.left ⟶ Y.left`, then `Sigma Y Z` is given by the composition `Z.left ⟶ Y.left ⟶ X`.

- `Reindex` is the reindexing of `Z : Over X` along `Y : Over X`. It is a syntactic sugar for
  `(Over.pullback Y.hom).obj Z`. If `Y : Over X` is given by `Y.left ⟶ X` and `Z : Over X`
  is given by `Z.left ⟶ X`, then `Reindex Y Z` is given by the pullback of `Z.left ⟶ X` along
  `Y.left ⟶ X`. This is the category-theoretic analogue of substitution for types.

## Notation

- `μ X Y` : is notation for `fstProj : Sigma Y (Reindex Y Z) ⟶ Z`
- `π X Y` : is notation for `sndProj : Sigma Y (Reindex Y Z) ⟶ Y`

## Main results

- `Over.mapPulbackNatIsoTensorLeft` constructs a natural isomorphism between the pull-push
  composition `(pullback Y.hom) ⋙ (map Y.hom)` and the left tensor product functor `tensorLeft Y`.

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

/-- `Over.Sigma Y U` a shorthand for `(Over.map Y.hom).obj U`. This is the categoy-theoretic
analogue of `Sigma` for types.
-/
abbrev Sigma {X : C} (Y : Over X) (U : Over Y.left) : Over X :=
  (map Y.hom).obj U

namespace Sigma

variable {X : C}

@[simp]
lemma hom {Y : Over X} (Z : Over Y.left) : (Sigma Y Z).hom = Z.hom ≫ Y.hom := map_obj_hom

/-- `Σ_ ` is functorial in the second argument. -/
def map {Y : Over X} {Z Z' : Over Y.left} (g : Z ⟶ Z') : Sigma Y Z ⟶ Sigma Y Z' :=
  (Over.map Y.hom).map g

@[simp]
lemma map_left {Y : Over X} {Z Z' : Over Y.left} {g : Z ⟶ Z'} :
    ((Over.map Y.hom).map g).left = g.left := Over.map_map_left

lemma map_homMk_left {Y : Over X} {Z Z' : Over Y.left} {g : Z ⟶ Z'} :
    map g = (Over.homMk g.left : Sigma Y Z ⟶ Sigma Y Z') := by
  rfl

/-- The first projection of the sigma object. -/
@[simps!]
def fst {Y : Over X} (Z : Over Y.left) : Sigma Y Z ⟶ Y := Over.homMk Z.hom

@[reassoc (attr := simp)]
lemma map_comp_fst {Y : Over X} {Z Z' : Over Y.left} (g : Z ⟶ Z') :
    (Over.map Y.hom).map g ≫ fst Z' = fst Z := by
  ext
  simp [Sigma.fst, Over.w]

/-- Promoting a morphism `g : Σ_Y Z ⟶ Σ_Y Z'` in `Over X` with `g ≫ fst Z' = fst Z`
to a morphism `Z ⟶ Z'` in `Over Y.left`. -/
def overHomMk {Y : Over X} {Z Z' : Over Y.left} (g : Sigma Y Z ⟶ Sigma Y Z')
    (w : g ≫ fst Z' = fst Z := by aesop_cat) : Z ⟶ Z' :=
  Over.homMk g.left (congr_arg CommaMorphism.left w)

end Sigma

/-- The reindexing of `Z : Over X` along `Y : Over X`, defined by pulling back `Z` along
`Y.hom : Y.left ⟶ X`. -/
abbrev Reindex {X : C} (Y : Over X) [HasPullbacksAlong Y.hom] (Z : Over X) : Over Y.left :=
  (Over.pullback Y.hom).obj Z


namespace Reindex

open Over Sigma

variable {X : C}

@[simp]
lemma hom {Y : Over X} {Z : Over X} [HasPullbacksAlong Y.hom] :
    (Reindex Y Z).hom = pullback.snd Z.hom Y.hom := by
  rfl

/-- `Reindex` is symmetric in its first and second arguments up to an isomorphism. -/
def symmetryObjIso (Y Z : Over X) [HasPullbacksAlong Y.hom] [HasPullbacksAlong Z.hom] :
    (Reindex Y Z).left ≅ (Reindex Z Y).left := pullbackSymmetry _ _

/-- The reindexed sum of `Z` along `Y` is isomorphic to the reindexed sum of `Y` along `Z` in the
category `Over X`. -/
@[simps!]
def sigmaSymmetryIso (Y Z : Over X) [HasPullbacksAlong Y.hom] [HasPullbacksAlong Z.hom] :
  Sigma Y (Reindex Y Z) ≅ Sigma Z (Reindex Z Y) := by
  apply Over.isoMk _ _
  · exact pullbackSymmetry ..
  · simp [pullback.condition]

lemma symmetry_hom {Y Z : Over X} [HasPullbacksAlong Y.hom] [HasPullbacksAlong Z.hom] :
    pullback.snd Z.hom Y.hom ≫ Y.hom =
    (pullbackSymmetry _ _).hom ≫ pullback.snd Y.hom Z.hom ≫ Z.hom  := by
  simp [← pullback.condition]

/-- The first projection out of the reindexed sigma object. -/
def fstProj (Y Z : Over X) [HasPullbacksAlong Y.hom] :
    Sigma Y (Reindex Y Z) ⟶ Y :=
  Over.homMk (pullback.snd Z.hom Y.hom) (by simp)

lemma fstProj_sigma_fst (Y Z : Over X) [HasPullbacksAlong Y.hom] :
    fstProj Y Z = Sigma.fst (Reindex Y Z) := by
  rfl

/-- The second projection out of the reindexed sigma object. -/
def sndProj (Y Z : Over X) [HasPullbacksAlong Y.hom] :
    Sigma Y (Reindex Y Z) ⟶ Z :=
  Over.homMk (pullback.fst Z.hom Y.hom) (by simp [pullback.condition])

/-- The notation for the first projection of the reindexed sigma object.
`π_` and `μ_` fit in the following pullback square:
```
                        μ_ Y Z
      Σ (Reindex Y Z) -----------> Z
            |                      |
            |                      |
     π_ Y Z |                      | Z.hom
            |                      |
            v                      v
            Y -------------------> X
```
-/
scoped notation " π_ " => fstProj

/-- The notation for the second projection of the reindexed sigma object.
`π_` and `μ_` fit in the following pullback square:

```
                        μ_ Y Z
      Σ (Reindex Y Z) -----------> Z
            |                      |
            |                      |
     π_ Y Z |                      | Z.hom
            |                      |
            v                      v
            Y -------------------> X
```
-/
scoped notation " μ_ " => sndProj

@[simp]
lemma counit_app_pullback_fst {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    μ_ Y Z = (mapPullbackAdj Y.hom).counit.app Z := by
  simp [mapPullbackAdj_counit_app]
  rfl

@[simp]
lemma counit_app_pullback_snd {Y Z : Over X} [HasPullbacksAlong Y.hom] [HasPullbacksAlong Z.hom] :
    π_ Y Z = (sigmaSymmetryIso Y Z).hom ≫ (mapPullbackAdj Z.hom).counit.app Y := by
  aesop

@[simp]
lemma counit_app_pullback_snd_eq_homMk {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    π_ Y Z = (homMk (Reindex Y Z).hom : Sigma Y (Reindex Y Z) ⟶ Y) :=
  OverMorphism.ext (by aesop)

end Reindex

section BinaryProduct

open CartesianMonoidalCategory Sigma Reindex MonoidalCategory

variable [HasFiniteWidePullbacks C] {X : C}

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
def isBinaryProductSigmaReindex (Y Z : Over X) :
    IsLimit <| BinaryFan.mk (P := Sigma Y (Reindex Y Z)) (π_ Y Z) (μ_ Y Z) := by
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

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

instance (X : C) : CartesianMonoidalCategory (Over X) := by
  infer_instance

/-- The object `Sigma Y (Reindex Y Z)` is isomorphic to the binary product `Y ⊗ Z`
in `Over X`. -/
@[simps!]
def sigmaReindexIsoProd (Y Z : Over X) :
    Sigma Y (Reindex Y Z) ≅ Y ⊗ Z := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProductSigmaReindex Y Z) (prodIsProd Y Z)

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the object
`(map f).obj ((pullback f).obj Y)` is isomorphic to the binary product of `Over.mk f` and `Y`. -/
def sigmaReindexIsoProdMk {Y : C} (f : Y ⟶ X) (Z : Over X) :
    (map f).obj ((pullback f).obj Z) ≅ Over.mk f ⊗ Z :=
  sigmaReindexIsoProd (Over.mk f) _

@[reassoc (attr := simp)]
lemma sigmaReindexIsoProd_hom_comp_fst {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ fst Y Z = π_ Y Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.left⟩

@[reassoc (attr := simp)]
lemma sigmaReindexIsoProd_hom_comp_snd {Y Z : Over X} :
    (sigmaReindexIsoProd Y Z).hom ≫ snd Y Z = μ_ Y Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.right⟩

end BinaryProduct

end Over

section TensorLeft

open MonoidalCategory Over Functor CartesianMonoidalCategory

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

variable [HasFiniteWidePullbacks C] {X : C}

/-- The pull-push composition `pullback Y.hom ⋙ map Y.hom` is naturally isomorphic
to the left tensor product functor `Y ⊗ _` in `Over X`. -/
def Over.sigmaReindexNatIsoTensorLeft (Y : Over X) :
    pullback Y.hom ⋙ map Y.hom ≅ tensorLeft Y := by
  fapply NatIso.ofComponents
  · intro Z
    simp only [const_obj_obj, Functor.id_obj, comp_obj, Over.pullback]
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

@[simp]
lemma Over.sigmaReindexNatIsoTensorLeft_hom_app {Y : Over X} (Z : Over X) :
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
    (NatIso.ofComponents fun X => Over.isoMk (Iso.refl _))
    (NatIso.ofComponents fun X => Iso.refl _)

namespace Over

variable {C}

@[simp]
lemma star_map [HasBinaryProducts C] {X : C} {Y Z : C} (f : Y ⟶ Z) :
    (star X).map f = Over.homMk (prod.map (𝟙 X) f) (by aesop) := by
  simp [star]

variable (X : C)

instance [HasBinaryProducts C] : (star X).IsRightAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`. -/
instance [HasBinaryProducts C] : (forget X).IsLeftAdjoint := ⟨_, ⟨forgetAdjStar X⟩⟩

namespace forgetAdjStar

variable [HasBinaryProducts C]

@[simp]
theorem unit_app {I : C} (X : Over I) :
    (Over.forgetAdjStar I).unit.app X = Over.homMk (prod.lift X.hom (𝟙 X.left)) := by
  ext
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

@[simp]
theorem counit_app {I : C} (X : C) : (Over.forgetAdjStar I).counit.app X = prod.snd := by
  simp [Over.forgetAdjStar, Adjunction.comp, Equivalence.symm]

theorem homEquiv {I : C} (X : Over I) (A : C) (f : X.left ⟶ A) :
    (Over.forgetAdjStar I).homEquiv X A f =
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
def starPullbackIsoStar [HasBinaryProducts C] {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f] :
    star Y ⋙ pullback f ≅ star X :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjStar Y)) (forgetAdjStar X) (mapForget f)

theorem iteratedSliceBackward_forget {X : C} (f : Over X) :
    iteratedSliceBackward f ⋙ forget f = Over.map f.hom :=
  rfl

/-- The functor `Over.pullback f : Over Y ⥤ Over X` is naturally isomorphic to
`Over.star : Over Y ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over X`. -/
def starIteratedSliceForwardIsoPullback [HasFiniteWidePullbacks C] {X Y : C} (f : X ⟶ Y) :
    star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjStar _))
  (mapPullbackAdj f) (eqToIso (iteratedSliceBackward_forget (Over.mk f)))

end Over

end CategoryTheory
