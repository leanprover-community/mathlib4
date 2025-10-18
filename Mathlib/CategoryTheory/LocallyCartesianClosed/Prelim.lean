/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
-- import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Preliminaries for the theory of locally cartesian closed categories

# Main declarations

## Notation

- `Σ_ Y Z` : metaprogram notation for `(Over.map Y.hom).obj Z` (dependent sum)
- `Δ_ f Z` : metaprogram notation for `(Over.pullback f).obj Z` (pullback/reindexing)
- `μ X Y` : is notation for `fstProj : sigma Y (reindex Y Z) ⟶ Z`
- `π X Y` : is notation for `sndProj : sigma Y (reindex Y Z) ⟶ Y`

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

class ChosenPullback {Y X : C} (f : Y ⟶ X) where
  pullback : Over X ⥤ Over Y
  mapPullbackAdj : Over.map f ⊣ pullback

instance {Y X : C} (f : Y ⟶ X) [h : HasPullbacksAlong f] : ChosenPullback f where
  pullback := Over.pullback f
  mapPullbackAdj := mapPullbackAdj f

/--
Syntax for the sigma notation `Σ_ Y Z` which represents `(Over.map Y.hom).obj Z`.
This provides a more natural syntax for dependent sums in the Over category.

The notation `Σ_ Y Z` where `Y : Over X` and `Z : Over Y.left` produces an object
in `Over X` representing the dependent sum. This is the categorical analogue of
the dependent sum type `Σ (y : Y), Z y` in type theory.

Example usage:
- If `Y : Over X` corresponds to a map `y : Y.left → X`
- And `Z : Over Y.left` corresponds to a map `z : Z.left → Y.left`
- Then `Σ_ Y Z : Over X` corresponds to the composite `Z.left → Y.left → X`
-/
syntax "Σ_" term:max term:max : term

/--
This macro provides syntactic sugar for the dependent sum construction in over categories.
When you write `Σ_ Y Z`, it gets expanded to the functor application that creates
the dependent sum object.

The expansion works as follows:
1. `Y : Over X` provides the base fibration `Y.left → X`
2. `Z : Over Y.left` provides the fiber `Z.left → Y.left`
3. `Σ_ Y Z` creates `(Over.map Y.hom).obj Z : Over X` which represents the total space
with morphism `Z.left → Y.left → X`
-/
macro_rules
| `(Σ_ $Y $Z) => `((Over.map ($Y).hom).obj $Z)

variable {X : C} (Y : Over X) (Z : Over Y.left)

/-- The notation `Σ_ Y Z` is definitionally equal to `(Over.map Y.hom).obj Z`. -/
lemma sigma_def : Σ_ Y Z = (Over.map Y.hom).obj Z := rfl

/-- The underlying morphism of `Σ_ Y Z` is the composition `Z.hom ≫ Y.hom`. -/
@[simp]
lemma sigma_hom : (Σ_ Y Z).hom = Z.hom ≫ Y.hom :=
  map_obj_hom

/-- The sigma notation is functorial in the second argument. -/
def sigma_map {Z Z' : Over Y.left} (f : Z ⟶ Z') : Σ_ Y Z ⟶ Σ_ Y Z' :=
  (Over.map Y.hom).map f

/--
Syntax for the pullback notation `Δ_ f Z` which represents `(Over.pullback f).obj Z`.
This provides a more natural syntax for reindexing/substitution in the Over category.

The notation `Δ_ f Z` where `f : Y → X` and `Z : Over X` produces an object
in `Over Y` representing the pullback. This is the categorical analogue of
substitution `Z[f]` in type theory.

Example usage:
- If `f : Y → X` is a morphism in the base category
- And `Z : Over X` corresponds to a map `z : Z.left → X`
- Then `Δ_ f Z : Over Y` corresponds to the pullback along `f`
-/
syntax "Δ_" term:max term:max : term

/--
Metaprogram that expands `Δ_ f Z` to `(Over.pullback f).obj Z`.

This macro provides syntactic sugar for the pullback/reindexing construction in over categories.
When you write `Δ_ f Z`, it gets expanded to the functor application that creates
the pullback object.

The expansion works as follows:
1. `f : Y → X` provides the morphism to pull back along
2. `Z : Over X` provides the object to be pulled back
3. `Δ_ f Z` creates `(Over.pullback f).obj Z : Over Y` which represents the pulled back object

This is the categorical analogue of substitution in dependent type theory,
where pulling back along `f` corresponds to substituting `f` in the dependent type.
-/
macro_rules
| `(Δ_ $Y $Z) => `((Over.pullback ($Y).hom).obj $Z)

variable {X Y : C} (Y : Over X) (Z : Over X) [HasPullbacksAlong Y.hom]

/-- The notation `Δ_ f Z` is definitionally equal to `(Over.pullback f).obj Z`. -/
lemma pullback_def : Δ_ Y Z = (Over.pullback Y.hom).obj Z := rfl

/-- The underlying morphism of `Δ_ f Z` is `pullback.snd Z.hom f`. -/
@[simp]
lemma pullback_hom : (Δ_ Y Z).hom = pullback.snd Z.hom Y.hom := by
  rfl

/-- The pullback notation is functorial in the second argument. -/
def pullback_map {Z Z' : Over X} (g : Z ⟶ Z') : Δ_ Y Z ⟶ Δ_ Y Z' :=
  (Over.pullback Y.hom).map g

/-- The notation for the first projection of the reindexed sigma object.
`π_` and `μ_` fit in the following pullback square:
```
                        μ_ Y Z
      Σ (reindex Y Z) -----------> Z
            |                      |
            |                      |
     π_ Y Z |                      | Z.hom
            |                      |
            v                      v
            Y -------------------> X
```
-/
def reindexFst (Y Z : Over X) [HasPullbacksAlong Y.hom] :
    (Σ_ Y (Δ_ Y Z)) ⟶ Y :=
  Over.homMk (pullback.snd Z.hom Y.hom) (by aesop)

scoped notation " π_ " => reindexFst

-- @[simp]
lemma reindexFst_left {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    (π_ Y Z).left = pullback.snd Z.hom Y.hom := by
  rfl

/-- The notation for the second projection of the reindexed sigma object.
`π_` and `μ_` fit in the following pullback square:

```
                        μ_ Y Z
      Σ (reindex Y Z) -----------> Z
            |                      |
            |                      |
     π_ Y Z |                      | Z.hom
            |                      |
            v                      v
            Y -------------------> X
```
-/
def reindexSnd (Y Z : Over X) [HasPullbacksAlong Y.hom] :
    Σ_ Y (Δ_ Y Z) ⟶ Z :=
  (mapPullbackAdj Y.hom).counit.app Z

scoped notation " μ_ " => reindexSnd

-- @[simp]
lemma reindexSnd_homMk_pullback_fst {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    μ_ Y Z = Over.homMk (pullback.fst Z.hom Y.hom) (by simp [pullback.condition]) := by
  simp [reindexSnd]

-- @[simp]
lemma reindexSnd_left {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    (μ_ Y Z).left = pullback.fst Z.hom Y.hom := by
  simp [reindexSnd, mapPullbackAdj_counit_app]

section BinaryProduct

open CartesianMonoidalCategory MonoidalCategory Limits

variable [HasFiniteWidePullbacks C] {X : C}

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
def isBinaryProductSigmaReindex (Y Z : Over X) :
    IsLimit <| BinaryFan.mk (P := Σ_ Y (Δ_ Y Z)) (π_ Y Z) (μ_ Y Z) := by
  refine IsLimit.mk (?lift) ?fac ?uniq
  · intro s
    fapply Over.homMk
    · exact pullback.lift (s.π.app ⟨.right⟩).left (s.π.app ⟨ .left ⟩).left (by aesop)
    · aesop
  · rintro s ⟨⟨l⟩|⟨r⟩⟩ <;> apply Over.OverMorphism.ext <;>

  · intro s m h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp?
    · refine (congr_arg CommaMorphism.left (h ⟨ .right⟩))
    · exact congr_arg CommaMorphism.left (h ⟨ .left ⟩)

attribute [local instance] CartesianMonoidalCategory.ofFiniteProducts

instance (X : C) : CartesianMonoidalCategory (Over X) := by
  infer_instance

/-- The object `sigma Y (reindex Y Z)` is isomorphic to the binary product `Y ⊗ Z`
in `Over X`. -/
@[simps!]
def mapPullackIsoProd (Y Z : Over X) :
    Σ_ Y (Δ_ Y Z) ≅ Y ⊗ Z := by
  apply IsLimit.conePointUniqueUpToIso (isBinaryProductSigmaReindex Y Z) (prodIsProd Y Z)

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the object
`(map f).obj ((pullback f).obj Y)` is isomorphic to the binary product of `Over.mk f` and `Y`. -/
def mapPullackIsoProd' {Y : C} (f : Y ⟶ X) (Z : Over X) :
    (map f).obj ((pullback f).obj Z) ≅ Over.mk f ⊗ Z :=
  mapPullackIsoProd (Over.mk f) _

@[reassoc (attr := simp)]
lemma mapPullackIsoProd_hom_comp_fst {Y Z : Over X} :
    (mapPullackIsoProd Y Z).hom ≫ fst Y Z = π_ Y Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.left⟩

@[reassoc (attr := simp)]
lemma mapPullackIsoProd_hom_comp_snd {Y Z : Over X} :
    (mapPullackIsoProd Y Z).hom ≫ snd Y Z = μ_ Y Z :=
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
def Over.sigmaReindexNatIsoTensorLeft (Y : Over X) : pullback Y.hom ⋙ map Y.hom ≅ tensorLeft Y :=
  NatIso.ofComponents
    (fun Z => mapPullackIsoProd Y Z)
    (by
      intro Z Z' f
      simp
      ext1 <;> simp_rw [assoc]
      · simp_rw [whiskerLeft_fst]
        iterate rw [mapPullackIsoProd_hom_comp_fst]
        ext
        simp
      · simp_rw [whiskerLeft_snd]
        iterate rw [mapPullackIsoProd_hom_comp_snd, ← assoc, mapPullackIsoProd_hom_comp_snd]
        ext
        simp [reindexSnd])

@[simp]
lemma Over.sigmaReindexNatIsoTensorLeft_hom_app {Y : Over X} (Z : Over X) :
    (Over.sigmaReindexNatIsoTensorLeft Y).hom.app Z = (mapPullackIsoProd Y Z).hom := by
  aesop

end TensorLeft

/-- The functor from `C` to `Over (⊤_ C)` which sends `X : C` to `terminal.from X`. -/
@[simps! obj_left obj_hom map_left]
def Functor.toOverTerminal (X : C) (h : IsTerminal X) : C ⥤ Over X where
  obj X := Over.mk <| h.from X
  map {X Y} f := Over.homMk f

/-- The slice category over the terminal object is equivalent to the original category. -/
def equivOverTerminal (X : C) (h : IsTerminal X) : Over (X) ≌ C where
  functor := Over.forget _
  inverse := Functor.toOverTerminal X h
  unitIso := NatIso.ofComponents fun _ =>
    Over.isoMk (Iso.refl _) (by apply IsTerminal.hom_ext;exact h)
  counitIso := NatIso.ofComponents fun X => Iso.refl _
  functor_unitIso_comp := by aesop

namespace Over

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

namespace Over

open Adjunction

/-- `star (⊤_ C) : C ⥤ Over (⊤_ C)` is naturally isomorphic to `Functor.toOverTerminal C`. -/
def starIsoToOverTerminal [HasBinaryProducts C] (X : C) (h : IsTerminal X) :
    star X ≅ Functor.toOverTerminal X h :=
  rightAdjointUniq (forgetAdjStar X) (equivOverTerminal X h |>.toAdjunction)

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
