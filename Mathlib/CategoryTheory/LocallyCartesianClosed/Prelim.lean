/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
-- import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
-- import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Preliminaries for the theory of locally cartesian closed categories

# Main declarations

- `ChosenPullback` : a typeclass over morphims `f : Y ⟶ X` in `C` which provides a
choice of pullback functor `Over X ⥤ Over Y` along `f` as a right adjoint to `Over.map f`.

## Notation

- `Σ_ Y Z` : a convenient notation for `(Over.map Y.hom).obj Z` (dependent sum)
- `Δ_ f Z` : a convenient notation for `(Over.pullback f).obj Z` (pullback/reindexing)
- `π X Y` : a convenient notation for `Σ_ Y (Δ_ Y Z) ⟶ Y` (the first projection)
- `μ X Y` : a convenient notation for `Σ_ Y (Δ_ Y Z) ⟶ Z` (the second projection)


## Main results

- `Over.ChosenPullback.isPullback` proves that the morphisms `μ_` and `π_`, defined from the
the data `mapPullbackAdj` of adjunction `Over.map f ⊣ Over.pullback f`, form a pullback square.

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

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category Limits Comonad CartesianMonoidalCategory MonoidalCategory Limits

variable {C : Type u₁} [Category.{v₁} C]

namespace Over

class ChosenPullback {Y X : C} (f : Y ⟶ X) where
  pullback : Over X ⥤ Over Y
  mapPullbackAdj : Over.map f ⊣ pullback

namespace ChosenPullback

instance ofOverMk {Y X : C} (f : Y ⟶ X) [ChosenPullback f] : ChosenPullback (Over.mk f).hom := by
  dsimp [Over.mk]
  infer_instance

@[simps]
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [h : HasPullbacksAlong f] :
    ChosenPullback f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- In a cartesian monoidal category, the morphisms to the terminal object have a chosen pullback.-/
instance ofCartesianMonoidalCategory [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullback f where
      pullback := {
        obj Y := Over.mk (fst X Y.left)
        map {Y Z} f := Over.homMk (X ◁ f.left)
      }
      mapPullbackAdj := sorry

/--
Notation for dependent sums in the Over category.
The notation `Σ_ Y Z` where `Y : Over X` and `Z : Over Y.left` produces an object
in `Over X` representing the analogue of dependent sum in type theory.
-/
syntax "Σ_" term:max term:max : term

macro_rules
| `(Σ_ $Y $Z) => `((Over.map ($Y).hom).obj $Z)

/--
Notation for reindexing/substitution in the Over category.
The notation `Δ_ f Z` where `f : Y → X` and `Z : Over X` produces an object
in `Over Y` representing the pullback. This is the categorical analogue of
substitution `Z[f]` in type theory.
-/
syntax "Δ_" term:max term:max : term

macro_rules
| `(Δ_ $Y $Z) => `((ChosenPullback.pullback ($Y).hom).obj $Z)

variable {X : C}

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
def reindexFst (Y Z : Over X) [ChosenPullback Y.hom] :
    (Σ_ Y (Δ_ Y Z)) ⟶ Y :=
  Over.homMk ((pullback Y.hom).obj Z).hom (by aesop)

lemma reindexFst_left {Y Z : Over X} [ChosenPullback Y.hom] :
    (reindexFst Y Z).left = ((pullback Y.hom).obj Z).hom := by
  rfl

@[inherit_doc]
scoped notation "π_ " => reindexFst

attribute [local instance] ofHasPullbacksAlong in
lemma reindexFst_left_eq_pullback_snd {Y Z : Over X} [HasPullbacksAlong Y.hom] :
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
def reindexSnd (Y Z : Over X) [ChosenPullback Y.hom] :
    Σ_ Y (Δ_ Y Z) ⟶ Z :=
  (mapPullbackAdj).counit.app Z

scoped notation "μ_ " => reindexSnd

attribute [local instance] ofHasPullbacksAlong in
lemma reindexSnd_left {Y Z : Over X} [HasPullbacksAlong Y.hom] :
    (μ_ Y Z).left = pullback.fst Z.hom Y.hom := by
  simp [reindexSnd, mapPullbackAdj]

lemma _root_.CommSq.of_cone_cospan {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ X} (s : Cone (cospan f g)) :
    s.π.app WalkingCospan.right ≫ g = s.π.app WalkingCospan.left ≫ f := by
  have h₁ := s.π.naturality WalkingCospan.Hom.inl
  have h₂ := s.π.naturality WalkingCospan.Hom.inr
  aesop

/-- Morphisms `μ_` and `π_` form a pullback square. -/
@[simps]
def isPullback (Y Z : Over X) [ChosenPullback Y.hom] :
    IsPullback (π_ Y Z).left (μ_ Y Z).left Y.hom Z.hom where
  w := by simp
  isLimit' := ⟨ by
    let u (s : Cone (cospan Y.hom Z.hom)) : s.pt ⟶ Y.left := s.π.app WalkingCospan.left
    let v (s : Cone (cospan Y.hom Z.hom)) : s.pt ⟶ Z.left := s.π.app WalkingCospan.right
    have comm (s : Cone (cospan Y.hom Z.hom)) : v s ≫ Z.hom = u s ≫ Y.hom :=
      CommSq.of_cone_cospan s
    let U (s : Cone (cospan Y.hom Z.hom)) := Over.mk (u s)
    let v₂ (s : Cone (cospan Y.hom Z.hom)) : Σ_Y (U s) ⟶ Z := Over.homMk (v s) (comm s)
    let v₃ (s : Cone (cospan Y.hom Z.hom)) : U s ⟶ (pullback Y.hom).obj Z :=
      (mapPullbackAdj).homEquiv (U s) Z (v₂ s)
    refine IsLimit.mk (fun s => ?lift) (fun s => ?fac) (fun s => ?uniq)
    · exact v₃ s |>.left
    · rintro (⟨⟩ | ⟨⟨⟩⟩)
      · aesop
      · have : (Over.map (Y.hom)).map (v₃ s) ≫ (π_ Y Z) = U s := by
          simp [reindexSnd]
          symm
          rw [← Adjunction.homEquiv_counit]
          simp [v₃]
        dsimp
        have hh := congr_arg CommaMorphism.left this
        simp only [Over.comp_left, v₂, v] at hh
        simpa using hh

        simpa [Over.comp_left, v₂] using hh
      · apply w
    · intro m h
      simp only [v₃]
      have hl := h WalkingCospan.left
      have hr := h WalkingCospan.right
      simp at hl hr
      let m' : U s ⟶ (pullback Y.hom).obj Z :=
        Over.homMk m (by rw [← reindexFst_left]; exact hl)
      have : m = m'.left := rfl
      rw [this]
      apply congr_arg CommaMorphism.left
      rw [Adjunction.eq_homEquiv_apply, Adjunction.homEquiv_counit]
      simp [v₂, v, reindexSnd] at *
      apply (forget X).map_injective
      simp [m', hr]
      ⟩

section BinaryProduct

variable (Y Z : Over X) [ChosenPullback Y.hom]

/-- The canonical pullback cone constructed by `π_` and `μ_`. -/
def pullbackCone : PullbackCone Y.hom Z.hom :=
  (isPullback Y Z).cone

/-- The canonical pullback cone constructed by `π_` and `μ_` is a limit cone.
Note: The source of noncomputability is the non-constructive implementation of `IsPullback`.
Otherwise, `ChosenPullback.isPullback` is constructive.
-/
noncomputable def isLimitPullbackCone : IsLimit (pullbackCone Y Z) :=
  (isPullback Y Z).isLimit

abbrev binaryFanMkMapPullback : BinaryFan Y Z :=
  BinaryFan.mk (P := Σ_ Y (Δ_ Y Z)) (π_ Y Z) (μ_ Y Z)

/-- The binary fan provided by `μ_` and `π_` is a binary product in `Over X`. -/
noncomputable def isBinaryProductPullbackMap :
    IsLimit <| binaryFanMkMapPullback Y Z := by
  have := (isLimitPullbackCone Y Z).pullbackConeEquivBinaryFanFunctor
  simp [pullbackCone] at this
  have h1 : homMk (μ_ Y Z).left = μ_ Y Z := by rfl
  have h2 : homMk (π_ Y Z).left = π_ Y Z := by rfl
  rw [binaryFanMkMapPullback, ← h1, ← h2]

  convert this
  aesop

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] braidedCategory

/-- The object `Σ_ Y (Δ_ Y Z)` is isomorphic to the binary product `Y ⊗ Z` in `Over X`. -/
@[simps!]
noncomputable def mapPullbackIsoProd [HasPullbacks C] : Σ_ Y (Δ_ Y Z) ≅ Z ⊗ Y :=
  IsLimit.conePointUniqueUpToIso
    (isBinaryProductPullbackMap Y Z) (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor

/-- Given a morphism `f : X' ⟶ X` and an object `Y` over `X`, the object
`(map f).obj ((pullback f).obj Y)` is isomorphic to the binary product of `Over.mk f` and `Y`. -/
noncomputable def mapPullackIsoProd' [HasPullbacks C] {W : C} (f : W ⟶ X) [ChosenPullback f]
    (Z : Over X) : (map f).obj ((pullback f).obj Z) ≅ Z ⊗ Over.mk f :=
  mapPullbackIsoProd (Over.mk f) _

@[reassoc (attr := simp)]
lemma sigmaReindexIsoProd_hom_comp_fst [HasPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ ((β_ Z Y).hom ≫ fst Y Z) = π_ Y Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductPullbackMap Y Z) (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor ⟨.left⟩

@[reassoc (attr := simp)]
lemma sigmaReindexIsoProd_hom_comp_snd [HasPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ snd Y Z = μ_ Y Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isBinaryProductSigmaReindex Y Z) (Limits.prodIsProd Y Z) ⟨.right⟩


end BinaryProduct

section TensorLeft

attribute [local instance] Over.cartesianMonoidalCategory

attribute [local instance] ofHasPullbacksAlong in
/-- The pull-push composition `pullback Y.hom ⋙ map Y.hom` is naturally isomorphic
to the left tensor product functor `Y ⊗ _` in `Over X`. -/
noncomputable def Over.pullbackMapNatIsoTensorLeft [HasPullbacks C] (Y : Over X) :
    pullback Y.hom ⋙ map Y.hom ≅ tensorRight Y :=
  NatIso.ofComponents
    (fun Z => mapPullbackIsoProd Y Z)
    (by
      intro Z Z' f
      simp
      ext1 <;> simp_rw [assoc]
      · simp_rw [whiskerRight_fst]
        iterate rw [mapPullackIsoProd_hom_comp_fst]
        ext
        simp [reindexFst]
      · simp_rw [whiskerRight_snd]
        iterate rw [mapPullackIsoProd_hom_comp_snd, ← assoc, mapPullackIsoProd_hom_comp_snd]
        ext
        simp [reindexSnd])

@[simp]
lemma Over.pullbackMapNatIsoTensorLeft_hom_app {Y : Over X} (Z : Over X) :
    (Over.pullbackMapNatIsoTensorLeft Y).hom.app Z = (mapPullackIsoProd Y Z).hom := by
  aesop

end TensorLeft

end ChosenPullback

end Over

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
