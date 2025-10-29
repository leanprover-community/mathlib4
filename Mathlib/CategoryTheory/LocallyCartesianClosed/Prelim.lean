/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Preliminaries for the theory of locally cartesian closed categories

# Main declarations

- `ChosenPullback` : a typeclass over morphims `f : Y ⟶ X` in `C` which provides a
choice of pullback functor `Over X ⥤ Over Y` along `f` as a right adjoint to `Over.map f`.

## Main results

- We prove that `ChosenPullback` has good closure properties, e.g., isos have chosen pullbacks, and
  composition of morphisms with chosen pullbacks have chosen pullbacks.

- `Over.ChosenPullback.isPullback` proves that the reindexing squares of an instance of
  `ChosenPullback g` are pullback squares.

- `binaryFanIsBinaryProduct` shows that the binary fan constructed from the projections of
  `ChosenPullback` is a binary product in `Over X`, and computably so!

- We prove that in cartesian monoidal categories, morphisms to the terminal object and the product
  projections have chosen pullbacks.

- We prove that in the category of types, all morphisms have chosen pullbacks.
  See `Limits.Types.chosenPullback`. Moreover, these chosen pullbacks have good definitional
  properties as they agree with the explicit pullbacks in the category of types defined by
  `Types.PullbackObj`.

- `Over.mapPulbackNatIsoTensorRight` constructs a natural isomorphism between the pull-push
  composition `(pullback Z.hom) ⋙ (map Z.hom)` and the functor `tensorRight Z`.

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

open Category Limits CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

namespace Over

/-- A choice of pullback functor `Over X ⥤ Over Y` along a morphism `f : Y ⟶ X` in `C`
as a right adjoint to the functor `Over.map f`. -/
class ChosenPullback {Y X : C} (f : Y ⟶ X) where
  /-- The pullback functor along `f`. -/
  pullback : Over X ⥤ Over Y
  /-- The adjunction between `Over.map f` and `pullback f`. -/
  mapPullbackAdj (f) : Over.map f ⊣ pullback

namespace ChosenPullback

/-- `ChosenPullback (Over.mk f).hom` from  `ChosenPullback f`. -/
def ofOverMk {Y X : C} (f : Y ⟶ X) [ChosenPullback f] : ChosenPullback (Over.mk f).hom :=
  inferInstanceAs (ChosenPullback f)

/-- Relating the existing noncomputable `HasPullbacksAlong` typeclass to `ChosenPullback`. -/
@[simps]
noncomputable def ofHasPullbacksAlong {Y X : C} (f : Y ⟶ X) [HasPullbacksAlong f] :
    ChosenPullback f where
  pullback := Over.pullback f
  mapPullbackAdj := Over.mapPullbackAdj f

/-- The identity morphism has a chosen pullback. -/
@[simps]
def id {X : C} : ChosenPullback (𝟙 X) where
  pullback := 𝟭 _
  mapPullbackAdj := (Adjunction.id).ofNatIsoLeft (Over.mapId _).symm

/-- The composition of morphisms with chosen pullbacks has a chosen pullback. -/
@[simps]
def comp {Z Y X : C} (f : Y ⟶ X) (g : Z ⟶ Y)
    [ChosenPullback f] [ChosenPullback g] : ChosenPullback (g ≫ f) where
  pullback := pullback f ⋙ pullback g
  mapPullbackAdj := ((mapPullbackAdj g).comp (mapPullbackAdj f)).ofNatIsoLeft
    (Over.mapComp g f).symm

/-- In cartesian monoidal categories, any morphism to the terminal object has a chosen pullback. -/
@[simps]
def cartesianMonoidalCategoryToTerminal [CartesianMonoidalCategory C] {X : C} (f : X ⟶ 𝟙_ C) :
    ChosenPullback f where
  pullback.obj Y := Over.mk (fst X Y.left)
  pullback.map {Y Z} g := Over.homMk (X ◁ g.left)
  mapPullbackAdj := Adjunction.mkOfHomEquiv
    { homEquiv U Z :=
      { toFun z := Over.homMk (lift U.hom z.left)
        invFun u := Over.homMk (u.left ≫ snd X Z.left)
        left_inv k := by simp
        right_inv k := by
          ext
          dsimp
          ext
          · simpa using k.w.symm
          · aesop } }

/-- In cartesian monoidal categories, the second product projections `snd` have chosen pullbacks. -/
@[simps]
def cartesianMonoidalCategorySnd [CartesianMonoidalCategory C] {X Y : C} :
    ChosenPullback (snd X Y : X ⊗ Y ⟶ Y) where
  pullback.obj Z := Over.mk (X ◁ Z.hom)
  pullback.map g := Over.homMk (X ◁ g.left)
  mapPullbackAdj.unit.app T := Over.homMk (lift (T.hom ≫ fst _ _) (𝟙 _))
  mapPullbackAdj.counit.app U := Over.homMk (snd _ _)

section PullbackFromChosenPullbacks

variable {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullback g]

/-- The underlying object of the chosen pullback along `g` of `f`. -/
abbrev pullbackObj := ((pullback g).obj (Over.mk f)).left

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk f`. -/
abbrev fst' := (mapPullbackAdj g).counit.app (Over.mk f)

/-- The first projection from the chosen pullback along `g` of `f` to the domain of `f`. -/
abbrev fst : pullbackObj f g ⟶ Y := fst' f g |>.left

theorem fst'_left : (fst' f g).left = fst f g := by
  rfl

/-- The second projection from the chosen pullback along `g` of `f` to the domain of `g`. -/
abbrev snd : pullbackObj f g ⟶ Z := (pullback g).obj (Over.mk f) |>.hom

/-- A morphism in `Over X` from the chosen pullback along `g` of `f` to `Over.mk g`. -/
abbrev snd' : (Over.map g).obj ((pullback g).obj (Over.mk f)) ⟶ (Over.mk g) :=
  Over.homMk (snd f g)

theorem snd'_left : (snd' f g).left = snd f g := by
  rfl

variable {f g}

@[reassoc]
theorem condition : fst f g ≫ f = snd f g ≫ g :=
  Over.w (fst' f g)

variable (f g) in

@[ext]
theorem hom_ext {W : C} {φ₁ φ₂ : W ⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _)
    (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ snd _ _) :
    φ₁ = φ₂ := by
  let adj := mapPullbackAdj g
  let U : Over Z := Over.mk (φ₁ ≫ snd f g)
  let φ₁' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₁
  let φ₂' : U ⟶ (pullback g).obj (Over.mk f) := Over.homMk φ₂ (by simpa using h₂.symm)
  have : (adj.homEquiv U _).symm φ₁' = (adj.homEquiv U _).symm φ₂' := by
    simp [adj.homEquiv_symm_apply]
    apply (forget X).map_injective
    simpa using h₁
  have : φ₁' = φ₂' := by
    apply (adj.homEquiv U _).symm.injective
    exact this
  apply congr_arg CommaMorphism.left this

section Lift

variable {W : C} (a : W ⟶ Y) (b : W ⟶ Z) (h : a ≫ f = b ≫ g)

/-- Given morphisms `a : W ⟶ Y` and `b : W ⟶ Z` satisfying `a ≫ f = b ≫ g`,
constructs the unique morphism `W ⟶ pullbackObj f g`. -/
def lift : W ⟶ pullbackObj f g :=
  (((mapPullbackAdj g).homEquiv (Over.mk b) (Over.mk f)) (Over.homMk a)).left

@[reassoc (attr := simp)]
theorem lift_fst : lift a b h ≫ fst f g = a := by
  let adj := mapPullbackAdj g
  let a' : (Over.map g).obj (Over.mk b) ⟶ Over.mk f := Over.homMk a h
  let l' := adj.homEquiv (Over.mk b) (Over.mk f) (Over.homMk a)
  have : (Over.map g).map l' ≫ fst' f g = a' := by
    simp [← Adjunction.homEquiv_counit]
    aesop
  apply congr_arg CommaMorphism.left this

@[reassoc (attr := simp)]
theorem lift_snd : lift a b h ≫ snd f g = b := by
  simp [lift]

theorem isPullback {Y Z X : C} (f : Y ⟶ X) (g : Z ⟶ X) [ChosenPullback g] :
    IsPullback (fst f g) (snd f g) f g where
  w := condition
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift s.fst s.snd s.condition)
      (by simp) (by simp) (by aesop)⟩

end Lift

end PullbackFromChosenPullbacks

section ChosenPullbackForTypes

universe u

@[simps]
instance _root_.Limits.Types.chosenPullback {X Y : Type u} (f : Y ⟶ X) :
    ChosenPullback (C:= Type u) f where
  pullback.obj Z := Over.mk (fun p : Types.PullbackObj Z.hom f => p.1.2)
  pullback.map {W Z} k := Over.homMk (fun p => ⟨(k.left p.1.1, p.1.2), by
    have : Z.hom (k.left p.1.1) = W.hom p.1.1  := congr_fun k.w p.1.1
    rw [this]
    simpa using p.2⟩)
  mapPullbackAdj.unit.app P := Over.homMk (fun p => ⟨(p, P.hom p), by simp⟩)
  mapPullbackAdj.unit.naturality := by
    intro P Q g
    ext p
    have := congr_fun g.w p
    simpa using this
  mapPullbackAdj.counit.app U := by
    simp
    exact Over.homMk (fun p => p.1.1)

variable {X Y Z : Type u} {f : Y → X} {g : Z → X}

example : pullbackObj (C:= Type u) f g = Types.PullbackObj f g := rfl

example : fst (C:= Type u) g f = fun p => p.1.1 := by rfl

example : snd (C:= Type u) g f = fun p => p.1.2 := by rfl

example {W : Type u} {a : W → Y} {b : W → Z} {h : ∀ w : W, f (a w) = g (b w)} :
    lift (C:= Type u) a b (types_ext _ _ h) = fun w => ⟨(a w, b w), h w⟩ := by rfl

end ChosenPullbackForTypes

section BinaryProduct

variable {X : C} (Y Z : Over X) [ChosenPullback Z.hom]

/-- The canonical pullback cone constructed by `π_` and `μ_` is a limit cone.
Note: The source of noncomputability is the non-constructive implementation of `IsPullback`.
Otherwise, `ChosenPullback.isPullback` is constructive.
-/
noncomputable def isLimitPullbackCone [ChosenPullback Z.hom] :
    IsLimit (isPullback Y.hom Z.hom |>.cone) :=
  isPullback Y.hom Z.hom |>.isLimit

/-- The binary fan provided by `fst'` and `snd'`. -/
def binaryFan [ChosenPullback Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P:= Over.mk (Y := pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

@[simp]
theorem binaryFan_pt :
    (binaryFan Y Z).pt = Over.mk (Y:= pullbackObj Y.hom Z.hom) (snd Y.hom Z.hom ≫ Z.hom) := by
  rfl

@[simp]
theorem binaryFan_pt_hom : (binaryFan Y Z).pt.hom = snd Y.hom Z.hom ≫ Z.hom := by
  rfl

/-- The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`. -/
def binaryFanIsBinaryProduct :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [w u, w v])) (by simp))
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b => by simp [binaryFan]; aesop)
    (fun a b m h₁ h₂ => by
      apply Over.OverMorphism.ext
      simp only [homMk_left]
      apply hom_ext (f:= Y.hom) (g:= Z.hom) <;> aesop)

attribute [local instance] Over.cartesianMonoidalCategory

/-- The push-pull object `Σ_ Y (Δ_ Y Z)` is isomorphic to the cartesian product `Y ⊗ Z`
in the slice category `Over X`. -/
@[simps!]
noncomputable def mapPullbackIsoProd [HasPullbacks C] :
    (map Z.hom).obj ((pullback Z.hom).obj Y) ≅ Y ⊗ Z :=
  IsLimit.conePointUniqueUpToIso
    (binaryFanIsBinaryProduct Y Z) (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor

attribute [local instance] ofHasPullbacksAlong in
/-- Given a morphism `g : W ⟶ X` and an object `Y` over `X`, the object
`(map g).obj ((pullback g).obj Y)` is isomorphic to the cartesian product of `Y` and `Over.mk f`. -/
noncomputable def mapPullackIsoProd' [HasPullbacks C] {W : C} (g : W ⟶ X) :
    (map g).obj ((pullback g).obj Y) ≅ Y ⊗ Over.mk g :=
  mapPullbackIsoProd Y (Over.mk g)

attribute [local instance] ofHasPullbacksAlong in
@[reassoc (attr := simp)]
theorem mapPullbackIsoProd_hom_comp_fst [HasPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ CartesianMonoidalCategory.fst Y Z = fst' Y.hom Z.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (binaryFanIsBinaryProduct Y Z)
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor ⟨.left⟩

attribute [local instance] ofHasPullbacksAlong in
@[reassoc (attr := simp)]
theorem mapPullbackIsoProd_hom_comp_snd [HasPullbacks C] :
    (mapPullbackIsoProd Y Z).hom ≫ CartesianMonoidalCategory.snd Y Z = snd' Y.hom Z.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (binaryFanIsBinaryProduct Y Z)
    (pullback.isLimit _ _).pullbackConeEquivBinaryFanFunctor ⟨.right⟩

end BinaryProduct

section TensorRight

variable {X : C}

attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] ofHasPullbacksAlong in
/-- The pull-push composition `pullback Z.hom ⋙ map Z.hom` is naturally isomorphic
to the right tensor product functor `_ ⊗ Z` in the slice category `Over X`. -/
noncomputable def pullbackMapNatIsoTensorRight [HasPullbacks C] (Z : Over X) :
    pullback Z.hom ⋙ map Z.hom ≅ tensorRight Z :=
  NatIso.ofComponents
    (fun Y => mapPullbackIsoProd Y Z)
    (by
      intro Y Y' f
      simp
      ext1 <;> simp_rw [assoc]
      · rw [whiskerRight_fst]
        ext
        rw [mapPullbackIsoProd_hom_comp_fst, mapPullbackIsoProd_hom_comp_fst_assoc]
        simp [fst']
      · simp_rw [whiskerRight_snd]
        ext
        iterate rw [mapPullbackIsoProd_hom_comp_snd]
        simp [snd])

attribute [local instance] ofHasPullbacksAlong in
@[simp]
theorem Over.pullbackMapNatIsoTensorRight_hom_app [HasPullbacks C] {Y : Over X} (Z : Over X) :
    (pullbackMapNatIsoTensorRight Z).hom.app Y = (mapPullbackIsoProd Y Z).hom := by
  aesop

end TensorRight

end ChosenPullback

end Over

/-- The functor from `C` to `Over (⊤_ C)` which sends `X : C` to `terminal.from X`. -/
@[simps! obj_left obj_hom map_left]
def Functor.toOverTerminal (X : C) (h : IsTerminal X) : C ⥤ Over X where
  obj X := Over.mk <| h.from X
  map {X Y} f := Over.homMk f

/-- The slice category over the terminal object is equivalent to the original category. -/
def equivOverTerminal (X : C) (h : IsTerminal X) : Over X ≌ C where
  functor := Over.forget _
  inverse := Functor.toOverTerminal X h
  unitIso := NatIso.ofComponents fun _ =>
    Over.isoMk (Iso.refl _) (by apply IsTerminal.hom_ext;exact h)
  counitIso := NatIso.ofComponents fun X => Iso.refl _
  functor_unitIso_comp := by aesop

namespace Over

@[simp]
theorem star_map [HasBinaryProducts C] {X : C} {Y Z : C} (f : Y ⟶ Z) :
    (star X).map f = Over.homMk (prod.map (𝟙 X) f) := by
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
noncomputable def starIsoToOverTerminal [HasBinaryProducts C] (X : C) (h : IsTerminal X) :
    star X ≅ Functor.toOverTerminal X h :=
  rightAdjointUniq (forgetAdjStar X) (equivOverTerminal X h |>.toAdjunction)

/-- A natural isomorphism between the functors `star X` and `star Y ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
noncomputable def starPullbackIsoStar [HasBinaryProducts C] {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] :
    star Y ⋙ pullback f ≅ star X :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjStar Y)) (forgetAdjStar X) (mapForget f)

theorem iteratedSliceBackward_forget {X : C} (f : Over X) :
    iteratedSliceBackward f ⋙ forget f = Over.map f.hom :=
  rfl

attribute [local instance] Over.cartesianMonoidalCategory

/-- The functor `Over.pullback f : Over Y ⥤ Over X` is naturally isomorphic to
`Over.star : Over Y ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivlanece `Over (Over.mk f) ⥤ Over X`. -/
noncomputable def starIteratedSliceForwardIsoPullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    star (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjStar _))
  (mapPullbackAdj f) (eqToIso (iteratedSliceBackward_forget (Over.mk f)))

end Over

end CategoryTheory
