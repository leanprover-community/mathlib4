/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.Adjunction.Over
import Mathlib.CategoryTheory.Closed.Cartesian

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally cartesian closed categories. For instance
the following two definitions are equivalent:

1. A locally cartesian closed category is a category `C` such that for every object `I`
  the slice category `Over I` is cartesian closed.

2. Equivalently, a locally cartesian closed category is a category with pullbacks such that
  the base change functor `Over.pullback f`, for every morphisms `f : I ⟶ J`, has a right adjoint.
  This condition is equivalent to exponentiability of `f` in `Over J`. The right adjoint of
  `Over.pullback f` is called the pushforward functor.

In this file we prove the equivalence of these conditions.

## Implementation notes

The type class `LocallyCartesianClosed` extends `HasPushforwards` with the extra data carrying the
witness of cartesian closedness of the slice categories. `HasPushforwards.cartesianClosedOver` shows
that the cartesian closed structure of the slices follows from existence of pushforwards
along all morphisms. As such when instantiating a `LocallyCartesianClosed` structure,
providing the the cartesian closed structure of the slices is not necessary and it will be filled
in automatically. See `LocallyCartesianClosed.mkOfHasPushforwards` and
`LocallyCartesianClosed.mkOfCartesianClosedOver`.

The advanatge we obtain from this implementation is that when using a
`LocallyCartesianClosed` structure, both the pushforward functor and the cartesian closed structure
of slices are automatically available.

## Main results

- `pushforwardFunctor` constructs, in a category with cartesian closed slices, the pushforward
  functor along a morphism `f : I ⟶ J`. On objects, this functors is defined
  as a certain pullback in the slice category `Over J`.
- `CartesianClosedOver.hasPushforwards` shows that `pushforwardFunctor` is right adjoint to the
  pullback functor.
- `HasPushforwards.cartesianClosedOver` shows that, in a category with pushforwards along all
  morphisms, the slice categories are cartesian closed.
- `LocallyCartesianClosed.cartesianClosed` proves that a locally cartesian closed category with a
  terminal object is cartesian closed.
- `LocallyCartesianClosed.overLocallyCartesianClosed` shows that the slices of a locally cartesian
  closed category are locally cartesian closed.

## Notations

- `Π X Y` is a notation for the pushforward of `Y` along `X` in the slice category `Over I`. It is
  defined as `(pushforward X.hom).obj Y`.

-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category MonoidalCategory Limits Functor Adjunction Over

universe v u

variable {C : Type u} [Category.{v} C]

/-- A morphism `f : I ⟶ J` is exponentiable if the pullback functor `Over J ⥤ Over I`
has a right adjoint. -/
class ExponentiableMorphism [HasPullbacks C] {I J : C} (f : I ⟶ J) where
  /-- The pushforward functor -/
  pushforward : Over I ⥤ Over J
  /-- The pushforward functor is right adjoint to the pullback functor -/
  adj : pullback f ⊣ pushforward := by infer_instance

namespace ExponentiableMorphism

variable [HasPullbacks C]

instance OverMkHom {I J : C} {f : I ⟶ J} [ExponentiableMorphism f] :
    ExponentiableMorphism (Over.mk f).hom := by
  dsimp
  infer_instance

/-- The identity morphisms `𝟙` are exponentiable. -/
@[simps]
instance id {I : C} : ExponentiableMorphism (𝟙 I) where
  pushforward := 𝟭 (Over I)
  adj := ofNatIsoLeft (F:= 𝟭 _) Adjunction.id (pullbackId).symm

/-- The conjugate iso between the pushforward of the identity and the identity of the
pushforward. -/
def pushfowardIdIso {I : C} : (id : ExponentiableMorphism (𝟙 I)).pushforward ≅ 𝟭 (Over I) :=
  conjugateIsoEquiv Adjunction.id id.adj pullbackId

/-- The composition of exponentiable morphisms is exponentiable. -/
def comp {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  ExponentiableMorphism (f ≫ g) where
  pushforward := (pushforward f) ⋙ (pushforward g)
  adj := ofNatIsoLeft (gexp.adj.comp fexp.adj) (pullbackComp f g).symm

/-- The conjugate isomorphism between pushforward of the composition and the composition of
pushforward functors. -/
def pushforwardCompIso {I J K : C} (f : I ⟶ J) (g : J ⟶ K)
  [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
  (comp f g).pushforward ≅ fexp.pushforward ⋙ gexp.pushforward  :=
  conjugateIsoEquiv (gexp.adj.comp fexp.adj) ((comp f g).adj) (pullbackComp f g)

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

/-- A morphism with a pushforward is exponentiable in the slice category. -/
instance exponentiableOverMk [HasFiniteWidePullbacks C] {X I : C} (f : X ⟶ I)
    [ExponentiableMorphism f] :
    Exponentiable (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := by
    apply ofNatIsoLeft _ _
    · exact Over.pullback f ⋙ Over.map f
    · exact Adjunction.comp ExponentiableMorphism.adj (Over.mapPullbackAdj _)
    · exact sigmaReindexNatIsoTensorLeft (Over.mk f)

end ExponentiableMorphism

variable (C)

/-- A category `HasPushforwards` if every morphism is exponentiable. -/
class HasPushforwards [HasFiniteWidePullbacks C] where
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace HasPushforwards

open Over

variable {C} [HasFiniteWidePullbacks C] [HasPushforwards C]

def pushforward {I J : C} (f : I ⟶ J) :
    Over I ⥤ Over J :=
  (exponentiable f).pushforward

attribute [scoped instance] ChosenFiniteProducts.ofFiniteProducts

/-- In a category with pushforwards along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver
    [HasFiniteWidePullbacks C] [HasPushforwards C] (I : C) :
    CartesianClosed (Over I) where
  closed X := {
    rightAdj := (Over.pullback X.hom ⋙ (HasPushforwards.exponentiable X.hom).pushforward)
    adj := ofNatIsoLeft (F := (Over.pullback X.hom ⋙ Over.map X.hom))
      (((HasPushforwards.exponentiable X.hom).adj).comp (Over.mapPullbackAdj X.hom))
      (Over.sigmaReindexNatIsoTensorLeft _)
  }

section Notation

def pushforwardObj {I : C} (X : Over I) (Y : Over (X.left)) : Over I :=
  (pushforward X.hom).obj Y

set_option quotPrecheck false in
scoped notation " Π_ " => pushforwardObj

end Notation

end HasPushforwards

namespace CartesianClosedOver

open Over Reindex IsIso ChosenFiniteProducts CartesianClosed HasPushforwards

variable {C} [HasFiniteWidePullbacks C] {I J : C} [CartesianClosed (Over J)] (f : I ⟶ J)

/-- The first leg of a cospan constructing a pullback diagram in `Over J` used to define
the pushforward along `f`. -/
def curryId : Over.mk (𝟙 J) ⟶ (Over.mk f ⟹ Over.mk f) :=
  CartesianClosed.curry (fst _ _)

/-- The second leg of a cospan constructing a pullback diagram in `Over J` used to define
the pushforward along `f`. -/
def expMapFstProj (X : Over I) :
    (Over.mk f ⟹ ((Over.map f).obj X)) ⟶ (Over.mk f ⟹ Over.mk f) :=
  (exp _).map (Over.homMk X.hom)

/-- Pushforward along `f : I ⟶ J` as a pullback in `Over J`. -/
def pushforwardObj (X : Over I) : Over J :=
  pullback (curryId f) (expMapFstProj f X)

/-- The functoriality of the pushforward derived form the functoriality of the exponentiation and
the functoriality of the pullback construction in the slice category `Over J`. -/
def pushforwardMap {X X' : Over I} (u : X ⟶ X') :
    (pushforwardObj f X) ⟶ (pushforwardObj f X') := by
  refine pullback.map _ _ _ _ (𝟙 (Over.mk (𝟙 J)))
      ((exp _).map ((Over.map f).map u)) (𝟙 (Over.mk f ⟹ Over.mk f))
    ?_ ?_
  · simp
  · unfold expMapFstProj
    simp only [comp_id, ← (exp (Over.mk f)).map_comp]
    congr
    simp [map_obj_left, mk_left, map_map_left, homMk_left, w]

/-- The pushforward functor `(Over I) ⥤ (Over J)` of a morphism `f : I ⟶ J` in a category `C`
using the cartesian closedness of `Over J`. -/
@[simps]
def pushforwardFunctor :
    (Over I) ⥤ (Over J) where
  obj X := pullback (curryId f) (expMapFstProj f X)
  map u := pushforwardMap f u
  map_id X := by
    apply pullback.hom_ext
    · simp [pushforwardMap]
    · simp [pushforwardMap, expMapFstProj]
  map_comp := by
    apply fun X Y Z u v ↦ pullback.hom_ext _ _
    · unfold pushforwardMap
      simp
    · simp [pushforwardMap, expMapFstProj]

variable {f}

/-- An auxiliary morphism used to define the currying of a morphism in `Over I` to a morphism
in `Over J`. See `pushforwardCurry`. -/
def pushforwardCurryAux {X : Over I} {A : Over J} (u : (Over.pullback f).obj A ⟶ X) :
    A ⟶ (Over.mk f ⟹ (Over.map f).obj X) :=
  CartesianClosed.curry ((sigmaReindexIsoProd _ _).inv ≫ (Over.map f).map u)

/-- The currying of `(Over.pullback f).obj A ⟶ X` in `Over I` to a morphism
`A ⟶ (pushforward f).obj X` in `Over J`. -/
def pushforwardCurry {X : Over I} {A : Over J} (u : (Over.pullback f).obj A ⟶ X) :
    A ⟶ (pushforwardFunctor f).obj X := by
  apply pullback.lift ((mkIdTerminal (X := J)).from A) (pushforwardCurryAux u)
    ((uncurry_injective (A := Over.mk f)) _)
  rw [uncurry_natural_left, curryId, pushforwardCurryAux]
  simp [uncurry_curry, expMapFstProj, uncurry_natural_right]
  have sigmaReindexIsoProd_inv_comp_pi :
      (sigmaReindexIsoProd (Over.mk f) A).inv ≫ (π_ (Over.mk f) A) = fst (Over.mk f) A := by
    rw [Iso.inv_comp_eq]
    simp [sigmaReindexIsoProd_hom_comp_fst]
  have : ((Over.map f).map u ≫ (homMk X.hom rfl : (Over.map f).obj X ⟶ Over.mk f)) =
      π_ (Over.mk f) A  := OverMorphism.ext (by aesop_cat)
  simp_rw [this, sigmaReindexIsoProd_inv_comp_pi]

/-- The uncurrying of `A ⟶ (pushforward f).obj X` in `Over J` to a morphism
`(Over.pullback f).obj A ⟶ X` in `Over I`. -/
def pushforwardUncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforwardFunctor f).obj X) :
    (Over.pullback f).obj A ⟶ X := by
  let v₁ : A ⟶ Over.mk (𝟙 J) := v ≫ (pullback.fst ..)
  let v₂ : A ⟶ ((Over.mk f) ⟹ ((Over.map f).obj X)) := v ≫ pullback.snd ..
  have w : (mkIdTerminal (X := J)).from A ≫ (curryId f) =
      v₂ ≫ (expMapFstProj f X) := by
    rw [IsTerminal.hom_ext mkIdTerminal ( (mkIdTerminal (X := J)).from A) v₁]
    simp [v₁, v₂, pullback.condition]
  dsimp [curryId, expMapFstProj] at w
  have w' := homEquiv_naturality_right_square (F := MonoidalCategory.tensorLeft (Over.mk f))
    (adj := exp.adjunction (Over.mk f)) _ _ _ _ w
  simp [CartesianClosed.curry] at w'
  refine Sigma.overHomMk ((sigmaReindexIsoProd _ _).hom ≫ (CartesianClosed.uncurry v₂)) ?_
  · dsimp [CartesianClosed.uncurry] at *
    simp [Over.Sigma.fst, Over.Sigma]
    rw [← w']
    simp [sigmaReindexIsoProd_hom_comp_fst]

@[simp]
theorem pushforward_curry_uncurry {X : Over I} {A : Over J} (v : A ⟶ (pushforwardFunctor f).obj X) :
    pushforwardCurry (pushforwardUncurry v) = v := by
  dsimp [pushforwardCurry, pushforwardUncurry, pushforwardCurryAux]
  let v₁ : A ⟶ Over.mk (𝟙 J) := v ≫ (pullback.fst ..)
  let v₂ : A ⟶ ((Over.mk f) ⟹ ((Over.map f).obj X)) := v ≫ pullback.snd _ _
  apply pullback.hom_ext
  · simp
    rw [IsTerminal.hom_ext mkIdTerminal ((mkIdTerminal (X := J)).from A) v₁]
  · simp
    apply (CartesianClosed.curry_eq_iff _ _).mpr
    ext
    simp [Sigma.overHomMk]
    rw [← assoc]
    have inv_hom_id := (sigmaReindexIsoProd (Over.mk f) A).inv_hom_id
    apply_fun (Over.forget _).map at inv_hom_id
    rw [(Over.forget _).map_id, (Over.forget _).map_comp] at inv_hom_id
    simp at inv_hom_id
    exact inv_hom_id ▸ id_comp (CartesianClosed.uncurry v₂).left

theorem pushforward_uncurry_curry {X : Over I} {A : Over J} (u : (Over.pullback f).obj A ⟶ X) :
    pushforwardUncurry (pushforwardCurry u) = u := by
  unfold pushforwardCurry pushforwardUncurry pushforwardCurryAux
  ext
  simp [Sigma.overHomMk]

end CartesianClosedOver

attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

/-- A category with cartesian closed slices has pushforwards along all morphisms. -/
instance CartesianClosedOver.hasPushforwards [HasFiniteWidePullbacks C]
    [Π (I : C), CartesianClosed (Over I)] : HasPushforwards C where
  exponentiable {I J} f := {
    pushforward := pushforwardFunctor f
    adj := mkOfHomEquiv {
      homEquiv A X := {
        toFun := pushforwardCurry
        invFun := pushforwardUncurry
        left_inv := pushforward_uncurry_curry
        right_inv := pushforward_curry_uncurry
      }
      homEquiv_naturality_left_symm := by
        intro A' A X g v
        unfold pushforwardUncurry
        dsimp
        have natiso := (Over.sigmaReindexNatIsoTensorLeft (Over.mk f)).hom.naturality g
        simp only [Over.sigmaReindexNatIsoTensorLeft_hom_app, tensorLeft_map] at natiso
        simp_rw [CartesianClosed.uncurry_natural_left, MonoidalCategory.whiskerLeft_comp]
        simp_rw [← assoc, ← natiso]
        simp [Sigma.overHomMk]
        rfl
      homEquiv_naturality_right := by
        intro A X' X u g
        unfold pushforwardCurry
        dsimp
        apply pullback.hom_ext (IsTerminal.hom_ext mkIdTerminal _ _)
        unfold pushforwardCurryAux pushforwardMap
        simp [pullback.lift_snd]
        rw [← CartesianClosed.curry_natural_right, assoc]
    }
  }

/-- A category with `FiniteWidePullbacks` is locally cartesian closed if every morphisms in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [HasFiniteWidePullbacks C] extends
    HasPushforwards C where
  cartesianClosedOver : Π (I : C), CartesianClosed (Over I) := HasPushforwards.cartesianClosedOver

namespace LocallyCartesianClosed

open Over Sigma Reindex HasPushforwards

variable {C} [HasFiniteWidePullbacks C]

attribute [scoped instance] hasFiniteLimits_of_hasTerminal_and_pullbacks

instance mkOfHasPushforwards [HasPushforwards C] : LocallyCartesianClosed C where

instance mkOfCartesianClosedOver [Π (I : C), CartesianClosed (Over I)] :
  LocallyCartesianClosed C where

variable [LocallyCartesianClosed C]

/-- The exponential `X^^A` in the slice category `Over I` is isomorphic to the pushforward of the
pullback of `X` along `A`. -/
def expIso {I : C} (A X : Over I) :  Π_ A (Δ_ A X) ≅ X^^A := Iso.refl _

/-- The dependent evaluation morphisms. -/
abbrev ev {I : C} (X : Over I) (Y : Over X.left) : Δ_ X (Π_ X Y) ⟶ Y :=
  (exponentiable X.hom).adj.counit.app Y

/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
def cartesianClosed [HasTerminal C] :
    CartesianClosed C := cartesianClosedOfEquiv <| equivOverTerminal C

/-- The slices of a locally cartesian closed category are locally cartesian closed. -/
def overLocallyCartesianClosed (I : C) : LocallyCartesianClosed (Over I) := by
  apply (config := { allowSynthFailures:= true}) mkOfCartesianClosedOver
  intro X
  exact cartesianClosedOfEquiv (C := Over (X.left)) X.iteratedSliceEquiv.symm

end LocallyCartesianClosed

end CategoryTheory
