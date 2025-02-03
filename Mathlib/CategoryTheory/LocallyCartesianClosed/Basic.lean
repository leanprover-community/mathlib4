/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/

import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Adjunction.Over

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally
cartesian closed categories.

1. A locally cartesian closed category is a category C such that all
the slices `Over I` are cartesian closed categories.

2. Equivalently, a locally cartesian closed category `C` is a category with pullbacks such that
each base change functor has a right adjoint, called the pushforward functor.

In this file we prove the equivalence of these conditions.

We also show that a locally cartesian closed category with a terminal object is cartesian closed.

Cartesian closedness of slices follows
from the exponentiability of morphisms. When instantiating a `LocallyCartesianClosed` structure,
the `overCartesianClosed` is not  necessary, and it will be filled in by default. When using the
`LocallyCartesianClosed` structure, `overCartesianClosed` can be accessed on top of
exponentiablity of all morphisms which is more ergonomic.


-/

noncomputable section

namespace CategoryTheory

open CategoryTheory Category Limits Functor Adjunction Over

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

-- attribute [local instance] monoidalOfHasFiniteProducts
-- attribute [local instance] hasFiniteWidePullbacks_of_hasFiniteLimits
-- attribute [local instance] ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
--attribute [local instance] monoidalOfChosenFiniteProducts
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
    · exact mapPulbackNatIsoTensorLeft (Over.mk f)

end ExponentiableMorphism

-- attribute [local instance] monoidalOfChosenFiniteProducts
-- attribute [local instance] hasFiniteWidePullbacks_of_hasFiniteLimits
-- attribute [local instance] ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
attribute [local instance] ChosenFiniteProducts.ofFiniteProducts

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

/-- In a category with pushforwards for all morphisms, every slice `Over I` is cartesian closed. -/
instance cartesianClosedOver
    [HasFiniteWidePullbacks C] [HasPushforwards C] (I : C) :
    CartesianClosed (Over I) where
  closed X := {
    rightAdj := (Over.pullback X.hom ⋙ (HasPushforwards.exponentiable X.hom).pushforward)
    adj := ofNatIsoLeft (F := (Over.pullback X.hom ⋙ Over.map X.hom))
      (((HasPushforwards.exponentiable X.hom).adj).comp (Over.mapPullbackAdj X.hom))
      (Over.mapPulbackNatIsoTensorLeft _)
  }

section Notation

def pushforwardObj {I : C} (X : Over I) (Y : Over (X.left)) : Over I :=
  (pushforward X.hom).obj Y

set_option quotPrecheck false in
scoped notation " Π_ " => pushforwardObj

end Notation

end HasPushforwards

namespace CartesianClosedOver

open Over mapPullbackAdj IsIso ChosenFiniteProducts CartesianClosed

variable {C} [HasFiniteWidePullbacks C] {I J : C} [CartesianClosed (Over J)] (f : I ⟶ J)

-- [Π (I : C), CartesianClosed (Over I)]
/-- The first leg of cospan of a pullback diagram defining the pushforward object in `Over J`. -/
def curryIdTranspose : Over.mk (𝟙 J) ⟶ (Over.mk f ⟹ Over.mk f) :=
  CartesianClosed.curry (fst _ _)

/-- The second leg of cospan of a pullback diagram defining the pushforward object in `Over J`. -/
def expMapFstProj (X : Over I) :
    (Over.mk f ⟹ ((Over.map f).obj X)) ⟶ (Over.mk f ⟹ Over.mk f) :=
  (exp _).map (Over.homMk X.hom)

/-- Pushforward along `f : I ⟶ J` as a pullback in the cartesian closed slice category `Over J`. -/
def pushforwardObj (X : Over I) : Over J :=
  pullback (curryIdTranspose f) (expMapFstProj f X)

/-- The functoriality of the pushforward derived form the functoriality of the pullback
construction in the slice category `Over J`. -/
def pushforwardMap (X X' : Over I) (u : X ⟶ X') :
    (pushforwardObj f X) ⟶ (pushforwardObj f X') := by
  refine pullback.map _ _ _ _ (𝟙 (Over.mk (𝟙 J)))
      ((exp _).map ((Over.map f).map u)) (𝟙 (Over.mk f ⟹ Over.mk f))
    ?_ ?_
  · simp
  · unfold expMapFstProj
    simp only [comp_id, ← (exp (Over.mk f)).map_comp]
    congr
    simp [map_obj_left, mk_left, map_map_left, homMk_left, w]

/-- The pushforward functor constructed from cartesian closed slices. -/
@[simps]
def pushforwardFunctor :
    (Over I) ⥤ (Over J) where
  obj X := pullback (curryIdTranspose f) (expMapFstProj f X)
  map u := pushforwardMap f _ _ u
  map_id X := by
    apply pullback.hom_ext
    · simp [pushforwardMap]
    · simp [pushforwardMap, expMapFstProj]
  map_comp := by
    apply fun X Y Z u v ↦ pullback.hom_ext _ _
    · unfold pushforwardMap
      simp
    · simp [pushforwardMap, expMapFstProj]

-- def Sigma.snd (X A : Over I) (Y : Over X.left) (u : Δ_ X A ⟶ Y) [CartesianClosed (Over I)] :
--     A ⟶ (Σ_ X Y) ^^ X :=
--   CartesianClosed.curry ((mapPulbackObjIsoProd X A).inv ≫ (Over.map X.hom).map u)

def pushforwardTransposeAux [HasFiniteWidePullbacks C] (Y : Over I) (A : Over J)
    (u : (Over.pullback f).obj A ⟶ Y) :
    A ⟶ (Over.mk f ⟹ (Over.map f).obj Y) :=
  CartesianClosed.curry ((mapPulbackObjIsoProd _ _).inv ≫ (Over.map f).map u)

/-- The transpose of `(Over.pullback f).obj Y ⟶ X`. -/
def pushforwardTranspose [HasFiniteWidePullbacks C]
    (Y : Over I) (A : Over J) (u : (Over.pullback f).obj A ⟶ Y) :
    A ⟶ (pushforwardFunctor f).obj Y := by
  dsimp [pushforwardFunctor_obj]
  apply pullback.lift ((mkIdTerminal (X := J)).from A) (pushforwardTransposeAux f Y A u)
    ((uncurry_injective (A := Over.mk f)) _)
  rw [uncurry_natural_left, curryIdTranspose, pushforwardTransposeAux]
  rw [uncurry_curry, expMapFstProj, uncurry_natural_right, uncurry_curry]
  simp only [whiskerLeft_fst, mk_left, mk_hom, assoc]
  have h₁ : (mapPulbackObjIsoProd (Over.mk f) A).inv ≫ (π_ (Over.mk f) A) = fst (Over.mk f) A := by
    rw [Iso.inv_comp_eq]
    simp [mapPulbackObjIsoProd_hom_comp_fst]
  have h₂ : ((Over.map f).map u ≫ (homMk Y.hom rfl : (Over.map f).obj Y ⟶ Over.mk f)) =
    π_ (Over.mk f) A  := OverMorphism.ext (by aesop_cat)
  simp_rw [h₂, h₁]

/-- A category with cartesian closed slices has pushforwards along all morphisms. -/
instance hasPushforwards [Π (I : C), CartesianClosed (Over I)] : HasPushforwards C where
  exponentiable {I J} f := {
    pushforward := pushforwardFunctor f
    adj := mkOfHomEquiv {
      homEquiv X Y := {
        toFun := _
        invFun := _
        left_inv := _
        right_inv := _
      }
      homEquiv_naturality_left_symm := _
      homEquiv_naturality_right := _
    }
  }

end CartesianClosedOver












variable (C)

/-- A category with `FiniteWidePullbacks` is locally cartesian closed if every morphisms in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [HasFiniteWidePullbacks C] extends
    HasPushforwards C where
  cartesianClosedOver : Π (I : C), CartesianClosed (Over I) := HasPushforwards.cartesianClosedOver

namespace LocallyCartesianClosed

open Over

variable {C} [HasFiniteWidePullbacks C] [LocallyCartesianClosed C]

def pushforward {I J : C} (f : I ⟶ J) :
    Over I ⥤ Over J :=
  (HasPushforwards.exponentiable f).pushforward

section

def pushforwardObj {I : C} (X : Over I) (Y : Over (X.left)) : Over I :=
  (pushforward X.hom).obj Y

set_option quotPrecheck false in
scoped notation " Π_ " => pushforwardObj

end

/-- The exponential `X^^A` in the slice category `Over I` is isomorphic to the pushforward of the
pullback of `X` along `A`. -/
def expIso {I : C} (A X : Over I) : X^^A ≅ Π_ A (Δ_ A X) := Iso.refl _




-- def pushfowardIdObjIso {I : C} (X : Over I) : Π_ (Over.mk (𝟙 I)) X = X := by
--   simp [pushforwardObj]
--   simp [pushforward]
--   have := Functor.congr_obj (ExponentiableMorphism.id_pushforward) X
--   simp only [Functor.id_obj] at this
--   rw [this]

#check Iso.refl




  -- refine .mk _ fun X ↦ .mk X (Over.pullback X.hom ⋙ (HasPushforwards.exponentiable X.hom).pushforward)(ofNatIsoLeft (F := ?functor )
  --   ?adj ?iso )
  -- case functor => exact (Over.pullback f.hom ⋙ Over.map f.hom)
  -- case adj => exact ((adj f.hom).comp (Over.mapPullbackAdj f.hom))
  -- case iso => exact NatOverProdIso _


end LocallyCartesianClosed






end CategoryTheory
