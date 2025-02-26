/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.Basic


/-!
# Beck-Chevalley natural transformations and natural isomorphisms
-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans ExponentiableMorphism

universe v u

namespace Over
variable {C : Type u} [Category.{v} C]

section BeckChevalleyTrans

--h ≫ g = f ≫ k -- h → k
theorem map_square_eq {X Y Z W : C}
    (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) :
    Over.map h ⋙ Over.map g = Over.map f ⋙ Over.map k := by
  rw [← mapComp_eq, sq.w, mapComp_eq]

/-- Promoting the equality `mapSquare_eq` of functors to an isomorphism.
```
        Over X -- .map h -> Over Z
           |                  |
   .map f  |         ≅        | .map g
           ↓                  ↓
        Over Y -- .map k -> Over W
```
The Beck Chevalley transformations are iterated mates of this isomorphism in the
horizontal and vertical directions. -/
def mapSquareIso {X Y Z W : C}
    (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) :
    Over.map h ⋙ Over.map g ≅ Over.map f ⋙ Over.map k :=
  eqToIso (map_square_eq f h g k sq)

variable [HasPullbacks C]

/-- The Beck-Chevalley natural transformation constructed as a mate of `mapSquareIso`:
```
          Over X -- .map h -> Over Z
             ↑                  ↑
.pullback f  |         ↘        | .pullback g
             |                  |
          Over Y -- .map k -> Over W
```
-/
def pullbackBeckChevalleySquare {X Y Z W : C}
    (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) :
    pullback f ⋙ map h ⟶ map k ⋙ pullback g :=
  mateEquiv (mapPullbackAdj f) (mapPullbackAdj g) (mapSquareIso f h g k sq).hom

/--
Special case of the Beck-Chevalley natural transformation above:
```
          Over X --.forget X -> C
             ↑                  |
.pullback f  |         ↘        | 𝟭
             |                  |
          Over Y --.forget Y -> C
```
-/
def pullbackBeckChevalleyTriangle {X Y : C} (f : X ⟶ Y) :
    pullback f ⋙ forget X ⟶ forget Y := by
  let iso := (mapForget f).inv
  rw [← Functor.comp_id (forget X)] at iso
  exact (mateEquiv (mapPullbackAdj f) (Adjunction.id)) iso

/-- The isomorphism between the pullbacks along a commutative square.  This is constructed as the
conjugate of the `mapSquareIso`. -/
def pullbackSquareIso {X Y Z W : C} (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) : pullback k ⋙ pullback f ≅ pullback g ⋙ pullback h :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (mapPullbackAdj k))
  ((mapPullbackAdj h).comp (mapPullbackAdj g)) (mapSquareIso f h g k sq)

/-- The Beck-Chevalley natural transformations in a square of pullbacks and pushforwards.-/
def pushforwardBeckChevalleySquare {X Y Z W : C} (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
    pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f :=
  conjugateEquiv ((mapPullbackAdj k).comp gexp.adj) (fexp.adj.comp (mapPullbackAdj h))
    (pullbackBeckChevalleySquare f h g k sq)

/-- The conjugate isomorphism between the pushforwards along a commutative square. -/
def pushforwardSquareIso {X Y Z W : C} (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
    (sq : CommSq h f g k) [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g]
    [hexp : ExponentiableMorphism h] [kexp : ExponentiableMorphism k] :
    pushforward h ⋙ pushforward g ≅ pushforward f ⋙ pushforward k :=
  conjugateIsoEquiv (gexp.adj.comp hexp.adj) (kexp.adj.comp fexp.adj) (pullbackSquareIso f h g k sq)

end BeckChevalleyTrans

end Over

section BeckChevalleyIsos

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

open IsPullback Over

/-- Calculating the counit components of mapAdjunction. -/
theorem mapPullbackAdj.counit.app_pullback.fst {X Y : C} (f : X ⟶ Y) (y : Over Y) :
    ((mapPullbackAdj f).counit.app y).left = pullback.fst _ _ := by simp

def pullbackNatTrans.app.map [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).obj ((pullback h ⋙ map f).obj y) ⟶ (forget X).obj ((map k ⋙ pullback g).obj y) :=
  pullback.map y.hom h (y.hom ≫ k) g (𝟙 y.left) f k (Eq.symm (id_comp (y.hom ≫ k))) w.symm

theorem pullbackBeckChevalleyComponent_pullbackMap [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (w : f ≫ g = h ≫ k) (y : Over Y) :
    (forget X).map ((pullbackBeckChevalleySquare f g h k w).app y) =
    pullbackNatTrans.app.map f g h k w y := by
  dsimp
  ext <;> simp [pullbackNatTrans.app.map, pullbackBeckChevalleySquare, mapSquareIso]

-- NB: I seem to have symmetry of HasPullback but not IsPullback
-- SH: yes, we do have that: it is given by the function `.flip`
theorem pullbackNatTrans_of_IsPullback_component_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (y : Over Y) :
    IsIso ((forget X).map ((pullbackBeckChevalleySquare f g h k pb.w).app y)) := by
  rw [pullbackBeckChevalleyComponent_pullbackMap f g h k pb.w y]
  have P := pasteHorizIsPullback rfl (isLimit pb.flip) (pullbackIsPullback y.hom h)
  have Q := pullbackIsPullback (y.hom ≫ k) g
  let conemap :
      (PullbackCone.mk _ _
        (show pullback.fst y.hom h ≫ y.hom ≫ k = (pullback.snd y.hom h ≫ f) ≫ g by
          simp [reassoc_of% pullback.condition (f := y.hom) (g := h), pb.w])) ⟶
      (PullbackCone.mk
        (pullback.fst (y.hom ≫ k) g) (pullback.snd _ _) pullback.condition) := {
    hom := pullbackNatTrans.app.map f g h k pb.w y
    w := by
      rintro (_|(left|right)) <;>
      · unfold pullbackNatTrans.app.map
        simp
  }
  haveI mapiso := IsLimit.hom_isIso P Q conemap
  exact ((Cones.forget _).map_isIso conemap)

/-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pullbackBeckChevalleySquare_of_IsPullback_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z) (pb : IsPullback f h g k) :
    IsIso (pullbackBeckChevalleySquare f g h k pb.w) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro y
  have := pullbackNatTrans_of_IsPullback_component_is_iso f g h k pb y
  apply (forget_reflects_iso (X := X)).reflects
    ((pullbackBeckChevalleySquare f g h k pb.w).app y)

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleyNatTrans_of_IsPullback_is_iso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (gexp : ExponentiableMorphism g) (hexp : ExponentiableMorphism h) :
    IsIso (pushforwardBeckChevalleyNatTrans f g h k pb.w gexp hexp) := by
  have := pullbackBeckChevalleySquare_of_IsPullback_is_iso f g h k pb
  apply conjugateEquiv_iso

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleyNatTrans_of_isPullback_isIso [HasPullbacks C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Z) (h : W ⟶ Y) (k : Y ⟶ Z)
    (pb : IsPullback f h g k)
    (gexp : ExponentiableMorphism g) (hexp : ExponentiableMorphism h) :
    IsIso (pushforwardBeckChevalleyNatTrans f g h k pb.w gexp hexp) := by
  have := pullbackBeckChevalleySquare_of_IsPullback_is_iso f g h k pb
  apply conjugateEquiv_iso

end BeckChevalleyIsos
