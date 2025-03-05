/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.Basic

/-!
# Beck-Chevalley natural transformations and natural isomorphisms

We construct the so-called Beck-Chevalley natural transformations and isomorphisms through the
repeated applications of the mate construction in the vertical and horizontal directions.

## Main declarations

- `Over.mapSquareIso`: The isomorphism between the functors `Over.map h ⋙ Over.map g` and
  `Over.map f ⋙ Over.map k` for a commutative square of morphisms `h ≫ g = f ≫ k`.
- `Over.pullbackBeckChevalleySquare`: The Beck-Chevalley natural transformation for a commutative
  square of morphisms `h ≫ g = f ≫ k` in the slice category `Over Y`.
- `Over.pullbackBeckChevalleyTriangle`: The Beck-Chevalley natural transformation for the identity
  morphism `f : X ⟶ Y` in the slice category `Over Y`.
- `Over.pullbackSquareIso`: The isomorphism between the pullbacks along a commutative square of
  morphisms `h ≫ g = f ≫ k`.
- `Over.pushforwardBeckChevalleySquare`: The Beck-Chevalley natural transformation for a commutative
  square of morphisms `h ≫ g = f ≫ k` in the slice category `Over Y`.
- `Over.pushforwardSquareIso`: The isomorphism between the pushforwards along a commutative
  square of morphisms `h ≫ g = f ≫ k`.

## Implementation notes
The lax naturality squares are constructed by the mate equivalence `mateEquiv` and
the natural iso-squares are constructed by the more special conjugation equivalence
`conjugateIsoEquiv`.

## References

The methodology and the notation of the successive mate constructions to obtain the Beck-Chevalley
natural transformations and isomorphisms are based on the following paper:

* [A 2-categorical proof of Frobenius for fibrations defined from a generic point,
in Mathematical Structures in Computer Science, 2024][Hazratpour_Riehl_2024]

-/

noncomputable section
namespace CategoryTheory

open Category Functor Adjunction Limits NatTrans ExponentiableMorphism

universe v u

namespace Over

variable {C : Type u} [Category.{v} C]

section BeckChevalleyTrans

--h ≫ g = f ≫ k -- h → k
theorem map_square_eq {X Y Z W : C} {f : X ⟶ Y} {h : X ⟶ Z} {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k := by aesop) :
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
def mapSquareIso {X Y Z W : C} {f : X ⟶ Y} {h : X ⟶ Z} {g : Z ⟶ W} {k : Y ⟶ W}
    (sq : CommSq h f g k := by aesop) :
    Over.map h ⋙ Over.map g ≅ Over.map f ⋙ Over.map k :=
  eqToIso (map_square_eq sq)

variable [HasPullbacks C]

variable {X Y Z W : C} (f : X ⟶ Y) (h : X ⟶ Z) (g : Z ⟶ W) (k : Y ⟶ W)
(sq : CommSq h f g k)

/-- The Beck-Chevalley natural transformation constructed as a mate of `mapSquareIso`:
```
          Over X -- .map h -> Over Z
             ↑                  ↑
.pullback f  |         ↘        | .pullback g
             |                  |
          Over Y -- .map k -> Over W
```
-/
def pullbackBeckChevalleySquare :
    pullback f ⋙ map h ⟶ map k ⋙ pullback g :=
  mateEquiv (mapPullbackAdj f) (mapPullbackAdj g) (mapSquareIso sq).hom

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
def pullbackBeckChevalleyTriangle :
    pullback f ⋙ forget X ⟶ forget Y := by
  let iso := (mapForget f).inv
  rw [← Functor.comp_id (forget X)] at iso
  exact (mateEquiv (mapPullbackAdj f) (Adjunction.id)) iso

/-- The isomorphism between the pullbacks along a commutative square.  This is constructed as the
conjugate of the `mapSquareIso`.
```
          Over X ←--.pullback h-- Over Z
             ↑                       ↑
.pullback f  |          ≅            | .pullback g
             |                       |
          Over Y ←--.pullback k-- Over W
```
-/
def pullbackSquareIso : pullback k ⋙ pullback f ≅ pullback g ⋙ pullback h :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (mapPullbackAdj k))
  ((mapPullbackAdj h).comp (mapPullbackAdj g)) (mapSquareIso sq)

/-- The Beck-Chevalley natural transformations in a square of pullbacks and pushforwards.
```
              Over X ←-.pullback h-- Over Z
                |                     |
.pushforward f  |          ↖          | .pushforward g
                ↓                     ↓
              Over Y ←-.pullback k-- Over W
```
-/
def pushforwardBeckChevalleySquare
    [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
    pushforward g ⋙ pullback k ⟶ pullback h ⋙ pushforward f :=
  conjugateEquiv ((mapPullbackAdj k).comp gexp.adj) (fexp.adj.comp (mapPullbackAdj h))
    (pullbackBeckChevalleySquare f h g k sq)
-- (pullbackBeckChevalleySquare f h g k sq)

/-- The conjugate isomorphism between the pushforwards along a commutative square.
```
            Over X --.pushforward h -→ Over Z
               |                        |
.pushforward f |           ≅            | .pushforward g
               ↓                        ↓
            Over Y --.pushforward k -→ Over W
```
-/
def pushforwardSquareIso [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g]
    [hexp : ExponentiableMorphism h] [kexp : ExponentiableMorphism k] :
    pushforward h ⋙ pushforward g ≅ pushforward f ⋙ pushforward k :=
  conjugateIsoEquiv (gexp.adj.comp hexp.adj) (kexp.adj.comp fexp.adj) (pullbackSquareIso f h g k sq)
-- pullbackSquareIso f h g k sq

end BeckChevalleyTrans

end Over

section BeckChevalleyComponents

variable {C : Type u} [Category.{v} C]

namespace IsPullback

/--
In a commutative cube diagram if the front, back and the right face are pullback squares then
the the left face is also a pullback square.
```
          P ---p₂------  X
         /|             /|
    i₄  / |       i₂   / |
       /  |           /  | f₂
      Q ----q₂-----  Z   |
      |   |          |   |
      |   W -f₁----- | - S
  q₁  |  /           |  /
      | / i₁         | / i₃
      |/             |/
      Y ----g₁------ T
```
-/
theorem left_face_of_comm_cube {P W X Y Q Z S T : C}
    (p₁ : P ⟶ W) (p₂ : P ⟶ X) (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (q₁ : Q ⟶ Y) (q₂ : Q ⟶ Z) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (i₄ : P ⟶ Q)
    (sq_top : CommSq p₂ i₄ i₂ q₂)
    (sq_bot : CommSq f₁ i₁ i₃ g₁)
    (sq_left : CommSq i₄ p₁ q₁ i₁)
    (pb_back : IsPullback p₂ p₁ f₂ f₁)
    (pb_front : IsPullback q₂ q₁ g₂ g₁)
    (pb_right : IsPullback i₂ f₂ g₂ i₃) :
    IsPullback i₄ p₁ q₁ i₁ := by
  have paste_horiz_pb := paste_horiz pb_back pb_right
  rw [sq_top.w, sq_bot.w] at paste_horiz_pb
  exact of_right paste_horiz_pb sq_left.w pb_front

/--
In a commutative cube diagram if the front, the left and the right face are pullback squares then
the the back face is also a pullback square.
```
          P ---p₂------  X
         /|             /|
    i₄  / |       i₂   / |
       /  |           /  | f₂
      Q ----q₂-----  Z   |
      |   |          |   |
      |   W -f₁----- | - S
  q₁  |  /           |  /
      | / i₁         | / i₃
      |/             |/
      Y ----g₁------ T
```
-/
theorem back_face_of_comm_cube {P W X Y Q Z S T : C}
    (p₁ : P ⟶ W) (p₂ : P ⟶ X) (f₁ : W ⟶ S) (f₂ : X ⟶ S)
    (q₁ : Q ⟶ Y) (q₂ : Q ⟶ Z) (g₁ : Y ⟶ T) (g₂ : Z ⟶ T)
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T) (i₄ : P ⟶ Q)
    (sq_top : CommSq p₂ i₄ i₂ q₂)
    (sq_bot : CommSq f₁ i₁ i₃ g₁)
    (sq_back : CommSq p₂ p₁ f₂ f₁)
    (pb_front : IsPullback q₂ q₁ g₂ g₁)
    (pb_left : IsPullback i₄ p₁ q₁ i₁)
    (pb_right : IsPullback i₂ f₂ g₂ i₃) :
    IsPullback p₂ p₁ f₂ f₁ := by
  have paste_horiz_pb := paste_horiz pb_left pb_front
  rw [← sq_top.w, ← sq_bot.w] at paste_horiz_pb
  exact of_right paste_horiz_pb sq_back.w pb_right

/-- The pullback comparison map `pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃` between two
pullback squares is an isomorphism if  `i₁` is an isomorphism and one of the
connecting morphisms is an isomorphism. -/
theorem pullback.map_isIso_of_pullback_right_of_comm_cube {W X Y Z S T : C}
    (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasPullback g₁ g₂]
    (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (sq_bot : CommSq f₁ i₁ i₃ g₁)
    [IsIso i₁] (pb_right : IsPullback i₂ f₂ g₂ i₃) :
    IsIso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ sq_bot.w pb_right.w.symm) := by
  let m := pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ sq_bot.w pb_right.w.symm
  have sq_top : CommSq (pullback.snd f₁ f₂) m i₂ (pullback.snd g₁ g₂) := by
    aesop
  have sq_left : CommSq m (pullback.fst f₁ f₂) (pullback.fst g₁ g₂) i₁ := by
    aesop
  let pb' : IsPullback m (pullback.fst f₁ f₂)  (pullback.fst g₁ g₂) i₁ := by
    apply IsPullback.left_face_of_comm_cube (sq_top := sq_top) (sq_bot := sq_bot)
      (sq_left := sq_left) (pb_back := (IsPullback.of_hasPullback f₁ f₂).flip)
      (pb_front := (IsPullback.of_hasPullback g₁ g₂).flip)
      (pb_right := pb_right)
  have is_iso : IsIso m := isIso_fst_of_isIso pb'
  exact is_iso

end IsPullback

variable [HasPullbacks C]

variable {X Y Z W : C} {f : X ⟶ Y} {h : X ⟶ Z} {g : Z ⟶ W} {k : Y ⟶ W}
(sq : CommSq h f g k) (A : Over Y)

open IsPullback Over

theorem mapPullbackAdj.counit_app_left  :
    ((mapPullbackAdj f).counit.app A).left = pullback.fst _ _ := by
  simp only [mapPullbackAdj_counit_app, homMk_left]

@[simp]
theorem pullbackBeckChevalleySquare_app :
    (pullbackBeckChevalleySquare f h g k sq).app A =
    Over.homMk (pullback.map _ _ (A.hom ≫ k) _ _ h k (id_comp _).symm sq.w.symm) (by aesop) := by
  ext
  simp only [homMk_left, pullbackBeckChevalleySquare, mapSquareIso]
  aesop

theorem forget_map_pullbackBeckChevalleySquare :
    (forget Z).map ((pullbackBeckChevalleySquare f h g k sq).app A) =
    pullback.map _ _ _ _ (𝟙 _) h k (id_comp _).symm sq.w.symm := by
  simp only [forget_map, pullbackBeckChevalleySquare_app, homMk_left]

theorem isIso_forgetMapPullbackBeckChevalleySquare_of_isPullback (pb : IsPullback h f g k) :
    IsIso ((forget Z).map ((pullbackBeckChevalleySquare f h g k pb.toCommSq).app A)) := by
  rw [forget_map_pullbackBeckChevalleySquare (sq:= pb.toCommSq)]
  let paste_horiz_pb := paste_horiz (IsPullback.of_hasPullback f A.hom) pb
  apply pullback.map_isIso_of_pullback_right_of_comm_cube
  assumption'
  aesop

/-- The pullback Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pullbackBeckChevalleySquare_of_isPullback_isIso (pb : IsPullback h f g k) :
    IsIso (pullbackBeckChevalleySquare f h g k pb.toCommSq) := by
  apply (config := { allowSynthFailures:= true}) NatIso.isIso_of_isIso_app
  intro A
  have := isIso_forgetMapPullbackBeckChevalleySquare_of_isPullback A pb
  exact ReflectsIsomorphisms.reflects (forget Z)
    ((pullbackBeckChevalleySquare f h g k pb.toCommSq).app A)

/-- The pushforward Beck-Chevalley natural transformation of a pullback square is an isomorphism. -/
instance pushforwardBeckChevalleySquare_of_isPullback_isIso (pb : IsPullback h f g k)
    [fexp : ExponentiableMorphism f] [gexp : ExponentiableMorphism g] :
    IsIso (pushforwardBeckChevalleySquare f h g k pb.toCommSq) := by
  have := pullbackBeckChevalleySquare_of_isPullback_isIso pb
  apply conjugateEquiv_iso


end BeckChevalleyComponents

end CategoryTheory

end
