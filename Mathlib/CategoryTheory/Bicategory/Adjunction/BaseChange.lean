/-
Copyright (c) 2025 Christian Merten, Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Sites.Descent.PullbackStruct
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Monad.Comonadicity

/-!
# Base change morphisms associated to commutative squares

-/

namespace CategoryTheory

-- TODO: move
namespace CommSq

variable {C : Type*} [Category C]

def toLoc {C : Type*} [Category C] {W X Y Z : C}
    {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (sq : CommSq f g h i) :
    CommSq f.toLoc g.toLoc h.toLoc i.toLoc where
  w := by simp [← Quiver.Hom.comp_toLoc, sq.w]

section Horizontal

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
  {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
  {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
  (sq : CommSq t l m b) (sq' : CommSq t' m r b')
  {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
  (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

include ht hb sq sq'

/--
```
  X₁ ---t---> Y₁ ---t'---> Z₁
  |           |            |
  l           m            r
  |           |            |
  v           v            v
  X₂ ---b---> Y₂ ---b'---> Z₂
```
-/
lemma horiz_comp' : CommSq t'' l r b'' := ht ▸ hb ▸ sq.horiz_comp sq'

end Horizontal

section Vertical

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
  {t : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} {b : X₃ ⟶ Y₃}
  {l : X₁ ⟶ X₂} {l' : X₂ ⟶ X₃}
  {r : Y₁ ⟶ Y₂} {r' : Y₂ ⟶ Y₃}
  (sq : CommSq t l r m)
  (sq' : CommSq m l' r' b)
  {l'' : X₁ ⟶ X₃} {r'' : Y₁ ⟶ Y₃}
  (hl : l ≫ l' = l'') (hr : r ≫ r' = r'')

include hl hr sq sq'

/--
```
  X₁ ---t---> Y₁
  |           |
  l           r
  |           |
  v           v
  X₂ ---m---> Y₂
  |           |
  l'          r'
  |           |
  v           v
  X₃ ---b---> Y₃
```
-/
lemma vert_comp' : CommSq t l'' r'' b := hl ▸ hr ▸ sq.vert_comp sq'

end Vertical

end CommSq

section

-- TODO: move
end

open Bicategory Limits Opposite

@[simps]
def Bicategory.Adjunction.toCategory {C D : Cat} {F : C ⟶ D} {G : D ⟶ C}
    (adj : Bicategory.Adjunction F G) :
    CategoryTheory.Adjunction F G where
  unit := adj.unit
  counit := adj.counit
  left_triangle_components X := by
    have := congr_app adj.left_triangle X
    dsimp [leftZigzag, bicategoricalComp] at this
    simpa [Cat.associator_hom_app, Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app] using this
  right_triangle_components X := by
    have := congr_app adj.right_triangle X
    dsimp [rightZigzag, bicategoricalComp] at this
    simpa [Cat.associator_inv_app, Cat.leftUnitor_inv_app] using this

variable {C : Type*} [Category C]

namespace Pseudofunctor

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) (Adj Cat)) {X S  : C} (f : X ⟶ S)

/-
I was trying to provide some notation for `(F.map f.op.toLoc).f` (resp. `(F.map f.op.toLoc).g`)
with this we could write `f[F]^*` (resp. `f[F]_*`) for pullback (resp. pushforward).
I am not yet convinced though.
-/
notation f "[" F "]" " ^* " =>
  Adj.Hom.f <|
    Prefunctor.map
    (PrelaxFunctorStruct.toPrefunctor <| PrelaxFunctor.toPrelaxFunctorStruct <|
      Pseudofunctor.toPrelaxFunctor F)
      (Quiver.Hom.toLoc <| Opposite.op f)

notation f "[" F "]" " _* " =>
  Adj.Hom.g <|
    Prefunctor.map
    (PrelaxFunctorStruct.toPrefunctor <| PrelaxFunctor.toPrelaxFunctorStruct <|
      Pseudofunctor.toPrelaxFunctor F)
      (Quiver.Hom.toLoc <| Opposite.op f)

/-- Given a commutative square, this is the natural map `f_* ⋙ g^* ⟶ p₁^* ⋙ p₂_*` -/
def baseChangeComparison {P X Y S : C} {p₁ : P ⟶ Y} {p₂ : P ⟶ X} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : CommSq p₁ p₂ g f) :
    (F.map f.op.toLoc).g ⋙ (F.map g.op.toLoc).f ⟶
      (F.map p₂.op.toLoc).f ⋙ (F.map p₁.op.toLoc).g :=
  letI u : (F.map f.op.toLoc).g ⟶
      (F.map p₂.op.toLoc).f ⋙ (F.map p₂.op.toLoc).g ⋙ (F.map f.op.toLoc).g :=
    (Functor.leftUnitor _).inv ≫
      whiskerRight (F.map p₂.op.toLoc).adj.unit (F.map f.op.toLoc).g ≫
      (Functor.associator _ _ _).hom
  letI v : (F.map p₂.op.toLoc).f ⋙ (F.map p₂.op.toLoc).g ⋙ (F.map f.op.toLoc).g ≅
      (F.map p₂.op.toLoc).f ⋙ (F.map p₁.op.toLoc).g ⋙ (F.map g.op.toLoc).g :=
    isoWhiskerLeft _ (Adj.forget₂.map₂Iso (F.isoMapOfCommSq sq.flip.op.toLoc).op)
  whiskerRight u (F.map g.op.toLoc).f ≫
    whiskerRight v.hom (F.map g.op.toLoc).f ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft ((F.map p₂.op.toLoc).f ⋙ (F.map p₁.op.toLoc).g)
      (F.map g.op.toLoc).adj.counit ≫
    (Functor.rightUnitor _).hom

/-
Let us think that `sq` is a square in `LocallyDiscrete B₀ᵒᵖ` that is dual to a square in `B₀`
```
    t                      b.unop
 X₁ ⟶ Y₁                  Y₂ ⟶ X₂
l|    |r   dual of  r.unop|    | l.unop
 v    v                   v    v
 X₂ ⟶ Y₂                  Y₁ ⟶ X₁
    b                      t.unop
```
This is the base change natural transformation
`l_* ≫ t^* ⟶ b^* ≫ r_*`
-/
def baseChangeAlt
    {B C : Type*} [Bicategory B] [Strict B] [Bicategory C] (F : Pseudofunctor B (Adj C))
    {X₁ X₂ Y₁ Y₂ : B} {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂}
    {r : Y₁ ⟶ Y₂} {b : X₂ ⟶ Y₂} (sq : CommSq t l r b) :
    (F.map l).g ≫ (F.map t).f ⟶ (F.map b).f ≫ (F.map r).g :=
  Bicategory.mateEquiv (F.map l).adj (F.map r).adj (F.isoMapOfCommSq sq).hom.τf

section Horizontal

variable {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} {t : X₁ ⟶ Y₁} {t' : Y₁ ⟶ Z₁}
  {l : X₁ ⟶ X₂} {m : Y₁ ⟶ Y₂} {r : Z₁ ⟶ Z₂}
  {b : X₂ ⟶ Y₂} {b' : Y₂ ⟶ Z₂}
  (sq : CommSq t l m b) (sq' : CommSq t' m r b')
  {t'' : X₁ ⟶ Z₁} {b'' : X₂ ⟶ Z₂}
  (ht : t ≫ t' = t'') (hb : b ≫ b' = b'')

lemma baseChangeComparision_horiz_comp' :
    baseChangeComparison F (sq.horiz_comp' sq' ht hb) =
      whiskerRight (Adj.forget₂.map₂
        (F.mapComp' b'.op.toLoc b.op.toLoc b''.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hb])).inv.op) _ ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ (baseChangeComparison F sq') ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (baseChangeComparison F sq) _ ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft _ (Adj.forget₂.map₂
        (F.mapComp' t'.op.toLoc t.op.toLoc t''.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, ht])).hom.op) := by
  sorry

end Horizontal

section Vertical

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
  {t : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} {b : X₃ ⟶ Y₃}
  {l : X₁ ⟶ X₂} {l' : X₂ ⟶ X₃}
  {r : Y₁ ⟶ Y₂} {r' : Y₂ ⟶ Y₃}
  (sq : CommSq t l r m)
  (sq' : CommSq m l' r' b)
  {l'' : X₁ ⟶ X₃} {r'' : Y₁ ⟶ Y₃}
  (hl : l ≫ l' = l'') (hr : r ≫ r' = r'')

lemma baseChangeComparison_vert_comp :
    baseChangeComparison F (sq.vert_comp' sq' hl hr) =
      whiskerLeft _ (Adj.forget₁.map₂
          (F.mapComp' _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hr])).hom) ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (baseChangeComparison F sq') _ ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft _ (baseChangeComparison F sq) ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (Adj.forget₁.map₂
          (F.mapComp' _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hl])).inv) _ :=
  sorry

end Vertical

end Pseudofunctor

end CategoryTheory
