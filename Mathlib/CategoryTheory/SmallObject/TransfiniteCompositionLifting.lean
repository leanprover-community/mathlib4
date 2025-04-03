/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# The left lifting property is stable under transfinite composition

Let `C` be a category, and `p : X ⟶ Y` be a morphism in `C`. In this file,
we show that a transfinite composition of morphisms that have the left
lifting property with respect to `p` also has the left lifting property with
respect to `p`, see `HasLiftingProperty.transfiniteComposition.hasLiftingProperty_ι_app_bot`.

About the proof, given a colimit cocone `c` for a well-order-continuous
functor `F : J ⥤ C` from a well-ordered type `J`, we introduce a projective
system `sqFunctor c p f g : Jᵒᵖ ⥤ Type _` which associates to any `j : J`
the structure `SqStruct c p f g j` which consists of those morphisms `f'`
which makes the diagram below commute. The data of such compatible `f'` for
all `j` shall give the expected lifting `c.pt ⟶ X` for the outer square.

```
         f
F.obj ⊥ --> X
   |      Λ |
   |   f'╱  |
   v    ╱   |
F.obj j     | p
   |        |
   |        |
   v    g   v
  c.pt ---> Y
```
This is constructed by transfinite induction on `j`:
* When `j = ⊥`, this is `f`;
* In order to pass from `j` to `Order.succ j`, we use the assumption that
`F.obj j ⟶ F.obj (Order.succ j)` has the left lifting property with respect to `p`;
* When `j` is a limit element, we use the "continuity" of `F`.

TODO: Given `P : MorphismProperty C`, deduce that the class of morphisms
that have the left lifting property with respect to `P` is stable
by transfinite composition.

-/

universe w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace HasLiftingProperty

variable {W : MorphismProperty C}
  {J : Type w} [LinearOrder J] [OrderBot J]

namespace transfiniteComposition

variable {F : J ⥤ C} (c : Cocone F) (hc : IsColimit c)
  {X Y : C} (p : X ⟶ Y) (f : F.obj ⊥ ⟶ X) (g : c.pt ⟶ Y)

/-- Given a cocone `c` for a functor `F : J ⥤ C` from a well-ordered type,
and maps `p : X ⟶ Y`, `f : F.obj ⊥ ⟶ X`, `g : c.pt ⟶ Y`, this structure
contains the data of a map `F.obj j ⟶ X` such that `F.map (homOfLE bot_le) ≫ f' = f`
and `f' ≫ p = c.ι.app j ≫ g`. (This implies that the outer square below
commutes, see `SqStruct.w`.)

```
         f
F.obj ⊥ --> X
   |      Λ |
   |   f'╱  |
   v    ╱   |
F.obj j     | p
   |        |
   |        |
   v    g   v
  c.pt ---> Y
```
-/
@[ext]
structure SqStruct (j : J) where
  /-- a morphism `F.obj j ⟶ X` -/
  f' : F.obj j ⟶ X
  w₁ : F.map (homOfLE bot_le) ≫ f' = f := by aesop_cat
  w₂ : f' ≫ p = c.ι.app j ≫ g := by aesop_cat

namespace SqStruct

attribute [reassoc (attr := simp)] w₁ w₂

variable {c p f g} {j : J} (sq' : SqStruct c p f g j)

include sq' in
@[reassoc]
lemma w : f ≫ p = c.ι.app ⊥ ≫ g := by
  rw [← sq'.w₁, assoc, sq'.w₂, Cocone.w_assoc]

/--
Given `sq' : SqStruct c p f g j`, this is the commutative square
```
               sq'.f'
F.obj j --------------------> X
   |                          |
   |                          |p
   v                      g   v
F.obj (succ j) ---> c.pt ---> Y
```

(Using the lifting property for this square is the key ingredient
in the proof that the left lifting property with respect to `p`
is stable under transfinite composition.) -/
lemma sq [SuccOrder J] :
    CommSq sq'.f' (F.map (homOfLE (Order.le_succ j))) p (c.ι.app _ ≫ g) where
  w := by simp

/-- Auxiliary definition for `sqFunctor`. -/
@[simps]
def map {j' : J} (α : j' ⟶ j) : SqStruct c p f g j' where
  f' := F.map α ≫ sq'.f'
  w₁ := by
    rw [← F.map_comp_assoc]
    exact sq'.w₁

end SqStruct

/-- The projective system `j ↦ SqStruct c p f g j.unop`. -/
@[simps]
def sqFunctor : Jᵒᵖ ⥤ Type _ where
  obj j := SqStruct c p f g j.unop
  map α sq' := sq'.map α.unop

variable [F.IsWellOrderContinuous]

namespace wellOrderInductionData

variable {p c f g} {j : J} (hj : Order.IsSuccLimit j)
  (s : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ sqFunctor c p f g).sections)

/-- Auxiliary definition for `transfiniteComposition.wellOrderInductionData`. -/
noncomputable def liftHom : F.obj j ⟶ X :=
  (F.isColimitOfIsWellOrderContinuous j hj).desc
    (Cocone.mk _
      { app := fun i ↦ (s.1 ⟨i⟩).f'
        naturality i i' g := by
          have := congr_arg SqStruct.f' (s.2 g.op)
          dsimp at this ⊢
          rw [this, comp_id] })

@[reassoc]
lemma liftHom_fac (i : J) (hi : i < j) :
    F.map (homOfLE hi.le) ≫ liftHom hj s = (s.1 ⟨⟨i, hi⟩⟩).f' :=
  (F.isColimitOfIsWellOrderContinuous j hj).fac _ ⟨i, hi⟩

/-- Auxiliary definition for `transfiniteComposition.wellOrderInductionData`. -/
@[simps]
noncomputable def lift : (sqFunctor c p f g).obj (Opposite.op j) where
  f' := liftHom hj s
  w₁ := by
    have h : ⊥ < j := Ne.bot_lt' (by
      rintro rfl
      exact Order.not_isSuccLimit_bot hj)
    rw [liftHom_fac hj s ⊥ h]
    simpa using (s.1 ⟨⊥, h⟩).w₁
  w₂ := (F.isColimitOfIsWellOrderContinuous j hj).hom_ext (fun ⟨i, hij⟩ ↦ by
    have := (s.1 ⟨i, hij⟩).w₂
    dsimp at this ⊢
    rw [liftHom_fac_assoc _ _ _ hij, this, Cocone.w_assoc])

lemma map_lift {i : J} (hij : i < j) :
    (lift hj s).map (homOfLE hij.le) = s.1 ⟨⟨i, hij⟩⟩ := by
  ext
  apply liftHom_fac

end wellOrderInductionData

variable {p} [SuccOrder J] [WellFoundedLT J]
  (hF : ∀ (j : J) (_ : ¬IsMax j), HasLiftingProperty (F.map (homOfLE (Order.le_succ j))) p)

open wellOrderInductionData in
/-- The projective system `sqFunctor c p f g` has a `WellOrderInductionData` structure. -/
noncomputable def wellOrderInductionData :
    (sqFunctor c p f g).WellOrderInductionData where
  succ j hj sq' :=
    have := hF j hj
    { f' := sq'.sq.lift
      w₁ := by
        dsimp
        simp only [← sq'.w₁]
        conv_rhs => rw [← sq'.sq.fac_left, ← F.map_comp_assoc]
        rfl }
  map_succ j hj sq' := by aesop_cat
  lift j hj s := lift hj s
  map_lift j hj s i hij := map_lift hj s hij

include hF hc

variable {c f g} (sq : CommSq f (c.ι.app ⊥) p g)

lemma hasLift : sq.HasLift := by
  obtain ⟨s, hs⟩ := (wellOrderInductionData c f g hF).surjective { w₂ := sq.w }
  replace hs := congr_arg SqStruct.f' hs
  dsimp at hs
  let t : Cocone F := Cocone.mk X
    { app j := (s.1 ⟨j⟩).f'
      naturality j j' g := by simpa using congr_arg SqStruct.f' (s.2 g.op) }
  let l := hc.desc t
  have hl (j : J) : c.ι.app j ≫ l = (s.1 ⟨j⟩).f' := hc.fac t j
  exact ⟨⟨{
    l := l
    fac_left := by rw [hl, hs]
    fac_right := hc.hom_ext (fun j ↦ by rw [reassoc_of% (hl j), SqStruct.w₂])}⟩⟩

lemma hasLiftingProperty_ι_app_bot : HasLiftingProperty (c.ι.app ⊥) p where
  sq_hasLift sq := hasLift hc hF sq

end transfiniteComposition

end HasLiftingProperty

end CategoryTheory
