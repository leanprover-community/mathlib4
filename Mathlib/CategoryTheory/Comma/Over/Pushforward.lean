/-
Copyright (c) 2025 Joseph Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Hua
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Pushforward

If pullbacks along a morphism `f : S ⟶ S'` exist,
we say that an object `Y : Over S'` is a pushforward along `f` of an object `X : Over S`
when it locally satisfies the right adjoint universal property with respect to
the pullback functor `Over.pullback f : Over Y ⥤ Over X`.
More formally,
this means that the object `Y` represents the presheaf `Hom(pullback f (-), X)`.

## Main declarations

- `IsPushforward f X Y` says that `Y` is a pushforward along `f` of `X`.
- `HasPushforward f X` says that a pushforward of `f` along `X` exists.
- `pushforward f : Over S ⥤ Over S'` is the functor induced by a morphism `f : S ⟶ S'`
  when all pushforwards along `f` exist.
- `pullbackPushforwardAdjunction f : pullback f ⊣ pushforward f` is the defining adjunction
  of pushforwards when all pushforwards along `f` exist.

## Notes

- There is a partial right adjoint induced by the condition `HasPushforward`.
  See `Mathlib.CategoryTheory.Adjunction.PartialAdjoint`.
- In the literature, the condition `HasPushforwards f` is also called "exponentiable",
  and `IsPushforwardf f X Y` is also read as "`Y` is the internal product".
-/

noncomputable section

universe v v₂ u u₂

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)
variable {D : Type u₂} [Category.{v₂} D]

variable {S S' : C} (f : S ⟶ S') [∀ {W} (h : W ⟶ S'), HasPullback h f]

/-- `Y` is the pushforward of `X` along `f` when it represents the presheaf
`Hom(pullback f (-), X)`. -/
abbrev IsPushforward (X : Over S) (Y : Over S') :=
  ((Over.pullback f).op ⋙ yoneda.obj X).RepresentableBy Y

/-- An object `X` in the slice over `S` has a pushforward along morphism `f : S ⟶ S'`
when the presheaf `Hom(pullback f (-), X)` is representable. -/
abbrev HasPushforward (X : Over S) : Prop :=
  ((Over.pullback f).op ⋙ yoneda.obj X).IsRepresentable

/-- Assuming a pushforward along along `f` of `X` exists,
`pushforward` chooses such a pushforward. -/
abbrev pushforward (X : Over S) [HasPushforward f X] : Over S' :=
  ((Over.pullback f).op ⋙ yoneda.obj X).reprX

/-- The pushforward of an object satisfies the universal property of the pushforward. -/
def pushforward.isPushforward (X : Over S) [HasPushforward f X] :
    IsPushforward f X (pushforward f X) :=
  ((Over.pullback f).op ⋙ yoneda.obj X).representableBy

/-- A morphism `f` has pushforwards when there is a pushforward
along `f` for any map into its domain. -/
abbrev HasPushforwards : Prop := ∀ (X : Over S), HasPushforward f X

namespace Over

variable [HasPushforwards f]

lemma pullback_rightAdjointObjIsDefined_eq_top :
    (Over.pullback f).rightAdjointObjIsDefined = ⊤ := by aesop_cat

instance : (pullback f).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  (pullback_rightAdjointObjIsDefined_eq_top f)

/-- When pushforwards along `f` exist,
we can define a left adjoint to the pullback functor between over categories. -/
def pushforward : Over S ⥤ Over S' :=
  (pullback f).rightAdjoint

/-- The pullback-pushforward adjunction. -/
def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  Adjunction.ofIsLeftAdjoint (pullback f)

end Over

end CategoryTheory
end
