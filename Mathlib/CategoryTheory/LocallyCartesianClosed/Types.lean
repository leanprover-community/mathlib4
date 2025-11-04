/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullback
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-! # Locally cartesian closed structure on `Type u`

## Main declarations

- `Limits.Types.chosenPullback` shows that every morphism in `Type u` has a chosen pullback. This is
  is an analogue of `Limits.Types.instHasPullbacksType: HasPullbacks.{u} (Type u)`

### TODO:
- Once the general theory of locally cartesian closed categories is merged to mathlib4,
  show that `Type u` is locally cartesian closed using this instance.
-/

namespace CategoryTheory

namespace Over

open Category Limits ChosenPullback

universe u

@[simps]
instance _root_.Limits.Types.chosenPullback {X Y : Type u} (f : Y ⟶ X) : ChosenPullback f where
  pullback.obj Z := Over.mk (fun p : Types.PullbackObj Z.hom f => p.1.2)
  pullback.map {W Z} k := Over.homMk (fun p => ⟨(k.left p.1.1, p.1.2), by
    have : Z.hom (k.left p.1.1) = W.hom p.1.1 := congr_fun k.w p.1.1
    rw [this]
    simpa using p.2⟩)
  mapPullbackAdj.unit.app P := Over.homMk (fun p => ⟨(p, P.hom p), by simp⟩)
  mapPullbackAdj.unit.naturality P Q g := by
    ext p
    simpa using congr_fun g.w p
  mapPullbackAdj.counit.app U := Over.homMk (fun p => p.1.1)

variable {X Y Z : Type u} {f : Y → X} {g : Z → X}

example : pullbackObj (C:= Type u) f g = Types.PullbackObj f g := rfl

example : fst (C:= Type u) g f = fun p => p.1.1 := rfl

example : snd (C:= Type u) g f = fun p => p.1.2 := rfl

example {W : Type u} {a : W → Y} {b : W → Z} {h : ∀ w : W, f (a w) = g (b w)} :
  lift (C:= Type u) a b (types_ext _ _ h) = fun w => ⟨(a w, b w), h w⟩ := rfl

end Over

end CategoryTheory
