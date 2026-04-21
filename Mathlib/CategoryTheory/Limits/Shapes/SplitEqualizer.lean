/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Split Equalizers

We define what it means for a triple of morphisms `f g : X ⟶ Y`, `ι : W ⟶ X` to be a split
equalizer: there is a retraction `r` of `ι` and a retraction `t` of `g`, which additionally satisfy
`t ≫ f = r ≫ ι`.

In addition, we show that every split equalizer is an equalizer
(`CategoryTheory.IsSplitEqualizer.isEqualizer`) and absolute
(`CategoryTheory.IsSplitEqualizer.map`)

A pair `f g : X ⟶ Y` has a split equalizer if there is a `W` and `ι : W ⟶ X` making `f,g,ι` a
split equalizer.
A pair `f g : X ⟶ Y` has a `G`-split equalizer if `G f, G g` has a split equalizer.

These definitions and constructions are useful in particular for the comonadicity theorems.

This file was adapted from `Mathlib/CategoryTheory/Limits/Shapes/SplitCoequalizer.lean`. Please try
to keep them in sync.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable {X Y : C} (f g : X ⟶ Y)

/-- A split equalizer diagram consists of morphisms

```
      ι   f
    W → X ⇉ Y
          g
```

satisfying `ι ≫ f = ι ≫ g` together with morphisms

```
      r   t
    W ← X ← Y
```

satisfying `ι ≫ r = 𝟙 W`, `g ≫ t = 𝟙 X` and `f ≫ t = r ≫ ι`.

The name "equalizer" is appropriate, since any split equalizer is an equalizer, see
`CategoryTheory.IsSplitEqualizer.isEqualizer`.
Split equalizers are also absolute, since a functor preserves all the structure above.
-/
structure IsSplitEqualizer {W : C} (ι : W ⟶ X) where
  /-- A map from `X` to the equalizer -/
  leftRetraction : X ⟶ W
  /-- A map in the opposite direction to `f` and `g` -/
  rightRetraction : Y ⟶ X
  /-- Composition of `ι` with `f` and with `g` agree -/
  condition : ι ≫ f = ι ≫ g := by cat_disch
  /-- `leftRetraction` splits `ι` -/
  ι_leftRetraction : ι ≫ leftRetraction = 𝟙 W := by cat_disch
  /-- `rightRetraction` splits `g` -/
  bottom_rightRetraction : g ≫ rightRetraction = 𝟙 X := by cat_disch
  /-- `f` composed with `rightRetraction` is `leftRetraction` composed with `ι` -/
  top_rightRetraction : f ≫ rightRetraction = leftRetraction ≫ ι := by cat_disch

instance {X : C} : Inhabited (IsSplitEqualizer (𝟙 X) (𝟙 X) (𝟙 X)) where
  default := { leftRetraction := 𝟙 X, rightRetraction := 𝟙 X }

open IsSplitEqualizer

attribute [reassoc] condition

attribute [reassoc (attr := simp)] ι_leftRetraction bottom_rightRetraction top_rightRetraction

variable {f g}

/-- Split equalizers are absolute: they are preserved by any functor. -/
@[simps]
def IsSplitEqualizer.map {W : C} {ι : W ⟶ X} (q : IsSplitEqualizer f g ι) (F : C ⥤ D) :
    IsSplitEqualizer (F.map f) (F.map g) (F.map ι) where
  leftRetraction := F.map q.leftRetraction
  rightRetraction := F.map q.rightRetraction
  condition := by rw [← F.map_comp, q.condition, F.map_comp]
  ι_leftRetraction := by rw [← F.map_comp, q.ι_leftRetraction, F.map_id]
  bottom_rightRetraction := by rw [← F.map_comp, q.bottom_rightRetraction, F.map_id]
  top_rightRetraction := by rw [← F.map_comp, q.top_rightRetraction, F.map_comp]

section

open Limits

/-- A split equalizer clearly induces a fork. -/
@[simps! pt]
def IsSplitEqualizer.asFork {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    Fork f g := Fork.ofι h t.condition

@[simp]
theorem IsSplitEqualizer.asFork_ι {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    t.asFork.ι = h := rfl

/--
The fork induced by a split equalizer is an equalizer, justifying the name. In some cases it
is more convenient to show a given fork is an equalizer by showing it is split.
-/
def IsSplitEqualizer.isEqualizer {W : C} {h : W ⟶ X} (t : IsSplitEqualizer f g h) :
    IsLimit t.asFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨ s.ι ≫ t.leftRetraction,
      by simp [- top_rightRetraction, ← t.top_rightRetraction, s.condition_assoc],
      fun hm => by simp [← hm] ⟩

end
variable (f g)

/--
The pair `f,g` is a cosplit pair if there is an `h : W ⟶ X` so that `f, g, h` forms a split
equalizer in `C`.
-/
class HasSplitEqualizer : Prop where
  /-- There is some split equalizer -/
  splittable : ∃ (W : C) (h : W ⟶ X), Nonempty (IsSplitEqualizer f g h)

/--
The pair `f,g` is a `G`-cosplit pair if there is an `h : W ⟶ G X` so that `G f, G g, h` forms a
split equalizer in `D`.
-/
abbrev Functor.IsCosplitPair : Prop :=
  HasSplitEqualizer (G.map f) (G.map g)

/-- Get the equalizer object from the typeclass `IsCosplitPair`. -/
noncomputable def HasSplitEqualizer.equalizerOfSplit [HasSplitEqualizer f g] : C :=
  (splittable (f := f) (g := g)).choose

/-- Get the equalizer morphism from the typeclass `IsCosplitPair`. -/
noncomputable def HasSplitEqualizer.equalizerι [HasSplitEqualizer f g] :
    HasSplitEqualizer.equalizerOfSplit f g ⟶ X :=
  (splittable (f := f) (g := g)).choose_spec.choose

/-- The equalizer morphism `equalizerι` gives a split equalizer on `f,g`. -/
noncomputable def HasSplitEqualizer.isSplitEqualizer [HasSplitEqualizer f g] :
    IsSplitEqualizer f g (HasSplitEqualizer.equalizerι f g) :=
  Classical.choice (splittable (f := f) (g := g)).choose_spec.choose_spec

/-- If `f, g` is cosplit, then `G f, G g` is cosplit. -/
instance map_is_cosplit_pair [HasSplitEqualizer f g] : HasSplitEqualizer (G.map f) (G.map g) where
  splittable :=
    ⟨_, _, ⟨IsSplitEqualizer.map (HasSplitEqualizer.isSplitEqualizer f g) _⟩⟩

namespace Limits

/-- If a pair has a split equalizer, it has an equalizer. -/
instance (priority := 1) hasEqualizer_of_hasSplitEqualizer [HasSplitEqualizer f g] :
    HasEqualizer f g :=
  HasLimit.mk ⟨_, (HasSplitEqualizer.isSplitEqualizer f g).isEqualizer⟩

end Limits

end CategoryTheory
