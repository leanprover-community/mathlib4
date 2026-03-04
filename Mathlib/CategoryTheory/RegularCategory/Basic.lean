/-
Copyright (c) 2025 Fernando Chu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fernando Chu
-/
module

public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.Basic

/-!
# Regular categories

A regular category is a category with finite limits such that each kernel pair has a coequalizer
and such that regular epimorphisms are stable under pullback.

These categories provide a good ground to develop the calculus of relations, as well as being the
semantics for regular logic.

## Main results

* We show that every regular category has strong epi-mono factorisations, following Theorem 1.11
  in [Gran2021].

## Future work
* Show Frobenius reciprocity
* Show that every topos is regular
* Show that regular logic has an interpretation in regular categories

## References
* [Marino Gran, An Introduction to Regular Categories][Gran2021]
* <https://ncatlab.org/nlab/show/regular+category>
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/--
A regular category is a category with finite limits, such that every kernel pair has a coequalizer,
and such that regular epimorphisms are stable under base change.
-/
class Regular extends HasFiniteLimits C where
  hasCoequalizer_of_isKernelPair {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X} :
    IsKernelPair f g₁ g₂ → HasCoequalizer g₁ g₂
  regularEpiIsStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange (.regularEpi C)

variable {C} [Regular C]

instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi f] :
    IsRegularEpi (pullback.snd f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g)
  dsimp [MorphismProperty.regularEpi]
  infer_instance

instance {X Y B : C} (f : X ⟶ B) (g : Y ⟶ B) [HasPullback f g] [IsRegularEpi g] :
    IsRegularEpi (pullback.fst f g) := by
  apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g).flip
  dsimp [MorphismProperty.regularEpi]
  infer_instance

instance : Preregular C where
  exists_fac f g := ⟨_, pullback.snd g f, inferInstance, pullback.fst g f, pullback.condition⟩

variable {X Y : C} (f : X ⟶ Y)

namespace Regular

local instance : HasCoequalizer (pullback.fst f f) (pullback.snd f f) :=
  Regular.hasCoequalizer_of_isKernelPair <| IsKernelPair.of_hasPullback f

instance : Mono (coequalizer.desc f pullback.condition) := by
  -- It suffices to show that the two projections from the kernel pair are equal:
  apply (IsKernelPair.of_hasPullback _).mono_of_eq_fst_snd
  /- We fill in the kernel pair square of `f` as follows:
  ```
                  g₁                   fst
  pullback f f------->pullback e k₁----------> X
        |                 |                    |
      g₂|                 |snd                 |e
        v        fst      v            k₁      v
  pullback k₂ e------>pullback m m---------->coeq
        |                                      |
     snd|                                      |m
        v              e ≫ m = f               v
        X------------------------------------->Y
  ```
  Where `m`, `e`, `k₁`, `k₂`, `g₁`, `g₂` are defined below, `fst` and `snd` denote the projections
  in the pullbacks indicated as the source of those morphisms, and `coeq` is the coequalizer of the
  two projections in from the kernel pair of `f`.
  -/
  let m := (coequalizer.desc f pullback.condition)
  let e := coequalizer.π (pullback.fst f f) (pullback.snd f f)
  let k₁ := pullback.fst m m
  let k₂ := pullback.snd m m
  let d : pullback f f ⟶ (pullback m m) :=
    pullback.lift (pullback.fst f f ≫ e) (pullback.snd f f ≫ e) (by simp [m, e, pullback.condition])
  let g₁ : pullback f f ⟶ (pullback e k₁) := pullback.lift (pullback.fst f f) d (by simp [d, k₁])
  let g₂ : pullback f f ⟶ (pullback k₂ e) := pullback.lift d (pullback.snd f f) (by simp [d, k₂])
  /-
  Since the big square, the bottom square, and the top right square above are pullback squares,
  the top left square is also a pullback square.
  -/
  have h : IsPullback g₁ g₂ (pullback.snd e k₁) (pullback.fst k₂ e) := by
    refine .of_right ?_ (by simp [g₁, g₂]) (.of_hasPullback e k₁)
    refine .of_bot ?_ ?_ (.paste_horiz (.of_hasPullback k₂ e) (.of_hasPullback m m))
    · simpa [g₁, g₂, e, m, pullback.lift_fst, pullback.lift_snd] using .of_hasPullback f f
    · simp [g₁, g₂, k₁, d]
  /-
  Since `g₁` is the base change of a regular epi (the map `fst` in the middle row of the diagram
  above, which itself is a regular epi because it is a base change of the regular epi `e`),
  it is a regular epi.
  -/
  have : IsRegularEpi g₁ := by
    apply Regular.regularEpiIsStableUnderBaseChange.of_isPullback h.flip
    dsimp [MorphismProperty.regularEpi]
    infer_instance
  -- We precompose with the epimorphism `g₁ ≫ pullback.snd e k₁`, and finish
  rw [← cancel_epi (g₁ ≫ pullback.snd e k₁)]
  convert coequalizer.condition (pullback.fst f f) (pullback.snd f f) using 1
  all_goals cat_disch

/--
In a regular category, every morphism `f : X ⟶ Y` factors as `e ≫ m`, where `e` is the projection
map to the coequalizer of the kernel pair of `f`, and `m` is the canonical map from that
coequalizer to `Y`. In particular, `f` factors as a strong epimorphism followed by a monomorphism.
-/
noncomputable def strongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := coequalizer (pullback.fst f f) (pullback.snd f f)
  m := coequalizer.desc f pullback.condition
  e := coequalizer.π (pullback.fst f f) (pullback.snd f f)

instance : IsRegularEpi (strongEpiMonoFactorisation f).e := by
  dsimp [strongEpiMonoFactorisation]
  infer_instance

/--
In a regular category, every morphism `f` factors as `e ≫ m`, with `e` a strong epimorphism
and `m` a monomorphism.
-/
instance hasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations C where
  has_fac f := ⟨strongEpiMonoFactorisation f⟩

/-- In a regular category, every extremal epimorphism is a regular epimorphism. -/
noncomputable def regularEpiOfExtremalEpi [h : ExtremalEpi f] : RegularEpi f :=
  have := h.isIso (strongEpiMonoFactorisation f).e (strongEpiMonoFactorisation f).m (by simp)
  RegularEpi.ofArrowIso (Arrow.isoMk (f := .mk (strongEpiMonoFactorisation f).e) (Iso.refl _)
    (asIso (strongEpiMonoFactorisation f).m)) (IsRegularEpi.getStruct _)

instance isRegularEpi_of_extremalEpi (f : X ⟶ Y) [ExtremalEpi f] : IsRegularEpi f :=
  ⟨⟨regularEpiOfExtremalEpi f⟩⟩

end Regular

end CategoryTheory
