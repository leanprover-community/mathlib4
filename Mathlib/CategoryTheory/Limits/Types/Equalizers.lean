/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Equalizers in Type

The equalizer of a pair of maps `(g, h)` from `X` to `Y` is the subtype `{x : Y // g x = h x}`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

/--
Show the given fork in `Type u` is an equalizer given that any element in the "difference kernel"
comes from `X`.
The converse of `unique_of_type_equalizer`.
-/
noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_fun s.condition i
    · funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).1
    · intro m hm
      funext i
      exact (Classical.choose_spec (t (s.ι i) (congr_fun s.condition i))).2 _ (congr_fun hm i)

/-- The converse of `type_equalizer_of_unique`. -/
theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := fun _ => y
  have hy' : y' ≫ g = y' ≫ h := funext fun _ => hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_fun (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply Fork.IsLimit.hom_ext t
  funext ⟨⟩
  apply hx'.trans (congr_fun (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm

theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

/-- Show that the subtype `{x : Y // g x = h x}` is an equalizer for the pair `(g,h)`. -/
def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (Subtype.val : { x : Y // g x = h x } → Y) (funext Subtype.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨fun i => ⟨s.ι i, by apply congr_fun s.condition i⟩, rfl, fun hm =>
        funext fun x => Subtype.ext (congr_fun hm x)⟩

variable (g h)

/-- The categorical equalizer in `Type u` is `{x : Y // g x = h x}`. -/
noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit

@[elementwise (attr := simp)]
theorem equalizerIso_hom_comp_subtype : (equalizerIso g h).hom ≫ Subtype.val = equalizer.ι g h := by
  rfl

@[elementwise (attr := simp)]
theorem equalizerIso_inv_comp_ι : (equalizerIso g h).inv ≫ equalizer.ι g h = Subtype.val :=
  limit.isoLimitCone_inv_π equalizerLimit WalkingParallelPair.zero

end CategoryTheory.Limits.Types
