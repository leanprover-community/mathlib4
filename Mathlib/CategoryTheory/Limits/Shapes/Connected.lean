/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!

# Connected shapes

In this file we prove that various shapes are connected.

-/

namespace CategoryTheory

open Limits

instance {J} : IsConnected (WidePullbackShape J) := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F H
  suffices ∀ i, F i = F none from fun j j' ↦ (this j).trans (this j').symm
  rintro ⟨⟩
  exacts [rfl, H (.term _)]

instance {J} : IsConnected (WidePushoutShape J) := by
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F H
  suffices ∀ i, F i = F none from fun j j' ↦ (this j).trans (this j').symm
  rintro ⟨⟩
  exacts [rfl, (H (.init _)).symm]

end CategoryTheory
