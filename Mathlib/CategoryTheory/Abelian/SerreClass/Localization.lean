/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Localization with respect to a Serre class

-/

universe v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

namespace Limits

variable [HasZeroMorphisms C]

lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (kernel.ι f), ← cancel_mono f,
    assoc, assoc, kernel.condition, comp_zero, zero_comp]

lemma isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] :
    IsZero (cokernel f) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (cokernel.π f), ← cancel_epi f,
    cokernel.condition_assoc, zero_comp, comp_zero, comp_zero]

end Limits

variable [Abelian C]

namespace SerreClass

variable (c : SerreClass C)

def W : MorphismProperty C := fun _ _ f ↦ c.prop (kernel f) ∧ c.prop (cokernel f)

lemma W_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] : c.W f ↔ c.prop (cokernel f) := by
  dsimp [W]
  have : c.prop (kernel f) := c.prop_of_isZero (isZero_kernel_of_mono f)
  tauto

lemma W_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : c.W f ↔ c.prop (kernel f) := by
  dsimp [W]
  have : c.prop (cokernel f) := c.prop_of_isZero (isZero_cokernel_of_epi f)
  tauto

lemma W_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : c.prop (cokernel f)) : c.W f := by
  rwa [W_iff_of_mono]

lemma W_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : c.prop (kernel f)) : c.W f := by
  rwa [W_iff_of_epi]

lemma W_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : c.W f :=
  c.W_of_epi _ (c.prop_of_isZero (isZero_kernel_of_mono f))

@[nolint unusedArguments]
structure Localization (c : SerreClass C) : Type u where
  obj : C

namespace Localization

variable {c}

structure Hom' (X Y : c.Localization) where
  X' : C
  Y' : C
  i : X' ⟶ X.obj
  [mono_i : Mono i]
  hi : c.W i
  p : Y.obj ⟶ Y'
  [mono_p : Epi p]
  hp : c.W p
  f : X' ⟶ Y'

namespace Hom'

attribute [instance] mono_i mono_p

noncomputable def ofHom {X Y : C} (f : X ⟶ Y ) : Hom' (.mk (c := c) X) (.mk Y) where
  X' := X
  Y' := Y
  i := 𝟙 X
  p := 𝟙 Y
  f := f
  hi := W_of_isIso c _
  hp := W_of_isIso c _

noncomputable def id (X : c.Localization) : Hom' X X := ofHom (𝟙 _)

--def comp {X Y Z : c.Localization} (f : Hom' X Y) (g : Hom' Y Z) : Hom' X Z := sorry


end Hom'

end Localization

end SerreClass

end CategoryTheory
