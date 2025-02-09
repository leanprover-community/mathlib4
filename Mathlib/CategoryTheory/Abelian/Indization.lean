/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Indization
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# The category of ind-objects is abelian
-/

universe v

open CategoryTheory.Abelian

namespace CategoryTheory

variable {C : Type v} [SmallCategory C] [Abelian C]

instance {X Y : Ind C} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) := by
  obtain ⟨I, _, _, F, G, ϕ, ⟨i⟩⟩ := Ind.exists_nonempty_arrow_mk_iso_ind_lim (f := f)
  let i' := coimageImageComparisonFunctor.mapIso i
  dsimp at i'
  rw [Arrow.isIso_iff_isIso_of_isIso i'.hom]
  have : Limits.HasFiniteBiproducts (Ind C) :=
    Limits.HasFiniteBiproducts.of_hasFiniteCoproducts
  have : Limits.HasZeroObject (Ind C) :=
    Limits.hasZeroObject_of_hasFiniteBiproducts _
  have : (Ind.lim I (C := C)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  rw [Arrow.isIso_iff_isIso_of_isIso (PreservesCoimageImageComparison.iso (Ind.lim I) ϕ).inv]
  infer_instance

noncomputable instance : Abelian (Ind C) :=
  .ofCoimageImageComparisonIsIso

end CategoryTheory
