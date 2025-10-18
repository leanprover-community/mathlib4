/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Discrete.StructuredArrow

/-!
# Characterization of connected categories using initial/final functors

A category `C` is connected iff the constant functor `C ⥤ Discrete PUnit`
is final (or initial).

We deduce that the projection `C × D ⥤ C` is final (or initial) if `D` is connected.

-/

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Type w} [Unique T]

lemma isConnected_iff_final_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Final := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

lemma isConnected_iff_initial_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Initial := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

instance (F : C ⥤ Discrete T) [IsConnected C] : F.Final := by
  rwa [← isConnected_iff_final_of_unique F]

instance (F : C ⥤ Discrete T) [IsConnected C] : F.Initial := by
  rwa [← isConnected_iff_initial_of_unique F]

instance final_fst [IsConnected D] : (Prod.fst C D).Final :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Final

instance final_snd [IsConnected C] : (Prod.snd C D).Final :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final

instance initial_fst [IsConnected D] : (Prod.fst C D).Initial :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Initial

instance initial_snd [IsConnected C] : (Prod.snd C D).Initial :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

end CategoryTheory
