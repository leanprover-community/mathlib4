/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sheafification

/-!

# The constant sheaf

We define the constant sheaf functor (the sheafification of the constant presheaf)
`constantSheaf : D ⥤ Sheaf J D` and prove that it is left adjoint to evaluation at a terminal
object (see `constantSheafAdj`).
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable (D : Type*) [Category D]

/-- The constant presheaf functor is left adjoint to evaluation at a terminal object. -/
noncomputable def constantPresheafAdj {T : C} (hT : IsTerminal T) :
    Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T) :=
  Adjunction.mkOfUnitCounit {
    unit := (Functor.constCompEvaluationObj D (op T)).hom
    counit := {
      app := fun F => {
        app := fun ⟨X⟩ => F.map (IsTerminal.from hT X).op
        naturality := fun _ _ _ => by
          simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.id_obj, Functor.const_obj_map,
            Category.id_comp, ← Functor.map_comp]
          congr
          simp }
      naturality := by intros; ext; simp /- Note: `aesop` works but is kind of slow -/ } }

variable [HasWeakSheafify J D]

/--
The functor which maps an object of `D` to the constant sheaf at that object, i.e. the
sheafification of the constant presheaf.
-/
noncomputable def constantSheaf : D ⥤ Sheaf J D := Functor.const Cᵒᵖ ⋙ (presheafToSheaf J D)

/-- The constant sheaf functor is left adjoint to evaluation at a terminal object. -/
noncomputable def constantSheafAdj {T : C} (hT : IsTerminal T) :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  (constantPresheafAdj D hT).comp (sheafificationAdjunction J D)

end CategoryTheory
