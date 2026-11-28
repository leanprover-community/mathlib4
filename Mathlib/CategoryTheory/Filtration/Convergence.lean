/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

module

public import Mathlib.CategoryTheory.Filtration.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels

/-!
# ...


-/

public section

namespace CategoryTheory

open Limits ZeroObject

variable {C I J : Type*} [Category* C] [Category* I]

namespace Filtration

variable {X : C}

@[expose, simps, implicit_reducible]
def coconeDiagram (F : Filtration X I) : Cocone F.diagram where
  pt := X
  ι := F.ι

class IsWeaklyConvergent (F : Filtration X I) : Prop where
  nonempty_isColimit : Nonempty (IsColimit F.coconeDiagram)

noncomputable def isColimitCoconeDiagram (F : Filtration X I) [F.IsWeaklyConvergent] :
    IsColimit F.coconeDiagram :=
  IsWeaklyConvergent.nonempty_isColimit.some

class IsConvergent [HasZeroMorphisms C] (F : Filtration X I) : Prop
    extends F.IsWeaklyConvergent where
  π_eq_zero (F) (c : Cone F.diagram) : c.π = 0

attribute [simp] IsConvergent.π_eq_zero

section

variable [HasZeroMorphisms C] [HasZeroObject C]

@[expose, simps, implicit_reducible]
noncomputable def coneDiagram (F : Filtration X I) : Cone F.diagram where
  pt := 0
  π := 0

noncomputable def isLimitConeDiagram (F : Filtration X I) [F.IsConvergent] :
    IsLimit F.coneDiagram where
  lift _ := 0

end

section

variable [HasZeroMorphisms C] [HasCokernels C] (F : Filtration X I)

@[expose, simps, implicit_reducible]
noncomputable def coneCokernelι : Cone (cokernel F.ι) where
  pt := X
  π := (cokernel.π F.ι)

class IsStronglyConvergent (F : Filtration X I) : Prop
    extends F.IsWeaklyConvergent where
  nonempty_isLimit : Nonempty (IsLimit F.coneCokernelι)

noncomputable def isLimitConeCokernelι [F.IsStronglyConvergent] : IsLimit F.coneCokernelι :=
  IsStronglyConvergent.nonempty_isLimit.some

open IsCofiltered in
instance [IsCofiltered I] [F.IsStronglyConvergent] : F.IsConvergent where
  π_eq_zero c := by
    ext i
    rw [← cancel_mono (F.ι.app i)]
    refine F.isLimitConeCokernelι.hom_ext (fun j ↦ ?_)
    dsimp
    rw [Category.assoc, ← c.w_assoc (minToLeft i j)]
    simp [F.w_assoc (minToLeft i j), ← F.w_assoc (minToRight i j),
      ← NatTrans.comp_app]

end

lemma isZero_obj_of_hom [HasZeroMorphisms C] (F : Filtration X I) {i j : I} (f : i ⟶ j)
    (hj : IsZero (F.obj j)) : IsZero (F.obj i) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (F.diagram.map f)]
  exact hj.eq_of_tgt ..

lemma isIso_ι_app_of_hom (F : Filtration X I) {i j : I} (f : i ⟶ j)
    (hi : IsIso (F.ι.app i) := by infer_instance) : IsIso (F.ι.app j) :=
  ⟨inv (F.ι.app i) ≫ F.diagram.map f, by simp [← cancel_mono (F.ι.app j)], by simp⟩

lemma isEventuallyConstantFrom_diagram_of_isIso
    (F : Filtration X I) (i : I) (hi : IsIso (F.ι.app i) := by infer_instance) :
    F.diagram.IsEventuallyConstantFrom i := by
  intro j f
  have := F.isIso_ι_app_of_hom f
  exact IsIso.of_isIso_fac_right (F.w f)

lemma isEventuallyConstantTo_cokernel_of_isZero
    [HasZeroMorphisms C] [HasCokernels C]
    (F : Filtration X I) (i : I) (hi : IsZero (F.obj i)) :
    (cokernel F.ι).IsEventuallyConstantTo i := by
  intro j f
  have hj : IsZero (F.obj j) := IsZero.of_mono (F.diagram.map f) hi
  let e : F.diagram.obj j ≅ F.diagram.obj i :=
    { hom := F.diagram.map f
      inv := 0
      hom_inv_id := hj.eq_of_src ..
      inv_hom_id := hi.eq_of_src .. }
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (cokernelMapArrowIso F.ι f)).2
    (cokernel.mapIso (F.ι.app j) (F.ι.app i) e (Iso.refl _) (hj.eq_of_src ..)).isIso_hom

class IsBounded (F : Filtration X I) : Prop where
  exists_isZero_obj (F) : ∃ (i : I), IsZero (F.obj i)
  exists_isIso_ι_app (F) : ∃ (i : I), IsIso (F.ι.app i)

export IsBounded (exists_isZero_obj exists_isIso_ι_app)

instance [IsFiltered I] (F : Filtration X I) [F.IsBounded] : F.IsWeaklyConvergent where
  nonempty_isColimit := by
    obtain ⟨i, hi⟩ := F.exists_isIso_ι_app
    have : IsIso (F.coconeDiagram.ι.app i) := hi
    exact ⟨(F.isEventuallyConstantFrom_diagram_of_isIso i).isColimitOfIsIso _⟩

instance [IsFiltered I] [IsCofiltered I] [HasZeroMorphisms C] [HasCokernels C]
    (F : Filtration X I) [F.IsBounded] :
    F.IsStronglyConvergent where
  nonempty_isLimit := by
    obtain ⟨i, hi⟩ := F.exists_isZero_obj
    have : IsIso (F.coneCokernelι.π.app i) :=
      ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
        (cokernelπAppArrowIso F.ι i)).2 (cokernel.π_of_zero (hi.eq_of_src ..))
    have := F.isEventuallyConstantTo_cokernel_of_isZero i hi
    exact ⟨(F.isEventuallyConstantTo_cokernel_of_isZero i hi).isLimitOfIsIso _⟩

end Filtration

end CategoryTheory
