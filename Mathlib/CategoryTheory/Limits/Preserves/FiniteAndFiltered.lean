/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Preservation of coproducts from finite coproducts and filtered colimits

A coproduct is the filtered colimit of its finite subcoproducts. Comparing these diagrams
after applying a functor reduces preservation of coproducts to the two preservation hypotheses.
-/

@[expose] public section

universe w v u v' u'

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace CoproductsFromFiniteFiltered

/-- The finite-subcoproduct diagram commutes with a functor preserving finite coproducts. -/
def liftToFinsetObjCompIso [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G] {α : Type w} (F : Discrete α ⥤ C) :
    liftToFinsetObj F ⋙ G ≅ liftToFinsetObj (F ⋙ G) := by
  refine Iso.symm (NatIso.ofComponents
    (fun S ↦ (PreservesCoproduct.iso G (fun x : S ↦ F.obj x)).symm) ?_)
  intro S T h
  dsimp [liftToFinsetObj]
  ext x
  simp

variable [HasFiniteCoproducts C] [HasFiniteCoproducts D] {α : Type w}
  [HasColimitsOfShape (Finset (Discrete α)) C] [HasColimitsOfShape (Finset (Discrete α)) D]
  [HasColimitsOfShape (Discrete α) C] [HasColimitsOfShape (Discrete α) D]
  (G : C ⥤ D) [PreservesFiniteCoproducts G] (F : Discrete α ⥤ C)
  [PreservesColimit (liftToFinsetObj F) G]

/-- The coproduct comparison factors through the colimits of finite subcoproducts. -/
lemma colimit_post : colimit.post F G =
    ((liftToFinsetColimIso (C := D) (α := α)).app (F ⋙ G)).inv ≫
      (HasColimit.isoOfNatIso (liftToFinsetObjCompIso G F)).inv ≫
        (preservesColimitIso G (liftToFinsetObj F)).inv ≫
          G.map (((liftToFinsetColimIso (C := C) (α := α)).app F).hom) := by
  apply colimit.hom_ext
  intro j
  -- It suffices to compare the maps on singleton subcoproducts.
  let js : ({j} : Finset (Discrete α)) := ⟨j, by simp⟩
  rw [colimit.ι_post, ← liftToFinsetColimIso_aux_assoc (F ⋙ G) js]
  simp only [liftToFinsetColimIso, NatIso.ofComponents.app, Iso.symm_hom, Iso.symm_inv]
  rw [Iso.inv_hom_id_assoc, HasColimit.ι_isoOfNatIso_inv_assoc]
  simp only [Functor.comp_obj, liftToFinsetObjCompIso, Iso.symm_inv,
    NatIso.ofComponents_hom_app, Iso.symm_hom,
    PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
    ι_preservesColimitIso_inv_assoc, ← G.map_comp]
  congr 1
  exact (liftToFinsetColimIso_aux F js).symm

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

/-- A functor preserving finite coproducts and filtered colimits preserves coproducts. -/
lemma preservesColimitsOfShape_discrete_of_preservesFiniteCoproducts_and_filteredColimits
    [HasFiniteCoproducts C] [HasFilteredColimitsOfSize.{w, w} C]
    [HasFiniteCoproducts D] [HasFilteredColimitsOfSize.{w, w} D]
    (G : C ⥤ D) [PreservesFiniteCoproducts G]
    [PreservesFilteredColimitsOfSize.{w, w} G] (α : Type w) :
    PreservesColimitsOfShape (Discrete α) G := by
  let : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  let : HasCoproducts.{w} D := hasCoproducts_of_finite_and_filtered
  constructor
  intro F
  have : IsIso (colimit.post F G) := by
    rw [colimit_post]
    infer_instance
  exact preservesColimit_of_isIso_post G F

end CategoryTheory.Limits
