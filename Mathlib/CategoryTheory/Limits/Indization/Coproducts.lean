/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Coproducts in the category of Ind-objects

We show that if `C` has finite coproducts, then `Ind C` has small coproducts. It is shown elsewhere
that the functor `C ⥤ Inc C` preserves finite coproducts if `C` has finite colimits. It is not true
that the functors `C ⥤ Ind C` or `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserves coproducts in general.
-/

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {α : Type v} {I : α → Type v} [∀ s, SmallCategory (I s)] [∀ s, IsFiltered (I s)]

instance final_eval (s : α) : (Pi.eval I s).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => IsFiltered.nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨IsFiltered.coeq f g, IsFiltered.coeqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_same]
    simpa using IsFiltered.coeq_condition _ _

variable  (F : ∀ s, I s ⥤ C) [HasColimitsOfShape (Discrete α) C]

-- This is the λ in my notes
@[simps!]
noncomputable def pointwiseCoproduct : (∀ s, I s) ⥤ C where
  obj i := ∐ (fun s => (F s).obj (i s))
  map f := Sigma.map (fun s => (F s).map (f s))

section step1

variable (i : ∀ s, I s)

noncomputable def collection : α → Ind C := fun s => Ind.yoneda.obj ((F s).obj (i s))

-- Could be streamlined using a `Cofan.map` definition
noncomputable def cofan : Cofan (collection F i) :=
  Cofan.mk (Ind.yoneda.obj (∐ fun s => (F s).obj (i s)))
    (fun s => Ind.yoneda.map (Sigma.ι (fun s => (F s).obj (i s)) s))

noncomputable def step1 : IsColimit (cofan F i) := by
  refine (Limits.Cocone.isColimitYonedaEquiv (cofan F i)).symm ?_
  intro L
  sorry

-- instance : HasColimit (Discrete.functor (collection F i)) :=
--   ⟨_, step1 F i⟩

-- noncomputable def step1iso : ∐ collection F i ≅ Ind.yoneda.obj (∐ fun s => (F s).obj (i s)) :=
--   IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (step1 F i)

end step1

section step15

noncomputable def collection15 : α → (∀ s, I s) ⥤ Ind C := fun s => Pi.eval I s ⋙ F s ⋙ Ind.yoneda

noncomputable def collection15CompEvaluation (i : ∀ s, I s) :
    Discrete.functor (collection15 F) ⋙ (evaluation _ _).obj i ≅
      Discrete.functor (collection F i) :=
  Discrete.compNatIsoDiscrete _ _

noncomputable def cofan15 : Cofan (collection15 F) :=
  Cofan.mk (pointwiseCoproduct F ⋙ Ind.yoneda) (fun s =>
    ((Functor.associator _ _ _).inv ≫ whiskerRight
        { app := fun i => Sigma.ι (fun s => (F s).obj (i s)) s } Ind.yoneda))

noncomputable def step15 : IsColimit (cofan15 F) := by
  apply evaluationJointlyReflectsColimits
  intro i
  let t := step1 F i
  let t' := (IsColimit.precomposeHomEquiv (collection15CompEvaluation F i) _).symm t
  refine IsColimit.ofIsoColimit t' (Cocones.ext (Iso.refl _))

end step15

section step2

noncomputable def collection2 : α → Ind C := fun s => colimit (Pi.eval I s ⋙ F s ⋙ Ind.yoneda)

noncomputable def collection15CompColim :
    Discrete.functor (collection15 F) ⋙ colim ≅ Discrete.functor (collection2 F) :=
  Discrete.compNatIsoDiscrete _ _

noncomputable def cofan2 : Cofan (collection2 F) :=
  Cofan.mk (colimit (pointwiseCoproduct F ⋙ Ind.yoneda))
    (fun s => colimMap ((Functor.associator _ _ _).inv ≫ whiskerRight
        { app := fun i => Sigma.ι (fun s => (F s).obj (i s)) s } Ind.yoneda))

noncomputable def step2 : IsColimit (cofan2 F) := by
  let t := PreservesColimit.preserves (F := colim) (step15 F)
  let t' := (IsColimit.precomposeInvEquiv (collection15CompColim F) _).symm t
  refine IsColimit.ofIsoColimit t' (Cocones.ext (Iso.refl _) ?_)
  intro ⟨j⟩
  simp [collection15CompColim, collection15, cofan15, cofan2]
  exact Category.id_comp _

theorem hasColimit_collection2 : HasColimit (Discrete.functor (collection2 F)) :=
  ⟨_, step2 F⟩

end step2

end

section

variable {α : Type v} [HasColimitsOfShape (Discrete α) C] (f : α → Ind C)

theorem final : HasColimit (Discrete.functor f) := by
  -- Evil evil defeq abuse here........
  let I : α → Type v := fun s => (f s).2.presentation.I
  let F : ∀ s, I s ⥤ C := fun s => (f s).2.presentation.F
  let q : ∀ s, collection2 F s ≅ f s := by
    intro s
    dsimp [collection2]
    refine (Functor.Final.colimitIso (Pi.eval I s) (F s ⋙ Ind.yoneda)) ≪≫ ?_
    have hInc : (Ind.inclusion C).FullyFaithful := .ofFullyFaithful _
    refine hInc.isoEquiv.symm ?_
    refine preservesColimitIso _ _ ≪≫ ?_
    refine HasColimit.isoOfNatIso (Functor.associator _ _ _) ≪≫ ?_
    refine HasColimit.isoOfNatIso (isoWhiskerLeft (F s) Ind.yonedaCompInclusion) ≪≫ ?_
    exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (f s).2.presentation.isColimit
  suffices Discrete.functor f ≅ Discrete.functor (collection2 F) by
    have _ := hasColimit_collection2 F
    apply hasColimitOfIso this
  apply Discrete.natIso
  exact fun s => (q s.as).symm

end

end CategoryTheory.Limits
