/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.TFAE
/-!

# Day's reflection theorem
-/

open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory

namespace CategoryTheory.Monoidal.Reflective

variable {C D : Type*} [Category C] [Category D]
variable [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]

section
variable (R : C ⥤ D)

/-- Day's reflection theorem. -/
theorem day_reflection [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)  :
    List.TFAE
    [ ∀ (c : C) (d : D), IsIso (adj.unit.app ((ihom d).obj (R.obj c)))
    , ∀ (c : C) (d : D), IsIso ((internalHom.map (adj.unit.app d).op).app (R.obj c))
    , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ▷ d'))
    , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ⊗ (adj.unit.app d')))] := by
  tfae_have 3 → 4
  · intro h
    have h' : ∀ d d', IsIso (L.map (d ◁ (adj.unit.app d'))) := by
      intro d d'
      have := BraidedCategory.braiding_naturality (𝟙 d) (adj.unit.app d')
      rw [← Iso.eq_comp_inv, id_tensorHom] at this
      rw [this]
      simp only [Functor.map_comp, Functor.id_obj, Functor.comp_obj, tensorHom_id, Category.assoc]
      infer_instance
    intro d d'
    have : (adj.unit.app d) ⊗ (adj.unit.app d') =
        (adj.unit.app d ▷ d') ≫ (((L ⋙ R).obj _) ◁ adj.unit.app d') := by
      simp [← tensorHom_id, ← id_tensorHom, ← tensor_comp]
    rw [this]
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp]
    infer_instance
  tfae_have 4 → 1
  · sorry
  tfae_have 1 → 3
  · sorry
  tfae_have 2 ↔ 3
  · sorry
  tfae_finish

end

section
variable [MonoidalCategory C]
variable (L : MonoidalFunctor D C) (R : C ⥤ D) [R.Faithful] [R.Full] (adj : L.toFunctor ⊣ R)

include adj in
instance (d d' : D) : IsIso (L.map ((adj.unit.app d) ⊗ (adj.unit.app d'))) := by
  have := L.μ_natural (adj.unit.app d) (adj.unit.app d')
  change _ = (asIso _).hom ≫ _ at this
  rw [← Iso.inv_comp_eq] at this
  rw [← this]
  infer_instance

include adj in
instance (c : C) (d : D) : IsIso (adj.unit.app ((ihom d).obj (R.obj c))) := by
  revert c d
  rw [((day_reflection _ _ adj).out 0 3:)]
  intro d d'
  infer_instance

/-- Auxiliary definition for `monoidalClosed`. -/
noncomputable def closed (c : C) : Closed c where
  rightAdj := R ⋙ (ihom (R.obj c)) ⋙ L.toFunctor
  adj := by
    let hR := Functor.FullyFaithful.ofFullyFaithful R
    refine ((ihom.adjunction (R.obj c)).comp adj).restrictFullyFaithful hR
      (Functor.FullyFaithful.id _) ?_ ?_
    · refine NatIso.ofComponents (fun _ ↦ ?_) (fun _ ↦ ?_)
      · exact (asIso (L.μ _ _)).symm ≪≫ asIso ((adj.counit.app _) ⊗ (adj.counit.app _))
      · simp? says simp only [Functor.comp_obj, tensorLeft_obj, Functor.id_obj, Functor.comp_map,
          tensorLeft_map, id_eq, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Functor.id_map,
          Category.assoc, IsIso.eq_inv_comp]
        rw [← L.μ_natural_right_assoc]
        simp [← id_tensorHom, ← tensor_comp]
    · exact NatIso.ofComponents (fun _ ↦ asIso (adj.unit.app ((ihom _).obj _)))

/--
Given a reflective functor `R : C ⥤ D` with a monoidal left adjoint, such that `D` is symmetric
monoidal closed, then `C` is monoidal closed.
-/
noncomputable def monoidalClosed : MonoidalClosed C where
  closed c := closed L R adj c

end

end CategoryTheory.Monoidal.Reflective
