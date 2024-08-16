import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Data.List.TFAE

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory.Monoidal.Reflective

variable {C D : Type*} [Category C] [Category D]
variable [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]

section
variable (R : C ⥤ D)

/-- Day's reflection theorem. -/
theorem day_reflection [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)  :
  List.TFAE
  [ ∀ (c : C) (d : D), IsIso (adj.unit.app ((ihom d).obj (R.obj c)))
  , ∀ (c : C) (d : D), IsIso ((internalHom.map (adj.unit.app d).op).app (R.obj c))
  , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ⊗ (𝟙 d')))
  , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ⊗ (adj.unit.app d')))] := sorry

end

section
variable [MonoidalCategory C] [BraidedCategory C]
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

noncomputable def monoidalClosed : MonoidalClosed C where
  closed c := closed L R adj c

end

end CategoryTheory.Monoidal.Reflective
