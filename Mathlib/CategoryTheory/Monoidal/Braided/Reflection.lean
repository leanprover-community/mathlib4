/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.TFAE
/-!

# Day's reflection theorem
-/

open CategoryTheory Category MonoidalCategory MonoidalClosed BraidedCategory

namespace CategoryTheory.Monoidal.Reflective

variable {C D : Type*} [Category C] [Category D]

-- TODO: relate to idempotent monads, algebra structure on `d` etc.
lemma isSplitMono_iff_isIso_unit (R : C ⥤ D) [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)
    (d : D) :
    IsSplitMono (adj.unit.app d) ↔ IsIso (adj.unit.app d) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  -- let ξ := retraction (adj.unit.app d)
  refine ⟨retraction (adj.unit.app d), by simp, ?_⟩
  erw [← Functor.map_id, ← IsSplitMono.id (adj.unit.app d), Functor.map_comp]
  have : (L ⋙ R).map (adj.unit.app d) = adj.unit.app ((L ⋙ R).obj d) := by
    let T := adj.toMonad
    let _ : Reflective R := { L := L, adj := adj }
    have : IsIso T.μ := μ_iso_of_reflective (R := R)
    have h₁ : whiskerLeft T.toFunctor T.η ≫ T.μ = 𝟙 _ := by ext; simp
    have h₂ : whiskerRight T.η T.toFunctor ≫ T.μ = 𝟙 _ := by ext; simp
    erw [← h₁, cancel_mono] at h₂
    rw [NatTrans.ext_iff, funext_iff] at h₂
    exact h₂ d
  rw [this]
  simp

lemma isIso_coyoneda_unit (R : C ⥤ D) [R.Full] (L : D ⥤ C) (adj : L ⊣ R)
    (d d' : D) : IsIso ((coyoneda.map (adj.unit.app d).op).app ((L ⋙ R).obj d')) := by
  constructor
  refine ⟨?_, ?_, ?_⟩
  · exact fun f ↦ R.map ((adj.homEquiv _ _).symm f)
  · ext f
    simp only [Functor.comp_obj, coyoneda_obj_obj, Functor.id_obj, Adjunction.homEquiv_counit,
      Functor.map_comp, types_comp_apply, coyoneda_map_app, Quiver.Hom.unop_op, assoc,
      types_id_apply]
    have : f = R.map (R.preimage f) := by simp
    rw [this]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc, -Functor.map_preimage]
  · ext
    simp

lemma isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((coyoneda.map f.op).app c) := by
  constructor
  · intro
    rw [← NatTrans.isIso_iff_isIso_app]
    infer_instance
  · intro h
    apply isIso_of_coyoneda_map_bijective
    intro c
    rw [← isIso_iff_bijective]
    exact h c

lemma isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((yoneda.map f).app ⟨c⟩) := by
  constructor
  · intro
    have : IsIso (yoneda.map f) := inferInstance
    intro c
    infer_instance
  · intro h
    apply isIso_of_yoneda_map_bijective
    intro c
    rw [← isIso_iff_bijective]
    exact h c

variable [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]

section
variable (R : C ⥤ D)

/-- Auxiliary definition for `adjRetraction`. -/
noncomputable def adjRetractionAux [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)
    (c : C) (d : D) [IsIso (L.map (adj.unit.app ((ihom d).obj (R.obj c)) ⊗ adj.unit.app d))] :
  d ⊗ ((L ⋙ R).obj ((ihom d).obj (R.obj c))) ⟶ (R.obj c) :=
  (β_ _ _).hom ≫ (_ ◁ adj.unit.app _) ≫ adj.unit.app _ ≫
    R.map (inv (L.map (adj.unit.app _ ⊗ adj.unit.app _))) ≫ (L ⋙ R).map (β_ _ _).hom ≫
      (L ⋙ R).map ((ihom.ev _).app _) ≫ inv (adj.unit.app _)

/-- The left inverse to the unit in the proof of `4 → 1` in `day_reflection` below. -/
noncomputable def adjRetraction [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)
    (c : C) (d : D) [IsIso (L.map (adj.unit.app ((ihom d).obj (R.obj c)) ⊗ adj.unit.app d))] :
    (L ⋙ R).obj ((ihom d).obj (R.obj c)) ⟶ ((ihom d).obj (R.obj c)) :=
  curry <| adjRetractionAux R L adj c d

lemma adjRetraction_is_retraction [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R) (c : C) (d : D)
    [IsIso (L.map (adj.unit.app ((ihom d).obj (R.obj c)) ⊗ adj.unit.app d))] :
    adj.unit.app ((ihom d).obj (R.obj c)) ≫ adjRetraction R L adj c d = 𝟙 _ := by
  suffices (_ ◁ adj.unit.app _) ≫ adjRetractionAux R L adj c d = (ihom.ev _).app _ by
    simp only [Functor.id_obj, Functor.comp_obj, adjRetraction, ← curry_natural_left, this]
    simp [curry_eq]
  simp only [Functor.id_obj, Functor.comp_obj, adjRetractionAux, Functor.map_inv, Functor.comp_map,
    braiding_naturality_right_assoc]
  slice_lhs 2 3 =>
    simp only [← id_tensorHom, ← tensorHom_id, ← tensor_comp, id_comp, comp_id]
  slice_lhs 2 4 =>
    rw [← adj.unit_naturality_assoc]
  simp

/-- Day's reflection theorem. -/
theorem day_reflection [R.Faithful] [R.Full] (L : D ⥤ C) (adj : L ⊣ R)  :
    List.TFAE
    [ ∀ (c : C) (d : D), IsIso (adj.unit.app ((ihom d).obj (R.obj c)))
    , ∀ (c : C) (d : D), IsIso ((pre (adj.unit.app d)).app (R.obj c))
    , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ▷ d'))
    , ∀ (d d' : D), IsIso (L.map ((adj.unit.app d) ⊗ (adj.unit.app d')))] := by
  tfae_have 3 → 4
  · intro h
    have h' : ∀ d d', IsIso (L.map (d ◁ (adj.unit.app d'))) := by
      intro d d'
      have := braiding_naturality (𝟙 d) (adj.unit.app d')
      rw [← Iso.eq_comp_inv, id_tensorHom] at this
      rw [this]
      simp only [Functor.map_comp, Functor.id_obj, Functor.comp_obj, tensorHom_id, assoc]
      infer_instance
    intro d d'
    have : (adj.unit.app d) ⊗ (adj.unit.app d') =
        (adj.unit.app d ▷ d') ≫ (((L ⋙ R).obj _) ◁ adj.unit.app d') := by
      simp [← tensorHom_id, ← id_tensorHom, ← tensor_comp]
    rw [this]
    simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp]
    infer_instance
  tfae_have 4 → 1
  · intros
    rw [← isSplitMono_iff_isIso_unit]
    exact ⟨⟨adjRetraction R L adj _ _, adjRetraction_is_retraction R L adj _ _⟩⟩
  tfae_have 1 → 3
  · intro h d d'
    suffices ∀ c, IsIso ((coyoneda.map (L.map (adj.unit.app d ▷ d')).op).app c) by
      rw [← NatTrans.isIso_iff_isIso_app] at this
      exact (isIso_op_iff _).mp <| isIso_of_reflects_iso (L.map (adj.unit.app d ▷ d')).op coyoneda
    intro c
    have w₁ : (coyoneda.map (L.map (adj.unit.app d ▷ d')).op).app c = (adj.homEquiv _ _).symm ∘
      (coyoneda.map (adj.unit.app d ▷ d').op).app (R.obj c) ∘ adj.homEquiv _ _ := by ext; simp
    rw [w₁, isIso_iff_bijective]
    simp only [Functor.comp_obj, coyoneda_obj_obj, Functor.id_obj, EquivLike.comp_bijective,
      EquivLike.bijective_comp]
    have w₂ : ((coyoneda.map (adj.unit.app d ▷ d').op).app (R.obj c)) =
        ((yoneda.obj (R.obj c)).mapIso (β_ _ _)).hom ∘
          ((coyoneda.map (d' ◁ adj.unit.app d).op).app (R.obj c)) ∘
            ((yoneda.obj (R.obj c)).mapIso (β_ _ _)).hom := by ext; simp
    rw [w₂, ← types_comp, ← types_comp, ← isIso_iff_bijective]
    refine IsIso.comp_isIso' (IsIso.comp_isIso' inferInstance ?_) inferInstance
    have w₃ : ((coyoneda.map (d' ◁ adj.unit.app d).op).app (R.obj c)) =
        ((ihom.adjunction d').homEquiv _ _).symm ∘
          ((coyoneda.map (adj.unit.app _).op).app _) ∘ (ihom.adjunction d').homEquiv _ _ := by
      ext
      simp only [Functor.id_obj, op_tensorObj, coyoneda_obj_obj, unop_tensorObj, Functor.comp_obj,
        coyoneda_map_app, Quiver.Hom.unop_op, tensorLeft_obj, Function.comp_apply]
      erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit]
      simp
    rw [w₃, isIso_iff_bijective]
    simp only [Functor.comp_obj, op_tensorObj, coyoneda_obj_obj, unop_tensorObj, Functor.id_obj,
      yoneda_obj_obj, tensorLeft_obj, EquivLike.comp_bijective, EquivLike.bijective_comp]
    have w₄ : (coyoneda.map (adj.unit.app d).op).app ((ihom d').obj (R.obj c)) ≫
        (coyoneda.obj ⟨d⟩).map (adj.unit.app ((ihom d').obj (R.obj c))) =
          (coyoneda.obj ⟨(L ⋙ R).obj d⟩).map (adj.unit.app ((ihom d').obj (R.obj c))) ≫
            (coyoneda.map (adj.unit.app d).op).app _ := by simp
    rw [← isIso_iff_bijective]
    suffices IsIso ((coyoneda.map (adj.unit.app d).op).app ((ihom d').obj (R.obj c)) ≫
        (coyoneda.obj ⟨d⟩).map (adj.unit.app ((ihom d').obj (R.obj c)))) from
      IsIso.of_isIso_comp_right _ ((coyoneda.obj ⟨d⟩).map (adj.unit.app ((ihom d').obj (R.obj c))))
    rw [w₄]
    refine IsIso.comp_isIso' inferInstance ?_
    exact isIso_coyoneda_unit _ _ _ _ _
  tfae_have 2 ↔ 3
  · -- `simp_rw [isIso_iff_isIso_coyoneda_map]` times out, so instead we use `conv`:
    conv => lhs; intro c d; rw [isIso_iff_isIso_yoneda_map]
    conv => rhs; intro d d'; rw [isIso_iff_isIso_coyoneda_map]
    -- this seems unnecessarily complicated to bring the quantifiers out of the `↔`:
    rw [forall_swap]; apply forall_congr'; intro d
    rw [forall_swap]; apply forall₂_congr; intro d' c
    have w₁ : ((coyoneda.map (L.map (adj.unit.app d ▷ d')).op).app c) =
        (adj.homEquiv _ _).symm ∘
          (coyoneda.map (adj.unit.app d ▷ d').op).app (R.obj c) ∘
            (adj.homEquiv _ _) := by ext; simp
    have w₂' : ((yoneda.map ((pre (adj.unit.app d)).app (R.obj c))).app ⟨d'⟩) ∘
        ((ihom.adjunction ((L ⋙ R).obj d)).homEquiv _ _) =
          ((ihom.adjunction d).homEquiv _ _) ∘
            ((coyoneda.map (adj.unit.app d ▷ d').op).app (R.obj c)) := by
      ext
      simp only [Functor.id_obj, yoneda_obj_obj, Functor.comp_obj, tensorLeft_obj,
        Function.comp_apply, yoneda_map_app, op_tensorObj, coyoneda_obj_obj, unop_tensorObj,
        op_whiskerRight, coyoneda_map_app, unop_whiskerRight, Quiver.Hom.unop_op]
      erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
      simp
    have w₂ : ((yoneda.map ((pre (adj.unit.app d)).app (R.obj c))).app ⟨d'⟩) =
          ((ihom.adjunction d).homEquiv _ _) ∘
            ((coyoneda.map (adj.unit.app d ▷ d').op).app (R.obj c)) ∘
              ((ihom.adjunction ((L ⋙ R).obj d)).homEquiv _ _).symm := by
      rw [← Function.comp.assoc, ← w₂']; ext; simp
    rw [w₂, w₁, isIso_iff_bijective, isIso_iff_bijective]
    simp
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
          assoc, IsIso.eq_inv_comp]
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
