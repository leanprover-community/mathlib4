/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Ben Eltschig
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `HToF`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully faithful.
  This is defined in terms of the units of the adjunctions, but a formula in terms of the counits
  is also given.
* `counit_unit_eq_whiskerRight`: when `G` is fully faithful, the natural transformation
  `H ⋙ G ⟶ F ⋙ G` given by `adj₂.counit ≫ adj₁.unit` is just `HToF` whiskered with `G`.
* `HToF_epi_iff_whiskerRight_unit_epi`: assuming `D` has all pushouts, `HToF : H ⟶ F` is epic iff
  the whiskering `H ⟶ F ⋙ G ⋙ H` of `adj₁.unit` and `H` is. For the components this holds even
  without assumptions on `D`.
* `HToF_epi_iff_counit_unit_epi`: assuming `D` has all pushouts, `HToF : H ⟶ F` is epic iff
  `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is. For the components this holds even without
  assumptions on `D`.
* `FToH`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `G` are fully
  faithful. This is defined in terms of the units of the adjunctions, but a formula in terms of the
  counits is also given.
* `counit_unit_eq_whiskerLeft`: when `F` and `H` are fully faithful, the natural transformation
  `G ⋙ F ⟶ G ⋙ H` given by `adj₁.counit ≫ adj₂.unit` is just `G` whiskered with `FToH`.
* `FToH_mono_iff_whiskerLeft_unit_mono`: assuming `D` has all pullbacks, `FToH : F ⟶ H` is monic iff
  the whiskering `F ⟶ F ⋙ G ⋙ H` of `F` and `adj₂.unit` is. For the components this holds even
  without assumptions on `D`.
* `FToH_mono_iff_counit_unit_mono`: assuming `D` has all pullbacks, `FToH : H ⟶ F` is monic iff
  `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` is. For the components this holds even without
  assumptions on `D`.
-/

open CategoryTheory Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D]
variable {F H : C ⥤ D} {G : D ⥤ C}
variable (adj₁ : F ⊣ G) (adj₂ : G ⊣ H)

lemma isIso_unit_iff_isIso_counit : IsIso adj₁.unit ↔ IsIso adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := adj₁.comp adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso adj₁.unit).symm
    exact adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso adj₂.counit)
    exact adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso adj₂.counit := by
      rw [← adj₁.isIso_unit_iff_isIso_counit adj₂]
      infer_instance
    adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso adj₁.unit := by
      rw [adj₁.isIso_unit_iff_isIso_counit adj₂]
      infer_instance
    adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the unit of the first adjunction under `H`. -/
lemma homEquiv_counit_unit_app_eq_H_map_unit {X : C} :
    adj₂.homEquiv _ _ (adj₂.counit.app X ≫ adj₁.unit.app X) = H.map (adj₁.unit.app X) := by
  simp [Adjunction.homEquiv_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the counit of the second adjunction under `F`. -/
lemma homEquiv_symm_counit_unit_app_eq_F_map_counit {X : C} :
    (adj₁.homEquiv _ _).symm (adj₂.counit.app X ≫ adj₁.unit.app X) = F.map (adj₂.counit.app X) := by
  simp [Adjunction.homEquiv_symm_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the unit of the second adjunction under `G`. -/
lemma homEquiv_counit_unit_app_eq_G_map_unit {X : D} :
    adj₁.homEquiv _ _ (adj₁.counit.app X ≫ adj₂.unit.app X) = G.map (adj₂.unit.app X) := by
  simp [homEquiv_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the counit of the first adjunction under `G`. -/
lemma homEquiv_symm_counit_unit_app_eq_G_map_counit {X : D} :
    (adj₂.homEquiv _ _).symm (adj₁.counit.app X ≫ adj₂.unit.app X) = G.map (adj₁.counit.app X) := by
  simp [homEquiv_symm_apply]

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the two natural transformations
`H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and units of either
adjunction agree. Note that this is also true when `F` and `H` are fully faithful instead of `G`;
see `whiskered_counit_unit_eq_of_outer` for the corresponding variant of this lemma. -/
lemma whiskered_counit_unit_eq_of_inner :
    whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (adj₁.counit_naturality <| (whiskerRight adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (adj₂.counit_naturality (adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣ H` where `G`
is fully faithful, given here as the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction
followed by the inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second. -/
@[simps!]
noncomputable def HToF : H ⟶ F :=
  H.leftUnitor.inv ≫ whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
  inv (whiskerLeft F adj₂.unit) ≫ F.rightUnitor.hom

/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second. -/
lemma HToF_eq_counits :
    HToF adj₁ adj₂ = H.rightUnitor.inv ≫ inv (whiskerLeft H adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; dsimp [HToF]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app (whiskered_counit_unit_eq_of_inner adj₁ adj₂) X

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the components of the natural
transformation `H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are simply
the images of the components of the natural transformation `H ⟶ F` under `G`. -/
lemma counit_unit_app_eq_map_HToF {X : C} :
    adj₂.counit.app X ≫ adj₁.unit.app X = G.map ((HToF adj₁ adj₂).app X) := by
  refine ((adj₂.homEquiv _ _).symm_apply_apply _).symm.trans ?_
  rw [homEquiv_counit_unit_app_eq_H_map_unit]; dsimp
  rw [Adjunction.homEquiv_symm_apply, ← Adjunction.inv_map_unit, ← G.map_inv,
    ← G.map_comp, HToF_app]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions is simply the
natural transformation `H ⟶ F` whiskered with `G`. -/
lemma counit_unit_eq_whiskerRight : adj₂.counit ≫ adj₁.unit = whiskerRight (HToF adj₁ adj₂) G := by
  ext X; exact counit_unit_app_eq_map_HToF adj₁ adj₂

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is dual to the natural transformation `F.op ⟶ H.op` obtained from the dual adjoint
triple `H.op ⊣ G.op ⊣ F.op`. -/
lemma HToF_op : NatTrans.op (HToF adj₁ adj₂) = HToF adj₂.op adj₁.op := by
  ext; rw [HToF, HToF_eq_counits]; simp

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the components of the
natural transformation `H ⟶ F` are dual to the components of the natural transformation
`F.op ⟶ H.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op`. -/
lemma HToF_app_op {X : C} : ((HToF adj₁ adj₂).app X).op = (HToF adj₂.op adj₁.op).app (.op X) :=
  NatTrans.congr_app (HToF_op adj₁ adj₂) _

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the unit of the adjunction `F ⊣ G` under `H` is. -/
lemma HToF_app_epi_iff_map_unit_app_epi {X : C} :
    Epi ((HToF adj₁ adj₂).app X) ↔ Epi (H.map (adj₁.unit.app X)) := by
  rw [← epi_isIso_comp_iff (H.map (adj₂.counit.app _)) (H.map (adj₁.unit.app _)),
    ← H.map_comp, counit_unit_app_eq_map_HToF]
  exact Functor.epi_map_congr_iso _ (asIso (adj₂.unit))

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and its codomain has
all pushouts, the natural transformation `H ⟶ F` is epic iff the unit of the adjunction `F ⊣ G`
whiskered with `H` is. -/
lemma HToF_epi_iff_whiskerRight_unit_epi [HasPushouts D] :
    Epi (HToF adj₁ adj₂) ↔ Epi (whiskerRight adj₁.unit H) := by
  repeat rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun _ ↦ adj₁.HToF_app_epi_iff_map_unit_app_epi adj₂

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint), the components of the natural
transformation `H ⟶ F` are epic iff the respective components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are. -/
lemma HToF_app_epi_iff_counit_unit_app_epi [H.PreservesEpimorphisms] {X : C} :
    Epi ((HToF adj₁ adj₂).app X) ↔ Epi (adj₂.counit.app X ≫ adj₁.unit.app X) := by
  have _ := adj₂.isLeftAdjoint
  refine ⟨fun h ↦ by rw [counit_unit_app_eq_map_HToF]; exact G.map_epi _, fun h ↦ ?_⟩
  rw [HToF_app, ← homEquiv_counit_unit_app_eq_H_map_unit adj₁ adj₂, adj₂.homEquiv_apply]
  infer_instance

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint) and both categories have
all pushouts, the natural transformation `H ⟶ F` is epic iff the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions is. -/
lemma HToF_epi_iff_counit_unit_epi [HasPushouts C] [HasPushouts D] [H.PreservesEpimorphisms] :
    Epi (HToF adj₁ adj₂) ↔ Epi (adj₂.counit ≫ adj₁.unit) := by
  repeat rw [NatTrans.epi_iff_epi_app]
  exact forall_congr' fun _ ↦ adj₁.HToF_app_epi_iff_counit_unit_app_epi adj₂

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

omit [F.Full] [F.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the two natural
transformations `H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and unit
of either adjunction agree. Note that this is also true when `G` is fully faithful instead of `F`
and `H`; see `whiskered_counit_unit_eq_of_inner` for the corresponding variant of this lemma. -/
lemma whiskered_counit_unit_eq_of_outer :
    whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (adj₁.counit_naturality <| (whiskerRight adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (adj₂.counit_naturality (adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣ H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the first. -/
@[simps!]
noncomputable def FToH : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight adj₁.unit H) ≫ H.leftUnitor.hom

/-- The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` and `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first. -/
lemma FToH_eq_counits :
    FToH adj₁ adj₂ = F.leftUnitor.inv ≫ inv (whiskerRight adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [FToH]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app (whiskered_counit_unit_eq_of_outer adj₁ adj₂).symm X

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions
are simply the components of the natural transformation `F ⟶ H` at `G`. -/
lemma counit_unit_app_eq_FToH_app {X : D} :
    adj₁.counit.app X ≫ adj₂.unit.app X = (FToH adj₁ adj₂).app (G.obj X) := by
  refine ((adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_
  rw [homEquiv_symm_counit_unit_app_eq_G_map_counit, adj₂.homEquiv_apply, FToH_app, ← H.map_inv]
  congr
  exact IsIso.eq_inv_of_hom_inv_id (adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions is simply
the natural transformation `F ⟶ H` whiskered from the left with `G`. -/
lemma counit_unit_eq_whiskerLeft : adj₁.counit ≫ adj₂.unit = whiskerLeft G (FToH adj₁ adj₂) := by
  ext X; exact counit_unit_app_eq_FToH_app adj₁ adj₂

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is dual to the natural transformation `H.op ⟶ F.op` obtained from the
dual adjoint triple `H.op ⊣ G.op ⊣ F.op`. -/
lemma FToH_op : NatTrans.op (FToH adj₁ adj₂) = FToH adj₂.op adj₁.op := by
  ext; rw [FToH, FToH_eq_counits]; simp

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `F ⟶ H` are dual to the components of the natural transformation
`H.op ⟶ F.op` obtained from the dual adjoint triple `H.op ⊣ G.op ⊣ F.op`. -/
lemma FToH_app_op {X : C} : ((FToH adj₁ adj₂).app X).op = (FToH adj₂.op adj₁.op).app (.op X) :=
  NatTrans.congr_app (FToH_op adj₁ adj₂) _

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the unit of the adjunction `G ⊣ H` is monic
at `F.obj X`. -/
lemma FToH_app_mono_iff_unit_app_mono {X : C} :
    Mono ((FToH adj₁ adj₂).app X) ↔ Mono (adj₂.unit.app (F.obj X)) := by
  rw [← mono_isIso_comp_iff (adj₁.counit.app _) (adj₂.unit.app _), counit_unit_app_eq_FToH_app]
  exact NatTrans.mono_app_congr_iso (asIso (adj₁.unit.app X))

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful and their codomain has
all pullbacks, the natural transformation `F ⟶ H` is monic iff `F` whiskered with the unit of the
adjunction `G ⊣ H` is. -/
lemma FToH_mono_iff_whiskerLeft_unit_mono [HasPullbacks D] :
    Mono (FToH adj₁ adj₂) ↔ Mono (whiskerLeft F adj₂.unit) := by
  repeat rw [NatTrans.mono_iff_mono_app]
  exact forall_congr' fun _ ↦ adj₁.FToH_app_mono_iff_unit_app_mono adj₂

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, all components of the
natural transformation `F ⟶ H` are monic iff all components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are.
Note that unlike `HToF_app_epi_iff_counit_unit_app_epi`, this equivalence does not make sense on a
per-object basis because the components of the two natural transformations are indexed by different
categories. -/
lemma FToH_app_mono_iff_counit_unit_app_mono :
    (∀ X, Mono ((FToH adj₁ adj₂).app X)) ↔ ∀ X, Mono (adj₁.counit.app X ≫ adj₂.unit.app X) := by
  refine ⟨fun h X ↦ by rw [counit_unit_app_eq_FToH_app]; exact h _, fun h X ↦ ?_⟩
  specialize h (H.obj X)
  rw [counit_unit_app_eq_FToH_app] at h
  exact (NatTrans.mono_app_congr_iso (asIso (adj₂.counit.app X))).1 h

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful and their codomain has
all pullbacks, the natural transformation `F ⟶ H` is monic iff the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions is. -/
lemma FToH_mono_iff_counit_unit_mono [HasPullbacks D] :
    Mono (FToH adj₁ adj₂) ↔ Mono (adj₁.counit ≫ adj₂.unit) := by
  repeat rw [NatTrans.mono_iff_mono_app]
  exact adj₁.FToH_app_mono_iff_counit_unit_app_mono adj₂

end OuterFullyFaithful

end CategoryTheory.Adjunction
