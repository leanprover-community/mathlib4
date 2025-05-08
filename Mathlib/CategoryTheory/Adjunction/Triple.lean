/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Ben Eltschig
-/
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Monad.Adjunction
/-!

# Adjoint triples

This file concerns adjoint triples `F ⊣ G ⊣ H` of functors `F H : C ⥤ D`, `G : D ⥤ C`. We first
prove that `F` is fully faithful iff `H` is, and then prove results about the two special cases
where `G` is fully faithful or `F` and `H` are.

## Main results

All results are about an adjoint triple `F ⊣ G ⊣ H` where `adj₁ : F ⊣ G` and `adj₂ : G ⊣ H`. We
bundle the adjunctions in a structure `Triple F G H`.
* `fullyFaithfulEquiv`: `F` is fully faithful iff `H` is.
* `rightToLeft`: the canonical natural transformation `H ⟶ F` that exists whenever `G` is fully
  faithful. This is defined in terms of the units of the adjunctions, but a formula in terms of the
  counits is also given.
* `counit_unit_eq_whiskerRight`: when `G` is fully faithful, the natural transformation
  `H ⋙ G ⟶ F ⋙ G` given by `adj₂.counit ≫ adj₁.unit` is just `rightToLeft` whiskered with `G`.
* `rightToLeft_app_epi_iff_map_unit_app_epi`: `rightToLeft : H ⟶ F` is epi at `X` iff the image of
  `adj₁.unit.app X` under `H` is.
* `rightToLeft_app_epi_iff_counit_unit_app_epi`: when `H` preserves epimorphisms,
  `rightToLeft : H ⟶ F` is epic at `X` iff `adj₂.counit ≫ adj₁.unit : H ⋙ G ⟶ F ⋙ G` is.
* `leftToRight`: the canonical natural transformation `F ⟶ H` that exists whenever `F` and `G` are
  fully faithful. This is defined in terms of the units of the adjunctions, but a formula in terms
  of the counits is also given.
* `counit_unit_eq_whiskerLeft`: when `F` and `H` are fully faithful, the natural transformation
  `G ⋙ F ⟶ G ⋙ H` given by `adj₁.counit ≫ adj₂.unit` is just `G` whiskered with `leftToRight`.
* `leftToRight_app_mono_iff_unit_app_mono`: `leftToRight : F ⟶ H` is monic at `X` iff `adj₂.unit`
  is monic at `F.obj X`.
* `leftToRight_app_mono_iff_counit_unit_app_mono`: all components of `leftToRight : H ⟶ F` are
  monic iff all components of `adj₁.counit ≫ adj₂.unit : G ⋙ F ⟶ G ⋙ H` are.
-/

open CategoryTheory

variable {C D : Type*} [Category C] [Category D]
variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

/-- Structure containing the two adjunctions of an adjoint triple `F ⊣ G ⊣ H`. -/
structure CategoryTheory.Adjunction.Triple where
  /- Adjunction `F ⊣ G` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₁ : F ⊣ G
  /- Adjunction `G ⊣ H` of the adjoint triple `F ⊣ G ⊣ H`. -/
  adj₂ : G ⊣ H

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

lemma isIso_unit_iff_isIso_counit : IsIso t.adj₁.unit ↔ IsIso t.adj₂.counit := by
  let adj : F ⋙ G ⊣ H ⋙ G := t.adj₁.comp t.adj₂
  constructor
  · intro h
    let idAdj : 𝟭 C ⊣ H ⋙ G := adj.ofNatIsoLeft (asIso t.adj₁.unit).symm
    exact t.adj₂.isIso_counit_of_iso (idAdj.rightAdjointUniq id)
  · intro h
    let adjId : F ⋙ G ⊣ 𝟭 C := adj.ofNatIsoRight (asIso t.adj₂.counit)
    exact t.adj₁.isIso_unit_of_iso (adjId.leftAdjointUniq id)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the unit of the first adjunction under `H`. -/
lemma homEquiv_counit_unit_app_eq_H_map_unit {X : C} :
    t.adj₂.homEquiv _ _ (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) = H.map (t.adj₁.unit.app X) := by
  simp [Adjunction.homEquiv_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the counit of the second adjunction under `F`. -/
lemma homEquiv_symm_counit_unit_app_eq_F_map_counit {X : C} :
    (t.adj₁.homEquiv _ _).symm (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) =
      F.map (t.adj₂.counit.app X) := by
  simp [Adjunction.homEquiv_symm_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the first adjunction adjunct to the image of the unit of the second adjunction under `G`. -/
lemma homEquiv_counit_unit_app_eq_G_map_unit {X : D} :
    t.adj₁.homEquiv _ _ (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) = G.map (t.adj₂.unit.app X) := by
  simp [homEquiv_apply]

/-- For an adjoint triple `F ⊣ G ⊣ H`, the components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are
under the second adjunction adjunct to the image of the counit of the first adjunction under `G`. -/
lemma homEquiv_symm_counit_unit_app_eq_G_map_counit {X : D} :
    (t.adj₂.homEquiv _ _).symm (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) =
      G.map (t.adj₁.counit.app X) := by
  simp [homEquiv_symm_apply]

section InnerFullyFaithful

variable [G.Full] [G.Faithful]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the two natural transformations
`H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and units of either
adjunction agree. Note that this is also true when `F` and `H` are fully faithful instead of `G`;
see `whiskered_counit_unit_eq_of_outer` for the corresponding variant of this lemma. -/
lemma whiskered_counit_unit_eq_of_inner :
    whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (t.adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (t.adj₂.counit_naturality (t.adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| t.adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `H ⟶ F` that exists for every adjoint triple `F ⊣ G ⊣ H` where `G`
is fully faithful, given here as the whiskered unit `H ⟶ F ⋙ G ⋙ H` of the first adjunction
followed by the inverse of the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second. -/
@[simps!]
noncomputable def rightToLeft : H ⟶ F :=
  H.leftUnitor.inv ≫ whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom ≫
  inv (whiskerLeft F t.adj₂.unit) ≫ F.rightUnitor.hom

/-- The natural transformation `H ⟶ F` for an adjoint triple `F ⊣ G ⊣ H` with `G` fully faithful
is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first adjunction
followed by the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second. -/
lemma rightToLeft_eq_counits :
    t.rightToLeft = H.rightUnitor.inv ≫ inv (whiskerLeft H t.adj₁.counit) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom := by
  ext X; dsimp [rightToLeft]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app t.whiskered_counit_unit_eq_of_inner X

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the components of the natural
transformation `H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are simply
the images of the components of the natural transformation `H ⟶ F` under `G`. -/
lemma counit_unit_app_eq_map_rightToLeft {X : C} :
    t.adj₂.counit.app X ≫ t.adj₁.unit.app X = G.map (t.rightToLeft.app X) := by
  refine ((t.adj₂.homEquiv _ _).symm_apply_apply _).symm.trans ?_
  rw [homEquiv_counit_unit_app_eq_H_map_unit]; dsimp
  rw [Adjunction.homEquiv_symm_apply, ← Adjunction.inv_map_unit, ← G.map_inv,
    ← G.map_comp, rightToLeft_app]

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions is simply the
natural transformation `H ⟶ F` whiskered with `G`. -/
lemma counit_unit_eq_whiskerRight : t.adj₂.counit ≫ t.adj₁.unit = whiskerRight t.rightToLeft G := by
  ext X; exact t.counit_unit_app_eq_map_rightToLeft

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful, the natural transformation
`H ⟶ F` is epic at `X` iff the image of the unit of the adjunction `F ⊣ G` under `H` is. -/
lemma rightToLeft_app_epi_iff_map_unit_app_epi {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (H.map (t.adj₁.unit.app X)) := by
  rw [← epi_isIso_comp_iff (H.map (t.adj₂.counit.app _)) (H.map (t.adj₁.unit.app _)),
    ← H.map_comp, counit_unit_app_eq_map_rightToLeft]
  exact Functor.epi_map_congr_iso _ (asIso t.adj₂.unit)

/-- For an adjoint triple `F ⊣ G ⊣ H` where `G` is fully faithful and `H` preserves epimorphisms
(which is for example the case if `H` has a further right adjoint), the components of the natural
transformation `H ⟶ F` are epic iff the respective components of the natural transformation
`H ⋙ G ⟶ F ⋙ G` obtained from the units and counits of the adjunctions are. -/
lemma rightToLeft_app_epi_iff_counit_unit_app_epi [H.PreservesEpimorphisms] {X : C} :
    Epi (t.rightToLeft.app X) ↔ Epi (t.adj₂.counit.app X ≫ t.adj₁.unit.app X) := by
  have _ := t.adj₂.isLeftAdjoint
  refine ⟨fun h ↦ by rw [counit_unit_app_eq_map_rightToLeft]; exact G.map_epi _, fun h ↦ ?_⟩
  rw [rightToLeft_app, ← t.homEquiv_counit_unit_app_eq_H_map_unit, t.adj₂.homEquiv_apply]
  infer_instance

end InnerFullyFaithful

section OuterFullyFaithful

variable [F.Full] [F.Faithful] [H.Full] [H.Faithful]

omit [F.Full] [F.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the two natural
transformations `H ⋙ G ⋙ F ⟶ F ⋙ G ⋙ H` obtained by following the whiskered counit and unit
of either adjunction agree. Note that this is also true when `G` is fully faithful instead of `F`
and `H`; see `whiskered_counit_unit_eq_of_inner` for the corresponding variant of this lemma. -/
lemma whiskered_counit_unit_eq_of_outer :
    whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom ≫ H.leftUnitor.inv ≫
    whiskerRight t.adj₁.unit H ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).inv ≫ whiskerRight t.adj₂.counit F ≫ F.leftUnitor.hom ≫
    F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit := by
  ext X
  dsimp; simp only [Category.id_comp, Category.comp_id]
  refine (t.adj₁.counit_naturality <| (whiskerRight t.adj₁.unit H).app X).symm.trans ?_
  rw [whiskerRight_app, (asIso (t.adj₂.counit.app (G.obj _))).eq_comp_inv.2
      (t.adj₂.counit_naturality (t.adj₁.unit.app X)),
    ← (asIso _).comp_hom_eq_id.1 <| t.adj₂.left_triangle_components (F.obj X)]
  simp

/-- The natural transformation `F ⟶ H` that exists for every adjoint triple `F ⊣ G ⊣ H` where `F`
and `H` are fully faithful, given here as the whiskered unit `F ⟶ F ⋙ G ⋙ H` of the second
adjunction followed by the inverse of the whiskered unit `F ⋙ G ⋙ H ⟶ H` of the first. -/
@[simps!]
noncomputable def leftToRight : F ⟶ H :=
  F.rightUnitor.inv ≫ whiskerLeft F t.adj₂.unit ≫ (Functor.associator _ _ _).inv ≫
  inv (whiskerRight t.adj₁.unit H) ≫ H.leftUnitor.hom

/-- The natural transformation `F ⟶ H` for an adjoint triple `F ⊣ G ⊣ H` with `F` and `H`
fully faithful is also equal to the inverse of the whiskered counit `H ⋙ G ⋙ F ⟶ F` of the second
adjunction followed by the whiskered counit `H ⋙ G ⋙ F ⟶ H` of the first. -/
lemma leftToRight_eq_counits :
    t.leftToRight = F.leftUnitor.inv ≫ inv (whiskerRight t.adj₂.counit F) ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft H t.adj₁.counit ≫ H.rightUnitor.hom := by
  ext X; dsimp [leftToRight]
  simp only [NatIso.isIso_inv_app, Functor.comp_obj, Category.comp_id, Category.id_comp]
  rw [IsIso.comp_inv_eq]
  simpa using congr_app t.whiskered_counit_unit_eq_of_outer.symm X

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the components of the
natural transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions
are simply the components of the natural transformation `F ⟶ H` at `G`. -/
lemma counit_unit_app_eq_leftToRight_app {X : D} :
    t.adj₁.counit.app X ≫ t.adj₂.unit.app X = t.leftToRight.app (G.obj X) := by
  refine ((t.adj₂.homEquiv _ _).apply_symm_apply _).symm.trans ?_
  rw [homEquiv_symm_counit_unit_app_eq_G_map_counit, homEquiv_apply, leftToRight_app, ← H.map_inv]
  congr
  exact IsIso.eq_inv_of_hom_inv_id (t.adj₁.right_triangle_components _)

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions is simply
the natural transformation `F ⟶ H` whiskered from the left with `G`. -/
lemma counit_unit_eq_whiskerLeft : t.adj₁.counit ≫ t.adj₂.unit = whiskerLeft G t.leftToRight := by
  ext X; exact t.counit_unit_app_eq_leftToRight_app

omit [H.Full] [H.Faithful] in
/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, the natural
transformation `F ⟶ H` is monic at `X` iff the unit of the adjunction `G ⊣ H` is monic
at `F.obj X`. -/
lemma leftToRight_app_mono_iff_unit_app_mono {X : C} :
    Mono (t.leftToRight.app X) ↔ Mono (t.adj₂.unit.app (F.obj X)) := by
  rw [← mono_isIso_comp_iff (t.adj₁.counit.app _) (t.adj₂.unit.app _),
    counit_unit_app_eq_leftToRight_app]
  exact NatTrans.mono_app_congr_iso (asIso (t.adj₁.unit.app X))

/-- For an adjoint triple `F ⊣ G ⊣ H` where `F` and `H` are fully faithful, all components of the
natural transformation `F ⟶ H` are monic iff all components of the natural transformation
`G ⋙ F ⟶ G ⋙ H` obtained from the units and counits of the adjunctions are.
Note that unlike `rightToLeft_app_epi_iff_counit_unit_app_epi`, this equivalence does not make sense
on a per-object basis because the components of the two natural transformations are indexed by
different categories. -/
lemma leftToRight_app_mono_iff_counit_unit_app_mono :
    (∀ X, Mono (t.leftToRight.app X)) ↔ ∀ X, Mono (t.adj₁.counit.app X ≫ t.adj₂.unit.app X) := by
  refine ⟨fun h X ↦ by rw [counit_unit_app_eq_leftToRight_app]; exact h _, fun h X ↦ ?_⟩
  specialize h (H.obj X)
  rw [counit_unit_app_eq_leftToRight_app] at h
  exact (NatTrans.mono_app_congr_iso (asIso (t.adj₂.counit.app X))).1 h

end OuterFullyFaithful

end CategoryTheory.Adjunction.Triple
