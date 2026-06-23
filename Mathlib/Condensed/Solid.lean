/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Thomas Riepe
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits
import Mathlib.Topology.Category.Profinite.AsLimit
/-!
# Solid modules

This file contains the definition of a solid `R`-module: `CondensedMod.IsSolid R`.
Solid modules were introduced in [scholze2019condensed], Definition 5.1.

## Main theorems

* `CondensedMod.profiniteSolidCounit_isIso`
* `CondensedMod.profiniteSolidification_isIso_at_fintype`
* `CondensedMod.isSolid_of_isLimit_gen`
* `CondensedMod.profiniteSolid_obj_isSolid` (modulo two axioms)

## Axioms

* `surj_factor`, `sol_leftCancel`: mathematically proved in Clausen-Scholze,
  Condensed Mathematics Theorem 5.8. Not yet formalizable in Lean without
  the CompHaus ↔ TopMod equivalence.

## TODO

* `surj_factor` can be eliminated using `finFree_isColimit_at` once the
  Mathlib API for discrete condensed modules stabilizes.
-/

universe u
variable (R : Type (u + 1)) [Ring R]
open CategoryTheory Limits Profinite Condensed
noncomputable section
namespace Condensed

abbrev finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

abbrev profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R :=
  profiniteToCondensed ⋙ free R

def profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R :=
  Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

def profiniteSolidCounit : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R :=
  Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

instance : (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R) := by
  dsimp only [profiniteSolidCounit, profiniteSolid]; infer_instance

def profiniteSolidIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _ (profiniteSolidCounit R)).IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _
    (NatTrans.id (profiniteFree R))

end Condensed

class CondensedMod.IsSolid (A : CondensedMod.{u} R) : Prop where
  isIso_solidification_map : ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map
    ((Condensed.profiniteSolidification R).app X).op)

namespace CondensedMod

open CategoryTheory Limits Profinite Condensed Functor Opposite

lemma profiniteSolidCounit_isIso (T : FintypeCat.{u}) :
    IsIso ((profiniteSolidCounit R).app T) := by
  haveI : IsIso (profiniteSolidCounit R) :=
    (profiniteSolidIsPointwiseRightKanExtension R).isIso_hom
  infer_instance

lemma profiniteSolidification_comp_counit (T : FintypeCat.{u}) :
    (profiniteSolidification R).app (FintypeCat.toProfinite.obj T) ≫
    (profiniteSolidCounit R).app T = CategoryStruct.id _ := by
  simp only [profiniteSolidification]
  exact (profiniteSolid R).liftOfIsRightKanExtension_fac_app
          (profiniteSolidCounit R) (profiniteFree R) (NatTrans.id _) T

lemma profiniteSolidification_isIso_at_fintype (T : FintypeCat.{u}) :
    IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) := by
  haveI := profiniteSolidCounit_isIso R T
  exact isIso_of_comp_hom_eq_id ((profiniteSolidCounit R).app T)
          (profiniteSolidification_comp_counit R T)

theorem profiniteSolid_isSolid_at_fintype (S : Profinite.{u}) (T : FintypeCat.{u}) :
    IsIso ((yoneda.obj ((profiniteSolid R).obj S)).map
           ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)).op) := by
  haveI : IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) :=
    profiniteSolidification_isIso_at_fintype R T
  infer_instance

noncomputable def finFreeIsoSolid (T : FintypeCat.{u}) :
    (profiniteSolid R).obj (FintypeCat.toProfinite.obj T) ≅ (finFree R).obj T :=
  @asIso _ _ _ _ ((profiniteSolidCounit R).app T) (profiniteSolidCounit_isIso R T)

lemma sol_map_counit (T : FintypeCat.{u}) (X : Profinite.{u})
    (psi : X ⟶ FintypeCat.toProfinite.obj T) :
    (profiniteSolidification R).app X ≫ (profiniteSolid R).map psi ≫
    (finFreeIsoSolid R T).hom = (profiniteFree R).map psi := by
  rw [show (finFreeIsoSolid R T).hom = (profiniteSolidCounit R).app T from rfl,
      ← Category.assoc, ← (profiniteSolidification R).naturality psi,
      Category.assoc, profiniteSolidification_comp_counit, Category.comp_id]

axiom surj_factor (T : FintypeCat.{u}) (X : Profinite.{u})
    (h : (profiniteFree R).obj X ⟶ (finFree R).obj T) :
    ∃ (U₀ : FintypeCat.{u}) (q₀ : X ⟶ FintypeCat.toProfinite.obj U₀)
      (h₀ : (profiniteFree R).obj (FintypeCat.toProfinite.obj U₀) ⟶ (finFree R).obj T),
      h = (profiniteFree R).map q₀ ≫ h₀

axiom sol_leftCancel (T : FintypeCat.{u}) (X : Profinite.{u})
    (f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T)
    (h : (profiniteSolidification R).app X ≫ f =
         (profiniteSolidification R).app X ≫ g) : f = g

theorem profiniteSolid_fintype_isSolid (T : FintypeCat.{u}) :
    ((profiniteSolid R).obj (FintypeCat.toProfinite.obj T)).IsSolid := by
  constructor; intro X
  rw [show IsIso _ ↔ Function.Bijective _ from isIso_iff_bijective _]
  constructor
  · intro g g' hgg'
    have h_step : g ≫ (finFreeIsoSolid R T).hom = g' ≫ (finFreeIsoSolid R T).hom :=
      sol_leftCancel R T X _ _
        (by have h1 := congrArg (· ≫ (finFreeIsoSolid R T).hom) hgg'
            simp only [Category.assoc] at h1; exact h1)
    have key := congrArg (· ≫ (finFreeIsoSolid R T).inv) h_step
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at key; exact key
  · intro h
    let h' : (profiniteFree R).obj X ⟶ (finFree R).obj T :=
      h ≫ (finFreeIsoSolid R T).hom
    obtain ⟨U₀, q₀, h₀, hfact⟩ := surj_factor R T X h'
    refine ⟨(profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom ≫
            h₀ ≫ (finFreeIsoSolid R T).inv, ?_⟩
    have step1 := congrArg (· ≫ h₀ ≫ (finFreeIsoSolid R T).inv) (sol_map_counit R U₀ X q₀)
    have step2 : (profiniteFree R).map q₀ ≫ h₀ ≫ (finFreeIsoSolid R T).inv = h := by
      have key2 := congrArg (· ≫ (finFreeIsoSolid R T).inv) hfact.symm
      simp only [Category.assoc] at key2
      rw [key2, show h' = h ≫ (finFreeIsoSolid R T).hom from rfl,
          Category.assoc, (finFreeIsoSolid R T).hom_inv_id, Category.comp_id]
    exact step1.trans step2

lemma isSolid_of_isLimit_gen {J : Type*} [Category J] {F : J ⥤ CondensedMod.{u} R}
    (c : Cone F) (hc : IsLimit c) (hj : ∀ j, (F.obj j).IsSolid) : c.pt.IsSolid := by
  refine ⟨fun X => ?_⟩
  rw [show IsIso _ ↔ Function.Bijective _ from isIso_iff_bijective _]
  set sol := (profiniteSolidification R).app X
  -- Convert IsIso to bijective for each j using isIso_iff_bijective with explicit argument
  have bijFun : ∀ j, Function.Bijective ((yoneda.obj (F.obj j)).map sol.op) := by
    intro j
    have h := (hj j).isIso_solidification_map X
    exact (isIso_iff_bijective ((yoneda.obj (F.obj j)).map sol.op)).mp h
  constructor
  · intro f g hfg
    apply hc.hom_ext; intro j
    exact (bijFun j).1 (congrArg (· ≫ c.π.app j) hfg)
  · intro h_map
    choose g_j hg_j using fun j => (bijFun j).2 (h_map ≫ c.π.app j)
    have compat : ∀ {j k : J} (phi : j ⟶ k), g_j j ≫ F.map phi = g_j k :=
      fun j k phi =>
        (bijFun k).1 ((by rw [← Category.assoc, hg_j j, Category.assoc, c.w phi]).trans
                      (hg_j k).symm)
    let g_cone : Cone F :=
      { pt := (profiniteSolid R).obj X
        π  := { app := g_j
                naturality := fun j k phi => by
                  simp only [Category.id_comp]
                  exact (compat phi).symm } }
    refine ⟨hc.lift g_cone, ?_⟩
    apply hc.hom_ext; intro j
    rw [Category.assoc, hc.fac g_cone j]; exact hg_j j

theorem finFree_isSolid (T : FintypeCat.{u}) : ((finFree R).obj T).IsSolid := by
  constructor; intro X
  rw [show IsIso _ ↔ Function.Bijective _ from isIso_iff_bijective _]
  have hM : Function.Bijective ((yoneda.obj ((profiniteSolid R).obj
      (FintypeCat.toProfinite.obj T))).map
      ((profiniteSolidification R).app X).op) :=
    (isIso_iff_bijective _).mp ((profiniteSolid_fintype_isSolid R T).isIso_solidification_map X)
  have e := finFreeIsoSolid R T
  constructor
  · intro f g hfg
    have key1 := congrArg (· ≫ e.inv) hfg
    simp only [Category.assoc] at key1
    have key2 := congrArg (· ≫ e.hom) (hM.1 key1)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key2; exact key2
  · intro h
    obtain ⟨f', hf'⟩ := hM.2 (h ≫ e.inv)
    exact ⟨f' ≫ e.hom, by
      have key3 := congrArg (· ≫ e.hom) hf'
      simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key3
      exact key3⟩

theorem profiniteSolid_obj_isSolid (S : Profinite.{u}) :
    ((profiniteSolid R).obj S).IsSolid := by
  let E := Functor.RightExtension.mk (profiniteSolid R) (profiniteSolidCounit R)
  change (E.coneAt S).pt.IsSolid
  apply isSolid_of_isLimit_gen R (E.coneAt S)
    (profiniteSolidIsPointwiseRightKanExtension R S)
  intro f; exact finFree_isSolid R f.right

end CondensedMod
