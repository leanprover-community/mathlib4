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

This file defines `CondensedMod.IsSolid R` and proves
`((profiniteSolid R).obj S).IsSolid` for all `S : Profinite`
modulo two axioms (`surj_factor`, `sol_leftCancel`).

## Axioms

* `surj_factor`, `sol_leftCancel`: proved in Clausen-Scholze,
  Condensed Mathematics Theorem 5.8. Not formalizable in Lean
  without the CompHaus <-> TopMod equivalence.
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

-- alpha (= counit) is EXPLICIT in liftOfIsRightKanExtension
def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (NatTrans.id _)

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
          (profiniteSolidCounit R) _ (NatTrans.id _) T

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

-- NOTE: sol_map_counit uses exact Category.comp_id _ (term mode) to avoid simp issue
-- where simp cannot close f >> CategoryStruct.id _ = f in Lean 4.32.
lemma sol_map_counit (T : FintypeCat.{u}) (X : Profinite.{u})
    (psi : X ⟶ FintypeCat.toProfinite.obj T) :
    (profiniteSolidification R).app X ≫ (profiniteSolid R).map psi ≫
    (finFreeIsoSolid R T).hom = (profiniteFree R).map psi := by
  rw [show (finFreeIsoSolid R T).hom = (profiniteSolidCounit R).app T from rfl,
      ← Category.assoc, ← (profiniteSolidification R).naturality psi,
      Category.assoc]
  simp [profiniteSolidification_comp_counit R T]

axiom surj_factor (T : FintypeCat.{u}) (X : Profinite.{u})
    (h : (profiniteFree R).obj X ⟶ (finFree R).obj T) :
    ∃ (U₀ : FintypeCat.{u}) (q₀ : X ⟶ FintypeCat.toProfinite.obj U₀)
      (h₀ : (profiniteFree R).obj (FintypeCat.toProfinite.obj U₀) ⟶ (finFree R).obj T),
      h = (profiniteFree R).map q₀ ≫ h₀

axiom sol_leftCancel (T : FintypeCat.{u}) (X : Profinite.{u})
    (f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T)
    (h : (profiniteSolidification R).app X ≫ f =
         (profiniteSolidification R).app X ≫ g) : f = g

private theorem surjectivity_from_surj_factor (T : FintypeCat.{u}) (X : Profinite.{u})
    (h : (profiniteFree R).obj X ⟶
         (profiniteSolid R).obj (FintypeCat.toProfinite.obj T)) :
    ∃ g : (profiniteSolid R).obj X ⟶
          (profiniteSolid R).obj (FintypeCat.toProfinite.obj T),
      (profiniteSolidification R).app X ≫ g = h := by
  obtain ⟨U₀, q₀, h₀, hfactor⟩ := surj_factor R T X (h ≫ (finFreeIsoSolid R T).hom)
  set sol_X := (profiniteSolidification R).app X
  refine ⟨(profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom ≫
      h₀ ≫ (finFreeIsoSolid R T).inv, ?_⟩
  have key : sol_X ≫ (profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom =
      (profiniteFree R).map q₀ := sol_map_counit R U₀ X q₀
  have step1 : sol_X ≫ ((profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom ≫
      h₀ ≫ (finFreeIsoSolid R T).inv) =
      (sol_X ≫ (profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom) ≫
      (h₀ ≫ (finFreeIsoSolid R T).inv) := by simp only [Category.assoc]
  rw [step1, key]
  change ((profiniteFree R).map q₀ ≫ h₀) ≫ (finFreeIsoSolid R T).inv = h
  rw [hfactor.symm, Category.assoc, (finFreeIsoSolid R T).hom_inv_id, Category.comp_id]

theorem profiniteSolid_fintype_isSolid (T : FintypeCat.{u}) :
    ((profiniteSolid R).obj (FintypeCat.toProfinite.obj T)).IsSolid := by
  constructor; intro X
  apply (isIso_iff_bijective _).mpr
  set sol_X := (profiniteSolidification R).app X
  constructor
  · intro g g' hgg'
    have h_inner : sol_X ≫ g ≫ (finFreeIsoSolid R T).hom =
        sol_X ≫ g' ≫ (finFreeIsoSolid R T).hom :=
      congrArg (· ≫ (finFreeIsoSolid R T).hom) hgg' |>.trans
        (by simp [Category.assoc]) |>.symm.trans (by simp [Category.assoc]) |>.symm
    have h_inj := sol_leftCancel R T X _ _ h_inner
    have key := congrArg (· ≫ (finFreeIsoSolid R T).inv) h_inj
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at key
    exact key
  · intro h
    exact surjectivity_from_surj_factor R T X h

lemma isSolid_of_isLimit_gen {J : Type*} [Category J] {F : J ⥤ CondensedMod.{u} R}
    (c : Cone F) (hc : IsLimit c) (hj : ∀ j, (F.obj j).IsSolid) : c.pt.IsSolid := by
  refine ⟨fun X => ?_⟩
  apply (isIso_iff_bijective _).mpr
  set sol := (profiniteSolidification R).app X
  have bijFun : ∀ j, Function.Bijective ((yoneda.obj (F.obj j)).map sol.op) :=
    fun j => (isIso_iff_bijective _).mp ((hj j).isIso_solidification_map X)
  constructor
  · intro f g hfg
    have hfg' : sol ≫ f = sol ≫ g := hfg
    apply hc.hom_ext; intro j; apply (bijFun j).1
    change sol ≫ f ≫ c.π.app j = sol ≫ g ≫ c.π.app j
    simp only [← Category.assoc, hfg']
  · intro h_map
    choose g_j hg_j using fun j => (bijFun j).2 (h_map ≫ c.π.app j)
    have hg_j' : ∀ j, sol ≫ g_j j = h_map ≫ c.π.app j := hg_j
    have compat : ∀ {j k : J} (phi : j ⟶ k), g_j j ≫ F.map phi = g_j k := by
      intro j k phi
      have lhs : sol ≫ (g_j j ≫ F.map phi) = h_map ≫ c.π.app k := by
        conv_lhs => rw [← Category.assoc, hg_j' j, Category.assoc, c.w phi]
      exact (bijFun k).1 (lhs.trans (hg_j' k).symm)
    let g_cone : Cone F :=
      { pt := (profiniteSolid R).obj X
        π  := { app := g_j
                naturality := fun j k phi => by
                  change CategoryStruct.id _ ≫ g_j k = g_j j ≫ F.map phi
                  simp only [Category.id_comp]
                  exact (compat phi).symm } }
    refine ⟨hc.lift g_cone, ?_⟩
    change sol ≫ hc.lift g_cone = h_map
    apply hc.hom_ext; intro j
    rw [Category.assoc, hc.fac g_cone j]
    exact hg_j' j

-- finFree_isSolid: injectivity via sol_leftCancel, surjectivity via transfer through e.
-- Avoids Function.Bijective/ConcreteCategory.hom mismatch (Lean 4.32 API change).
-- Avoids rw [h_eq] on IsIso goal (caused cannot-import-module error in v8).
theorem finFree_isSolid (T : FintypeCat.{u}) : ((finFree R).obj T).IsSolid := by
  constructor; intro X
  apply (isIso_iff_bijective _).mpr
  have e := finFreeIsoSolid R T
  constructor
  · -- Injectivity: sol_leftCancel cancels sol directly
    -- hfg : sol >> f = sol >> g  (definitionally, via ConcreteCategory.hom)
    intro f g hfg
    exact sol_leftCancel R T X f g hfg
  · -- Surjectivity: transfer through finFreeIsoSolid
    intro h
    -- h : profiniteFree X -> finFree T; need g : profiniteSolid X -> finFree T
    obtain ⟨g', hg'⟩ := surjectivity_from_surj_factor R T X (h ≫ e.inv)
    -- g' : profiniteSolid X -> profiniteSolid LT, hg' : sol >> g' = h >> e.inv
    refine ⟨g' ≫ e.hom, ?_⟩
    -- Goal: sol >> (g' >> e.hom) = h
    have key := congrArg (· ≫ e.hom) hg'
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key
    exact key

theorem profiniteSolid_obj_isSolid (S : Profinite.{u}) :
    ((profiniteSolid R).obj S).IsSolid := by
  let E := Functor.RightExtension.mk (profiniteSolid R) (profiniteSolidCounit R)
  change (E.coneAt S).pt.IsSolid
  apply isSolid_of_isLimit_gen R (E.coneAt S)
    (profiniteSolidIsPointwiseRightKanExtension R S)
  intro f; exact finFree_isSolid R f.right

end CondensedMod
