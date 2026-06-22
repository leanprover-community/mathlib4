/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Thomas Riepe
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Condensed.Discrete.Characterization
import Mathlib.Condensed.Discrete.Colimit
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits
import Mathlib.Topology.Category.Profinite.AsLimit
/-!
# Solid modules

This file defines solid `R`-modules and proves `((profiniteSolid R).obj S).IsSolid`
for all `S : Profinite`, modulo one axiom (`sol_leftCancel`).

`surj_factor` (formerly an axiom) is now proved via `finFree_isColimit_at`.

## Axioms

* `sol_leftCancel`: left-cancellability of solidification into `finFree T`.
  Proved mathematically by Clausen-Scholze, Condensed Mathematics Thm 5.8+5.9.
  Not yet formalizable: requires CompHaus <-> TopMod equivalence.
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

-- Note: 𝟙 below is CategoryTheory.id (identity MORPHISM, U+1D7D9),
-- NOT Functor.id (𝟭, U+1D7ED). Written as NatTrans.id to avoid Unicode issues.
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
    (profiniteSolidCounit R).app T = CategoryTheory.id _ := by
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

-- surj_factor infrastructure

private lemma finFree_obj_isDiscrete (T : FintypeCat.{u}) :
    ((finFree R).obj T).IsDiscrete := by
  have hSet : (profiniteToCondensed.obj (FintypeCat.toProfinite.obj T)).IsDiscrete :=
    (CondensedSet.isDiscrete_tfae _).out 3 0 |>.mp
      (CondensedSet.mem_locallyConstant_essImage_of_isColimit_mapCocone _ fun S =>
        (Condensed.isColimitLocallyConstantPresheafDiagram (ULift.{u+1, u} T.obj) S))
  rw [(CondensedMod.isDiscrete_tfae R ((finFree R).obj T)).out 0 3]
  obtain ⟨X, ⟨i⟩⟩ := (CondensedSet.isDiscrete_tfae _).out 0 3 |>.mp hSet
  exact ⟨(ModuleCat.free R).obj X,
    ⟨(Condensed.free_LC_iso R).symm.app X ≪≫ (Condensed.free R).mapIso i⟩⟩

private noncomputable def finFree_isColimit_at' (T : FintypeCat.{u}) (S : Profinite.{u}) :
    IsColimit ((profiniteToCompHaus.op ⋙ ((finFree R).obj T).val).mapCocone
      S.asLimitCone.op) :=
  ((CondensedMod.isDiscrete_tfae R ((finFree R).obj T)).out 0 6 |>.mp
    (finFree_obj_isDiscrete R T) S).some

private abbrev cH' (Z : Profinite.{u}) := profiniteToCompHaus.obj Z

private noncomputable def buildEta (Y : Profinite.{u}) (F : CondensedSet.{u})
    (x : F.obj.obj (.op (cH' Y))) : profiniteToCondensed.obj Y ⟶ F := by
  refine ⟨⟨fun S s => cast (congrArg F.obj.obj (Opposite.op_unop S))
      (F.obj.map s.down.op x), ?_⟩⟩
  intro S S' f; funext s
  simp only [Function.comp, cast_eq]
  show F.obj.map (s.down.op ≫ f) x = F.obj.map f (F.obj.map s.down.op x)
  rw [F.obj.map_comp]; rfl

-- pTC_inj: uses CategoryTheory.id (written as id_) to avoid Unicode 𝟙 vs 𝟭 confusion
private lemma pTC_inj (Y : Profinite.{u}) (F : CondensedSet.{u})
    (e1 e2 : profiniteToCondensed.obj Y ⟶ F)
    (h : e1.hom.app (.op (cH' Y)) (ULift.up (CategoryTheory.id (cH' Y))) =
         e2.hom.app (.op (cH' Y)) (ULift.up (CategoryTheory.id (cH' Y)))) : e1 = e2 := by
  ext S s
  have key : ∀ e : profiniteToCondensed.obj Y ⟶ F,
      e.hom.app S s =
        F.obj.map s.down.op
          (e.hom.app (.op (cH' Y)) (ULift.up (CategoryTheory.id (cH' Y)))) := by
    intro e
    have nat := e.hom.naturality s.down.op
    simp only [Opposite.op_unop] at nat
    rw [show s = (profiniteToCondensed.obj Y).obj.map s.down.op
          (ULift.up (CategoryTheory.id (cH' Y))) from rfl,
        show e.hom.app S
               ((profiniteToCondensed.obj Y).obj.map s.down.op
                 (ULift.up (CategoryTheory.id (cH' Y)))) =
             ((profiniteToCondensed.obj Y).obj.map s.down.op ≫ e.hom.app S)
               (ULift.up (CategoryTheory.id (cH' Y))) from rfl,
        nat]; rfl
  rw [key e1, key e2, h]

/-- Every morphism `profiniteFree X ⟶ finFree T` factors through a finite level. -/
lemma surj_factor (T : FintypeCat.{u}) (X : Profinite.{u})
    (h : (profiniteFree R).obj X ⟶ (finFree R).obj T) :
    ∃ (U₀ : FintypeCat.{u}) (q₀ : X ⟶ FintypeCat.toProfinite.obj U₀)
      (h₀ : (profiniteFree R).obj (FintypeCat.toProfinite.obj U₀) ⟶ (finFree R).obj T),
      h = (profiniteFree R).map q₀ ≫ h₀ := by
  have h_type : IsColimit (mapCocone (forget (ModuleCat R))
      ((profiniteToCompHaus.op ⋙ ((finFree R).obj T).val).mapCocone X.asLimitCone.op)) := by
    haveI := (preservesFilteredColimitsOfSize_of_univLE.{u+1, u+1, u, u}
      (forget (ModuleCat R))).preserves_filtered_colimits (DiscreteQuotient X)ᵒᵖ
    exact isColimitOfPreserves (forget (ModuleCat R)) (finFree_isColimit_at' R T X)
  let F_set := (Condensed.forget R).obj ((finFree R).obj T)
  let eta_adj := (Condensed.freeForgetAdjunction R).homEquiv _ _ h
  let elem : F_set.obj.obj (.op (cH' X)) :=
    eta_adj.hom.app (.op (cH' X)) (ULift.up (CategoryTheory.id (cH' X)))
  obtain ⟨⟨j⟩, elem₀, hj⟩ := Types.jointly_surjective_of_isColimit h_type elem
  let q_j := X.asLimitCone.π.app j
  let eta0 := buildEta (X.diagram.obj j) F_set elem₀
  let h₀ := ((Condensed.freeForgetAdjunction R).homEquiv _ _).symm eta0
  refine ⟨X.fintypeDiagram.obj j, q_j, h₀, ?_⟩
  have h_eq : h = ((Condensed.freeForgetAdjunction R).homEquiv _ _).symm eta_adj :=
    (Equiv.symm_apply_apply _ h).symm
  have eta_eq : eta_adj = profiniteToCondensed.map q_j ≫ eta0 :=
    pTC_inj _ _ _ _ <| by
      have lhs :
          (ConcreteCategory.hom (eta_adj.hom.app (.op (cH' X))))
            { down := CategoryTheory.id (cH' X) } = elem := rfl
      have rhs :
          (ConcreteCategory.hom
              ((profiniteToCondensed.map q_j ≫ eta0).hom.app (.op (cH' X))))
            { down := CategoryTheory.id (cH' X) } = elem :=
        (show (ConcreteCategory.hom
                ((profiniteToCondensed.map q_j ≫ eta0).hom.app (.op (cH' X))))
              { down := CategoryTheory.id (cH' X) } =
              F_set.obj.map (profiniteToCompHaus.map q_j).op elem₀ from rfl).trans hj
      exact lhs.trans rhs.symm
  rw [h_eq, eta_eq]
  exact (Condensed.freeForgetAdjunction R).homEquiv_naturality_left_symm
    (profiniteToCondensed.map q_j) eta0

axiom sol_leftCancel (T : FintypeCat.{u}) (X : Profinite.{u})
    (f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T)
    (h : (profiniteSolidification R).app X ≫ f =
         (profiniteSolidification R).app X ≫ g) : f = g

theorem profiniteSolid_fintype_isSolid (T : FintypeCat.{u}) :
    ((profiniteSolid R).obj (FintypeCat.toProfinite.obj T)).IsSolid := by
  constructor; intro X
  rw [isIso_iff_bijective]
  constructor
  · intro g g' hgg'
    have h_step : g ≫ (finFreeIsoSolid R T).hom = g' ≫ (finFreeIsoSolid R T).hom :=
      sol_leftCancel R T X _ _
        (by have h1 := congrArg (· ≫ (finFreeIsoSolid R T).hom) hgg'
            simp only [Category.assoc] at h1; exact h1)
    have key := congrArg (· ≫ (finFreeIsoSolid R T).inv) h_step
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at key; exact key
  · intro h
    let h' : (profiniteFree R).obj X ⟶ (finFree R).obj T := h ≫ (finFreeIsoSolid R T).hom
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
  rw [isIso_iff_bijective]
  set sol := (profiniteSolidification R).app X
  have bijFun : ∀ j, Function.Bijective ((yoneda.obj (F.obj j)).map sol.op) :=
    fun j => isIso_iff_bijective.mp ((hj j).isIso_solidification_map X)
  constructor
  · intro f g hfg
    apply hc.hom_ext; intro j; exact (bijFun j).1 (congrArg (· ≫ c.π.app j) hfg)
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
                  -- identity morphism written out to avoid 𝟙 vs 𝟭 confusion
                  simp only [Category.id_comp]
                  exact (compat phi).symm } }
    refine ⟨hc.lift g_cone, ?_⟩
    apply hc.hom_ext; intro j
    rw [Category.assoc, hc.fac g_cone j]; exact hg_j j

theorem finFree_isSolid (T : FintypeCat.{u}) : ((finFree R).obj T).IsSolid := by
  constructor; intro X; rw [isIso_iff_bijective]
  have hM := (profiniteSolid_fintype_isSolid R T).isIso_solidification_map X
  rw [isIso_iff_bijective] at hM
  have e := finFreeIsoSolid R T
  refine ⟨fun f g hfg => ?, fun h => ?⟩
  · have key1 := congrArg (· ≫ e.inv) hfg
    simp only [Category.assoc] at key1
    have key2 := congrArg (· ≫ e.hom) (hM.1 key1)
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key2; exact key2
  · obtain ⟨f', hf'⟩ := hM.2 (h ≫ e.inv)
    refine ⟨f' ≫ e.hom, ?⟩
    have key3 := congrArg (· ≫ e.hom) hf'
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key3
    exact key3

theorem profiniteSolid_obj_isSolid (S : Profinite.{u}) :
    ((profiniteSolid R).obj S).IsSolid := by
  let E := Functor.RightExtension.mk (profiniteSolid R) (profiniteSolidCounit R)
  change (E.coneAt S).pt.IsSolid
  apply isSolid_of_isLimit_gen R (E.coneAt S) (profiniteSolidIsPointwiseRightKanExtension R S)
  intro f; exact finFree_isSolid R f.right

end CondensedMod
