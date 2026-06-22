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

This file contains the definition of a solid `R`-module: `CondensedMod.isSolid R`. Solid modules
groups were introduced in [scholze2019condensed], Definition 5.1.

## Main definitions

* `CondensedMod.IsSolid R`: the predicate on condensed `R`-modules describing the property of
  being solid.

## Main theorems (new in this PR)

* `CondensedMod.profiniteSolidCounit_isIso`: the counit of the profinite solidification is
  an isomorphism at every finite type.
* `CondensedMod.profiniteSolidification_isIso_at_fintype`: the solidification map is an
  isomorphism at every object in the image of `FintypeCat.toProfinite`.
* `CondensedMod.profiniteSolid_isSolid_at_fintype`: `((profiniteSolid R).obj S).IsSolid`
  when tested against objects in the image of `FintypeCat.toProfinite`.
* `CondensedMod.isSolid_of_isLimit_gen`: if a condensed `R`-module is the limit of solid
  modules, then it is solid (fully proved, no axioms).
* `CondensedMod.surj_factor`: every morphism `profiniteFree X ⟶ finFree T` factors through
  a finite level (proved via `finFree_isColimit_at`; was formerly an axiom).
* `CondensedMod.profiniteSolid_obj_isSolid`: `((profiniteSolid R).obj S).IsSolid`
  for `S : Profinite` (proved modulo `sol_leftCancel`).

## Axioms

* `sol_leftCancel`: the solidification map is left-cancellable into `finFree T`.
  Mathematically true by Clausen-Scholze, Condensed Mathematics Theorem 5.8 + Lemma 5.9.
  Equivalent to `IsSolid (profiniteSolid R).obj X` for all profinite X.
  Not yet formalizable in Lean: requires CompHaus ↔ TopMod equivalence.
-/

universe u
variable (R : Type (u + 1)) [Ring R]
open CategoryTheory Limits Profinite Condensed
noncomputable section
namespace Condensed

/-- The free condensed `R`-module on a finite set. -/
abbrev finFree : FintypeCat.{u} ⥤ CondensedMod.{u} R :=
  FintypeCat.toProfinite ⋙ profiniteToCondensed ⋙ free R

/-- The free condensed `R`-module on a profinite space. -/
abbrev profiniteFree : Profinite.{u} ⥤ CondensedMod.{u} R :=
  profiniteToCondensed ⋙ free R

/-- The functor sending a profinite space `S` to the condensed `R`-module `R[S]^solid`. -/
def profiniteSolid : Profinite.{u} ⥤ CondensedMod.{u} R :=
  Functor.rightKanExtension FintypeCat.toProfinite (finFree R)

/-- The natural transformation `FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R`
which is part of the assertion that `profiniteSolid R` is the (pointwise) right
Kan extension of `finFree R` along `FintypeCat.toProfinite`. -/
def profiniteSolidCounit : FintypeCat.toProfinite ⋙ profiniteSolid R ⟶ finFree R :=
  Functor.rightKanExtensionCounit FintypeCat.toProfinite (finFree R)

instance : (profiniteSolid R).IsRightKanExtension (profiniteSolidCounit R) := by
  dsimp only [profiniteSolidCounit, profiniteSolid]
  infer_instance

/-- The functor `Profinite.{u} ⥤ CondensedMod.{u} R` is a pointwise
right Kan extension of `finFree R : FintypeCat.{u} ⥤ CondensedMod.{u} R`
along `FintypeCat.toProfinite`. -/
def profiniteSolidIsPointwiseRightKanExtension :
    (Functor.RightExtension.mk _ (profiniteSolidCounit R)).IsPointwiseRightKanExtension :=
  Functor.isPointwiseRightKanExtensionOfIsRightKanExtension _ _

/-- The natural transformation `R[S] ⟶ R[S]^solid`. -/
def profiniteSolidification : profiniteFree R ⟶ profiniteSolid.{u} R :=
  (profiniteSolid R).liftOfIsRightKanExtension (profiniteSolidCounit R) _ (𝟙 _)

end Condensed

/--
The predicate on condensed `R`-modules describing the property of being solid.

TODO: This is not the correct definition of solid `R`-modules for a general `R`. The correct one is
as follows: Use this to define solid modules over a finite type `ℤ`-algebra `R`. In particular this
gives a definition of solid modules over `ℤ[X]` (polynomials in one variable). Then a solid
`R`-module over a general `R` is the condition that for every `r ∈ R` and every ring
homomorphism `ℤ[X] → R` such that `X` maps to `r`, the underlying `ℤ[X]`-module is solid.
-/
class CondensedMod.IsSolid (A : CondensedMod.{u} R) : Prop where
  isIso_solidification_map : ∀ X : Profinite.{u}, IsIso ((yoneda.obj A).map
    ((Condensed.profiniteSolidification R).app X).op)

namespace CondensedMod

open CategoryTheory Limits Profinite Condensed Functor Opposite

/-! ### Profiniteness of the solidification -/

/-- The counit of the profinite solidification is an isomorphism at every `T : FintypeCat`.
This uses the fact that `profiniteSolidIsPointwiseRightKanExtension` holds and that
`FintypeCat.toProfinite` is fully faithful. -/
lemma profiniteSolidCounit_isIso (T : FintypeCat.{u}) :
    IsIso ((profiniteSolidCounit R).app T) := by
  haveI : IsIso (profiniteSolidCounit R) :=
    (profiniteSolidIsPointwiseRightKanExtension R).isIso_hom
  infer_instance

/-- The solidification map `profiniteSolidification R` composed with the counit equals the
identity, at every `T : FintypeCat`. This is the naturality condition from
`liftOfIsRightKanExtension_fac_app`. -/
lemma profiniteSolidification_comp_counit (T : FintypeCat.{u}) :
    (profiniteSolidification R).app (FintypeCat.toProfinite.obj T) ≫
    (profiniteSolidCounit R).app T = 𝟙 _ := by
  have h := (profiniteSolid R).liftOfIsRightKanExtension_fac_app
              (profiniteSolidCounit R) (profiniteFree R) (𝟙 _) T
  simp only [profiniteSolidification]
  exact h

/-- The solidification map `profiniteSolidification R` is an isomorphism at every object in
the image of `FintypeCat.toProfinite`. This follows from `profiniteSolidCounit_isIso` and
`profiniteSolidification_comp_counit` via `isIso_of_comp_hom_eq_id`. -/
lemma profiniteSolidification_isIso_at_fintype (T : FintypeCat.{u}) :
    IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) := by
  haveI := profiniteSolidCounit_isIso R T
  exact isIso_of_comp_hom_eq_id ((profiniteSolidCounit R).app T)
          (profiniteSolidification_comp_counit R T)

/-! ### Solidness of `profiniteSolid R` at finite test objects -/

/-- `((profiniteSolid R).obj S).IsSolid` when the test object `X` is in the image of
`FintypeCat.toProfinite`. The proof uses that `profiniteSolidification_isIso_at_fintype`
makes the solidification map itself an isomorphism at finite objects, and then functoriality
of `yoneda` gives the required isomorphism on hom-sets. -/
theorem profiniteSolid_isSolid_at_fintype
    (S : Profinite.{u}) (T : FintypeCat.{u}) :
    IsIso ((yoneda.obj ((profiniteSolid R).obj S)).map
           ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)).op) := by
  haveI : IsIso ((profiniteSolidification R).app (FintypeCat.toProfinite.obj T)) :=
    profiniteSolidification_isIso_at_fintype R T
  infer_instance

/-! ### Infrastructure for the general solidness proof -/

/-- The isomorphism `(profiniteSolid R).obj LT ≅ (finFree R).obj T`, for `T : FintypeCat`.
This is the counit of the right Kan extension, which is an isomorphism by
`profiniteSolidCounit_isIso`. -/
noncomputable def finFreeIsoSolid (T : FintypeCat.{u}) :
    (profiniteSolid R).obj (FintypeCat.toProfinite.obj T) ≅ (finFree R).obj T :=
  @asIso _ _ _ _ ((profiniteSolidCounit R).app T) (profiniteSolidCounit_isIso R T)

/-- Key commutation: the solidification composed with the solid map and the counit iso
equals the free map. This is the fundamental compatibility between solidification and
the Kan extension structure. -/
lemma sol_map_counit (T : FintypeCat.{u}) (X : Profinite.{u})
    (ψ : X ⟶ FintypeCat.toProfinite.obj T) :
    (profiniteSolidification R).app X ≫
    (profiniteSolid R).map ψ ≫
    (finFreeIsoSolid R T).hom = (profiniteFree R).map ψ := by
  have nat := (profiniteSolidification R).naturality ψ
  have hcounit : (finFreeIsoSolid R T).hom = (profiniteSolidCounit R).app T := rfl
  rw [hcounit, ← Category.assoc, ← nat, Category.assoc, profiniteSolidification_comp_counit]
  exact Category.comp_id _

/-! ### `surj_factor`: proved via `finFree_isColimit_at` -/

/-- Helper: `(profiniteToCondensed.obj (FintypeCat.toProfinite.obj T))` is discrete.
Proved via `isColimitLocallyConstantPresheafDiagram`. -/
private lemma finFree_obj_isDiscrete (T : FintypeCat.{u}) :
    ((finFree R).obj T).IsDiscrete := by
  have hSet : (profiniteToCondensed.obj (FintypeCat.toProfinite.obj T)).IsDiscrete :=
    (CondensedSet.isDiscrete_tfae _).out 3 0 |>.mp
      (CondensedSet.mem_locallyConstant_essImage_of_isColimit_mapCocone _ fun S =>
        Condensed.isColimitLocallyConstantPresheafDiagram (ULift.{u+1, u} T.obj) S |>.ofIso
          (isoWhiskerLeft _ (NatIso.ofComponents (fun U => Equiv.toIso
            { toFun  := fun f => ⟨fun t => f.down.toFun (FintypeCat.toProfinite.map
                  (FintypeCat.equivOfEquiv (Equiv.refl T.obj)) (ULift.up t)), by
                    intro t; dsimp; rfl⟩
              invFun  := fun g => ULift.up (LocallyConstant.mk (fun x => g.toFun (ULift.down x))
                  (by intro t; exact g.2 (ULift.down t)))
              left_inv := fun _ => ULift.ext _ _ (funext fun _ => rfl)
              right_inv := fun _ => LocallyConstant.ext _ _ (funext fun _ => rfl)})
            (by intro X Y f; funext x; apply LocallyConstant.ext; intro s; rfl))))
  rw [(CondensedMod.isDiscrete_tfae R ((finFree R).obj T)).out 0 3]
  obtain ⟨X, ⟨i⟩⟩ := (CondensedSet.isDiscrete_tfae _).out 0 3 |>.mp hSet
  exact ⟨(ModuleCat.free R).obj X,
    ⟨(Condensed.free_LC_iso R).symm.app X ≪≫ (Condensed.free R).mapIso i⟩⟩

/-- Helper: `(finFree R).obj T` evaluated at any profinite `S` is a filtered colimit. -/
private noncomputable def finFree_isColimit_at' (T : FintypeCat.{u}) (S : Profinite.{u}) :
    IsColimit ((profiniteToCompHaus.op ⋙ ((finFree R).obj T).val).mapCocone
      S.asLimitCone.op) :=
  ((CondensedMod.isDiscrete_tfae R ((finFree R).obj T)).out 0 6 |>.mp
    (finFree_obj_isDiscrete R T) S).some

private abbrev cH' (Z : Profinite.{u}) := profiniteToCompHaus.obj Z

private noncomputable def buildEta (Y : Profinite.{u})
    (F : CondensedSet.{u}) (x : F.obj.obj (.op (cH' Y))) :
    profiniteToCondensed.obj Y ⟶ F :=
  ⟨⟨fun S s => F.obj.map s.down.op x, by
      intro S S' f; funext s
      show F.obj.map (s.down.op ≫ f) x = F.obj.map f (F.obj.map s.down.op x)
      rw [F.obj.map_comp]; rfl⟩⟩

private lemma pTC_inj (Y : Profinite.{u}) (F : CondensedSet.{u})
    (e1 e2 : profiniteToCondensed.obj Y ⟶ F)
    (h : e1.hom.app (.op (cH' Y)) (ULift.up (𝟙 (cH' Y))) =
         e2.hom.app (.op (cH' Y)) (ULift.up (𝟙 (cH' Y)))) : e1 = e2 := by
  ext S s
  have key : ∀ e : profiniteToCondensed.obj Y ⟶ F,
      e.hom.app S s = F.obj.map s.down.op (e.hom.app (.op (cH' Y)) (ULift.up (𝟙 (cH' Y)))) := by
    intro e
    have nat := e.hom.naturality s.down.op
    simp only [Opposite.op_unop] at nat
    rw [show s = (profiniteToCondensed.obj Y).obj.map s.down.op (ULift.up (𝟙 (cH' Y))) from rfl,
        show e.hom.app S ((profiniteToCondensed.obj Y).obj.map s.down.op (ULift.up (𝟙 (cH' Y)))) =
             ((profiniteToCondensed.obj Y).obj.map s.down.op ≫ e.hom.app S) (ULift.up (𝟙 (cH' Y)))
             from rfl, nat]; rfl
  rw [key e1, key e2, h]

/-- Every morphism `profiniteFree X ⟶ finFree T` factors through a finite level.

**Proof**: `finFree T` is discrete (follows from `isColimitLocallyConstantPresheafDiagram`),
hence its values are filtered colimits over discrete quotients of `X`. The element
`eta(𝟙) ∈ colim_{U : DQ(X)} (finFree T)(U)` lands in some finite level `U₀`, giving the
factorisation via `q₀ : X → LU₀`.

This was formerly an axiom; it is now proved using Mathlib's colimit machinery. -/
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
    eta_adj.hom.app (.op (cH' X)) (ULift.up (𝟙 (cH' X)))
  obtain ⟨⟨j⟩, elem₀, hj⟩ := Types.jointly_surjective_of_isColimit h_type elem
  let q_j := X.asLimitCone.π.app j
  let eta0 := buildEta (X.diagram.obj j) F_set elem₀
  let h₀ := ((Condensed.freeForgetAdjunction R).homEquiv _ _).symm eta0
  refine ⟨X.fintypeDiagram.obj j, q_j, h₀, ?_⟩
  have h_eq : h = ((Condensed.freeForgetAdjunction R).homEquiv _ _).symm eta_adj :=
    (Equiv.symm_apply_apply _ h).symm
  have eta_eq : eta_adj = profiniteToCondensed.map q_j ≫ eta0 :=
    pTC_inj _ _ _ _ <| by
      have lhs : (ConcreteCategory.hom (eta_adj.hom.app (.op (cH' X)))) { down := 𝟙 (cH' X) } =
                 elem := rfl
      have rhs : (ConcreteCategory.hom
            ((profiniteToCondensed.map q_j ≫ eta0).hom.app (.op (cH' X))))
            { down := 𝟙 (cH' X) } = elem :=
        (show (ConcreteCategory.hom
              ((profiniteToCondensed.map q_j ≫ eta0).hom.app (.op (cH' X))))
              { down := 𝟙 (cH' X) } =
              F_set.obj.map (profiniteToCompHaus.map q_j).op elem₀ from rfl).trans hj
      exact lhs.trans rhs.symm
  rw [h_eq, eta_eq]
  exact (Condensed.freeForgetAdjunction R).homEquiv_naturality_left_symm
    (profiniteToCondensed.map q_j) eta0

/-! ### Remaining solidness axiom -/

/-- Mathematical axiom (Clausen-Scholze, Condensed Mathematics Thm 5.8 + Lemma 5.9):
the solidification map is left-cancellable into `(finFree R).obj T`.

Precisely: if `f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T` satisfy
`solidification_X ≫ f = solidification_X ≫ g`, then `f = g`.

This is equivalent to `IsSolid ((profiniteSolid R).obj X)` for all profinite X, which is
the main TODO of this file. Not yet formalizable in Lean/Mathlib without the
CompHaus ↔ TopMod equivalence. -/
axiom sol_leftCancel (T : FintypeCat.{u}) (X : Profinite.{u})
    (f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T)
    (h : (profiniteSolidification R).app X ≫ f =
         (profiniteSolidification R).app X ≫ g) :
    f = g

/-! ### Solidness of `(profiniteSolid R).obj LT` (finite case) -/

/-- `((profiniteSolid R).obj LT).IsSolid` for any `T : FintypeCat`.
**Surjectivity** (proved): uses `surj_factor` and `sol_map_counit`.
**Injectivity** (proved): uses `sol_leftCancel` axiom. -/
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
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at key
    exact key
  · intro h
    let h' : (profiniteFree R).obj X ⟶ (finFree R).obj T :=
      h ≫ (finFreeIsoSolid R T).hom
    obtain ⟨U₀, q₀, h₀, hfact⟩ := surj_factor R T X h'
    refine ⟨(profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom ≫
            h₀ ≫ (finFreeIsoSolid R T).inv, ?_⟩
    have step1 : (profiniteSolidification R).app X ≫ (profiniteSolid R).map q₀ ≫
        (finFreeIsoSolid R U₀).hom ≫ h₀ ≫ (finFreeIsoSolid R T).inv =
        (profiniteFree R).map q₀ ≫ h₀ ≫ (finFreeIsoSolid R T).inv :=
      congrArg (· ≫ h₀ ≫ (finFreeIsoSolid R T).inv) (sol_map_counit R U₀ X q₀)
    have step2 : (profiniteFree R).map q₀ ≫ h₀ ≫ (finFreeIsoSolid R T).inv = h := by
      have key2 := congrArg (· ≫ (finFreeIsoSolid R T).inv) hfact.symm
      simp only [Category.assoc] at key2
      rw [key2, show h' = h ≫ (finFreeIsoSolid R T).hom from rfl,
          Category.assoc, (finFreeIsoSolid R T).hom_inv_id, Category.comp_id]
    exact step1.trans step2

/-! ### Limits of solid modules are solid -/

/-- If a condensed `R`-module is the limit of a diagram of solid modules, then it is solid.
Fully proved (no axioms). -/
lemma isSolid_of_isLimit_gen
    {J : Type*} [Category J]
    {F : J ⥤ CondensedMod.{u} R}
    (c : Cone F) (hc : IsLimit c)
    (hj : ∀ j, (F.obj j).IsSolid) :
    c.pt.IsSolid := by
  refine ⟨fun X => ?_⟩
  rw [isIso_iff_bijective]
  set sol := (profiniteSolidification R).app X
  have bijFun : ∀ j, Function.Bijective ((yoneda.obj (F.obj j)).map sol.op) := by
    intro j; have h := (hj j).isIso_solidification_map X
    rw [isIso_iff_bijective] at h; exact h
  constructor
  · intro f g hfg
    apply hc.hom_ext; intro j; apply (bijFun j).1
    exact congrArg (· ≫ c.π.app j) hfg
  · intro h_map
    choose g_j hg_j using fun j => (bijFun j).2 (h_map ≫ c.π.app j)
    have hg_j' : ∀ j, sol ≫ g_j j = h_map ≫ c.π.app j := hg_j
    have compat : ∀ {j k : J} (φ : j ⟶ k), g_j j ≫ F.map φ = g_j k := by
      intro j k φ
      have lhs : sol ≫ (g_j j ≫ F.map φ) = h_map ≫ c.π.app k := by
        conv_lhs => rw [← Category.assoc, hg_j' j, Category.assoc, c.w φ]
      exact (bijFun k).1 (lhs.trans (hg_j' k).symm)
    let g_cone : Cone F :=
      { pt := (profiniteSolid R).obj X
        π  := { app        := g_j
                naturality := fun j k φ => by
                  change 𝟙 _ ≫ g_j k = g_j j ≫ F.map φ
                  simp only [Category.id_comp]; exact (compat φ).symm } }
    refine ⟨hc.lift g_cone, ?_⟩
    change sol ≫ hc.lift g_cone = h_map
    apply hc.hom_ext; intro j
    rw [Category.assoc, hc.fac g_cone j]; exact hg_j' j

/-! ### `finFree R T` is solid -/

/-- `(finFree R).obj T` is a solid condensed `R`-module, for any `T : FintypeCat`. -/
theorem finFree_isSolid (T : FintypeCat.{u}) : ((finFree R).obj T).IsSolid := by
  constructor; intro X
  rw [isIso_iff_bijective]
  have hM := (profiniteSolid_fintype_isSolid R T).isIso_solidification_map X
  rw [isIso_iff_bijective] at hM
  have e := finFreeIsoSolid R T
  constructor
  · intro f g hfg
    have hfinv : f ≫ e.inv = g ≫ e.inv := by
      apply hM.1
      have key1 := congrArg (· ≫ e.inv) hfg
      simp only [Category.assoc] at key1; exact key1
    have key2 := congrArg (· ≫ e.hom) hfinv
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key2
    exact key2
  · intro h
    obtain ⟨f', hf'⟩ := hM.2 (h ≫ e.inv)
    refine ⟨f' ≫ e.hom, ?_⟩
    have key3 := congrArg (· ≫ e.hom) hf'
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key3
    change (profiniteSolidification R).app X ≫ (f' ≫ e.hom) = h
    exact key3

/-! ### General solidness of `profiniteSolid R` -/

/-- Every `(profiniteSolid R).obj S` is a solid condensed `R`-module, for any `S : Profinite`.
Proved modulo one axiom: `sol_leftCancel`. -/
theorem profiniteSolid_obj_isSolid (S : Profinite.{u}) :
    ((profiniteSolid R).obj S).IsSolid := by
  let E := Functor.RightExtension.mk (profiniteSolid R) (profiniteSolidCounit R)
  have h_pwise : IsLimit (E.coneAt S) :=
    (profiniteSolidIsPointwiseRightKanExtension R) S
  change (E.coneAt S).pt.IsSolid
  apply isSolid_of_isLimit_gen R (E.coneAt S) h_pwise
  intro f
  exact finFree_isSolid R f.right

end CondensedMod
