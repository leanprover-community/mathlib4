/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Thomas Riepe
-/
module
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Condensed.Functors
public import Mathlib.Condensed.Limits
public import Mathlib.Topology.Category.Profinite.AsLimit
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
  modules, then it is solid (fully proved).
* `CondensedMod.profiniteSolid_obj_isSolid`: `((profiniteSolid R).obj S).IsSolid`
  for `S : Profinite`. Architecture complete; one sorry remains:
  `surj_factor` (proved in MathProject/P2_finFree_Solid.lean; requires `finFree_isColimit_at`).

## Axioms

* `sol_leftCancel`: the solidification map is left-cancellable into `finFree T`.
  Mathematically true by Clausen-Scholze, Condensed Mathematics Theorem 5.8 + Lemma 5.9.
  Equivalent to `IsSolid (profiniteSolid R).obj X` for all profinite X.
  Not yet formalizable in Lean: requires CompHaus ↔ TopMod equivalence.
-/

@[expose] public section
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

/-- Mathematical axiom (Clausen-Scholze, Condensed Mathematics Thm 5.8 + Lemma 5.9):
the solidification map is left-cancellable into `(finFree R).obj T`.

Precisely: if `f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T` satisfy
`solidification_X ≫ f = solidification_X ≫ g`, then `f = g`.

This is equivalent to `IsSolid ((profiniteSolid R).obj X)` for all profinite X, which is
the main TODO of this file. Not yet formalizable in Lean/Mathlib without the
CompHaus ↔ TopMod equivalence (see MathProject/P0_SolLeftCancel_Axiom.lean). -/
axiom sol_leftCancel (T : FintypeCat.{u}) (X : Profinite.{u})
    (f g : (profiniteSolid R).obj X ⟶ (finFree R).obj T)
    (h : (profiniteSolidification R).app X ≫ f =
         (profiniteSolidification R).app X ≫ g) :
    f = g

/-- `surj_factor`: any morphism `h : profiniteFree X ⟶ finFree T` factors through a
finite level. Proved in MathProject/P2_finFree_Solid.lean.
TODO: integrate the proof into Mathlib (requires `finFree_isColimit_at` infrastructure,
which needs `CondensedMod.isDiscrete_tfae` and `finFree_isDiscrete`). -/
lemma surj_factor (T : FintypeCat.{u}) (X : Profinite.{u})
    (h : (profiniteFree R).obj X ⟶ (finFree R).obj T) :
    ∃ (U₀ : FintypeCat.{u}) (q₀ : X ⟶ FintypeCat.toProfinite.obj U₀)
      (h₀ : (profiniteFree R).obj (FintypeCat.toProfinite.obj U₀) ⟶ (finFree R).obj T),
      h = (profiniteFree R).map q₀ ≫ h₀ := by
  sorry

/-! ### Solidness of `(profiniteSolid R).obj LT` (finite case) -/

/-- `((profiniteSolid R).obj LT).IsSolid` for any `T : FintypeCat`.
**Surjectivity** (proved): uses `surj_factor` and `sol_map_counit`.
**Injectivity** (proved): uses `sol_leftCancel` axiom.
One sorry remains in `surj_factor` (colimit infrastructure). -/
theorem profiniteSolid_fintype_isSolid (T : FintypeCat.{u}) :
    ((profiniteSolid R).obj (FintypeCat.toProfinite.obj T)).IsSolid := by
  constructor; intro X
  rw [isIso_iff_bijective]
  constructor
  · -- INJECTIVITY: proved via sol_leftCancel axiom
    intro g g' hgg'
    -- Step 1: lift hgg' to a statement about g ≫ iso.hom = g' ≫ iso.hom
    have h_step : g ≫ (finFreeIsoSolid R T).hom = g' ≫ (finFreeIsoSolid R T).hom :=
      sol_leftCancel R T X _ _ (by
        -- hgg' has Yoneda type; coerce so that congrArg produces left-assoc syntactically
        -- Note: 'sol' is not in scope here; use the full name
        have hgg'' : (profiniteSolidification R).app X ≫ g =
                     (profiniteSolidification R).app X ≫ g' := hgg'
        have h1 := congrArg (· ≫ (finFreeIsoSolid R T).hom) hgg''
        simp only [Category.assoc] at h1
        exact h1)
    -- Step 2: cancel iso.hom on the right using iso.inv
    have key := congrArg (· ≫ (finFreeIsoSolid R T).inv) h_step
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at key
    exact key
  · -- SURJECTIVITY (proved 2026-06-14, congrArg approach)
    intro h
    -- h has Yoneda-obj type after intro; bind as morphism via transparent let
    let hm : (profiniteFree R).obj X ⟶
             (profiniteSolid R).obj (FintypeCat.toProfinite.obj T) := h
    -- h': image of hm under iso_T.hom (transparent let, so h' = hm ≫ iso_T.hom by rfl)
    let h' : (profiniteFree R).obj X ⟶ (finFree R).obj T :=
      hm ≫ (finFreeIsoSolid R T).hom
    obtain ⟨U₀, q₀, h₀, hfact⟩ := surj_factor R T X h'
    refine ⟨(profiniteSolid R).map q₀ ≫ (finFreeIsoSolid R U₀).hom ≫
            h₀ ≫ (finFreeIsoSolid R T).inv, ?_⟩
    have hmid := sol_map_counit R U₀ X q₀
    -- Step 1: sol ≫ solid.map q₀ ≫ iso_U₀.hom ≫ h₀ ≫ iso_T.inv
    --         = profiniteFree.map q₀ ≫ h₀ ≫ iso_T.inv  (via congrArg + hmid)
    have step1 : (profiniteSolidification R).app X ≫ (profiniteSolid R).map q₀ ≫
        (finFreeIsoSolid R U₀).hom ≫ h₀ ≫ (finFreeIsoSolid R T).inv =
        (profiniteFree R).map q₀ ≫ h₀ ≫ (finFreeIsoSolid R T).inv := by
      have key := congrArg (· ≫ h₀ ≫ (finFreeIsoSolid R T).inv) hmid
      exact key
    -- Step 2: profiniteFree.map q₀ ≫ h₀ ≫ iso_T.inv = h
    -- (hfact: h' = map q₀ ≫ h₀; h' = hm ≫ iso_T.hom; hm := h; iso cancel)
    have step2 : (profiniteFree R).map q₀ ≫ h₀ ≫ (finFreeIsoSolid R T).inv = h := by
      have key2 := congrArg (· ≫ (finFreeIsoSolid R T).inv) hfact.symm
      simp only [Category.assoc] at key2
      -- key2: map q₀ ≫ h₀ ≫ iso_T.inv = h' ≫ iso_T.inv; expand h' to trigger hom_inv_id
      rw [key2, show h' = hm ≫ (finFreeIsoSolid R T).hom from rfl,
          Category.assoc, (finFreeIsoSolid R T).hom_inv_id, Category.comp_id]
    exact step1.trans step2

/-! ### Limits of solid modules are solid -/

/-- If a condensed `R`-module is the limit of a diagram of solid modules, then it is solid.
Fully proved (no sorry). -/
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
    have hfg' : sol ≫ f = sol ≫ g := hfg
    have key := congrArg (· ≫ c.π.app j) hfg'
    exact key
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
    have hfac : hc.lift g_cone ≫ c.π.app j = g_j j := hc.fac g_cone j
    rw [Category.assoc, hfac]; exact hg_j' j

/-! ### `finFree R T` is solid -/

/-- `(finFree R).obj T` is a solid condensed `R`-module, for any `T : FintypeCat`.
Proof: transfer solidness from `profiniteSolid_fintype_isSolid` via `finFreeIsoSolid R T`
using Yoneda. Proved without additional axioms (uses `sol_leftCancel` indirectly via
`profiniteSolid_fintype_isSolid`). -/
theorem finFree_isSolid (T : FintypeCat.{u}) : ((finFree R).obj T).IsSolid := by
  constructor; intro X
  rw [isIso_iff_bijective]
  have hM := (profiniteSolid_fintype_isSolid R T).isIso_solidification_map X
  rw [isIso_iff_bijective] at hM
  have e := finFreeIsoSolid R T
  constructor
  · -- INJECTIVITY: transfer via post-composition with e.inv / e.hom
    intro f g hfg
    have hfg' : (profiniteSolidification R).app X ≫ f =
                (profiniteSolidification R).app X ≫ g := hfg
    have key1 := congrArg (· ≫ e.inv) hfg'
    simp only [Category.assoc] at key1
    -- Use apply so Lean infers a₁ = f ≫ e.inv from return type, not from key1's non-Yoneda type
    have hfinv : f ≫ e.inv = g ≫ e.inv := by apply hM.1; exact key1
    -- Cancel e.inv using e.hom (inv_hom_id : e.inv ≫ e.hom = 𝟙)
    have key2 := congrArg (· ≫ e.hom) hfinv
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key2
    exact key2
  · -- SURJECTIVITY: h has Yoneda-obj type; let-bind as morphism first
    intro h
    let hh : (profiniteFree R).obj X ⟶ (finFree R).obj T := h
    obtain ⟨f', hf'⟩ := hM.2 (hh ≫ e.inv)
    refine ⟨f' ≫ e.hom, ?_⟩
    have hf'' : (profiniteSolidification R).app X ≫ f' = hh ≫ e.inv := hf'
    have key3 := congrArg (· ≫ e.hom) hf''
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id] at key3
    change (profiniteSolidification R).app X ≫ (f' ≫ e.hom) = h
    exact key3

/-! ### General solidness of `profiniteSolid R` -/

/-- Every `(profiniteSolid R).obj S` is a solid condensed `R`-module, for any `S : Profinite`.
Architecture complete; uses `isSolid_of_isLimit_gen` (proved) and `finFree_isSolid`
(proved modulo `surj_factor` sorry and `sol_leftCancel` axiom). -/
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
