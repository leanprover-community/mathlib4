/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# The skyscraper sheaf as a sheaf of modules

In this file, we define the skyscraper sheaf on a topological space at a point `p` over a sheaf of
rings `R` valued in a module `M` over the stalk of `R` at `p`.

# Implementation notes

We opt to not construct this using `PresheafOfModules.ofPresheaf`, even though this might appear
to be more convenient at first glance. This is because doing so produces expressions of the form
`ModuleCat.of _ (if _ then _ else _)` which are horrible to work with.
-/

open Opposite CategoryTheory Limits ZeroObject

/-
In this file we define the skyscraper sheaf as a sheaf of modules
-/

@[expose] public section

variable {X : TopCat} (p : X)

variable (R : TopCat.Presheaf RingCat X) (M : Type*) [AddCommGroup M] [Module (R.stalk p) M]

/--
The action of the skyscraper sheaf (of modules) on objects.
-/
noncomputable
def skyscraperPresheafOfModulesObj (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    ModuleCat ↑(R.obj U) := by
  classical
  exact if hp : p ∈ unop U then
    letI _ := Module.compHom M (R.germ (unop U) p hp).hom
    .of _ M
  else 0

lemma skyscraperPresheafOfModulesObj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∈ unop U) :
    skyscraperPresheafOfModulesObj p R M U =
    letI _ := Module.compHom M (R.germ (unop U) p hp).hom
    .of (R.obj U) M := dif_pos hp

lemma skyscraperPresheafOfModulesObj_neg {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∉ unop U) :
    skyscraperPresheafOfModulesObj p R M U = 0 := dif_neg hp

open Classical in
/-- The restriction map of the skyscraper presheaf of modules between two opens both
containing `p`: it is the identity on `k(p)`, semilinear with respect to restriction of
scalars along `Γ(X, U) ⟶ Γ(X, V)`. -/
noncomputable
def skyscraperPresheafOfModulesRestriction {U V : (TopologicalSpace.Opens X)ᵒᵖ}
    (i : U ⟶ V) (h : p ∈ unop V) :
    letI _ := Module.compHom M (R.germ (unop U) p (i.unop.le h)).hom
    letI _ := Module.compHom M (R.germ (unop V) p h).hom
    (ModuleCat.of ↑(R.obj U) ↑M) ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map i))).obj
        (ModuleCat.of ↑(R.obj V) ↑M) :=
  letI _ := Module.compHom M (R.germ (unop U) p (i.unop.le h)).hom
  letI _ := Module.compHom M (R.germ (unop V) p h).hom
  ModuleCat.ofHom
    (X := ModuleCat.of ↑(R.obj U) ↑M)
    (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map i))).obj
      (ModuleCat.of ↑(R.obj V) ↑M))
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' a b := by
        -- Both scalar actions are given by acting by the germ in the stalk, and the germ is
        -- unchanged by restriction.
        change ((R.germ (unop U) p (i.unop.le h)).hom a : ↑(R.stalk p)) • b
          = ((R.germ (unop V) p h).hom ((R.map i).hom a) :
            ↑(R.stalk p)) • b
        rw [(TopCat.Presheaf.germ_res_apply' R i p h a)]
    }

open Classical in
lemma skyscraperPresheafOfModulesRestriction_id {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) : skyscraperPresheafOfModulesRestriction p R M (𝟙 U) h =
    letI _ := Module.compHom M (R.germ (unop U) p h).hom
    (ModuleCat.restrictScalarsId'App (RingCat.Hom.hom (R.map (𝟙 U)))
      (congrArg RingCat.Hom.hom (R.map_id U))
      (ModuleCat.of _ M)).inv := rfl

open Classical in
lemma skyscraperPresheafOfModulesRestriction_comp {U V W : (TopologicalSpace.Opens X)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (h : p ∈ unop W) :
    skyscraperPresheafOfModulesRestriction p R M (i ≫ j) h =
      letI _ := Module.compHom M (R.germ (unop W) p h).hom
      skyscraperPresheafOfModulesRestriction p R M i (j.unop.le h) ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map i))).map
          (skyscraperPresheafOfModulesRestriction p R M j h) ≫
        (ModuleCat.restrictScalarsComp'App
          (RingCat.Hom.hom (R.map i))
          (RingCat.Hom.hom (R.map j))
          (RingCat.Hom.hom (R.map (i ≫ j)))
          (by rw [R.map_comp]; rfl)
          (ModuleCat.of _ M)).inv := rfl

open Classical in
/-- The restriction map of the skyscraper presheaf of modules. -/
noncomputable
def skyscraperPresheafOfModulesMap {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    skyscraperPresheafOfModulesObj p R M U ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (R.map i))).obj
      (skyscraperPresheafOfModulesObj p R M V) :=
  if h : p ∈ unop V then
    eqToHom (skyscraperPresheafOfModulesObj_pos p R M (i.unop.le h)) ≫
    skyscraperPresheafOfModulesRestriction p R M i h ≫
    (ModuleCat.restrictScalars _).map (eqToHom (skyscraperPresheafOfModulesObj_pos p R M h).symm)
  else 0

lemma skyscraperPresheafOfModulesMap_pos
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (h : p ∈ unop V) :
    skyscraperPresheafOfModulesMap p R M i =
    eqToHom (skyscraperPresheafOfModulesObj_pos p R M (i.unop.le h)) ≫
    skyscraperPresheafOfModulesRestriction p R M i h ≫
      (ModuleCat.restrictScalars _).map
      (eqToHom (skyscraperPresheafOfModulesObj_pos p R M h).symm) := dif_pos h

lemma skyscraperPresheafOfModulesMap_neg {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∉ unop V) : skyscraperPresheafOfModulesMap p R M i = 0 := dif_neg h

lemma skyscraperPresheafOfModulesObj_isZero_of_neg {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∉ unop U) : IsZero (skyscraperPresheafOfModulesObj p R M U) := by
  rw [skyscraperPresheafOfModulesObj_neg p R M h]
  exact isZero_zero _

lemma skyscraperPresheafOfModulesObj_subsingleton_of_neg {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∉ unop U) : Subsingleton (skyscraperPresheafOfModulesObj p R M U) :=
  ModuleCat.isZero_iff_subsingleton.mp <| skyscraperPresheafOfModulesObj_isZero_of_neg p R M h

open Classical in
noncomputable
def skyscraperPresheafOfModules : PresheafOfModules R where
  obj U := skyscraperPresheafOfModulesObj p R M U
  map i := skyscraperPresheafOfModulesMap p R M i
  map_id X := by
    by_cases h : p ∈ unop X
    · simp [skyscraperPresheafOfModulesMap_pos p R M (𝟙 X) h,
        skyscraperPresheafOfModulesRestriction_id p R M h, ModuleCat.restrictScalarsId'_inv_app,
        ← ModuleCat.restrictScalarsId'App_inv_naturality]
    · rw [skyscraperPresheafOfModulesMap_neg p R M (𝟙 X) h]
      exact (skyscraperPresheafOfModulesObj_isZero_of_neg p R M h).isInitial.hom_ext _ _
  map_comp {U V W} i j := by
    by_cases h : p ∈ unop W
    · rw [skyscraperPresheafOfModulesMap_pos p R M (i ≫ j) h,
      skyscraperPresheafOfModulesMap_pos p R M i (j.unop.le h),
      skyscraperPresheafOfModulesMap_pos p R M j h,
        skyscraperPresheafOfModulesRestriction_comp p R M i j h]
      simp only [ModuleCat.restrictScalarsComp'_inv_app, Functor.map_comp, Category.assoc]
      rw [ModuleCat.restrictScalarsComp'App_inv_naturality]
      simp only [eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · exact ((ModuleCat.restrictScalars _).map_isZero
        (skyscraperPresheafOfModulesObj_isZero_of_neg p R M h)).eq_of_tgt _ _

lemma skyscraperPresheafOfModules_presheaf_map {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    (skyscraperPresheafOfModules p R M).presheaf.map i =
    (forget₂ (ModuleCat _) Ab).map (skyscraperPresheafOfModulesMap p R M i) := rfl

lemma skyscraperPresheafOfModules_forget_map
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (h : p ∈ unop V) :
    (forget₂ (ModuleCat _) Ab).map (skyscraperPresheafOfModulesRestriction p R M i h) = 𝟙 _ := rfl
section Iso

lemma skyscraperPresheafOfModules_presheaf_obj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) :
    (skyscraperPresheafOfModules p R M).presheaf.obj U = AddCommGrpCat.of M := by
  change (forget₂ (ModuleCat _) Ab).obj (skyscraperPresheafOfModulesObj p R M U) = _
  rw [skyscraperPresheafOfModulesObj_pos p R M h]
  rfl

lemma skyscraperPresheafOfModules_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∉ unop U) : IsZero ((skyscraperPresheafOfModules p R M).presheaf.obj U) :=
  (forget₂ (ModuleCat _) Ab).map_isZero (skyscraperPresheafOfModulesObj_isZero_of_neg p R M h)

lemma skyscraperPresheafOfModules_presheaf_map_pos {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∈ unop V) :
    (skyscraperPresheafOfModules p R M).presheaf.map i =
      eqToHom ((skyscraperPresheafOfModules_presheaf_obj_pos p R M (i.unop.le h)).trans
        (skyscraperPresheafOfModules_presheaf_obj_pos p R M h).symm) := by
  rw [skyscraperPresheafOfModules_presheaf_map, skyscraperPresheafOfModulesMap_pos p R M i h]
  simp only [Functor.map_comp, eqToHom_map]
  rw [skyscraperPresheafOfModules_forget_map]
  exact (_ ≫= Category.id_comp _).trans (eqToHom_trans _ _)

open Classical in
/--
The isomorphism from the underlying sheaf of `skyscraperPresheafOfModules` to `skyscraperSheaf` at
an open `U`.
-/
noncomputable
def skyscraperPresheafOfModulesPresheafIsoSkyscraperApp (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (skyscraperPresheafOfModules p R M).presheaf.obj U ≅
    ((skyscraperSheaf p (AddCommGrpCat.of M)).presheaf.obj U) :=
  if h : p ∈ unop U then
    eqToIso ((skyscraperPresheafOfModules_presheaf_obj_pos p R M h).trans
    (if_pos h).symm)
  else
    (skyscraperPresheafOfModules_presheaf_obj_isZero p R M h).iso
    (isTerminalSkyscraperSheafObjObjOfNotMem h).isZero

lemma skyscraperPresheafOfModulesPresheafIsoSkyscraperApp_pos {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) :
    skyscraperPresheafOfModulesPresheafIsoSkyscraperApp p R M U =
      eqToIso ((skyscraperPresheafOfModules_presheaf_obj_pos p R M h).trans (if_pos h).symm) :=
  dif_pos h

open Classical in
/--
When `p ∈ V`, the restriction map of the skyscraper presheaf is an `eqToHom`.
-/
lemma skyscraperAb_presheaf_map_pos {X : TopCat} (p : ↑X)
  [(U : TopologicalSpace.Opens ↑X) → Decidable (p ∈ U)] {C : Type*}
  [Category* C] (A : C) [HasTerminal C] {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∈ unop V) :
    (skyscraperSheaf p A).presheaf.map i =
      eqToHom ((if_pos (i.unop.le h)).trans (if_pos h).symm) := by simp [h]

open Classical in
/--
The underlying presheaf of the skyscraper sheaf of modules is isomorphic to `skyscraperSheaf`
-/
noncomputable def skyscraperPresheafOfModulesPresheafIsoSkyscraper :
    (skyscraperPresheafOfModules p R M).presheaf ≅
    (skyscraperSheaf p (AddCommGrpCat.of M)).presheaf := by
  refine NatIso.ofComponents (skyscraperPresheafOfModulesPresheafIsoSkyscraperApp p R M) ?_
  intro U V i
  by_cases h : p ∈ unop V
  · rw [skyscraperPresheafOfModulesPresheafIsoSkyscraperApp_pos p R M (i.unop.le h),
      skyscraperPresheafOfModulesPresheafIsoSkyscraperApp_pos p R M h,
      skyscraperPresheafOfModules_presheaf_map_pos p R M i h,
      skyscraperAb_presheaf_map_pos p (AddCommGrpCat.of M) i h]
    simp only [eqToIso.hom]
    exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm
  · exact (isTerminalSkyscraperSheafObjObjOfNotMem h).isZero.eq_of_tgt _ _

end Iso

open Classical in
/--
The skyscraper sheaf at a point `p` of a scheme as a sheaf of
-/
noncomputable
def skyscraperSheafOfModules (R : TopCat.Sheaf RingCat X)
    (M : Type*) [AddCommGroup M] [Module (R.presheaf.stalk p) M] : SheafOfModules R where
  val := skyscraperPresheafOfModules p R.presheaf M
  isSheaf := TopCat.Presheaf.isSheaf_of_iso (
    skyscraperPresheafOfModulesPresheafIsoSkyscraper p R.presheaf M).symm
    (skyscraperSheaf p (AddCommGrpCat.of M)).2
