import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf

open AlgebraicGeometry Opposite CategoryTheory Limits

/-
In this file we define the skyscraper sheaf as a sheaf of modules
-/

@[expose] public section

universe u

variable {X : Scheme.{u}} (p : X)

section generalised

namespace Test

variable (R : TopCat.Sheaf RingCat ↑X.toPresheafedSpace)
  (M : Type u) [AddCommGroup M] [Module (R.presheaf.stalk p) M]

open Classical in
noncomputable
def skyscraperPresheafOfModulesObj (U : (TopologicalSpace.Opens X)ᵒᵖ) : ModuleCat ↑(R.obj.obj U) :=
  if hp : p ∈ unop U then
    letI _ := Module.compHom M (R.presheaf.germ (unop U) p hp).hom
    .of _ M
  else terminal _

lemma skyscraperPresheafOfModulesObj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∈ unop U) :
    skyscraperPresheafOfModulesObj p R M U =
      letI _ := Module.compHom M (R.presheaf.germ (unop U) p hp).hom
      .of (R.obj.obj U) M := dif_pos hp

lemma skyscraperPresheafOfModulesObj_neg {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∉ unop U) :
    skyscraperPresheafOfModulesObj p R M U = terminal _ := dif_neg hp

open Classical in
/-- The restriction map of the skyscraper presheaf of modules between two opens both
containing `p`: it is the identity on `k(p)`, semilinear with respect to restriction of
scalars along `Γ(X, U) ⟶ Γ(X, V)`. -/
noncomputable
def skyscraperPresheafOfModulesRestriction {U V : (TopologicalSpace.Opens X)ᵒᵖ}
    (i : U ⟶ V) (h : p ∈ unop V) :
    letI _ := Module.compHom M (R.presheaf.germ (unop U) p (i.unop.le h)).hom
    letI _ := Module.compHom M (R.presheaf.germ (unop V) p h).hom
    (ModuleCat.of ↑(R.obj.obj U) ↑M) ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (R.obj.map i))).obj
        (ModuleCat.of ↑(R.obj.obj V) ↑M) :=
  letI _ := Module.compHom M (R.presheaf.germ (unop U) p (i.unop.le h)).hom
  letI _ := Module.compHom M (R.presheaf.germ (unop V) p h).hom
  ModuleCat.ofHom
    (X := ModuleCat.of ↑(R.obj.obj U) ↑M)
    (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (R.obj.map i))).obj
      (ModuleCat.of ↑(R.obj.obj V) ↑M))
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' a b := by sorry
    }

open Classical in
lemma skyscraperPresheafOfModulesRestriction_id {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) : skyscraperPresheafOfModulesRestriction p R M (𝟙 U) h =
    letI _ := Module.compHom M (R.presheaf.germ (unop U) p h).hom
    (ModuleCat.restrictScalarsId'App (RingCat.Hom.hom (R.obj.map (𝟙 U)))
      (congrArg RingCat.Hom.hom (R.obj.map_id U))
      (ModuleCat.of _ M)).inv := by
  apply ModuleCat.hom_ext
  rfl

open Classical in
lemma skyscraperPresheafOfModulesRestriction_comp {U V W : (TopologicalSpace.Opens X)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) (h : p ∈ unop W) :
    skyscraperPresheafOfModulesRestriction p R M (i ≫ j) h =
      letI _ := Module.compHom M (R.presheaf.germ (unop W) p h).hom
      skyscraperPresheafOfModulesRestriction p R M i (j.unop.le h) ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (R.obj.map i))).map
          (skyscraperPresheafOfModulesRestriction p R M j h) ≫
        (ModuleCat.restrictScalarsComp'App
          (RingCat.Hom.hom (R.obj.map i))
          (RingCat.Hom.hom (R.obj.map j))
          (RingCat.Hom.hom (R.obj.map (i ≫ j)))
          (by rw [R.obj.map_comp]; rfl)
          (ModuleCat.of _ M)).inv := by
  apply ModuleCat.hom_ext
  rfl

open Classical in
/-- The restriction map of the skyscraper presheaf of modules. -/
noncomputable
def skyscraperPresheafOfModulesMap {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    skyscraperPresheafOfModulesObj p R M U ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (R.obj.map i))).obj
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

open Limits ZeroObject in
lemma skyscraperPresheafOfModulesObj_isZero_of_neg {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∉ unop U) : Limits.IsZero (skyscraperPresheafOfModulesObj p R M U) := by
  rw [skyscraperPresheafOfModulesObj_neg p R M h]
  exact (isZero_zero _).of_iso (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal)

open Classical in
noncomputable
def skyscraperPresheafOfModules : PresheafOfModules R.obj where
  obj U := skyscraperPresheafOfModulesObj p R M U
  map i := skyscraperPresheafOfModulesMap p R M i
  map_id X := by
    by_cases h : p ∈ unop X
    · rw [skyscraperPresheafOfModulesMap_pos p R M (𝟙 X) h,
        skyscraperPresheafOfModulesRestriction_id p R M h]
      simp only [ModuleCat.restrictScalarsId'_inv_app]
      rw [← ModuleCat.restrictScalarsId'App_inv_naturality]
      simp
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

section Iso

/-- Applying `eqToHom` commutes with application in `ModuleCat` (stated heterogeneously). -/
lemma heq_eqToHom_apply_moduleCat {R : Type*} [Ring R] {M N : ModuleCat R}
    (e : M = N) (x : M) : HEq ((eqToHom e) x) x := by
  subst e
  rfl

/-- Applying `eqToHom` commutes with application in `Ab` (stated heterogeneously). -/
lemma heq_eqToHom_apply_ab {M N : Ab} (e : M = N) (x : M) :
    HEq ((eqToHom e) x) x := by
  subst e
  rfl

lemma skyscraperPresheafOfModules_presheaf_obj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) :
    (skyscraperPresheafOfModules p R M).presheaf.obj U = AddCommGrpCat.of M := by
  change (forget₂ (ModuleCat _) Ab).obj (skyscraperPresheafOfModulesObj p R M U) = _
  rw [skyscraperPresheafOfModulesObj_pos p R M h]
  rfl

/-
open Classical in
lemma skyscraperAb_presheaf_obj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∈ unop U) :
    (skyscraperSheaf p (AddCommGrpCat.of M)).presheaf.obj U = AddCommGrpCat.of M := if_pos h

lemma skyscraper2_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∉ unop U) :
    IsZero ((skyscraper2 p).presheaf.obj U) :=
  (forget₂ (ModuleCat _) Ab).map_isZero (skyObj_isZero_of_neg p h)-/

lemma skyscraperPresheafOfModules_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∉ unop U) : IsZero ((skyscraperPresheafOfModules p R M).presheaf.obj U) :=
  (forget₂ (ModuleCat _) Ab).map_isZero (skyscraperPresheafOfModulesObj_isZero_of_neg p R M h)

noncomputable
instance : Unique ((⊤_ Ab).carrier : Type u) := by
  suffices Unique (ToType (⊤_ Ab.{u})) by
    exact this
  infer_instance

open Classical in
/--
NOTE: This is not general enough. This is here whilst I try and inline every use of it - if this
is successful, remove
-/
lemma skyscraperAb_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∉ unop U) :
    IsZero ((skyscraperSheaf p (AddCommGrpCat.of M)).presheaf.obj U) := by
  simp [h, AddCommGrpCat.isZero_of_subsingleton]

/--
When `p ∈ V`, the restriction map of the underlying `Ab`-presheaf of `skyscraper2` is the
identity of the residue field, i.e. an `eqToHom`.
-/
lemma skyscraperPresheafOfModules_presheaf_map_pos {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∈ unop V) :
    (skyscraperPresheafOfModules p R M).presheaf.map i =
      eqToHom ((skyscraperPresheafOfModules_presheaf_obj_pos p R M (i.unop.le h)).trans
        (skyscraperPresheafOfModules_presheaf_obj_pos p R M h).symm) := by
  ext x
  change (skyscraperPresheafOfModulesMap p R M i) x =
    (eqToHom ((skyscraperPresheafOfModules_presheaf_obj_pos p R M (i.unop.le h)).trans
    (skyscraperPresheafOfModules_presheaf_obj_pos p R M h).symm)) x
  rw [skyscraperPresheafOfModulesMap_pos p R M i h]
  exact eq_of_heq
    (((heq_eqToHom_apply_moduleCat (skyscraperPresheafOfModulesObj_pos p R M h).symm _).trans
    (heq_eqToHom_apply_moduleCat (skyscraperPresheafOfModulesObj_pos p R M (i.unop.le h)) x)).trans
    (heq_eqToHom_apply_ab _ x).symm)

open Classical in
/--
The component at `U` of the isomorphism between the underlying `Ab`-presheaf of `skyscraper2`
and the skyscraper presheaf: when `p ∈ U` both objects are equal to (the `Ab`-bundling of) the
residue field at `p`; otherwise both objects are zero objects.
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
    (by simp [h, AddCommGrpCat.isZero_of_subsingleton])

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
      eqToHom ((if_pos (i.unop.le h)).trans (if_pos h).symm) := by
  change (skyscraperPresheaf p A).map i = _
  rw [skyscraperPresheaf_map, dif_pos h]

open Classical in
/--
The underlying `Ab`-presheaf of `skyscraper2` is isomorphic to the skyscraper presheaf valued in
the residue field at `p`.
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
    simp
    sorry
  · have : IsZero ((skyscraperSheaf p (AddCommGrpCat.of M)).presheaf.obj V) := by
      simp [h, AddCommGrpCat.isZero_of_subsingleton]
    exact this.eq_of_tgt _ _

open Classical in
/--
The skyscraper sheaf of modules at `p` valued in the residue field at `p`: the underlying
presheaf of modules is `skyscraper2`, and the sheaf condition is transported along
`skyscraper2PresheafIsoSkyscraper` from the sheaf condition for the skyscraper sheaf.
-/
noncomputable
def skyscraperSheafOfModules : SheafOfModules R where
  val := skyscraperPresheafOfModules p R M
  isSheaf := TopCat.Presheaf.isSheaf_of_iso (
    skyscraperPresheafOfModulesPresheafIsoSkyscraper p R M).symm
    (skyscraperSheaf p (AddCommGrpCat.of M)).2
end Iso


instance : Module ↑(X.ringCatSheaf.presheaf.stalk p) ↑(X.residueField p) := sorry

noncomputable abbrev skyscraperResidueField :=
  skyscraperSheafOfModules p (X.ringCatSheaf) ↑(X.residueField p)

end Test

end generalised

open Classical in
/--
This definition is a bit of a placeholder - it will almost certainly become inlined at some point,
it's mainly just here to make porting easier
-/
noncomputable
def skyscraperAb : TopCat.Sheaf Ab X := skyscraperSheaf p (.of <| X.residueField p)

noncomputable
def instModuleResidueField (U : X.Opens) (hP : p ∈ U) :
  Module ↑(X.ringCatSheaf.obj.obj (op U)) ↑(X.residueField p) := (X.evaluation U p hP).hom.toModule


/-
This definition of the skyscraper sheaf as a sheaf of modules
has kind of bad defeqs...

The following is a skeleton of a definition of the skyscraper
sheaf which has the if outside any Module.of calls, and also
has the benefit of having the right terminal object in the
else case
-/

open Classical in
/-- The underlying module of the skyscraper presheaf of modules over an open `U`:
the residue field `k(p)` (as a module over the sections over `U`) when `p ∈ U`, and the
terminal (zero) module otherwise. -/
noncomputable
def skyObj (U : (TopologicalSpace.Opens X)ᵒᵖ) : ModuleCat ↑(X.ringCatSheaf.obj.obj U) :=
  if hp : p ∈ unop U then
    letI _ := instModuleResidueField p (unop U) hp
    .of _ (X.residueField p)
  else terminal _

lemma skyObj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∈ unop U) :
    skyObj p U =
      letI _ := instModuleResidueField p (unop U) hp
      .of _ (X.residueField p) :=
  dif_pos hp

lemma skyObj_neg {U : (TopologicalSpace.Opens X)ᵒᵖ} (hp : p ∉ unop U) :
    skyObj p U = terminal _ :=
  dif_neg hp

open Classical in
/-- The restriction map of the skyscraper presheaf of modules between two opens both
containing `p`: it is the identity on `k(p)`, semilinear with respect to restriction of
scalars along `Γ(X, U) ⟶ Γ(X, V)`. -/
noncomputable
def coreMap {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (h : p ∈ unop V) :
    letI _ := instModuleResidueField p (unop U) (i.unop.le h)
    letI _ := instModuleResidueField p (unop V) h
    (ModuleCat.of ↑(X.ringCatSheaf.obj.obj U) ↑(X.residueField p)) ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map i))).obj
        (ModuleCat.of ↑(X.ringCatSheaf.obj.obj V) ↑(X.residueField p)) :=
  letI _ := instModuleResidueField p (unop V) h
  letI _ := instModuleResidueField p (unop U) (i.unop.le h)
  ModuleCat.ofHom
    (X := ModuleCat.of ↑(X.ringCatSheaf.obj.obj U) ↑(X.residueField p))
    (Y := (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map i))).obj
      (ModuleCat.of ↑(X.ringCatSheaf.obj.obj V) ↑(X.residueField p)))
    { toFun x := x
      map_add' _ _ := rfl
      map_smul' a b := by
        have key : (X.evaluation (unop U) p (i.unop.le h)).hom a
            = (X.evaluation (unop V) p h).hom ((X.ringCatSheaf.obj.map i).hom a) := by
          rw [show (X.ringCatSheaf.obj.map i).hom a = X.presheaf.map i a from rfl,
            ← Scheme.germ_residue, ← Scheme.germ_residue, CommRingCat.comp_apply,
            CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply']
        show (X.evaluation (unop U) p (i.unop.le h)).hom a * b
          = (X.evaluation (unop V) p h).hom ((X.ringCatSheaf.obj.map i).hom a) * b
        rw [key] }

open Classical in
/-- The restriction map of the skyscraper presheaf of modules. -/
noncomputable
def skyMap {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) :
    skyObj p U ⟶
      (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map i))).obj (skyObj p V) :=
  if h : p ∈ unop V then
    eqToHom (skyObj_pos p (i.unop.le h)) ≫ coreMap p i h ≫
      (ModuleCat.restrictScalars _).map (eqToHom (skyObj_pos p h).symm)
  else
    0

lemma skyMap_pos {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (h : p ∈ unop V) :
    skyMap p i = eqToHom (skyObj_pos p (i.unop.le h)) ≫ coreMap p i h ≫
      (ModuleCat.restrictScalars _).map (eqToHom (skyObj_pos p h).symm) :=
  dif_pos h

lemma skyMap_neg {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (h : p ∉ unop V) :
    skyMap p i = 0 :=
  dif_neg h

open Classical in
lemma coreMap_id {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∈ unop U) :
    coreMap p (𝟙 U) h =
      letI _ := instModuleResidueField p (unop U) h
      (ModuleCat.restrictScalarsId'App (RingCat.Hom.hom (X.ringCatSheaf.obj.map (𝟙 U)))
        (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_id U))
        (ModuleCat.of _ (X.residueField p))).inv := by
  apply ModuleCat.hom_ext
  rfl

open Classical in
lemma coreMap_comp {U V W : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W)
    (h : p ∈ unop W) :
    coreMap p (i ≫ j) h =
      letI _ := instModuleResidueField p (unop W) h
      coreMap p i (j.unop.le h) ≫
        (ModuleCat.restrictScalars (RingCat.Hom.hom (X.ringCatSheaf.obj.map i))).map
          (coreMap p j h) ≫
        (ModuleCat.restrictScalarsComp'App
          (RingCat.Hom.hom (X.ringCatSheaf.obj.map i))
          (RingCat.Hom.hom (X.ringCatSheaf.obj.map j))
          (RingCat.Hom.hom (X.ringCatSheaf.obj.map (i ≫ j)))
          (by rw [X.ringCatSheaf.obj.map_comp]; rfl)
          (ModuleCat.of _ (X.residueField p))).inv := by
  apply ModuleCat.hom_ext
  rfl

open Limits ZeroObject in
lemma skyObj_isZero_of_neg {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∉ unop U) :
    Limits.IsZero (skyObj p U) := by
  rw [skyObj_neg p h]
  exact (isZero_zero _).of_iso (terminalIsTerminal.uniqueUpToIso (isZero_zero _).isTerminal)

open Classical in
noncomputable
def skyscraper2 : PresheafOfModules X.ringCatSheaf.obj where
  obj U := skyObj p U
  map i := skyMap p i
  map_id X := by
    by_cases h : p ∈ unop X
    · rw [skyMap_pos p (𝟙 X) h, coreMap_id p h]
      simp only [ModuleCat.restrictScalarsId'_inv_app]
      rw [← ModuleCat.restrictScalarsId'App_inv_naturality]
      simp
    · rw [skyMap_neg p (𝟙 X) h]
      exact (skyObj_isZero_of_neg p h).isInitial.hom_ext _ _
  map_comp {U V W} i j := by
    by_cases h : p ∈ unop W
    · rw [skyMap_pos p (i ≫ j) h, skyMap_pos p i (j.unop.le h), skyMap_pos p j h,
        coreMap_comp p i j h]
      simp only [ModuleCat.restrictScalarsComp'_inv_app, Functor.map_comp, Category.assoc]
      rw [ModuleCat.restrictScalarsComp'App_inv_naturality]
      simp only [eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    · exact ((ModuleCat.restrictScalars _).map_isZero (skyObj_isZero_of_neg p h)).eq_of_tgt _ _

section PresheafIsoSkyscraper

open Limits

/-- Applying `eqToHom` commutes with application in `ModuleCat` (stated heterogeneously). -/
lemma heq_eqToHom_apply_moduleCat {R : Type*} [Ring R] {M N : ModuleCat R}
    (e : M = N) (x : M) : HEq ((eqToHom e) x) x := by
  subst e
  rfl

/-- Applying `eqToHom` commutes with application in `Ab` (stated heterogeneously). -/
lemma heq_eqToHom_apply_ab {M N : Ab} (e : M = N) (x : M) :
    HEq ((eqToHom e) x) x := by
  subst e
  rfl

lemma skyscraper2_presheaf_obj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∈ unop U) :
    (skyscraper2 p).presheaf.obj U = AddCommGrpCat.of (X.residueField p) := by
  change (forget₂ (ModuleCat _) Ab).obj (skyObj p U) = _
  rw [skyObj_pos p h]
  rfl

lemma skyscraperAb_presheaf_obj_pos {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∈ unop U) :
    (skyscraperAb p).presheaf.obj U = AddCommGrpCat.of (X.residueField p) := if_pos h

lemma skyscraper2_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∉ unop U) :
    IsZero ((skyscraper2 p).presheaf.obj U) :=
  (forget₂ (ModuleCat _) Ab).map_isZero (skyObj_isZero_of_neg p h)

noncomputable
instance : Unique ((⊤_ Ab).carrier : Type u) := by
  suffices Unique (ToType (⊤_ Ab.{u})) by
    exact this
  infer_instance

lemma skyscraperAb_presheaf_obj_isZero {U : (TopologicalSpace.Opens X)ᵒᵖ} (h : p ∉ unop U) :
    IsZero ((skyscraperAb p).presheaf.obj U) := by
  have : (skyscraperAb p).presheaf.obj U = ⊤_ Ab := if_neg h
  rw [this]
  exact AddCommGrpCat.isZero_of_subsingleton _

/--
When `p ∈ V`, the restriction map of the underlying `Ab`-presheaf of `skyscraper2` is the
identity of the residue field, i.e. an `eqToHom`.
-/
lemma skyscraper2_presheaf_map_pos {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∈ unop V) :
    (skyscraper2 p).presheaf.map i =
      eqToHom ((skyscraper2_presheaf_obj_pos p (i.unop.le h)).trans
        (skyscraper2_presheaf_obj_pos p h).symm) := by
  ext x
  change (skyMap p i) x = (eqToHom ((skyscraper2_presheaf_obj_pos p (i.unop.le h)).trans
    (skyscraper2_presheaf_obj_pos p h).symm)) x
  rw [skyMap_pos p i h]
  exact eq_of_heq (((heq_eqToHom_apply_moduleCat (skyObj_pos p h).symm _).trans
    (heq_eqToHom_apply_moduleCat (skyObj_pos p (i.unop.le h)) x)).trans
    (heq_eqToHom_apply_ab _ x).symm)

open Classical in
/--
When `p ∈ V`, the restriction map of the skyscraper presheaf is an `eqToHom`.
-/
lemma skyscraperAb_presheaf_map_pos {U V : (TopologicalSpace.Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p ∈ unop V) :
    (skyscraperAb p).presheaf.map i =
      eqToHom ((skyscraperAb_presheaf_obj_pos p (i.unop.le h)).trans
        (skyscraperAb_presheaf_obj_pos p h).symm) := by
  change (skyscraperPresheaf p (AddCommGrpCat.of (X.residueField p))).map i = _
  rw [skyscraperPresheaf_map, dif_pos h]
  rfl

open Classical in
/--
The component at `U` of the isomorphism between the underlying `Ab`-presheaf of `skyscraper2`
and the skyscraper presheaf: when `p ∈ U` both objects are equal to (the `Ab`-bundling of) the
residue field at `p`; otherwise both objects are zero objects.
-/
noncomputable
def skyscraper2PresheafIsoSkyscraperApp (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (skyscraper2 p).presheaf.obj U ≅ (skyscraperAb p).presheaf.obj U :=
  if h : p ∈ unop U then
    eqToIso ((skyscraper2_presheaf_obj_pos p h).trans (skyscraperAb_presheaf_obj_pos p h).symm)
  else
    (skyscraper2_presheaf_obj_isZero p h).iso (skyscraperAb_presheaf_obj_isZero p h)

lemma skyscraper2PresheafIsoSkyscraperApp_pos {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (h : p ∈ unop U) :
    skyscraper2PresheafIsoSkyscraperApp p U =
      eqToIso ((skyscraper2_presheaf_obj_pos p h).trans
        (skyscraperAb_presheaf_obj_pos p h).symm) :=
  dif_pos h

/--
The underlying `Ab`-presheaf of `skyscraper2` is isomorphic to the skyscraper presheaf valued in
the residue field at `p`.
-/
noncomputable
def skyscraper2PresheafIsoSkyscraper :
    (skyscraper2 p).presheaf ≅ (skyscraperAb p).presheaf :=
  NatIso.ofComponents (skyscraper2PresheafIsoSkyscraperApp p) (by
    intro U V i
    by_cases h : p ∈ unop V
    · rw [skyscraper2PresheafIsoSkyscraperApp_pos p (i.unop.le h),
        skyscraper2PresheafIsoSkyscraperApp_pos p h,
        skyscraper2_presheaf_map_pos p i h, skyscraperAb_presheaf_map_pos p i h]
      simp
    · exact (skyscraperAb_presheaf_obj_isZero p h).eq_of_tgt _ _)

end PresheafIsoSkyscraper

/--
The skyscraper sheaf of modules at `p` valued in the residue field at `p`: the underlying
presheaf of modules is `skyscraper2`, and the sheaf condition is transported along
`skyscraper2PresheafIsoSkyscraper` from the sheaf condition for the skyscraper sheaf.
-/
noncomputable
def skyscraper2SheafOfModules : SheafOfModules X.ringCatSheaf where
  val := skyscraper2 p
  isSheaf := TopCat.Presheaf.isSheaf_of_iso (skyscraper2PresheafIsoSkyscraper p).symm
    (skyscraperAb p).2
