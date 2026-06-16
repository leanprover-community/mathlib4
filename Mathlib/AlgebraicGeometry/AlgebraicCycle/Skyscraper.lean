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
      map_smul' a b := by
        -- Both scalar actions are given by acting by the germ in the stalk, and the germ is
        -- unchanged by restriction.
        have key : (R.presheaf.germ (unop U) p (i.unop.le h)).hom a
            = (R.presheaf.germ (unop V) p h).hom ((R.obj.map i).hom a) :=
          (TopCat.Presheaf.germ_res_apply' R.presheaf i p h a).symm
        change ((R.presheaf.germ (unop U) p (i.unop.le h)).hom a : ↑(R.presheaf.stalk p)) • b
          = ((R.presheaf.germ (unop V) p h).hom ((R.obj.map i).hom a) :
            ↑(R.presheaf.stalk p)) • b
        rw [key]
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
    simp only [eqToIso.hom]
    -- The remaining equation composes `eqToHom`s whose middle objects are spelled differently;
    -- elementwise, both sides are casts of `x`.
    ext x
    exact eq_of_heq (((heq_eqToHom_apply_ab _ _).trans (heq_eqToHom_apply_ab _ x)).trans
      ((heq_eqToHom_apply_ab _ _).trans (heq_eqToHom_apply_ab _ x)).symm)
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

/--
The residue field at `p` is a module over the `RingCat`-valued stalk of the structure sheaf,
via the canonical comparison map to the `CommRingCat`-valued stalk followed by the residue map.
-/
noncomputable instance : Module ↑(X.ringCatSheaf.presheaf.stalk p) ↑(X.residueField p) :=
  Module.compHom _ (RingCat.Hom.hom
    (colimit.post ((TopologicalSpace.OpenNhds.inclusion p).op ⋙ X.presheaf)
        (forget₂ CommRingCat RingCat) ≫
      (forget₂ CommRingCat RingCat).map (X.residue p)))

open TopologicalSpace in
/--
Germ-compatibility for the module structure above: acting on the residue field by a section
through its `RingCat`-valued germ is multiplication by the evaluation of the section at `p`.

TODO: Move this somewhere sensible
-/
lemma residueField_compHom_smul_eq {U : X.Opens} (hp' : p ∈ U)
    (a : ↑(X.ringCatSheaf.presheaf.obj (op U))) (m : ↑(X.residueField p)) :
    letI : Module ↑(X.ringCatSheaf.presheaf.obj (op U)) ↑(X.residueField p) :=
      Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
    a • m = (X.evaluation U p hp').hom a * m := by
  -- The comparison map `colimit.post` intertwines the `RingCat`- and `CommRingCat`-germs.
  have hpost : (RingCat.Hom.hom (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat))) ((X.ringCatSheaf.presheaf.germ U p hp').hom a) =
      (X.presheaf.germ U p hp').hom a := by
    have h := colimit.ι_post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) (op ⟨U, hp'⟩)
    exact congrArg (fun f => (RingCat.Hom.hom f) a) h
  change (X.residue p).hom ((RingCat.Hom.hom (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat))) ((X.ringCatSheaf.presheaf.germ U p hp').hom a)) * m =
    (X.evaluation U p hp').hom a * m
  rw [hpost]
  rfl
