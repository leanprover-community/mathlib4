import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf

open AlgebraicGeometry Opposite CategoryTheory

/-
In this file we define the skyscraper sheaf as a sheaf of modules
-/

@[expose] public section

universe u

variable {X : Scheme.{u}} (p : X)

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

def module_pos_of_ab {P : Prop} (R : Type*) (M N : AddCommGrpCat) [CommRing R]
    [Decidable P] (h : P) [m : Module R M] :
    Module R (AddCommGrpCat.carrier (if P then M else N)) := by
  have : (if P then M else N) = M := if_pos h
  convert m
  congr

def module_neg_of_ab {P : Prop} (R : Type*) (M N : AddCommGrpCat) [CommRing R]
    [Decidable P] (h : ¬P) [m : Module R N] :
    Module R (AddCommGrpCat.carrier (if P then M else N)) := by
  have : (if P then M else N) = N := if_neg h
  convert m
  congr

noncomputable
instance : Unique ((⊤_ Ab).carrier : Type u) := by
  suffices Unique (ToType (⊤_ Ab.{u})) by
    exact this
  infer_instance

noncomputable
instance {R : Type u} [CommRing R] : Module R (ToType (⊤_ Ab.{u})) where
  smul a b := b
  mul_smul a b c := rfl
  one_smul a := rfl
  smul_zero a := rfl
  smul_add a b c := rfl
  add_smul a b c := by apply Subsingleton.elim
  zero_smul a := by apply Subsingleton.elim

instance {R : Type*} [CommRing R] {a : Type*} [AddCommMonoid a] [Unique a] :
    Unique (Module R a) := by
  constructor
  intro a
  · ext a b
    apply Subsingleton.elim
  · constructor
    exact {
      smul a b := b
      mul_smul a b c := rfl
      one_smul a := rfl
      smul_zero a := rfl
      smul_add a b c := rfl
      add_smul a b c := by apply Subsingleton.elim
      zero_smul a := by apply Subsingleton.elim
    }

open Classical in
noncomputable
instance (U : (TopologicalSpace.Opens X)ᵒᵖ) : Module ↑(X.ringCatSheaf.obj.obj U)
  ↑((skyscraperAb p).presheaf.obj U) := by
  simp [skyscraperAb, skyscraperSheaf, skyscraperPresheaf]
  by_cases o : p ∈ unop U
  · suffices Module ↑(X.sheaf.obj.obj U) (AddCommGrpCat.of <| X.residueField p) from
      module_pos_of_ab (X.sheaf.obj.obj U) ((AddCommGrpCat.of ↑(X.residueField p))) (⊤_ Ab) o
    exact instModuleResidueField p (unop U) o
  · exact module_neg_of_ab (X.sheaf.obj.obj U) ((AddCommGrpCat.of ↑(X.residueField p))) (⊤_ Ab) o

noncomputable
def skyscraperPresheafOfModules : PresheafOfModules X.ringCatSheaf.obj := by
  classical
  apply PresheafOfModules.ofPresheaf (skyscraperAb p).presheaf
  intro U V k s s'
  simp only [skyscraperAb, skyscraperSheaf, skyscraperPresheaf]
  -- The nontrivial case is when p ∈ V and p ∈ U: scalar action of Γ(X,U)
  -- on k(p) must be compatible with restriction. This follows because
  -- both actions factor through the stalk at p.
  split_ifs
  · rename_i hV
    have hU : p ∈ unop U := leOfHom k.unop hV
    --simp only [module_pos_of_ab, instModuleResidueField]
    --trace_state
    sorry
  · rename_i h
    have : Subsingleton
        (↑(if p ∈ unop V then AddCommGrpCat.of ↑(X.residueField p) else ⊤_ Ab.{u})) := by
      rw [if_neg h]; infer_instance
    exact Subsingleton.elim _ _
  --split_ifs <;> first | apply Subsingleton.elim | sorry

noncomputable
def skyscraperSheafOfModules : SheafOfModules X.ringCatSheaf where
  val := skyscraperPresheafOfModules p
  isSheaf := (skyscraperAb p).2


open Limits
open Classical in
lemma skyscraperSheafOfModules_val_obj {U : (X.Opens)} :
    (skyscraperSheafOfModules p).val.obj (op U) =
    if hp : p ∈ U
    then
      letI _ := instModuleResidueField p U hp
      .of _ (X.residueField p)
    else terminal _ := by
  --have : ((skyscraperSheafOfModules p).val.obj (op U)) = (skyscraperSheafOfModules p).val.presheaf.obj (op U) := sorry
  simp [skyscraperSheafOfModules, skyscraperPresheafOfModules, skyscraperAb,
    PresheafOfModules.ofPresheaf, skyscraperSheaf_obj_obj]

  sorry

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

def skyscraper2PresheafIsoSkyscraper :
    (skyscraper2 p).presheaf ≅ (skyscraperAb p).presheaf := sorry
