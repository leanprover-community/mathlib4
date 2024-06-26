import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

universe u v w

variable (ℛ : SheafedSpace CommRingCat.{u})

/--
For a comm-ringed space `ℛ`, think `ℛ.sheaf` as a sheaf of (not necessarily commutative) rings.
-/
def forget2Ring :=
  sheafCompose (Opens.grothendieckTopology ℛ) (forget₂ CommRingCat RingCat) |>.obj ℛ.sheaf


variable (ℳ : SheafOfModules $ forget2Ring ℛ)
variable (pt : ℛ) (U U' V V' : Opens ℛ)
variable (pt_mem : pt ∈ U) (pt_mem' : pt ∈ V) (pt_mem'' : pt ∈ V') (pt_mem''' : pt ∈ U')
section modules

abbrev sectionSMulSection
    (r : (ℛ.presheaf.obj $ op U))
    (m : (ℳ.1.obj $ op V)) :
    (ℳ.1.obj $ op $ U ⊓ V) :=
    (ℛ.presheaf.map (op $ homOfLE $ fun x hx => by exact hx.1) r :
      (forget2Ring ℛ).1.obj (op $ U ⊓ V)) •
    (ℳ.1.map (op $ homOfLE $ fun x hx => by exact hx.2) m :
      ℳ.1.obj (op $ U ⊓ V))

lemma sectionSMulSection.restrict
    (r : ℛ.presheaf.obj $ op U)
    (U' : Opens ℛ) (i : U' ⟶ U)
    (m : ℳ.1.obj $ op V)
    (V' : Opens ℛ) (j : V' ⟶ V) :
    ℳ.1.map (op (homOfLE fun x hx => ⟨leOfHom i hx.1, leOfHom j hx.2⟩) : op (U ⊓ V) ⟶ op (U' ⊓ V'))
      (sectionSMulSection ℛ ℳ U V r m) =
    sectionSMulSection ℛ ℳ U' V' (ℛ.presheaf.map (op i) r) (ℳ.1.map (op j) m) := by
  simp only [Opens.coe_inf, sectionSMulSection]
  erw [ℳ.1.map_smul]

  change (ℳ.1.module _).smul _ _ = (ℳ.1.module _).smul _ _
  congr 1
  · change (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _ = (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _
    rw [← ℛ.presheaf.map_comp, ← ℛ.presheaf.map_comp]
    rfl
  · change (ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _) _ = (ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _) _
    rw [← ℳ.1.presheaf.map_comp, ← ℳ.1.presheaf.map_comp]
    rfl

lemma sectionSMulSection.germ
    (r : (ℛ.presheaf.obj $ op U))
    (m : (ℳ.1.obj $ op V))
    (m' : (ℳ.1.obj $ op V'))
    (h : TopCat.Presheaf.germ (F := ℳ.1.presheaf) ⟨pt, pt_mem'⟩ m =
      TopCat.Presheaf.germ (F := ℳ.1.presheaf) ⟨pt, pt_mem''⟩ m') :
    TopCat.Presheaf.germ (F := ℳ.1.presheaf) (⟨pt, ⟨pt_mem, pt_mem'⟩⟩ : (U ⊓ V : Opens _))
      (sectionSMulSection ℛ ℳ U V r m) =
    TopCat.Presheaf.germ (F := ℳ.1.presheaf) (⟨pt, ⟨pt_mem, pt_mem''⟩⟩ : (U ⊓ V' : Opens _))
      (sectionSMulSection ℛ ℳ U V' r m') := by
  obtain ⟨W, mem, iV, iV', hW⟩ := TopCat.Presheaf.germ_eq (h := h)

  fapply TopCat.Presheaf.germ_ext
  · exact U ⊓ W
  · exact ⟨pt_mem, mem⟩
  · exact homOfLE $ inf_le_inf (le_refl _) (leOfHom iV)
  · exact homOfLE $ inf_le_inf (le_refl _) (leOfHom iV')

  erw [sectionSMulSection.restrict]
  pick_goal 2
  · exact 𝟙 U
  pick_goal 2
  · exact iV
  erw [sectionSMulSection.restrict]
  pick_goal 2
  · exact 𝟙 U
  pick_goal 2
  · exact iV'
  erw [hW]
  rfl

lemma sectionSMulSection.germ'
    (r : (ℛ.presheaf.obj $ op U))
    (r' : (ℛ.presheaf.obj $ op U'))
    (hr : ℛ.presheaf.germ ⟨pt, pt_mem⟩ r = ℛ.presheaf.germ ⟨pt, pt_mem'''⟩ r')
    (m : (ℳ.1.obj $ op V))
    (m' : (ℳ.1.obj $ op V'))
    (hm : TopCat.Presheaf.germ (F := ℳ.1.presheaf) ⟨pt, pt_mem'⟩ m =
      TopCat.Presheaf.germ (F := ℳ.1.presheaf) ⟨pt, pt_mem''⟩ m') :
    TopCat.Presheaf.germ (F := ℳ.1.presheaf) (⟨pt, ⟨pt_mem, pt_mem'⟩⟩ : (U ⊓ V : Opens _))
      (sectionSMulSection ℛ ℳ U V r m) =
    TopCat.Presheaf.germ (F := ℳ.1.presheaf) (⟨pt, ⟨pt_mem''', pt_mem''⟩⟩ : (U' ⊓ V' : Opens _))
      (sectionSMulSection ℛ ℳ U' V' r' m') := by
  obtain ⟨W, mem, iU, iU', hW⟩ := TopCat.Presheaf.germ_eq (h := hr)

  have eq1 :
      ℳ.1.presheaf.map
        (op $ homOfLE $ inf_le_inf (leOfHom iU') (le_refl _) : op (U' ⊓ V') ⟶ op (W ⊓ V'))
          (sectionSMulSection ℛ ℳ U' V' r' m') =
      ℳ.1.presheaf.map
        (op $ homOfLE $ inf_le_inf (leOfHom iU) (le_refl _) : op (U ⊓ V') ⟶ op (W ⊓ V'))
          (sectionSMulSection ℛ ℳ U V' r m') := by
    erw [sectionSMulSection.restrict]
    pick_goal 2
    · exact iU'
    pick_goal 2
    · exact 𝟙 _
    erw [sectionSMulSection.restrict]
    pick_goal 2
    · exact iU
    pick_goal 2
    · exact 𝟙 _
    erw [hW]
    rfl

  apply_fun TopCat.Presheaf.germ (F := ℳ.1.presheaf) (⟨pt, ⟨mem, pt_mem''⟩⟩ : (W ⊓ V' : Opens _)) at eq1
  erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at eq1
  simp only [Opens.coe_inf] at eq1
  erw [eq1]
  fapply sectionSMulSection.germ
  · exact pt_mem
  · exact pt_mem'
  · exact pt_mem''
  · exact hm

noncomputable def openSetModule (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    Opens ℛ :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose

noncomputable def openSetRing (x : ℛ.1.presheaf.stalk pt) :
    Opens ℛ :=
  (TopCat.Presheaf.germ_exist _ pt x).choose

lemma mem_openSetModule (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    pt ∈ openSetModule ℛ ℳ pt x :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose

lemma mem_openSetRing (x : ℛ.1.presheaf.stalk pt) :
    pt ∈ openSetRing _ pt x :=
  (TopCat.Presheaf.germ_exist _ pt x).choose_spec.choose

noncomputable def sectionOnOpenSetModule
    (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    ℳ.1.obj (op $ openSetModule ℛ ℳ pt x) :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose_spec.choose

noncomputable def sectionOnOpenSetRing (x : ℛ.1.presheaf.stalk pt) :
    ℛ.presheaf.obj (op $ openSetRing ℛ pt x) :=
    (TopCat.Presheaf.germ_exist _ pt x).choose_spec.choose_spec.choose

lemma germ_sectionOnOpenSetModule (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem_openSetModule ℛ ℳ pt x⟩
      (sectionOnOpenSetModule ℛ ℳ pt x) = x :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose_spec.choose_spec

lemma germ_sectionOnOpenSetRing (x : ℛ.1.presheaf.stalk pt) :
    ℛ.presheaf.germ ⟨pt, mem_openSetRing _ pt x⟩ (sectionOnOpenSetRing _ pt x) = x :=
    (TopCat.Presheaf.germ_exist _ pt x).choose_spec.choose_spec.choose_spec


noncomputable def sectionSMulStalk
    (x : (ℛ.presheaf.obj $ op U))
    (y : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
  TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt :=
    @TopCat.Presheaf.germ (F := ℳ.1.presheaf) _ _
      (U := U ⊓ openSetModule ℛ ℳ pt y)
      ⟨pt, ⟨pt_mem, mem_openSetModule _ _ _ _⟩⟩ $
        sectionSMulSection ℛ ℳ U _ x (sectionOnOpenSetModule ℛ ℳ pt y)

lemma section_smul_germ (r : ℛ.presheaf.obj $ op U) (m : ℳ.1.obj $ op V) :
    (sectionSMulStalk ℛ ℳ pt U pt_mem r
      (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, pt_mem'⟩ m)) =
    (TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, ⟨pt_mem, pt_mem'⟩⟩ : (U ⊓ V : Opens ℛ))
      (sectionSMulSection ℛ ℳ U V r m) :
        TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) := by
  dsimp [sectionSMulStalk]
  fapply sectionSMulSection.germ
  · exact pt_mem
  · exact mem_openSetModule _ _ _ _
  · exact pt_mem'
  · exact germ_sectionOnOpenSetModule _ _ _ _

noncomputable def stalkSMulStalk
    (x : (ℛ.presheaf.stalk pt))
    (y : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt :=
  @TopCat.Presheaf.germ (F := ℳ.1.presheaf) _ _
    (U := openSetRing _ pt x ⊓ openSetModule ℛ ℳ pt y)
    ⟨pt, ⟨mem_openSetRing _ pt x, mem_openSetModule _ _ _ _⟩⟩ $
      sectionSMulSection ℛ ℳ _ _ (sectionOnOpenSetRing _ _ _) (sectionOnOpenSetModule ℛ ℳ pt y)

lemma germ_smul_germ (r : ℛ.presheaf.obj $ op U) (m : ℳ.1.obj $ op V) :
    stalkSMulStalk ℛ ℳ pt
      (ℛ.presheaf.germ ⟨pt, pt_mem⟩ r)
      (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, pt_mem'⟩ m) =
    TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, ⟨pt_mem, pt_mem'⟩⟩ : (U ⊓ V : Opens ℛ))
      (sectionSMulSection _ _ U V r m) := by
  dsimp [stalkSMulStalk]
  fapply sectionSMulSection.germ'
  · apply mem_openSetRing
  · apply mem_openSetModule
  · assumption
  · assumption
  · apply germ_sectionOnOpenSetRing
  · apply germ_sectionOnOpenSetModule


end modules
