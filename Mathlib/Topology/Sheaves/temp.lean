import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
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

lemma sectionSMulSection.mul_smul
    (r : (ℛ.presheaf.obj $ op U))
    (r' : (ℛ.presheaf.obj $ op U'))
    (m : (ℳ.1.obj $ op V)) :
    sectionSMulSection ℛ ℳ _ _ (r|_ (U ⊓ U') * r' |_(U ⊓ U')) m =
    ℳ.1.presheaf.map (op $ homOfLE $ by dsimp; exact le_of_eq (inf_assoc _ _ _))
    (sectionSMulSection ℛ ℳ U _ r
      (sectionSMulSection ℛ ℳ U' V r' m)) := by
  delta sectionSMulSection
  rw [map_mul]
  erw [(ℳ.1.module _).mul_smul]
  erw [ℳ.1.map_smul, ℳ.1.map_smul, ℳ.1.map_smul]
  congr 1
  · change (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _ = (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _
    rw [← ℛ.presheaf.map_comp, ← ℛ.presheaf.map_comp]
    rfl
  · change _ = (ℳ.1.module _).smul ((ℛ.presheaf.map _ ≫ ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _) _
    rw [← ℛ.presheaf.map_comp, ← ℛ.presheaf.map_comp]
    congr 1
    · change (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _ = _
      rw [← ℛ.presheaf.map_comp]
      rfl
    · change _ = ((ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _) _)
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl

lemma sectionSMulSection.one_smul (m : (ℳ.1.obj $ op V)) :
    sectionSMulSection ℛ ℳ U V 1 m =
    ℳ.1.presheaf.map (op $ homOfLE $ inf_le_right) m := by
  delta sectionSMulSection
  rw [map_one]
  exact (ℳ.1.module _).one_smul _

lemma sectionSMulSection.smul_zero (r : (ℛ.presheaf.obj $ op U)) :
    sectionSMulSection ℛ ℳ U V r 0 = 0 := by
  delta sectionSMulSection
  rw [map_zero]
  exact (ℳ.1.module _).smul_zero _

lemma sectionSMulSection.smul_add (r : (ℛ.presheaf.obj $ op U)) (x y : (ℳ.1.obj $ op V)) :
    sectionSMulSection ℛ ℳ U V r (x + y) =
    sectionSMulSection ℛ ℳ U V r x + sectionSMulSection ℛ ℳ U V r y := by
  delta sectionSMulSection
  rw [map_add]
  exact (ℳ.1.module _).smul_add _ _ _

lemma sectionSMulSection.add_smul (r s : ℛ.presheaf.obj $ op U) (m : ℳ.1.obj $ op V) :
    sectionSMulSection ℛ ℳ U V (r + s) m =
    sectionSMulSection ℛ ℳ U V r m + sectionSMulSection ℛ ℳ U V s m := by
  delta sectionSMulSection
  rw [map_add]
  exact (ℳ.1.module _).add_smul _ _ _

lemma sectionSMulSection.zero_smul (m : ℳ.1.obj $ op V) :
    sectionSMulSection ℛ ℳ U V 0 m = 0 := by
  delta sectionSMulSection
  rw [map_zero]
  exact (ℳ.1.module _).zero_smul _

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

lemma section_res_smul_stalk (r : ℛ.presheaf.obj $ op U) (i : U' ⟶ U)
    (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt U' pt_mem''' (ℛ.presheaf.map (op i) r) m =
    sectionSMulStalk ℛ ℳ pt U pt_mem r m := by
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  dsimp [sectionSMulStalk]
  fapply sectionSMulSection.germ'
  · exact pt_mem'''
  · apply mem_openSetModule
  · apply mem_openSetModule
  · exact leOfHom i pt_mem'''
  · erw [TopCat.Presheaf.germ_res_apply]
  · rw [germ_sectionOnOpenSetModule]



lemma sectionSMulStalk.one_smul (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt U pt_mem 1 m = m := by
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  erw [section_smul_germ]
  rw [sectionSMulSection.one_smul]
  erw [TopCat.Presheaf.germ_res_apply]

lemma sectionSMulStalk.mul_smul
    (r : ℛ.presheaf.obj $ op U) (r' : ℛ.presheaf.obj $ op U')
    (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt _ (by exact ⟨pt_mem, pt_mem'''⟩ : pt ∈ U ⊓ U')
      (r|_ (U ⊓ U') * r' |_(U ⊓ U')) m =
    sectionSMulStalk ℛ ℳ pt _ pt_mem r
      (sectionSMulStalk ℛ ℳ pt _ pt_mem''' r' m) := by
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  erw [section_smul_germ, section_smul_germ]
  rw [sectionSMulSection.mul_smul]
  erw [TopCat.Presheaf.germ_res_apply]
  fapply sectionSMulSection.germ
  · exact pt_mem
  · exact ⟨pt_mem''', mem⟩
  · exact ⟨pt_mem''', by apply mem_openSetModule⟩
  fapply sectionSMulSection.germ
  · exact pt_mem'''
  · exact mem
  · apply mem_openSetModule
  · rw [germ_sectionOnOpenSetModule]; rfl

lemma sectionSMulStalk.mul_smul'
    (r r' : ℛ.presheaf.obj $ op U)
    (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt _ pt_mem (r * r') m =
    sectionSMulStalk ℛ ℳ pt _ pt_mem r
      (sectionSMulStalk ℛ ℳ pt _ pt_mem r' m) := by
  rw [← sectionSMulStalk.mul_smul]
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  erw [section_smul_germ, section_smul_germ]
  fapply sectionSMulSection.germ'
  · exact pt_mem
  · exact mem
  · exact mem
  · exact ⟨pt_mem, pt_mem⟩
  · fapply TopCat.Presheaf.germ_ext
    · exact U
    · exact pt_mem
    · exact 𝟙 U
    · exact homOfLE fun x hx => ⟨hx, hx⟩
    simp only [op_id, CategoryTheory.Functor.map_id, map_mul, id_apply]
    change _ = (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _ * (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _
    rw [← ℛ.presheaf.map_comp, ← op_comp]
    erw [ℛ.presheaf.map_id]
    rfl
  · rfl

lemma sectionSMulStalk.smul_add
    (r : ℛ.presheaf.obj $ op U)
    (m m' : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt _ pt_mem r (m + m') =
    sectionSMulStalk ℛ ℳ pt _ pt_mem r m + sectionSMulStalk ℛ ℳ pt _ pt_mem r m' := by

  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  obtain ⟨W', mem', w', rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m'
  have eq1 : TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem⟩ w +
      TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem'⟩ w' =
      TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, ⟨mem, mem'⟩⟩ : (W ⊓ W' : Opens _))
        (w |_ (W ⊓ W') + w' |_ (W ⊓ W')) := by
    rw [map_add]
    congr 1
    · fapply TopCat.Presheaf.germ_ext
      · exact W ⊓ W'
      · exact ⟨mem, mem'⟩
      · exact homOfLE fun x hx => by aesop
      · exact 𝟙 _
      · change _ = (ℳ.1.presheaf.map _ ≫ _) _
        rw [← ℳ.1.presheaf.map_comp]
        rfl
    · fapply TopCat.Presheaf.germ_ext
      · exact W ⊓ W'
      · exact ⟨mem, mem'⟩
      · exact homOfLE fun x hx => by aesop
      · exact 𝟙 _
      · change _ = (ℳ.1.presheaf.map _ ≫ _) _
        rw [← ℳ.1.presheaf.map_comp]
        rfl

  erw [eq1, section_smul_germ, section_smul_germ, section_smul_germ]
  rw [sectionSMulSection.smul_add, map_add]
  congr 1
  · fapply sectionSMulSection.germ
    · exact pt_mem
    · exact ⟨mem, mem'⟩
    · exact mem
    · erw [TopCat.Presheaf.germ_res_apply]
      rfl
  · fapply sectionSMulSection.germ
    · exact pt_mem
    · exact ⟨mem, mem'⟩
    · exact mem'
    · erw [TopCat.Presheaf.germ_res_apply]
      rfl

lemma sectionSMulStalk.add_smul
    (r s : ℛ.presheaf.obj $ op U)
    (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt _ pt_mem (r + s) m =
    sectionSMulStalk ℛ ℳ pt _ pt_mem r m + sectionSMulStalk ℛ ℳ pt _ pt_mem s m := by
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  erw [section_smul_germ, section_smul_germ, section_smul_germ]
  rw [sectionSMulSection.add_smul, map_add]

lemma sectionSMulStalk.zero_smul
    (m : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    sectionSMulStalk ℛ ℳ pt _ pt_mem 0 m = 0 := by
  obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
  erw [section_smul_germ]
  rw [sectionSMulSection.zero_smul, map_zero]

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

noncomputable instance SMul.section_stalk :
    SMul (ℛ.presheaf.obj $ op U)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  smul x y := sectionSMulStalk _ _ _ _ pt_mem x y

noncomputable instance MulAction.section_stalk :
    MulAction (ℛ.presheaf.obj $ op U)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  __ := SMul.section_stalk ℛ ℳ _ _ pt_mem
  one_smul m := by
    change sectionSMulStalk _ _ _ _ _ 1 m = m
    apply sectionSMulStalk.one_smul
  mul_smul r r' m := by
    change sectionSMulStalk _ _ _ _ _ _ _ =
      sectionSMulStalk _ _ _ _ _ _ (sectionSMulStalk _ _ _ _ _ _ _)
    apply sectionSMulStalk.mul_smul'

noncomputable instance DistribMulAction.section_stalk :
    DistribMulAction (ℛ.presheaf.obj $ op U)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  __ := MulAction.section_stalk ℛ ℳ _ _ pt_mem
  smul_zero r := by
    change sectionSMulStalk _ _ _ _ _ r 0 = 0
    rw [show (0 : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) =
      TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, pt_mem⟩ 0 by rw [map_zero]]
    erw [section_smul_germ]
    fapply TopCat.Presheaf.germ_ext
    · exact U
    · exact pt_mem
    · exact homOfLE fun x hx => ⟨hx, hx⟩
    · exact 𝟙 U
    · rw [sectionSMulSection.smul_zero]
      generalize_proofs h1
      erw [(ℳ.1.presheaf.map (homOfLE h1).op).map_zero]
      simp
  smul_add r m m' := by
    change sectionSMulStalk _ _ _ _ _ r _ =
      sectionSMulStalk _ _ _ _ _ r _ + sectionSMulStalk _ _ _ _ _ r _
    apply sectionSMulStalk.smul_add

noncomputable instance Module.section_stalk :
    Module (ℛ.presheaf.obj $ op U)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  __ := DistribMulAction.section_stalk ℛ ℳ _ _ pt_mem
  add_smul r s m := by
    change sectionSMulStalk _ _ _ _ _ (r + s) m =
      sectionSMulStalk _ _ _ _ _ r m + sectionSMulStalk _ _ _ _ _ s m
    apply sectionSMulStalk.add_smul
  zero_smul m := by
    change sectionSMulStalk _ _ _ _ _ 0 m = 0
    apply sectionSMulStalk.zero_smul

noncomputable instance SMul.stalk_stalk :
    SMul (ℛ.presheaf.stalk pt) (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  smul x y := stalkSMulStalk _ _ pt x y

noncomputable instance MulAction.stalk_stalk :
    MulAction (ℛ.presheaf.stalk pt)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  one_smul m := by
    obtain ⟨W, mem, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := ℳ.1.presheaf) _ m
    change stalkSMulStalk _ _ _ _ _ = _
    have eq1 : (1 : ℛ.presheaf.stalk pt) = ℛ.presheaf.germ (⟨pt, ⟨⟩⟩ : (⊤ : Opens _)) 1 := by
      rw [map_one]
    rw [eq1]
    erw [germ_smul_germ]
    rw [sectionSMulSection.one_smul]
    erw [TopCat.Presheaf.germ_res_apply]
  mul_smul r r' m := by
    obtain ⟨Or, mem_r, r, rfl⟩ := ℛ.presheaf.germ_exist _ r
    obtain ⟨Or', mem_r', r', rfl⟩ := ℛ.presheaf.germ_exist _ r'
    obtain ⟨W, memW, m, rfl⟩ := TopCat.Presheaf.germ_exist (F := ℳ.1.presheaf) _ m
    have eq1 : (ℛ.presheaf.germ ⟨pt, mem_r⟩) r * (ℛ.presheaf.germ ⟨pt, mem_r'⟩) r' =
      ℛ.presheaf.germ (⟨pt, ⟨mem_r, mem_r'⟩⟩ : (Or ⊓ Or' : Opens _))
        (r |_ _ * r' |_ _) := by
      rw [map_mul]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [eq1]
    change stalkSMulStalk _ _ _ _ _ = _
    erw [germ_smul_germ]
    rw [sectionSMulSection.mul_smul]
    erw [TopCat.Presheaf.germ_res_apply]
    change _ = stalkSMulStalk _ _ _ _ (stalkSMulStalk _ _ _ _ _)
    erw [germ_smul_germ]
    simp only [Opens.coe_inf, id_eq]
    fapply sectionSMulSection.germ <;> try assumption
    · exact ⟨mem_r', memW⟩
    · exact ⟨by apply mem_openSetRing, by apply mem_openSetModule⟩

    fapply sectionSMulSection.germ' <;> try assumption
    · apply mem_openSetModule
    · apply mem_openSetRing
    · rw [germ_sectionOnOpenSetRing]
    · rw [germ_sectionOnOpenSetModule]; rfl

noncomputable instance DistribMulAction.stalk_stalk :
    DistribMulAction (ℛ.presheaf.stalk pt)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  smul_zero r := by
    obtain ⟨Or, mem_r, r, rfl⟩ := ℛ.presheaf.germ_exist _ r
    change stalkSMulStalk _ _ _ _ _ = _
    rw [show (0 : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) =
      TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, mem_r⟩) 0 by rw [map_zero], germ_smul_germ,
      sectionSMulSection.smul_zero, map_zero, map_zero]
  smul_add r x y := by
    obtain ⟨Or, mem_r, r, rfl⟩ := ℛ.presheaf.germ_exist _ r
    obtain ⟨Ox, mem_x, x, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf _ x
    obtain ⟨Oy, mem_y, y, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf _ y
    change stalkSMulStalk _ _ _ _ _ =
      stalkSMulStalk _ _ _ _ _ + stalkSMulStalk _ _ _ _ _
    have eq1 : TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem_x⟩ x +
      TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem_y⟩ y =
      TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, ⟨mem_x, mem_y⟩⟩ : (Ox ⊓ Oy : Opens _))
        (x |_ (Ox ⊓ Oy) + y |_ (Ox ⊓ Oy)) := by
      rw [map_add]
      congr 1
      · fapply TopCat.Presheaf.germ_ext
        · exact Ox ⊓ Oy
        · exact ⟨mem_x, mem_y⟩
        · exact homOfLE fun x hx => by aesop
        · exact 𝟙 _
        · change _ = (ℳ.1.presheaf.map _ ≫ _) _
          rw [← ℳ.1.presheaf.map_comp]
          rfl
      · fapply TopCat.Presheaf.germ_ext
        · exact Ox ⊓ Oy
        · exact ⟨mem_x, mem_y⟩
        · exact homOfLE fun x hx => by aesop
        · exact 𝟙 _
        · change _ = (ℳ.1.presheaf.map _ ≫ _) _
          rw [← ℳ.1.presheaf.map_comp]
          rfl
    erw [eq1, germ_smul_germ, germ_smul_germ, germ_smul_germ]
    rw [sectionSMulSection.smul_add, map_add]
    congr 1
    · fapply sectionSMulSection.germ
      · exact mem_r
      · exact ⟨mem_x, mem_y⟩
      · exact mem_x
      · erw [TopCat.Presheaf.germ_res_apply]
        rfl
    · fapply sectionSMulSection.germ
      · exact mem_r
      · exact ⟨mem_x, mem_y⟩
      · exact mem_y
      · erw [TopCat.Presheaf.germ_res_apply]
        rfl

noncomputable instance Module.stalk_stalk :
    Module (ℛ.presheaf.stalk pt)
      (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) where
  add_smul r s m := by
    obtain ⟨Or, mem_r, r, rfl⟩ := ℛ.presheaf.germ_exist _ r
    obtain ⟨Os, mem_s, s, rfl⟩ := ℛ.presheaf.germ_exist _ s
    obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist (F := ℳ.1.presheaf) _ m
    change stalkSMulStalk _ _ _ _ _ =
      stalkSMulStalk _ _ _ _ _ + stalkSMulStalk _ _ _ _ _
    have eq1 : ℛ.presheaf.germ ⟨pt, mem_r⟩ r + ℛ.presheaf.germ ⟨pt, mem_s⟩ s =
      ℛ.presheaf.germ (⟨pt, ⟨mem_r, mem_s⟩⟩ : (Or ⊓ Os : Opens _))
        (r |_ _ + s |_ _) := by
      rw [map_add]
      erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    rw [eq1]
    erw [germ_smul_germ, germ_smul_germ]
    rw [sectionSMulSection.add_smul, map_add]
    congr 1
    · fapply sectionSMulSection.germ'
      · exact ⟨mem_r, mem_s⟩
      · exact mem
      · exact mem
      · exact mem_r
      · erw [TopCat.Presheaf.germ_res_apply]
      · rfl
    · fapply sectionSMulSection.germ'
      · exact ⟨mem_r, mem_s⟩
      · exact mem
      · apply mem_openSetModule
      · apply mem_openSetRing
      · erw [TopCat.Presheaf.germ_res_apply]
        erw [germ_sectionOnOpenSetRing]
      · erw [germ_sectionOnOpenSetModule]; rfl
  zero_smul m := by
    obtain ⟨W, mem, w, rfl⟩ := TopCat.Presheaf.germ_exist (F := ℳ.1.presheaf) _ m
    change stalkSMulStalk _ _ _ _ _ = 0
    have eq1 : (0 : ℛ.presheaf.stalk pt) = ℛ.presheaf.germ (⟨pt, ⟨⟩⟩ : (⊤ : Opens _)) 0 := by
      rw [map_zero]
    rw [eq1]
    erw [germ_smul_germ]
    rw [sectionSMulSection.zero_smul, map_zero]

end modules

section skyscraper

open Classical

noncomputable def injectiveHullModuleCat : ModuleCat (ℛ.presheaf.stalk pt) :=
  Injective.under <| ModuleCat.of _ (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt)

noncomputable abbrev skyAux : (Opens ℛ)ᵒᵖ ⥤ AddCommGrp :=
skyscraperPresheaf pt (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt)

noncomputable def skyAuxIsoOfMem (U : Opens ℛ) (h : pt ∈ U) :
    (skyAux ℛ ℳ pt).obj (op U) ≅
    (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :=
  eqToIso (by aesop)

noncomputable def skyAuxIsoOfNotMem (U : Opens ℛ) (h : pt ∉ U) :
    (skyAux ℛ ℳ pt).obj (op U) ≅ ⊤_ AddCommGrp.{u} :=
  eqToIso (by aesop)


noncomputable def toSkyAux : ℳ.1.presheaf ⟶ skyAux ℛ ℳ pt where
  app U :=
    if h : pt ∈ U.unop
    then TopCat.Presheaf.germ (F := ℳ.1.presheaf) ⟨pt, h⟩ ≫ (skyAuxIsoOfMem ℛ ℳ pt U.unop h).inv
    else 0
  naturality {U V} i := by
    if hV : pt ∈ V.unop
    then
      have hU : pt ∈ U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, op_unop, skyscraperPresheaf_map]
      rw [dif_pos hV, dif_pos hU, dif_pos hV]
      unfold skyAuxIsoOfMem
      simp only [op_unop, skyscraperPresheaf_obj, eqToIso.inv, Category.assoc, eqToHom_trans]
      rw [← Category.assoc]
      congr 1
      erw [TopCat.Presheaf.germ_res]
    else
      apply IsTerminal.hom_ext
      exact ((if_neg hV).symm.ndrec terminalIsTerminal)


noncomputable instance : Unique (⊤_ AddCommGrp.{u}) := by
  let e : ⊤_ AddCommGrp.{u} ≅ AddCommGrp.of PUnit :=
    terminalIsoIsTerminal (IsTerminal.ofUniqueHom (fun _ => 0) fun X f => by aesop)
  exact Equiv.unique ⟨e.hom, e.inv, Iso.hom_inv_id_apply e, Iso.inv_hom_id_apply e⟩

noncomputable instance skyAux.smul (U : Opens ℛ) :
    SMul (ℛ.presheaf.obj $ op U) ((skyAux ℛ ℳ pt).obj $ op U) where
  smul r x :=
    if h : pt ∈ U
    then (skyAuxIsoOfMem ℛ ℳ pt U h).inv $
      (Module.section_stalk ℛ ℳ pt U h).smul r
        ((skyAuxIsoOfMem ℛ ℳ pt U h).hom x)
    else 0

noncomputable instance skyAux.mulAction (U : Opens ℛ) :
    MulAction  (ℛ.presheaf.obj $ op U) ((skyAux ℛ ℳ pt).obj $ op U) where
  one_smul m := show dite _ _ _ = _ by
    split_ifs with h
    · convert Iso.hom_inv_id_apply (skyAuxIsoOfMem ℛ ℳ pt U h) _
      exact (Module.section_stalk ℛ ℳ _ _ _).one_smul _
    · apply_fun (skyAuxIsoOfNotMem ℛ ℳ pt U h).hom
      · apply Subsingleton.elim
      · exact (ConcreteCategory.bijective_of_isIso (skyAuxIsoOfNotMem ℛ ℳ pt U h).hom).injective
  mul_smul r s m := show dite _ _ _ = dite _ _ _ by
    split_ifs with h1
    · congr 1
      convert (Module.section_stalk ℛ ℳ _ _ _).mul_smul r s ((skyAuxIsoOfMem ℛ ℳ pt U h1).hom m)
      change (skyAuxIsoOfMem ℛ ℳ pt U h1).hom (dite _ _ _) = _
      rw [dif_pos h1]
      exact Iso.inv_hom_id_apply _ _
    · rfl

noncomputable instance skyAux.distribMulAction (U : Opens ℛ) :
    DistribMulAction  (ℛ.presheaf.obj $ op U) ((skyAux ℛ ℳ pt).obj $ op U) where
  smul_zero r := show dite _ _ _ = _ by
    split_ifs with h
    · convert Iso.hom_inv_id_apply (skyAuxIsoOfMem ℛ ℳ pt U h) 0
      rw [map_zero]
      erw [(skyAuxIsoOfMem ℛ ℳ pt U h).hom.map_zero]
      exact (Module.section_stalk ℛ ℳ _ _ _).smul_zero _
    · rfl
  smul_add r x y := show dite _ _ _ = dite _ _ _ + dite _ _ _ by
    split_ifs with h
    · rw [← map_add]
      congr 1
      rw [map_add]
      exact (Module.section_stalk ℛ ℳ _ _ _).smul_add _ _ _
    · rw [add_zero]

noncomputable instance skyAux.module (U : Opens ℛ) :
    Module (ℛ.presheaf.obj $ op U) ((skyAux ℛ ℳ pt).obj $ op U) where
  add_smul r s m := show dite _ _ _ = dite _ _ _ + dite _ _ _ by
    split_ifs with h
    · rw [← map_add]
      congr 1
      exact (Module.section_stalk ℛ ℳ _ _ _).add_smul _ _ _
    · rw [zero_add]
  zero_smul m := show dite _ _ _ = _ by
    split_ifs with h
    · convert Iso.hom_inv_id_apply (skyAuxIsoOfMem ℛ ℳ pt U h) 0
      erw [(skyAuxIsoOfMem ℛ ℳ pt U h).hom.map_zero]
      exact (Module.section_stalk ℛ ℳ _ _ _).zero_smul _
    · rfl

@[simps]
noncomputable def sky : SheafOfModules (forget2Ring ℛ) where
  val :=
  { presheaf := skyAux ℛ ℳ pt
    module := fun U => skyAux.module ℛ ℳ pt U.unop
    map_smul := by
      rintro U V i (r : ℛ.presheaf.obj $ U) (x : (skyAux ℛ ℳ pt).obj $ U)
      if hV : pt ∈ V.unop
      then
        have hU : pt ∈ U.unop := leOfHom i.unop hV
        simp only [skyscraperPresheaf_obj, skyscraperPresheaf_map, dif_pos hV]
        generalize_proofs h
        change (eqToHom h) (dite _ _ _) = dite _ _ _
        rw [dif_pos hU, dif_pos hV]
        simp only [op_unop, skyscraperPresheaf_obj, skyAuxIsoOfMem, eqToIso.inv, eqToIso.hom]
        generalize_proofs h2 h3 h4 h5
        change (eqToHom h2 ≫ eqToHom h) _ = _
        rw [eqToHom_trans]
        congr 1
        change (Module.section_stalk ℛ ℳ _ _ _).smul _ _ =
          (Module.section_stalk ℛ ℳ _ _ _).smul (ℛ.presheaf.map i r)
            ((eqToHom h ≫ eqToHom h5) x)
        change sectionSMulStalk _ _ _ _ _ _ _ = sectionSMulStalk _ _ _ _ _ _ _
        erw [section_res_smul_stalk]
        pick_goal 2
        · exact hU
        congr!
        rw [← eqToHom_trans]
      else
        apply_fun (skyAuxIsoOfNotMem ℛ ℳ pt V.unop hV).hom
        · apply Subsingleton.elim
        · exact (ConcreteCategory.bijective_of_isIso
            (skyAuxIsoOfNotMem ℛ ℳ pt V.unop hV).hom).injective }
  isSheaf := skyscraperPresheaf_isSheaf pt _

noncomputable def toSky : ℳ ⟶ sky ℛ ℳ pt where
  val :=
    { hom := toSkyAux ℛ ℳ pt
      map_smul := fun U (r : ℛ.presheaf.obj U) x => by
        dsimp only [sky_val_presheaf, skyscraperPresheaf_obj, toSkyAux, op_unop, sky_val_module]
        split_ifs with h
        · simp only [AddCommGrp.coe_comp', Function.comp_apply]
          change _ = dite _ _ _
          rw [dif_pos h]
          congr 1
          erw [Iso.inv_hom_id_apply]
          change (TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, h⟩)
            ((ℳ.1.module _).smul _ _) =
            sectionSMulStalk ℛ ℳ pt U.unop _ r ((TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, h⟩) x)
          erw [section_smul_germ]
          delta sectionSMulSection
          erw [← ℳ.1.map_smul]
          erw [TopCat.Presheaf.germ_res_apply]
          rfl
        · apply_fun (skyAuxIsoOfNotMem ℛ ℳ pt U.unop h).hom
          · apply Subsingleton.elim
          · exact (ConcreteCategory.bijective_of_isIso
              (skyAuxIsoOfNotMem ℛ ℳ pt U.unop h).hom).injective }

instance : Injective (sky ℛ ℳ pt) := by
  haveI inst1 : Injective (injectiveHullModuleCat ℛ ℳ pt) := Injective.injective_under _
  haveI inst2 := Injective.injective_of_adjoint
    (adj := stalkSkyscraperSheafAdjunction pt (C := ModuleCat.{u} (ℛ.presheaf.stalk pt)))
    (injectiveHullModuleCat ℛ ℳ pt)
  constructor
  rintro M₁ M₂ g f inst3
  sorry

end skyscraper
