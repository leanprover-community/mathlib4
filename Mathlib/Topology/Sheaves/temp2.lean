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

noncomputable instance : Unique (⊤_ AddCommGrp.{u}) := by
  let e : ⊤_ AddCommGrp.{u} ≅ AddCommGrp.of PUnit :=
    terminalIsoIsTerminal (IsTerminal.ofUniqueHom (fun _ => 0) fun X f => by aesop)
  exact Equiv.unique ⟨e.hom, e.inv, Iso.hom_inv_id_apply e, Iso.inv_hom_id_apply e⟩

lemma subsingleton__ (M : ModuleCat (ℛ.presheaf.stalk pt)) (W : Opens ℛ) (h : pt ∉ W) :
    Subsingleton ((skyscraperPresheaf pt $ AddCommGrp.of M).obj $ op W) := by
  let e : ((skyscraperPresheaf pt $ AddCommGrp.of M).obj $ op W) ≅ ⊤_ AddCommGrp :=
    eqToIso (by simp only [skyscraperPresheaf_obj, ite_eq_right_iff]; tauto)
  exact Equiv.subsingleton ⟨e.hom, e.inv, e.hom_inv_id_apply, e.inv_hom_id_apply⟩

noncomputable
instance skySMul (M : ModuleCat (ℛ.presheaf.stalk pt)) (U : Opens ℛ) :
    SMul (ℛ.presheaf.obj $ op U) $
      (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) where
  smul r m :=
    if h : pt ∈ U
    then
      let
        e : (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) ≅
            AddCommGrp.of M := eqToIso (by aesop)
      e.inv $ M.3.smul (ℛ.presheaf.germ ⟨pt, h⟩ r) (e.hom m)
    else 0

lemma skyModule.smul_def (M : ModuleCat (ℛ.presheaf.stalk pt)) (U : Opens ℛ)
    (r : (ℛ.presheaf.obj $ op U)) (m : (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U)) :
    r • m =
    if h : pt ∈ U
    then
      let
        e : (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) ≅
            AddCommGrp.of M := eqToIso (by aesop)
      e.inv $ M.3.smul (ℛ.presheaf.germ ⟨pt, h⟩ r) (e.hom m)
    else 0 := rfl

-- set_option maxHeartbeats 1000000 in
noncomputable
instance skyMulAction (M : ModuleCat (ℛ.presheaf.stalk pt)) (U : Opens ℛ) :
    MulAction (ℛ.presheaf.obj $ op U) $
      (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) where
  one_smul m := by
    rw [skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, map_one, eqToIso.hom]
    split_ifs with h
    · generalize_proofs _ _ h1 h2
      apply_fun eqToHom h1.symm
      pick_goal 2
      · exact (ConcreteCategory.bijective_of_isIso (eqToHom h1.symm)).injective
      erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans, eqToHom_refl, id_apply]
      exact M.3.one_smul (eqToHom h2 m)
    · exact (subsingleton__ ℛ _ _ _ h).elim _ _
  mul_smul r s m := by
    rw [skyModule.smul_def, skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, map_mul, eqToIso.hom]
    split_ifs with h
    · congr 1
      convert M.3.mul_smul (ℛ.presheaf.germ ⟨pt, h⟩ r) (ℛ.presheaf.germ ⟨pt, h⟩ s) _
      rw [skyModule.smul_def]
      simp only [AddCommGrp.coe_of, skyscraperPresheaf_obj, eqToIso.inv, eqToIso.hom]
      rw [dif_pos h]
      erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans, eqToHom_refl, id_apply]
      rfl
    · exact (subsingleton__ ℛ _ _ _ h).elim _ _

noncomputable
instance skyDistribMulAction (M : ModuleCat (ℛ.presheaf.stalk pt)) (U : Opens ℛ) :
    DistribMulAction (ℛ.presheaf.obj $ op U) $
      (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) where
  smul_zero r := by
    rw [skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, eqToIso.hom, map_zero,
      dite_eq_right_iff]
    intro h
    convert AddMonoidHom.map_zero _
    convert M.3.smul_zero _
  smul_add r m n := by
    rw [skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, eqToIso.hom, map_add]
    split_ifs with h
    · congr 1
      rw [skyModule.smul_def, skyModule.smul_def]
      simp only [AddCommGrp.coe_of, skyscraperPresheaf_obj, eqToIso.inv, eqToIso.hom]
      rw [dif_pos h, dif_pos h]
      conv_rhs => erw [← map_add]
      congr 1
      convert M.3.smul_add _ _ _
    · exact (subsingleton__ ℛ _ _ _ h).elim _ _

noncomputable
instance skyModule (M : ModuleCat (ℛ.presheaf.stalk pt)) (U : Opens ℛ) :
    Module (ℛ.presheaf.obj $ op U) $
      (skyscraperPresheaf pt $ AddCommGrp.of M).obj (op U) where
  add_smul r s m := by
    rw [skyModule.smul_def, skyModule.smul_def, skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, map_add, eqToIso.hom]
    split_ifs with h
    · conv_rhs => erw [← map_add]
      congr 1
      convert M.3.add_smul _ _ _
    · exact (subsingleton__ ℛ _ _ _ h).elim _ _
  zero_smul m := by
    rw [skyModule.smul_def]
    simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, map_zero, eqToIso.hom,
      dite_eq_right_iff]
    intro h
    convert AddMonoidHom.map_zero _
    convert M.3.zero_smul _


noncomputable def rightObj (M : ModuleCat (ℛ.presheaf.stalk pt)) : SheafOfModules (forget2Ring ℛ) where
val :=
{ presheaf := skyscraperPresheaf pt $ AddCommGrp.of M
  module := fun U => skyModule ℛ pt M U.unop
  map_smul := fun {U V} i r x => by
    simp only [skyscraperPresheaf_obj, skyscraperPresheaf_map]
    split_ifs with hV
    · rw [skyModule.smul_def, skyModule.smul_def]
      simp only [AddCommGrp.coe_of, op_unop, skyscraperPresheaf_obj, eqToIso.inv, eqToIso.hom]
      have hU : pt ∈ U.unop := leOfHom i.unop hV
      rw [dif_pos hV, dif_pos hU]
      erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans]
      congr 1
      congr 1
      · erw [TopCat.Presheaf.germ_res_apply]
      · erw [← CategoryTheory.comp_apply]
        rw [eqToHom_trans]
        rfl
    · exact (subsingleton__ ℛ _ _ _ hV).elim _ _ }
isSheaf := skyscraperPresheaf_isSheaf _ _

@[simps]
noncomputable def rightMap {M N : ModuleCat (ℛ.presheaf.stalk pt)} (l : M ⟶ N) :
    rightObj ℛ pt M ⟶ rightObj ℛ pt N where
  val :=
  { hom := skyscraperPresheafFunctor _ |>.map l.toAddMonoidHom
    map_smul := by
      rintro U (r : ℛ.presheaf.obj U) (x : ((skyscraperPresheaf pt (AddCommGrp.of M)).obj U))

      rw [skyModule.smul_def, skyModule.smul_def]
      simp only [skyscraperPresheaf_obj, skyscraperPresheaf_map, skyscraperPresheafFunctor_map,
        SkyscraperPresheafFunctor.map'_app, AddCommGrp.coe_of, op_unop, eqToIso.inv, eqToIso.hom]

      split_ifs with h
      . erw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply]
        rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        simp only [Category.assoc]
        rw [eqToHom_trans, eqToHom_refl, Category.comp_id]
        rw [CategoryTheory.comp_apply]
        erw [l.map_smul]
        congr
      · exact (subsingleton__ ℛ _ _ _ h).elim _ _ }

lemma rightMap_id (M : ModuleCat (ℛ.presheaf.stalk pt)) :
    rightMap ℛ pt (𝟙 M) = 𝟙 _ := by
  ext U x
  simp only [PresheafOfModules.Hom.app, rightMap_val_hom, skyscraperPresheafFunctor_map,
    SkyscraperPresheafFunctor.map'_app, skyscraperPresheaf_obj, IsTerminal.from_self,
    LinearMap.coe_mk, SheafOfModules.id_val, PresheafOfModules.Hom.id_hom, NatTrans.id_app]
  split_ifs with h
  · change _ = x
    generalize_proofs h1 h2
    suffices eqToHom h1 ≫ _ ≫ eqToHom h2 = 𝟙 _ by
      rw [this]; rfl
    rw [show LinearMap.toAddMonoidHom (𝟙 M) = 𝟙 (AddCommGrp.of M) from rfl,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
  · exact (subsingleton__ ℛ _ _ _ h).elim _ _

lemma rightMap_comp {A B C : ModuleCat (ℛ.presheaf.stalk pt)} (f : A ⟶ B) (g : B ⟶ C) :
    rightMap ℛ pt (f ≫ g) = rightMap ℛ pt f ≫ rightMap ℛ pt g := by
  ext U x
  simp only [PresheafOfModules.Hom.app, rightMap_val_hom, skyscraperPresheafFunctor_map,
    SkyscraperPresheafFunctor.map'_app, skyscraperPresheaf_obj, LinearMap.coe_mk,
    SheafOfModules.comp_val, PresheafOfModules.Hom.comp_hom, NatTrans.comp_app]
  split_ifs with h
  · rw [show LinearMap.toAddMonoidHom (f ≫ g) =
      (AddCommGrp.ofHom f.toAddMonoidHom : (AddCommGrp.of A ⟶ AddCommGrp.of B)) ≫
      (AddCommGrp.ofHom g.toAddMonoidHom : (AddCommGrp.of B ⟶ AddCommGrp.of C)) from rfl]
    conv_rhs => rw [Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rfl
  · exact (subsingleton__ ℛ _ _ _ h).elim _ _

@[simps]
noncomputable def right : ModuleCat (ℛ.presheaf.stalk pt) ⥤ SheafOfModules (forget2Ring ℛ) where
  obj := rightObj ℛ pt
  map := rightMap ℛ pt
  map_id := rightMap_id ℛ pt
  map_comp := rightMap_comp ℛ pt

noncomputable def leftObj (ℳ : SheafOfModules (forget2Ring ℛ)) :
    ModuleCat (ℛ.presheaf.stalk pt) :=
  ModuleCat.of _ $ TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt

@[simps]
noncomputable def leftMap {ℳ 𝒩 : SheafOfModules (forget2Ring ℛ)} (l : ℳ ⟶ 𝒩) :
    leftObj ℛ pt ℳ ⟶ leftObj ℛ pt 𝒩 where
  toFun := TopCat.Presheaf.stalkFunctor (C := AddCommGrp) pt |>.map l.1.1
  map_add' := map_add _
  map_smul' r m := by
    simp only [TopCat.Presheaf.stalkFunctor_obj, RingHom.id_apply]
    obtain ⟨U, memU, m, rfl⟩ := TopCat.Presheaf.germ_exist ℳ.1.presheaf pt m
    obtain ⟨V, memV, r, rfl⟩ := ℛ.presheaf.germ_exist pt r
    change (TopCat.Presheaf.stalkFunctor AddCommGrp pt).map l.val.hom (stalkSMulStalk _ _ _ _ _) =
      stalkSMulStalk _ _ _ _ _
    erw [germ_smul_germ]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply U ⟨pt, memU⟩]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply (V ⊓ U) ⟨pt, ⟨memV, memU⟩⟩]
    delta sectionSMulSection
    erw [l.1.map_smul]
    generalize_proofs _ _ h1 h2
    rw [show (l.val.hom.app { unop := V ⊓ U }) ((ℳ.val.map { unop := homOfLE h2 }) m) =
      𝒩.1.map (op $ homOfLE $ inf_le_right) (l.1.hom.app _ m) by
      erw [← CategoryTheory.comp_apply, l.1.hom.naturality]; rfl]
    change TopCat.Presheaf.germ 𝒩.val.presheaf ⟨pt, _⟩ (sectionSMulSection _ _ _ _ _ _) = _
    erw [germ_smul_germ]
    rfl

lemma leftMap_id (ℳ : SheafOfModules (forget2Ring ℛ)) :
    leftMap ℛ pt (𝟙 ℳ) = 𝟙 _ := by
  ext x
  rw [leftMap_apply]
  simp

lemma leftMap_comp {𝒜 ℬ 𝒞 : SheafOfModules (forget2Ring ℛ)} (f : 𝒜 ⟶ ℬ) (g : ℬ ⟶ 𝒞) :
    leftMap ℛ pt (f ≫ g) = leftMap ℛ pt f ≫ leftMap ℛ pt g := by
  ext x
  rw [leftMap_apply]
  simp only [TopCat.Presheaf.stalkFunctor_obj, SheafOfModules.comp_val,
    PresheafOfModules.Hom.comp_hom, Functor.map_comp, AddCommGrp.coe_comp, Function.comp_apply,
    ModuleCat.coe_comp]
  rw [leftMap_apply, leftMap_apply]
  rfl

@[simps]
noncomputable def left : SheafOfModules (forget2Ring ℛ) ⥤ ModuleCat (ℛ.presheaf.stalk pt) where
  obj := leftObj ℛ pt
  map := leftMap ℛ pt
  map_id := leftMap_id ℛ pt
  map_comp := leftMap_comp ℛ pt

@[simps]
noncomputable def adjHomEquivToFun (ℳ : SheafOfModules (forget2Ring ℛ))
    (N : ModuleCat (ℛ.presheaf.stalk pt))
    (f : leftObj ℛ pt ℳ ⟶ N) : (ℳ ⟶ rightObj ℛ pt N) where
  val :=
    { hom := (skyscraperPresheafStalkAdjunction pt).homEquiv _ _ f.toAddMonoidHom
      map_smul := fun U r x => by
        simp only [TopCat.Presheaf.stalkFunctor_obj, skyscraperPresheafFunctor_obj,
          skyscraperPresheafStalkAdjunction, Equiv.coe_fn_mk,
          StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, skyscraperPresheaf_obj]
        split_ifs with h
        · rw [skyModule.smul_def]
          simp only [AddCommGrp.coe_of, op_unop, skyscraperPresheaf_obj, eqToIso.inv, eqToIso.hom]
          rw [dif_pos h]
          erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]
          congr 1
          change f ((TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, h⟩) _) = _
          have eq : (TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, h⟩) (r • x) =
            sectionSMulStalk ℛ ℳ pt U.unop h r (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, h⟩ x) := by
            rw [section_smul_germ]
            delta sectionSMulSection
            fapply TopCat.Presheaf.germ_ext
            · exact U.unop
            · exact h
            · exact 𝟙 _
            · exact eqToHom (by aesop)
            · erw [ℳ.1.map_smul, ℳ.1.map_smul]
              congr 1
              · change _ = (ℛ.presheaf.map _ ≫ ℛ.presheaf.map _) _
                rw [← ℛ.presheaf.map_comp]
                rfl
              · change _ = (ℳ.1.presheaf.map _ ≫ _) _
                rw [← ℳ.1.presheaf.map_comp]
                rfl
          rw [eq]
          replace eq :
            sectionSMulStalk ℛ ℳ pt U.unop h r (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, h⟩ x) =
            stalkSMulStalk ℛ ℳ pt (ℛ.presheaf.germ ⟨pt, h⟩ r)
              (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, h⟩ x) := by
            rw [germ_smul_germ]
            symm
            fapply sectionSMulSection.germ
            · exact h
            · exact h
            · apply mem_openSetModule
            · rw [germ_sectionOnOpenSetModule]
          rw [eq]
          erw [f.map_smul ((ℛ.presheaf.germ ⟨pt, h⟩) r)
            ((TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, h⟩) x)]
          congr 1
          erw [← CategoryTheory.comp_apply]
          rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          rfl
        · exact (subsingleton__ ℛ _ _ _ h).elim _ _ }

noncomputable def adjHomEquivInvFun (ℳ : SheafOfModules (forget2Ring ℛ))
    (N : ModuleCat (ℛ.presheaf.stalk pt))
    (f : ℳ ⟶ rightObj ℛ pt N) :
    leftObj ℛ pt ℳ ⟶ N where
  toFun := (skyscraperPresheafStalkAdjunction pt).homEquiv _ _ |>.symm f.1.1
  map_add' := map_add _
  map_smul' r m := by
    simp only [TopCat.Presheaf.stalkFunctor_obj, AddCommGrp.coe_of, skyscraperPresheafFunctor_obj,
      skyscraperPresheafStalkAdjunction, Equiv.coe_fn_symm_mk, RingHom.id_apply]
    change (StalkSkyscraperPresheafAdjunctionAuxs.fromStalk pt f.val.hom)
      (stalkSMulStalk _ _ _ _ _) = _
    obtain ⟨U, memU, r, rfl⟩ := ℛ.presheaf.germ_exist pt r
    obtain ⟨V, memV, m, rfl⟩ := TopCat.Presheaf.germ_exist (F := ℳ.val.presheaf) pt m
    erw [germ_smul_germ]
    erw [← CategoryTheory.comp_apply]

    conv_lhs =>
      simp only [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk, TopCat.Presheaf.germ]
      rw [colimit.ι_desc]
    conv_rhs =>
      erw [← CategoryTheory.comp_apply]
      rhs
      simp only [StalkSkyscraperPresheafAdjunctionAuxs.fromStalk, TopCat.Presheaf.germ]
      rw [colimit.ι_desc]
    simp only [AddCommGrp.coe_of, Functor.comp_obj, Functor.op_obj, OpenNhds.inclusion_obj,
      skyscraperPresheaf_obj, Functor.const_obj_obj, comp_apply]
    erw [f.1.map_smul]

    have eq1 :
      (f.val.hom.app { unop := U ⊓ V }) ((ℳ.val.presheaf.map { unop := homOfLE inf_le_right }) m) =
      (rightObj ℛ pt N).1.presheaf.map (op $ homOfLE $ inf_le_right) (f.1.hom.app _ m) := by
      erw [← CategoryTheory.comp_apply, f.1.hom.naturality]; rfl
    erw [eq1]
    simp only [rightObj, skyscraperPresheaf_obj, skyscraperPresheaf_map]
    rw [dif_pos ⟨memU, memV⟩]
    erw [skyModule.smul_def]
    rw [dif_pos ⟨memU, memV⟩]
    simp only [AddCommGrp.coe_of, skyscraperPresheaf_obj, eqToIso.inv, Opens.coe_inf, eqToIso.hom]
    erw [← CategoryTheory.comp_apply]
    rw [eqToHom_trans, eqToHom_refl, id_apply]
    congr 1
    · erw [TopCat.Presheaf.germ_res_apply]
    · erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans]
      rfl

noncomputable def adjHomEquiv
    (ℳ : SheafOfModules (forget2Ring ℛ))
    (N : ModuleCat (ℛ.presheaf.stalk pt)) :
    (leftObj ℛ pt ℳ ⟶ N) ≃ (ℳ ⟶ rightObj ℛ pt N) where
  toFun := adjHomEquivToFun ℛ pt ℳ N
  invFun := adjHomEquivInvFun ℛ pt ℳ N
  left_inv f := by
    ext x
    simp only [adjHomEquivInvFun, TopCat.Presheaf.stalkFunctor_obj, AddCommGrp.coe_of,
      skyscraperPresheafFunctor_obj, adjHomEquivToFun, Equiv.symm_apply_apply,
      LinearMap.toAddMonoidHom_coe]
    rfl
  right_inv f := by
    ext U x
    simp only [PresheafOfModules.Hom.app, adjHomEquivToFun, TopCat.Presheaf.stalkFunctor_obj,
      skyscraperPresheafFunctor_obj, adjHomEquivInvFun, AddCommGrp.coe_of, LinearMap.coe_mk]
    have := (skyscraperPresheafStalkAdjunction pt).homEquiv ℳ.val.presheaf
      (AddCommGrp.of N) |>.right_inv f.1.1
    exact congr(($this).app U x)

noncomputable def adjUnit : 𝟭 (SheafOfModules (forget2Ring ℛ)) ⟶ left ℛ pt ⋙ right ℛ pt where
  app ℳ :=
  { val :=
    { hom := (skyscraperPresheafStalkAdjunction pt).unit.app ℳ.1.1
      map_smul := by
        rintro U (r : ℛ.presheaf.obj U) (x : ℳ.1.presheaf.obj U)
        simp only [Functor.comp_obj, left_obj, right_obj, Functor.id_obj,
          skyscraperPresheafStalkAdjunction, TopCat.Presheaf.stalkFunctor_obj,
          skyscraperPresheafFunctor_obj, StalkSkyscraperPresheafAdjunctionAuxs.unit_app,
          StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, skyscraperPresheaf_obj,
          Category.id_comp]
        split_ifs with hU
        · rw [skyModule.smul_def]
          rw [dif_pos hU]
          erw [CategoryTheory.comp_apply]
          simp only [AddCommGrp.coe_of, op_unop, skyscraperPresheaf_obj, eqToIso.inv, eqToIso.hom]
          congr 1
          change _ = stalkSMulStalk _ _ _ _ _
          erw [← CategoryTheory.comp_apply]
          rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          erw [germ_smul_germ]
          symm
          delta sectionSMulSection
          erw [← ℳ.1.map_smul]
          erw [TopCat.Presheaf.germ_res_apply]
        · exact (subsingleton__ ℛ _ _ _ hU).elim _ _ } }
  naturality {ℳ 𝒩} f := by
    ext U x
    simp only [Functor.comp_obj, left_obj, right_obj, Functor.id_obj, PresheafOfModules.Hom.app,
      Functor.id_map, SheafOfModules.comp_val, PresheafOfModules.Hom.comp_hom, NatTrans.comp_app,
      LinearMap.coe_mk, Functor.comp_map, left_map, right_map, rightMap_val_hom,
      skyscraperPresheafFunctor_map, SkyscraperPresheafFunctor.map'_app, skyscraperPresheaf_obj]
    have := (skyscraperPresheafStalkAdjunction pt).unit.naturality f.1.1
    simp only [Functor.id_obj, Functor.comp_obj, TopCat.Presheaf.stalkFunctor_obj,
      skyscraperPresheafFunctor_obj, Functor.id_map, Functor.comp_map,
      skyscraperPresheafFunctor_map] at this
    convert congr(($this).app U x)

noncomputable def adjCounit : right ℛ pt ⋙ left ℛ pt ⟶ 𝟭 (ModuleCat (ℛ.presheaf.stalk pt)) where
  app M :=
  { toFun := (skyscraperPresheafStalkAdjunction pt).counit.app $ AddCommGrp.of M
    map_add' := map_add _
    map_smul' := by
      rintro r x
      simp only [Functor.id_obj, Functor.comp_obj, skyscraperPresheafFunctor_obj,
        TopCat.Presheaf.stalkFunctor_obj, AddCommGrp.coe_of, skyscraperPresheafStalkAdjunction,
        StalkSkyscraperPresheafAdjunctionAuxs.counit_app, right_obj, left_obj, RingHom.id_apply]
      change (skyscraperPresheafStalkOfSpecializes pt (AddCommGrp.of ↑M) _).hom
        (stalkSMulStalk ℛ (rightObj ℛ pt M) _ _ _) = _
      obtain ⟨U, memU, r, rfl⟩ := ℛ.presheaf.germ_exist pt r
      obtain ⟨V, memV, x, rfl⟩ := TopCat.Presheaf.germ_exist (rightObj ℛ pt M).1.presheaf pt x
      erw [germ_smul_germ]
      erw [← CategoryTheory.comp_apply]
      erw [← CategoryTheory.comp_apply]
      conv_lhs => simp only [skyscraperPresheafStalkOfSpecializes, TopCat.Presheaf.germ]
      conv_rhs => rhs; simp only [skyscraperPresheafStalkOfSpecializes, TopCat.Presheaf.germ]

      rw [colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom]
      simp only [AddCommGrp.coe_of, skyscraperPresheafCoconeOfSpecializes_pt,
        skyscraperPresheafCoconeOfSpecializes_ι_app, Functor.comp_obj, Functor.op_obj,
        OpenNhds.inclusion_obj, skyscraperPresheaf_obj, Functor.const_obj_obj]
      have := skyModule.smul_def ℛ pt M (U ⊓ V) (r |_ (U ⊓ V)) (x |_ (U ⊓ V))
      simp only [skyscraperPresheaf_obj, AddCommGrp.coe_of, eqToIso.inv, Opens.coe_inf,
        eqToIso.hom] at this
      rw [dif_pos ⟨memU, memV⟩] at this
      simp only at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      simp only [Opens.coe_inf, Opens.infLELeft_apply_mk] at this
      apply_fun eqToHom (by rw [if_pos ⟨memU, memV⟩] :
        (if pt ∈ U ⊓ V then AddCommGrp.of M else ⊤_ AddCommGrp) = AddCommGrp.of M) at this
      convert this
      erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans, eqToHom_refl, id_apply]
      congr!
      erw [← CategoryTheory.comp_apply]
      simp only [rightObj, skyscraperPresheaf_obj, skyscraperPresheaf_map, comp_apply]
      rw [dif_pos ⟨memU, memV⟩]
      erw [← CategoryTheory.comp_apply]
      rw [eqToHom_trans] }
  naturality {M N} f := by
    ext x
    have := (skyscraperPresheafStalkAdjunction pt).counit.naturality $ AddCommGrp.ofHom
      f.toAddMonoidHom

    simp only [Functor.comp_obj, skyscraperPresheafFunctor_obj, TopCat.Presheaf.stalkFunctor_obj,
      Functor.id_obj, Functor.comp_map, skyscraperPresheafFunctor_map, Functor.id_map, right_obj,
      left_obj, right_map, left_map, AddCommGrp.coe_of, ModuleCat.coe_comp,
      Function.comp_apply] at this ⊢
    convert congr($this x)

noncomputable def adj : left ℛ pt ⊣ right ℛ pt where
  homEquiv := adjHomEquiv ℛ pt
  unit := adjUnit ℛ pt
  counit := adjCounit ℛ pt
  homEquiv_unit {ℳ N f} := by
    ext U x
    have := (skyscraperPresheafStalkAdjunction pt).homEquiv_unit
      (f := AddCommGrp.ofHom f.toAddMonoidHom)
    simp only [skyscraperPresheafFunctor_obj, TopCat.Presheaf.stalkFunctor_obj,
      whiskeringLeft_obj_obj, colimit.cocone_x, left_obj, Functor.id_obj, Functor.comp_obj,
      skyscraperPresheafFunctor_map, right_obj, right_map, SheafOfModules.comp_val,
      PresheafOfModules.Hom.comp_app, LinearMap.coe_comp, Function.comp_apply] at this ⊢
    exact congr(($this).app U x)

  homEquiv_counit {ℳ N f} := by
    ext x
    have := (skyscraperPresheafStalkAdjunction pt).homEquiv_counit (g := f.1.1)
    simp only [TopCat.Presheaf.stalkFunctor_obj, skyscraperPresheafFunctor_obj, right_obj,
      Functor.id_obj, left_obj, left_map, ModuleCat.coe_comp, Function.comp_apply] at this ⊢
    exact congr($this x)

noncomputable def injectiveHullModuleCat : ModuleCat (ℛ.presheaf.stalk pt) :=
  Injective.under <| ModuleCat.of _ (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt)

noncomputable def toInjectiveHullModuleCat :
    ModuleCat.of _ (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) ⟶
    injectiveHullModuleCat ℛ ℳ pt :=
  Injective.ι _

instance : Mono (toInjectiveHullModuleCat ℛ ℳ pt) := Injective.ι_mono _

noncomputable abbrev skyAux : (Opens ℛ)ᵒᵖ ⥤ AddCommGrp :=
skyscraperPresheaf pt (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt)

noncomputable def skyAuxIsoOfMem (U : Opens ℛ) (h : pt ∈ U) :
    (skyAux ℛ ℳ pt).obj (op U) ≅
    (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :=
  eqToIso (by aesop)

noncomputable def skyAuxIsoOfNotMem (U : Opens ℛ) (h : pt ∉ U) :
    (skyAux ℛ ℳ pt).obj (op U) ≅ ⊤_ AddCommGrp.{u} :=
  eqToIso (by aesop)


@[simps]
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

noncomputable def sky : SheafOfModules (forget2Ring ℛ) :=
  right ℛ pt |>.obj $
    ModuleCat.of _ (TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt)

noncomputable def toSky : ℳ ⟶ sky ℛ ℳ pt where
  val :=
    { hom := toSkyAux ℛ ℳ pt
      map_smul := fun U (r : ℛ.presheaf.obj U) x => by
        dsimp only [sky, right_obj, toSkyAux, skyscraperPresheaf_obj, op_unop]
        split_ifs with h
        · rw [skyModule.smul_def]
          simp only [skyAuxIsoOfMem, op_unop, skyscraperPresheaf_obj, eqToIso.inv,
            AddCommGrp.coe_of, eqToIso.hom]
          rw [dif_pos h]

          erw [CategoryTheory.comp_apply]
          congr 1
          erw [← CategoryTheory.comp_apply]
          rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
          change _ = stalkSMulStalk ℛ ℳ pt _ _
          erw [germ_smul_germ]
          symm
          delta sectionSMulSection
          erw [← ℳ.1.map_smul]
          erw [TopCat.Presheaf.germ_res_apply]
        · aesop
        · exact (smul_zero _).symm }


noncomputable def skies : SheafOfModules $ forget2Ring ℛ :=
  ∏ᶜ fun (pt : ℛ) => (sky ℛ ℳ pt)

noncomputable def toSkies : ℳ ⟶ skies ℛ ℳ :=
  Pi.lift fun pt => toSky ℛ ℳ pt

instance toSkies_mono : Mono (toSkies ℛ ℳ) where
  right_cancellation {𝒩} f g hfg := by
    ext U x
    refine TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf _).obj ℳ) ?_ ?_ ?_ ?_
    intro ⟨y, hy⟩
    have : PresheafOfModules.Hom.app (f ≫ toSkies ℛ ℳ).val U x
        = PresheafOfModules.Hom.app (g ≫ toSkies ℛ ℳ).val U x := by
      rw [hfg]
    apply_fun PresheafOfModules.Hom.app (Pi.π (sky ℛ ℳ) y).val U at this
    simp only [SheafOfModules.comp_val, PresheafOfModules.Hom.comp_app, LinearMap.coe_comp,
      Function.comp_apply, Functor.comp_obj, toSkies,
      ← LinearMap.comp_apply, ← PresheafOfModules.Hom.comp_app] at this
    erw [← LinearMap.comp_apply, ← LinearMap.comp_apply] at this
    simp only [ ← PresheafOfModules.Hom.comp_app, ← SheafOfModules.comp_val,
      Category.assoc, Pi.lift_π] at this
    simp only [sky, right_obj, PresheafOfModules.Hom.app, toSky, toSkyAux, skyscraperPresheaf_obj,
      op_unop, SheafOfModules.comp_val, PresheafOfModules.Hom.comp_hom, NatTrans.comp_app,
      LinearMap.coe_mk] at this
    rw [dif_pos hy] at this
    apply_fun (skyAuxIsoOfMem ℛ ℳ y U.unop hy).inv
    exact this
    · exact (ConcreteCategory.bijective_of_isIso (skyAuxIsoOfMem ℛ ℳ y U.unop hy).inv).1

noncomputable def nextSky : SheafOfModules (forget2Ring ℛ) :=
  (right ℛ pt).obj (injectiveHullModuleCat ℛ ℳ pt)

noncomputable def nextSkies : SheafOfModules (forget2Ring ℛ) := ∏ᶜ fun x => nextSky ℛ ℳ x

noncomputable def skiesToNextSkies : skies ℛ ℳ ⟶ nextSkies ℛ ℳ :=
  Pi.map fun pt => (right ℛ pt).map $ toInjectiveHullModuleCat _ _ _

instance : (left ℛ pt).PreservesMonomorphisms := by
  constructor
  intro ℳ 𝒩 f inst1
  let ℳ' := SheafOfModules.toSheaf (forget2Ring ℛ) |>.obj ℳ
  let 𝒩' := SheafOfModules.toSheaf (forget2Ring ℛ) |>.obj 𝒩
  let f' : ℳ' ⟶ 𝒩' := SheafOfModules.toSheaf (forget2Ring ℛ) |>.map f
  have : Mono f' := inferInstance
  have := TopCat.Presheaf.stalk_mono_of_mono (f := f') pt
  rw [ConcreteCategory.mono_iff_injective_of_preservesPullback] at this ⊢
  intro x y h
  exact @this x y h

instance : (right ℛ pt).IsRightAdjoint := (adj ℛ pt).isRightAdjoint

instance skiesToNextSkiesMono : Mono (skiesToNextSkies ℛ ℳ) := by
  unfold skiesToNextSkies; infer_instance

instance : Injective (nextSky ℛ ℳ pt) := by
  haveI inst1 : Injective (injectiveHullModuleCat ℛ ℳ pt) := Injective.injective_under _
  haveI inst2 : Injective _ :=
    Injective.injective_of_adjoint (adj := adj ℛ pt) (injectiveHullModuleCat ℛ ℳ pt)
  exact inst2

instance : Injective (nextSkies ℛ ℳ) := inferInstanceAs <| Injective $ ∏ᶜ fun _ => _

instance : EnoughInjectives (SheafOfModules (forget2Ring ℛ)) where
  presentation M := Nonempty.intro
    { J := nextSkies ℛ M
      injective := inferInstance
      f := toSkies ℛ M ≫ skiesToNextSkies ℛ M
      mono := inferInstance }

end skyscraper
