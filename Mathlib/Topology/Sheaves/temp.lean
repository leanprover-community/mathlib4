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
