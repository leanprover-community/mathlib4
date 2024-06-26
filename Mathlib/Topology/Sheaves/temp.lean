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
variable (pt : ℛ) (U V : Opens ℛ) (pt_mem : pt ∈ U) (pt_mem' : pt ∈ V)

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
  sorry



noncomputable def openSet (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    Opens ℛ :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose

lemma mem_openSet (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    pt ∈ openSet ℛ ℳ pt x := (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose

noncomputable def sectionOnOpenSet (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    ℳ.1.obj (op $ openSet ℛ ℳ pt x) :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose_spec.choose

lemma germ_sectionOnOpenSet (x : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
    TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, mem_openSet ℛ ℳ pt x⟩
      (sectionOnOpenSet ℛ ℳ pt x) = x :=
  (TopCat.Presheaf.germ_exist ℳ.1.presheaf pt x).choose_spec.choose_spec.choose_spec

noncomputable def sectionSMulStalk
    (x : (ℛ.presheaf.obj $ op U))
    (y : TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) :
  TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt :=
    @TopCat.Presheaf.germ (F := ℳ.1.presheaf) _ _
      (U := U ⊓ openSet ℛ ℳ pt y)
      ⟨pt, ⟨pt_mem, mem_openSet _ _ _ _⟩⟩ $
        sectionSMulSection ℛ ℳ U _ x (sectionOnOpenSet ℛ ℳ pt y)

set_option maxHeartbeats 800000 in
lemma section_smul_germ (r : ℛ.presheaf.obj $ op U) (m : ℳ.1.obj $ op V) :
    (sectionSMulStalk ℛ ℳ pt U pt_mem r
      (TopCat.Presheaf.germ ℳ.1.presheaf ⟨pt, pt_mem'⟩ m)) =
    (TopCat.Presheaf.germ ℳ.1.presheaf (⟨pt, ⟨pt_mem, pt_mem'⟩⟩ : (U ⊓ V : Opens ℛ))
      (sectionSMulSection ℛ ℳ U V r m) :
        TopCat.Presheaf.stalk.{u} (C := AddCommGrp) ℳ.1.presheaf pt) := by
  dsimp [sectionSMulStalk, sectionSMulSection]


  fapply TopCat.Presheaf.germ_ext.{u} (C := AddCommGrp) (X := ℛ.carrier) ℳ.1.presheaf
    (W := U ⊓ V ⊓ openSet ℛ ℳ pt (TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, pt_mem'⟩ m))
  · refine ⟨⟨pt_mem, pt_mem'⟩, mem_openSet _ _ _ _⟩
  · refine homOfLE fun x hx => ⟨hx.1.1, hx.2⟩
  · refine homOfLE fun x hx => ⟨hx.1.1, hx.1.2⟩
  erw [ℳ.1.map_smul, ℳ.1.map_smul]
  have := germ_sectionOnOpenSet ℛ ℳ pt ((TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, pt_mem'⟩) m)
  erw [TopCat.Presheaf.germ_res_apply]

    -- (iWV := homOfLE $ inf_le_left)
  --   (iWU := homOfLE $
  --     by rw [inf_assoc, inf_comm V, ← inf_assoc]; exact inf_le_left (α := Opens ℛ))
  -- · exact ⟨⟨pt_mem, pt_mem'⟩, mem_openSet _ _ _ _⟩
  -- · erw [sectionSMulSection.restrict]
  --   pick_goal 2
  --   · exact homOfLE (inf_le_left)
  --   pick_goal 2
  --   · exact 𝟙 _
  --   erw [ℳ.1.map_smul]
  --   change (ℳ.1.module _).smul _ _ = (ℳ.1.module _).smul _ _
  --   congr 1
  --   -- change (ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _) _ = (ℳ.1.presheaf.map _ ≫ ℳ.1.presheaf.map _) _
  --   -- rw [← ℳ.1.presheaf.map_comp]
  --   -- simp? [-Functor.map_comp, AddCommGrp.coe_comp', Function.comp_apply]

  --   -- generalize_proofs h1 h2 h3 h4 h5 h6
  --   -- have H := sectionSMulStalk.proof_1 ℛ ℳ pt ((TopCat.Presheaf.germ ℳ.val.presheaf ⟨pt, pt_mem'⟩) m)
  --   -- have := sectionSMulSection.restrict ℛ ℳ (U ⊓ V) H.choose
  --   -- erw [sectionSMulSection.restrict]
  --   -- pick_goal 2
  --   -- · exact homOfLE (inf_le_left)
  --   -- pick_goal 2
  --   -- ·
  --   -- simp only [sectionSMulSection]
  --   -- generalize_proofs h1 h2 h3 h4
  --   -- -- erw [ℳ.1.map_smul, ℳ.1.map_smul]
  --   sorry

end modules
#exit
/-
R(U) -> stalk of R at pt
(forget2Ring R).val.obj U ⟶ (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk R.sheaf.val pt)
-/
noncomputable def stalkIsColimit (pt : ℛ) : IsColimit
  (F := ((OpenNhds.inclusion pt).op ⋙ R.sheaf.1) ⋙ forget₂ CommRingCat RingCat)
  ((forget₂ CommRingCat RingCat).mapCocone $ colimit.cocone _) :=

  letI := @CommRingCat.FilteredColimits.forget₂RingPreservesFilteredColimits.{u}
  letI := this.1 (J := (OpenNhds pt)ᵒᵖ)
  PreservesColimit.preserves $
    colimit.isColimit ((OpenNhds.inclusion pt).op ⋙ R.sheaf.val)

/--
M| U -> M| U
-/
noncomputable def sectionSMul (pt : R) (U : (OpenNhds pt)ᵒᵖ) (M : SheafOfModules $ forget2Ring R)
    (s : R.presheaf.obj $ (OpenNhds.inclusion pt).op.obj U) : -- R(U)
    End (TopCat.Presheaf.stalkFunctor AddCommGrp pt |>.obj M.1.1) :=
  let e := TopCat.Presheaf.stalkPullbackIso (AddCommGrp)
    (f := (((OpenNhds.inclusion pt).obj U.unop).inclusion : (TopCat.of U.unop.1) ⟶ R.carrier))
    M.val.1 ⟨pt, U.unop.2⟩
  e.hom ≫
    (TopCat.Presheaf.stalkFunctor _ _).map
    { app := fun V => (TopCat.Presheaf.pullbackObjObjOfImageOpen
        (((OpenNhds.inclusion pt).obj U.unop).inclusion : (TopCat.of U.unop.1) ⟶ R.carrier)
          M.1.presheaf V.unop sorry).hom ≫
          { toFun := fun x => (M.1.module _).smul (R.presheaf.map (Opposite.op $ homOfLE $ sorry) s) x
            map_zero' := by
              simp only [Opens.coe_inclusion, Functor.op_obj]
              exact smul_zero _
            map_add' := by
              intros
              simp only [Opens.coe_inclusion, Functor.op_obj]
              exact smul_add _ _ _ } ≫
        (TopCat.Presheaf.pullbackObjObjOfImageOpen
          (((OpenNhds.inclusion pt).obj U.unop).inclusion : (TopCat.of U.unop.1) ⟶ R.carrier)
            M.1.presheaf V.unop sorry).inv
      naturality := fun V₁ V₂ i => by sorry }

    ≫ e.inv

noncomputable def stalkSMul (pt : R) (M : SheafOfModules $ forget2Ring R) :
  (forget₂ CommRingCat RingCat).obj ((TopCat.Presheaf.stalkFunctor CommRingCat pt).obj R.sheaf.1) ⟶
  RingCat.of (End (TopCat.Presheaf.stalkFunctor AddCommGrp pt |>.obj M.1.1)) :=
  (stalkIsColimit R pt).desc
    ⟨RingCat.of (End (TopCat.Presheaf.stalkFunctor AddCommGrp pt |>.obj M.1.1)),
    { app := fun U => {
      toFun := fun s => sectionSMul R pt U M s
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
    }
      naturality := sorry }⟩

/--
R -> End(M)

R -> M -> M
R × M -> M stalkFunctor.map
-/
noncomputable instance stalkModule (pt : R) (M : SheafOfModules $ forget2Ring R) : -- M is sheaf of modules over R
  Module ((TopCat.Presheaf.stalkFunctor CommRingCat pt).obj R.sheaf.1) -- stalk of R at x
    (TopCat.Presheaf.stalkFunctor (AddCommGrp) pt |>.obj M.1.1) -- stalk of M at x
    where
  smul x := (stalkSMul R pt M x).toFun
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

noncomputable def stalkInjectiveHull (pt : R) (M : SheafOfModules $ forget2Ring R) :
  ModuleCat ((TopCat.Presheaf.stalkFunctor CommRingCat pt).obj R.sheaf.1) :=
  let inst1 := EnoughInjectives.{u} (ModuleCat ((TopCat.Presheaf.stalkFunctor CommRingCat pt).obj R.sheaf.1))
  Injective.under (ModuleCat.of ((TopCat.Presheaf.stalkFunctor CommRingCat pt).obj R.sheaf.1)
    ((TopCat.Presheaf.stalkFunctor (AddCommGrp) pt |>.obj M.1.1)))

noncomputable def sectionModule (V : (Opens R)ᵒᵖ) (pt : R) (h : pt ∈ V.unop) (M : SheafOfModules $ forget2Ring R) :
    Module (R.presheaf.obj V) (stalkInjectiveHull R pt M) :=
    Module.compHom (stalkInjectiveHull R pt M)
      (R.presheaf.germ ⟨pt, h⟩ : R.presheaf.obj V ⟶ R.presheaf.stalk pt)

open Classical

instance : Unique (⊤_ AddCommGrp) := sorry

noncomputable instance (R : Type*) [Ring R] : Module R (⊤_ AddCommGrp) where
  smul := 0
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

noncomputable def sky (pt : R) (M : SheafOfModules $ forget2Ring R)  : SheafOfModules (forget2Ring R) where
  val :=
  { presheaf := skyscraperPresheaf pt $ AddCommGrp.of (stalkInjectiveHull R pt M)
    module := fun V =>
      if h : pt ∈ V.unop
      then
        let e : (skyscraperPresheaf pt (AddCommGrp.of (stalkInjectiveHull R pt M))).obj V ≅
          AddCommGrp.of (stalkInjectiveHull R pt M) := eqToIso (by
            simp only [skyscraperPresheaf, TopCat.Presheaf.stalkFunctor_obj, ite_eq_left_iff]
            tauto)
        letI m1 : Module (R.presheaf.obj V) ↑(AddCommGrp.of ↑(stalkInjectiveHull R pt M)) :=
          sectionModule R V pt h M
        letI :  SMul (R.presheaf.obj V)
            ((skyscraperPresheaf pt (AddCommGrp.of ↑(stalkInjectiveHull R pt M))).obj V) :=
          ⟨fun x y => e.inv $ x • e.hom y⟩
        Function.Injective.module (R.presheaf.obj V) (f := e.hom) (sorry) fun x y => by
          change e.hom (e.inv _) = _
          simp only [TopCat.Presheaf.stalkFunctor_obj, AddCommGrp.coe_of, skyscraperPresheaf_obj]
          change (e.inv ≫ e.hom) _ = _
          simp
      else
        let e : (skyscraperPresheaf pt (AddCommGrp.of (stalkInjectiveHull R pt M))).obj V ≅ ⊤_ AddCommGrp :=
          eqToIso (by
            simp only [skyscraperPresheaf, TopCat.Presheaf.stalkFunctor_obj, ite_eq_right_iff]
            tauto)
        letI :  SMul (R.presheaf.obj V)
            ((skyscraperPresheaf pt (AddCommGrp.of ↑(stalkInjectiveHull R pt M))).obj V) :=
          ⟨fun x y => 0⟩
        Function.Injective.module (R.presheaf.obj V) (f := e.hom) (sorry) fun x y => by
          simp only [TopCat.Presheaf.stalkFunctor_obj, skyscraperPresheaf_obj]
          change e.hom 0 = 0
          rw [map_zero]
    map_smul := sorry }
  isSheaf := skyscraperPresheaf_isSheaf _ _

-- Use adjunction between skyscraper and stalk
instance  (pt : R) (M : SheafOfModules $ forget2Ring R) : Injective (sky R pt M) := by
  have := stalkSkyscraperSheafAdjunction pt (C := CommRingCat)
  have := Injective.injective_of_adjoint (adj := stalkSkyscraperSheafAdjunction pt (C := CommRingCat))
  sorry


def toSky (pt : R) (M : SheafOfModules $ forget2Ring R) : M ⟶ sky R pt M := sorry

noncomputable def J (M : SheafOfModules $ forget2Ring R) : SheafOfModules $ forget2Ring R :=
  ∏ᶜ fun (pt : R) => (sky R pt M)

noncomputable def toJ (M : SheafOfModules $ forget2Ring R) : M ⟶ J R M :=
  Pi.lift fun pt => toSky R pt M

instance toJ_injective (M : SheafOfModules $ forget2Ring R) : Injective (J R M) :=
  inferInstanceAs $ Injective $ piObj _

instance toJ_mono (M : SheafOfModules $ forget2Ring R)  : Mono (toJ R M) := sorry

instance :
    EnoughInjectives
      (SheafOfModules $ forget2Ring R) where
  presentation M := Nonempty.intro
    { J := J R M
      injective := inferInstance
      f := toJ R M
      mono := inferInstance }
