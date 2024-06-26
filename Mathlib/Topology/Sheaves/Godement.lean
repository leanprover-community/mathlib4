import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u v w

variable (R : SheafedSpace.{u + 1, u, u} CommRingCat.{u})

/--
For a comm-ringed space `R`, think `R.sheaf` as a sheaf of (not necessarily commutative) rings.
-/
def forget2Ring :=
  sheafCompose (Opens.grothendieckTopology R) (forget₂ CommRingCat RingCat) |>.obj R.sheaf

/-
R(U) -> stalk of R at pt
(forget2Ring R).val.obj U ⟶ (forget₂ CommRingCat RingCat).obj (TopCat.Presheaf.stalk R.sheaf.val pt)
-/
noncomputable def stalkIsColimit (pt : R) : IsColimit
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
