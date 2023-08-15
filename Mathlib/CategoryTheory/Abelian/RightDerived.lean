/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import Mathlib.CategoryTheory.Abelian.InjectiveResolution
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Homology
import Mathlib.CategoryTheory.Abelian.Exact

#align_import category_theory.abelian.right_derived from "leanprover-community/mathlib"@"024a4231815538ac739f52d08dd20a55da0d6b23"

/-!
# Right-derived functors

We define the right-derived functors `F.rightDerived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
```
that is, we pick an injective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these right-derived functors can be calculated
on objects using any choice of injective resolution,
and on morphisms by any choice of lift to a cochain map between chosen injective resolutions.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.

## Main results
* `CategoryTheory.Functor.rightDerivedObj_injective_zero`: the `0`-th derived functor of `F` on
  an injective object `X` is isomorphic to `F.obj X`.
* `CategoryTheory.Functor.rightDerivedObj_injective_succ`: injective objects have no higher
  right derived functor.
* `CategoryTheory.NatTrans.rightDerived`: the natural isomorphism between right derived functors
  induced by natural transformation.

Now, we assume `PreservesFiniteLimits F`, then
* `CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono`: if `f` is
  mono and `Exact f g`, then `Exact (F.map f) (F.map g)`.
* `CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf`: if there are enough injectives,
  then there is a natural isomorphism `(F.rightDerived 0) ≅ F`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]

variable [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- The right derived functors of an additive functor. -/
def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.right_derived CategoryTheory.Functor.rightDerived

/-- We can compute a right derived functor using a chosen injective resolution. -/
@[simps!]
def Functor.rightDerivedObjIso (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C}
    (P : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (homologyFunctor D _ n).obj ((F.mapHomologicalComplex _).obj P.cocomplex) :=
  (HomotopyCategory.homologyFunctor D _ n).mapIso
      (HomotopyCategory.isoOfHomotopyEquiv
        (F.mapHomotopyEquiv (InjectiveResolution.homotopyEquiv _ P))) ≪≫
    (HomotopyCategory.homologyFactors D _ n).app _
#align category_theory.functor.right_derived_obj_iso CategoryTheory.Functor.rightDerivedObjIso

/-- The 0-th derived functor of `F` on an injective object `X` is just `F.obj X`. -/
@[simps!]
def Functor.rightDerivedObjInjectiveZero (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    (F.rightDerived 0).obj X ≅ F.obj X :=
  F.rightDerivedObjIso 0 (InjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((CochainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (CochainComplex.homologyFunctor0Single₀ D).app (F.obj X)
#align category_theory.functor.right_derived_obj_injective_zero CategoryTheory.Functor.rightDerivedObjInjectiveZero

open ZeroObject

/-- The higher derived functors vanish on injective objects. -/
@[simps! inv]
def Functor.rightDerivedObjInjectiveSucc (F : C ⥤ D) [F.Additive] (n : ℕ) (X : C) [Injective X] :
    (F.rightDerived (n + 1)).obj X ≅ 0 :=
  F.rightDerivedObjIso (n + 1) (InjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((CochainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (CochainComplex.homologyFunctorSuccSingle₀ D n).app (F.obj X) ≪≫ (Functor.zero_obj _).isoZero
#align category_theory.functor.right_derived_obj_injective_succ CategoryTheory.Functor.rightDerivedObjInjectiveSucc

/-- We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
theorem Functor.rightDerived_map_eq (F : C ⥤ D) [F.Additive] (n : ℕ) {X Y : C} (f : Y ⟶ X)
    {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : Q.cocomplex ⟶ P.cocomplex)
    (w : Q.ι ≫ g = (CochainComplex.single₀ C).map f ≫ P.ι) :
    (F.rightDerived n).map f =
      (F.rightDerivedObjIso n Q).hom ≫
        (homologyFunctor D _ n).map ((F.mapHomologicalComplex _).map g) ≫
          (F.rightDerivedObjIso n P).inv := by
  dsimp only [Functor.rightDerived, Functor.rightDerivedObjIso]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← Functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  apply Functor.mapHomotopy
  apply InjectiveResolution.descHomotopy f
  · simp
  · simp only [InjectiveResolution.homotopyEquiv_hom_ι_assoc]
    rw [← Category.assoc, w, Category.assoc]
    simp only [InjectiveResolution.homotopyEquiv_inv_ι]
#align category_theory.functor.right_derived_map_eq CategoryTheory.Functor.rightDerived_map_eq

/-- The natural transformation between right-derived functors induced by a natural transformation.-/
@[simps!]
def NatTrans.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.rightDerived n ⟶ G.rightDerived n :=
  whiskerLeft (injectiveResolutions C)
    (whiskerRight (NatTrans.mapHomotopyCategory α _) (HomotopyCategory.homologyFunctor D _ n))
#align category_theory.nat_trans.right_derived CategoryTheory.NatTrans.rightDerived

@[simp]
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) := by
  simp [NatTrans.rightDerived]
  rfl
#align category_theory.nat_trans.right_derived_id CategoryTheory.NatTrans.rightDerived_id

@[simp, nolint simpNF]
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [NatTrans.rightDerived]
#align category_theory.nat_trans.right_derived_comp CategoryTheory.NatTrans.rightDerived_comp

/-- A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution.
-/
theorem NatTrans.rightDerived_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) {X : C}
    (P : InjectiveResolution X) :
    (NatTrans.rightDerived α n).app X =
      (F.rightDerivedObjIso n P).hom ≫
        (homologyFunctor D _ n).map ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (G.rightDerivedObjIso n P).inv := by
  symm
  dsimp [NatTrans.rightDerived, Functor.rightDerivedObjIso]
  simp only [Category.comp_id, Category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← Functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  simp only [NatTrans.mapHomologicalComplex_naturality_assoc, ← Functor.map_comp]
  apply Homotopy.compLeftId
  rw [← Functor.map_id]
  apply Functor.mapHomotopy
  apply HomotopyEquiv.homotopyHomInvId
#align category_theory.nat_trans.right_derived_eq CategoryTheory.NatTrans.rightDerived_eq

end CategoryTheory

section

universe w v u

open CategoryTheory.Limits CategoryTheory CategoryTheory.Functor

variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]

variable (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace CategoryTheory.Abelian.Functor

open CategoryTheory.Preadditive

variable [Abelian C] [Abelian D] [Additive F]

/-- If `PreservesFiniteLimits F` and `Mono f`, then `Exact (F.map f) (F.map g)` if
`Exact f g`. -/
theorem preserves_exact_of_preservesFiniteLimits_of_mono [PreservesFiniteLimits F] [Mono f]
    (ex : Exact f g) : Exact (F.map f) (F.map g) :=
  Abelian.exact_of_is_kernel _ _ (by simp [← Functor.map_comp, ex.w]) <|
    Limits.isLimitForkMapOfIsLimit' _ ex.w (Abelian.isLimitOfExactOfMono _ _ ex)
#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono

theorem exact_of_map_injectiveResolution (P : InjectiveResolution X) [PreservesFiniteLimits F] :
    Exact (F.map (P.ι.f 0))
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).dFrom 0) :=
  Preadditive.exact_of_iso_of_exact' (F.map (P.ι.f 0)) (F.map (P.cocomplex.d 0 1)) _ _ (Iso.refl _)
    (Iso.refl _)
    (HomologicalComplex.xNextIso ((F.mapHomologicalComplex _).obj P.cocomplex) rfl).symm (by simp)
    (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, HomologicalComplex.dFrom_eq] <;> congr )
    (preserves_exact_of_preservesFiniteLimits_of_mono _ P.exact₀)
#align category_theory.abelian.functor.exact_of_map_injective_resolution CategoryTheory.Abelian.Functor.exact_of_map_injectiveResolution

/-- Given `P : InjectiveResolution X`, a morphism `(F.rightDerived 0).obj X ⟶ F.obj X` given
`PreservesFiniteLimits F`. -/
def rightDerivedZeroToSelfApp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ⟶ F.obj X :=
  (rightDerivedObjIso F 0 P).hom ≫
    (homologyIsoKernelDesc _ _ _).hom ≫
      kernel.map _ (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).dFrom 0)
      (cokernel.desc _ (𝟙 _) (by simp)) (𝟙 _)
          (by
            -- Porting note: was ext; simp
            ext
            dsimp
            simp) ≫
        -- Porting note: isIso_kernel_lift_of_exact_of_mono is no longer allowed as an
        -- instance for reasons I am not privy to
        have : IsIso <| kernel.lift _ _ (exact_of_map_injectiveResolution F P).w :=
          isIso_kernel_lift_of_exact_of_mono _ _ (exact_of_map_injectiveResolution F P)
        (asIso (kernel.lift _ _ (exact_of_map_injectiveResolution F P).w)).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp

/-- Given `P : InjectiveResolution X`, a morphism `F.obj X ⟶ (F.rightDerived 0).obj X`. -/
def rightDerivedZeroToSelfAppInv [EnoughInjectives C] {X : C} (P : InjectiveResolution X) :
    F.obj X ⟶ (F.rightDerived 0).obj X :=
  homology.lift _ _ _ (F.map (P.ι.f 0) ≫ cokernel.π _)
      (by
        have : (ComplexShape.up ℕ).Rel 0 1 := rfl
        rw [Category.assoc, cokernel.π_desc, HomologicalComplex.dFrom_eq _ this,
          mapHomologicalComplex_obj_d, ← Category.assoc, ← Functor.map_comp]
        simp only [InjectiveResolution.ι_f_zero_comp_complex_d, Functor.map_zero, zero_comp]) ≫
    (rightDerivedObjIso F 0 P).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv

theorem rightDerivedZeroToSelfApp_comp_inv [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    rightDerivedZeroToSelfApp F P ≫ rightDerivedZeroToSelfAppInv F P = 𝟙 _ := by
  dsimp [rightDerivedZeroToSelfApp, rightDerivedZeroToSelfAppInv]
  rw [← Category.assoc, Iso.comp_inv_eq, Category.id_comp, Category.assoc, Category.assoc, ←
    Iso.eq_inv_comp, Iso.inv_hom_id]
  -- Porting note: broken ext
  apply homology.hom_to_ext
  apply homology.hom_from_ext
  rw [Category.assoc, Category.assoc, homology.lift_ι, Category.id_comp]
  erw [homology.π'_ι] -- Porting note: had to insist
  rw [Category.assoc, ← Category.assoc _ _ (cokernel.π _),
    Abelian.kernel.lift.inv, ← Category.assoc,
    ← Category.assoc _ (kernel.ι _), Limits.kernel.lift_ι, Category.assoc, Category.assoc, ←
    Category.assoc (homologyIsoKernelDesc _ _ _).hom _ _, ← homology.ι, ← Category.assoc]
  erw [homology.π'_ι] -- Porting note: had to insist
  rw [Category.assoc, ← Category.assoc (cokernel.π _)]
  erw [cokernel.π_desc] -- Porting note: had to insist
  rw [whisker_eq]
  dsimp; simp -- Porting note: was convert
  apply exact_of_map_injectiveResolution -- Porting note: Abelian.kernel.lift.inv
  -- created an Exact goal which was no longer automatically discharged
#align category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp_comp_inv

theorem rightDerivedZeroToSelfAppInv_comp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    rightDerivedZeroToSelfAppInv F P ≫ rightDerivedZeroToSelfApp F P = 𝟙 _ := by
  dsimp [rightDerivedZeroToSelfApp, rightDerivedZeroToSelfAppInv]
  rw [← Category.assoc _ (F.rightDerivedObjIso 0 P).hom,
    Category.assoc _ _ (F.rightDerivedObjIso 0 P).hom, Iso.inv_hom_id, Category.comp_id, ←
    Category.assoc, ← Category.assoc]
  -- Porting note: this IsIso instance used to be filled automatically
  apply (@IsIso.comp_inv_eq D _ _ _ _ _ ?_ _ _).mpr
  · rw [Category.id_comp]
    ext
    simp only [Limits.kernel.lift_ι_assoc,
      Category.assoc, Limits.kernel.lift_ι, homology.lift]
    rw [← Category.assoc, ← Category.assoc,
      Category.assoc _ _ (homologyIsoKernelDesc _ _ _).hom]
    simp
    -- Porting note: this used to be an instance in ML3
  · apply isIso_kernel_lift_of_exact_of_mono _ _ (exact_of_map_injectiveResolution F P)
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv_comp

/-- Given `P : InjectiveResolution X`, the isomorphism `(F.rightDerived 0).obj X ≅ F.obj X` if
`PreservesFiniteLimits F`. -/
def rightDerivedZeroToSelfAppIso [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ≅ F.obj X where
  hom := rightDerivedZeroToSelfApp _ P
  inv := rightDerivedZeroToSelfAppInv _ P
  hom_inv_id := rightDerivedZeroToSelfApp_comp_inv _ P
  inv_hom_id := rightDerivedZeroToSelfAppInv_comp _ P
#align category_theory.abelian.functor.right_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIso

/-- Given `P : InjectiveResolution X` and `Q : InjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `rightDerivedZeroToSelf_natural`. -/
theorem rightDerivedZeroToSelf_natural [EnoughInjectives C] {X : C} {Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y) :
    F.map f ≫ rightDerivedZeroToSelfAppInv F Q =
      rightDerivedZeroToSelfAppInv F P ≫ (F.rightDerived 0).map f := by
  dsimp [rightDerivedZeroToSelfAppInv]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, ← Category.assoc]
  rw [Iso.comp_inv_eq, rightDerived_map_eq F 0 f (InjectiveResolution.desc f Q P) (by simp),
    Category.assoc, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, ← Category.assoc (F.rightDerivedObjIso 0 P).inv, Iso.inv_hom_id,
    Category.id_comp]
  dsimp only [homologyFunctor_map]
  -- Porting note: broken ext
  apply homology.hom_to_ext
  rw [Category.assoc, homology.lift_ι, Category.assoc]
  erw [homology.map_ι] -- Porting note: need to insist
  rw [←Category.assoc (homology.lift _ _ _ _ _) _ _]
  erw [homology.lift_ι] -- Porting note: need to insist
  rw [Category.assoc]
  erw [cokernel.π_desc] -- Porting note: need to insist
  rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc,
    HomologicalComplex.Hom.sqFrom_left, mapHomologicalComplex_map_f, ← Functor.map_comp,
    show f ≫ Q.ι.f 0 = P.ι.f 0 ≫ (InjectiveResolution.desc f Q P).f 0 from
      HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes f Q P).symm 0]
  rfl -- Porting note: extra rfl
#align category_theory.abelian.functor.right_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.rightDerivedZeroToSelf_natural

/-- Given `PreservesFiniteLimits F`, the natural isomorphism `(F.rightDerived 0) ≅ F`. -/
def rightDerivedZeroIsoSelf [EnoughInjectives C] [PreservesFiniteLimits F] : F.rightDerived 0 ≅ F :=
  Iso.symm <|
    NatIso.ofComponents
      (fun X => (rightDerivedZeroToSelfAppIso _ (InjectiveResolution.of X)).symm) fun _ =>
      rightDerivedZeroToSelf_natural _ _ _ _
#align category_theory.abelian.functor.right_derived_zero_iso_self CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf

end CategoryTheory.Abelian.Functor
