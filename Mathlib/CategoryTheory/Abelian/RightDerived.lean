/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison

! This file was ported from Lean 3 source module category_theory.abelian.right_derived
! leanprover-community/mathlib commit 024a4231815538ac739f52d08dd20a55da0d6b23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Abelian.InjectiveResolution
import Mathbin.Algebra.Homology.Additive
import Mathbin.CategoryTheory.Limits.Constructions.EpiMono
import Mathbin.CategoryTheory.Abelian.Homology
import Mathbin.CategoryTheory.Abelian.Exact

/-!
# Right-derived functors

We define the right-derived functors `F.right_derived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
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
* `category_theory.functor.right_derived_obj_injective_zero`: the `0`-th derived functor of `F` on
  an injective object `X` is isomorphic to `F.obj X`.
* `category_theory.functor.right_derived_obj_injective_succ`: injective objects have no higher
  right derived functor.
* `category_theory.nat_trans.right_derived`: the natural isomorphism between right derived functors
  induced by natural transformation.

Now, we assume `preserves_finite_limits F`, then
* `category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono`: if `f` is
  mono and `exact f g`, then `exact (F.map f) (F.map g)`.
* `category_theory.abelian.functor.right_derived_zero_iso_self`: if there are enough injectives,
  then there is a natural isomorphism `(F.right_derived 0) ≅ F`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {D : Type _} [Category D]

variable [Abelian C] [HasInjectiveResolutions C] [Abelian D]

/-- The right derived functors of an additive functor. -/
def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n
#align category_theory.functor.right_derived CategoryTheory.Functor.rightDerived

/-- We can compute a right derived functor using a chosen injective resolution. -/
@[simps]
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
@[simps]
def Functor.rightDerivedObjInjectiveZero (F : C ⥤ D) [F.Additive] (X : C) [Injective X] :
    (F.rightDerived 0).obj X ≅ F.obj X :=
  F.rightDerivedObjIso 0 (InjectiveResolution.self X) ≪≫
    (homologyFunctor _ _ _).mapIso ((CochainComplex.single₀MapHomologicalComplex F).app X) ≪≫
      (CochainComplex.homologyFunctor0Single₀ D).app (F.obj X)
#align category_theory.functor.right_derived_obj_injective_zero CategoryTheory.Functor.rightDerivedObjInjectiveZero

open ZeroObject

/-- The higher derived functors vanish on injective objects. -/
@[simps inv]
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
      (F.rightDerivedObjIso n Q).Hom ≫
        (homologyFunctor D _ n).map ((F.mapHomologicalComplex _).map g) ≫
          (F.rightDerivedObjIso n P).inv :=
  by
  dsimp only [functor.right_derived, functor.right_derived_obj_iso]
  dsimp; simp only [category.comp_id, category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  apply functor.map_homotopy
  apply Homotopy.trans
  exact HomotopyCategory.homotopyOutMap _
  apply InjectiveResolution.desc_homotopy f
  · simp
  · simp only [InjectiveResolution.homotopy_equiv_hom_ι_assoc]
    rw [← category.assoc, w, category.assoc]
    simp only [InjectiveResolution.homotopy_equiv_inv_ι]
#align category_theory.functor.right_derived_map_eq CategoryTheory.Functor.rightDerived_map_eq

/-- The natural transformation between right-derived functors induced by a natural transformation.-/
@[simps]
def NatTrans.rightDerived {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) :
    F.rightDerived n ⟶ G.rightDerived n :=
  whiskerLeft (injectiveResolutions C)
    (whiskerRight (NatTrans.mapHomotopyCategory α _) (HomotopyCategory.homologyFunctor D _ n))
#align category_theory.nat_trans.right_derived CategoryTheory.NatTrans.rightDerived

@[simp]
theorem NatTrans.rightDerived_id (F : C ⥤ D) [F.Additive] (n : ℕ) :
    NatTrans.rightDerived (𝟙 F) n = 𝟙 (F.rightDerived n) :=
  by
  simp [nat_trans.right_derived]
  rfl
#align category_theory.nat_trans.right_derived_id CategoryTheory.NatTrans.rightDerived_id

@[simp, nolint simp_nf]
theorem NatTrans.rightDerived_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
    NatTrans.rightDerived (α ≫ β) n = NatTrans.rightDerived α n ≫ NatTrans.rightDerived β n := by
  simp [nat_trans.right_derived]
#align category_theory.nat_trans.right_derived_comp CategoryTheory.NatTrans.rightDerived_comp

/-- A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution.
-/
theorem NatTrans.rightDerived_eq {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) (n : ℕ) {X : C}
    (P : InjectiveResolution X) :
    (NatTrans.rightDerived α n).app X =
      (F.rightDerivedObjIso n P).Hom ≫
        (homologyFunctor D _ n).map ((NatTrans.mapHomologicalComplex α _).app P.cocomplex) ≫
          (G.rightDerivedObjIso n P).inv :=
  by
  symm
  dsimp [nat_trans.right_derived, functor.right_derived_obj_iso]
  simp only [category.comp_id, category.id_comp]
  rw [← homologyFunctor_map, HomotopyCategory.homologyFunctor_map_factors]
  simp only [← functor.map_comp]
  congr 1
  apply HomotopyCategory.eq_of_homotopy
  simp only [nat_trans.map_homological_complex_naturality_assoc, ← functor.map_comp]
  apply Homotopy.compLeftId
  rw [← Functor.map_id]
  apply functor.map_homotopy
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

/-- If `preserves_finite_limits F` and `mono f`, then `exact (F.map f) (F.map g)` if
`exact f g`. -/
theorem preserves_exact_of_preservesFiniteLimits_of_mono [PreservesFiniteLimits F] [Mono f]
    (ex : Exact f g) : Exact (F.map f) (F.map g) :=
  Abelian.exact_of_is_kernel _ _ (by simp [← functor.map_comp, ex.w]) <|
    Limits.isLimitForkMapOfIsLimit' _ ex.w (Abelian.isLimitOfExactOfMono _ _ ex)
#align category_theory.abelian.functor.preserves_exact_of_preserves_finite_limits_of_mono CategoryTheory.Abelian.Functor.preserves_exact_of_preservesFiniteLimits_of_mono

theorem exact_of_map_injective_resolution (P : InjectiveResolution X) [PreservesFiniteLimits F] :
    Exact (F.map (P.ι.f 0))
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex).dFrom 0) :=
  Preadditive.exact_of_iso_of_exact' (F.map (P.ι.f 0)) (F.map (P.cocomplex.d 0 1)) _ _ (Iso.refl _)
    (Iso.refl _)
    (HomologicalComplex.xNextIso ((F.mapHomologicalComplex _).obj P.cocomplex) rfl).symm (by simp)
    (by rw [iso.refl_hom, category.id_comp, iso.symm_hom, HomologicalComplex.dFrom_eq] <;> congr )
    (preserves_exact_of_preserves_finite_limits_of_mono _ P.exact₀)
#align category_theory.abelian.functor.exact_of_map_injective_resolution CategoryTheory.Abelian.Functor.exact_of_map_injective_resolution

/-- Given `P : InjectiveResolution X`, a morphism `(F.right_derived 0).obj X ⟶ F.obj X` given
`preserves_finite_limits F`. -/
def rightDerivedZeroToSelfApp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ⟶ F.obj X :=
  (rightDerivedObjIso F 0 P).Hom ≫
    (homologyIsoKernelDesc _ _ _).Hom ≫
      kernel.map _ _ (cokernel.desc _ (𝟙 _) (by simp)) (𝟙 _)
          (by
            ext
            simp) ≫
        (asIso (kernel.lift _ _ (exact_of_map_injective_resolution F P).w)).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp

/-- Given `P : InjectiveResolution X`, a morphism `F.obj X ⟶ (F.right_derived 0).obj X`. -/
def rightDerivedZeroToSelfAppInv [EnoughInjectives C] {X : C} (P : InjectiveResolution X) :
    F.obj X ⟶ (F.rightDerived 0).obj X :=
  homology.lift _ _ _ (F.map (P.ι.f 0) ≫ cokernel.π _)
      (by
        have : (ComplexShape.up ℕ).Rel 0 1 := rfl
        rw [category.assoc, cokernel.π_desc, HomologicalComplex.dFrom_eq _ this,
          map_homological_complex_obj_d, ← category.assoc, ← functor.map_comp]
        simp only [InjectiveResolution.ι_f_zero_comp_complex_d, functor.map_zero, zero_comp]) ≫
    (rightDerivedObjIso F 0 P).inv
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv

theorem rightDerivedZeroToSelfApp_comp_inv [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    right_derived_zero_to_self_app F P ≫ right_derived_zero_to_self_app_inv F P = 𝟙 _ :=
  by
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv]
  rw [← category.assoc, iso.comp_inv_eq, category.id_comp, category.assoc, category.assoc, ←
    iso.eq_inv_comp, iso.inv_hom_id]
  ext
  rw [category.assoc, category.assoc, homology.lift_ι, category.id_comp, homology.π'_ι,
    category.assoc, ← category.assoc _ _ (cokernel.π _), abelian.kernel.lift.inv, ← category.assoc,
    ← category.assoc _ (kernel.ι _), limits.kernel.lift_ι, category.assoc, category.assoc, ←
    category.assoc (homologyIsoKernelDesc _ _ _).Hom _ _, ← homology.ι, ← category.assoc,
    homology.π'_ι, category.assoc, ← category.assoc (cokernel.π _), cokernel.π_desc, whisker_eq]
  convert category.id_comp (cokernel.π _)
#align category_theory.abelian.functor.right_derived_zero_to_self_app_comp_inv CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfApp_comp_inv

theorem rightDerivedZeroToSelfAppInv_comp [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) :
    right_derived_zero_to_self_app_inv F P ≫ right_derived_zero_to_self_app F P = 𝟙 _ :=
  by
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv]
  rw [← category.assoc _ (F.right_derived_obj_iso 0 P).Hom,
    category.assoc _ _ (F.right_derived_obj_iso 0 P).Hom, iso.inv_hom_id, category.comp_id, ←
    category.assoc, ← category.assoc, is_iso.comp_inv_eq, category.id_comp]
  ext
  simp only [limits.kernel.lift_ι_assoc, category.assoc, limits.kernel.lift_ι, homology.lift]
  rw [← category.assoc, ← category.assoc, category.assoc _ _ (homologyIsoKernelDesc _ _ _).Hom]
  simp
#align category_theory.abelian.functor.right_derived_zero_to_self_app_inv_comp CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppInv_comp

/-- Given `P : InjectiveResolution X`, the isomorphism `(F.right_derived 0).obj X ≅ F.obj X` if
`preserves_finite_limits F`. -/
def rightDerivedZeroToSelfAppIso [EnoughInjectives C] [PreservesFiniteLimits F] {X : C}
    (P : InjectiveResolution X) : (F.rightDerived 0).obj X ≅ F.obj X
    where
  Hom := right_derived_zero_to_self_app _ P
  inv := right_derived_zero_to_self_app_inv _ P
  hom_inv_id' := right_derived_zero_to_self_app_comp_inv _ P
  inv_hom_id' := right_derived_zero_to_self_app_inv_comp _ P
#align category_theory.abelian.functor.right_derived_zero_to_self_app_iso CategoryTheory.Abelian.Functor.rightDerivedZeroToSelfAppIso

/-- Given `P : InjectiveResolution X` and `Q : InjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `right_derived_zero_to_self_natural`. -/
theorem rightDerived_zero_to_self_natural [EnoughInjectives C] {X : C} {Y : C} (f : X ⟶ Y)
    (P : InjectiveResolution X) (Q : InjectiveResolution Y) :
    F.map f ≫ right_derived_zero_to_self_app_inv F Q =
      right_derived_zero_to_self_app_inv F P ≫ (F.rightDerived 0).map f :=
  by
  dsimp [right_derived_zero_to_self_app_inv]
  simp only [CategoryTheory.Functor.map_id, category.id_comp, ← category.assoc]
  rw [iso.comp_inv_eq, right_derived_map_eq F 0 f (InjectiveResolution.desc f Q P) (by simp),
    category.assoc, category.assoc, category.assoc, category.assoc, iso.inv_hom_id,
    category.comp_id, ← category.assoc (F.right_derived_obj_iso 0 P).inv, iso.inv_hom_id,
    category.id_comp]
  dsimp only [homologyFunctor_map]
  ext
  rw [category.assoc, homology.lift_ι, category.assoc, homology.map_ι, ←
    category.assoc (homology.lift _ _ _ _ _) _ _, homology.lift_ι, category.assoc, cokernel.π_desc,
    ← category.assoc, ← functor.map_comp, ← category.assoc, HomologicalComplex.Hom.sqFrom_left,
    map_homological_complex_map_f, ← functor.map_comp,
    show f ≫ Q.ι.f 0 = P.ι.f 0 ≫ (InjectiveResolution.desc f Q P).f 0 from
      HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes f Q P).symm 0]
#align category_theory.abelian.functor.right_derived_zero_to_self_natural CategoryTheory.Abelian.Functor.rightDerived_zero_to_self_natural

/-- Given `preserves_finite_limits F`, the natural isomorphism `(F.right_derived 0) ≅ F`. -/
def rightDerivedZeroIsoSelf [EnoughInjectives C] [PreservesFiniteLimits F] : F.rightDerived 0 ≅ F :=
  Iso.symm <|
    NatIso.ofComponents
      (fun X => (right_derived_zero_to_self_app_iso _ (InjectiveResolution.of X)).symm) fun X Y f =>
      right_derived_zero_to_self_natural _ _ _ _
#align category_theory.abelian.functor.right_derived_zero_iso_self CategoryTheory.Abelian.Functor.rightDerivedZeroIsoSelf

end CategoryTheory.Abelian.Functor

end

