/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
  into an adjunction between `freeFunctor` and the evaluation functor at `X`.
  (Alternatively, assuming specific universe parameters, we could show that
  `freeFunctor` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

@[expose] public section

universe u v₁ v₂ u₁ u₂
open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

namespace SheafOfModules

/-- The free sheaf of modules on a certain type `I`. -/
noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) ↦ unit R)

/-- The inclusions `unit R ⟶ free I`. -/
noncomputable def ιFree {I : Type u} (i : I) : unit R ⟶ free I :=
  Sigma.ι (fun (_ : I) ↦ unit R) i

/-- The tautological cofan with point `free I : SheafOfModules R`. -/
noncomputable def freeCofan (I : Type u) : Cofan (fun (_ : I) ↦ unit R) :=
  Cofan.mk (P := free I) ιFree

@[simp]
lemma freeCofan_inj {I : Type u} (i : I) :
    (freeCofan (R := R) I).inj i = ιFree i := rfl

/-- `free I` is the colimit of copies of `unit R` indexed by `I`. -/
noncomputable def isColimitFreeCofan (I : Type u) :
    IsColimit (freeCofan (R := R) I) :=
  coproductIsCoproduct _

set_option backward.isDefEq.respectTransparency false in
/-- The data of a morphism `free I ⟶ M` from a free sheaf of modules is
equivalent to the data of a family `I → M.sections` of sections of `M`. -/
noncomputable def freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} :
    (free I ⟶ M) ≃ (I → M.sections) where
  toFun f i := M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i ↦ M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i ↦ by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]

lemma freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

lemma freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i ↦ sectionsMap p (s i)) :=
  N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

/-- The tautological section of `free I : SheafOfModules R` corresponding to `i : I`. -/
noncomputable abbrev freeSection {I : Type u} (i : I) : (free (R := R) I).sections :=
  (free (R := R) I).freeHomEquiv (𝟙 (free I)) i

lemma freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (i : I) :
    freeHomEquiv M f i = sectionsMap f (freeSection i) :=
  rfl

lemma unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = ιFree i ≫ f := by
  simp [freeHomEquiv]

section

variable {I J : Type u} (f : I → J)

/-- The morphism of presheaves of `R`-modules `free I ⟶ free J` induced by
a map `f : I → J`. -/
noncomputable def freeMap : free (R := R) I ⟶ free J :=
  (freeHomEquiv _).symm (fun i ↦ freeSection (f i))

@[simp]
lemma freeHomEquiv_freeMap :
    (freeHomEquiv _ (freeMap (R := R) f)) = freeSection.comp f :=
  (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]
lemma sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]

lemma sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I → M.sections) (i : I) :
    sectionsMap ((freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

@[reassoc (attr := simp)]
lemma ιFree_freeMap (i : I) :
    ιFree (R := R) i ≫ freeMap f = ιFree (f i) := by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply, freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id]

end

/-- The functor `Type u ⥤ SheafOfModules.{u} R` which sends a type `I` to
`free I` which is a coproduct indexed by `I` of copies of `R` (thought of as a
presheaf of modules over itself). -/
noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R :=
  sigmaConst.obj (unit R)

@[simp]
lemma freeFunctor_obj (X : Type u) :
    (freeFunctor (R := R)).obj X = free X := rfl

@[simp]
lemma freeFunctor_map {X Y : Type u} (f : X ⟶ Y) :
    dsimp% (freeFunctor (R := R)).map f = freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i ↦ (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)

instance : PreservesColimitsOfSize.{v₂, u₂} (freeFunctor (R := R)) :=
  inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))

section

variable (I J : Type u)

/-- A binary coproduct of free sheaves of modules is the free sheaf
of modules on the sum type. -/
noncomputable def freeSumIso : free I ⨿ free J ≅ free (R := R) (I ⊕ J) :=
  IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

@[reassoc (attr := simp)]
lemma inl_freeSumIso_hom :
    coprod.inl ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inl := by
  rw [← dsimp% freeFunctor_map (TypeCat.ofHom (Sum.inl : I → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

@[reassoc (attr := simp)]
lemma inr_freeSumIso_hom :
    coprod.inr ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inr := by
  rw [← dsimp% freeFunctor_map (TypeCat.ofHom (Sum.inr : J → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

end

section

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  (I : Type u) [PreservesColimitsOfShape (Discrete I) F]

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
If `F` preserves coproducts, a morphism `η : F.obj (unit R) ⟶ unit S` induces a morphism
from `F.obj (free I)` to `free (R := S) I`. This is the non-iso version of `mapFreeIso`. -/
noncomputable def mapFree (η : F.obj (unit R) ⟶ unit S) : F.obj (free I) ⟶ free (R := S) I :=
  (isColimitOfPreserves F (isColimitFreeCofan I)).map (freeCofan I) (Discrete.natTrans fun _ ↦ η)

@[reassoc (attr := simp)]
lemma map_ιFree_mapFree (η : F.obj (unit R) ⟶ unit S) (i : I) :
    F.map (ιFree i) ≫ mapFree F I η = η ≫ ιFree i :=
  IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ ↦ η) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFree

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
If `F` preserves coproducts and `F.obj (unit R) ≅ unit S`, then `F` preserves free sheaves of
modules. -/
noncomputable def mapFreeIso (η : F.obj (unit R) ≅ unit S) : F.obj (free I) ≅ free (R := S) I :=
  (isColimitOfPreserves F (isColimitFreeCofan I)).coconePointsIsoOfNatIso
    (isColimitFreeCofan I) (Discrete.natIso fun _ ↦ η)

lemma mapFreeIso_hom (η : F.obj (unit R) ≅ unit S) :
    (mapFreeIso F I η).hom = mapFree F I η.hom := rfl

@[reassoc (attr := simp)]
lemma ιFree_mapFreeIso_inv (η : F.obj (unit R) ≅ unit S) (i : I) :
    ιFree i ≫ (mapFreeIso F I η).inv = η.inv ≫ F.map (ιFree i) :=
  IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ ↦ η.inv) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_inv

end

end SheafOfModules
