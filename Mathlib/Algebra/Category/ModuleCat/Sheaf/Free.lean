/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

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
@[simps]
noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R where
  obj := free
  map f := freeMap f
  map_id X := (freeHomEquiv _).injective (by ext1 i; simp)
  map_comp {I J K} f g := (freeHomEquiv _).injective (by ext1; simp [freeHomEquiv_comp_apply])

section

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  (η : F.obj (unit R) ≅ unit S) (I : Type u) (i : I)
  [PreservesColimitsOfShape (Discrete I) F]

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
If `F` preserves coproducts and `F.obj (unit R) ≅ unit S`, then `F` preserves free sheaves of
modules. -/
noncomputable def mapFree : F.obj (free I) ≅ free (R := S) I :=
  (isColimitOfPreserves F (isColimitFreeCofan I)).coconePointsIsoOfEquivalence
    (isColimitFreeCofan I) CategoryTheory.Equivalence.refl (Discrete.natIso fun _ ↦ η).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ιFree_mapFree_inv :
    ιFree i ≫ (mapFree F η I).inv = η.inv ≫ F.map (ιFree i) := by
  simp [mapFree, ← freeCofan_inj, Cofan.inj]

@[reassoc (attr := simp)]
lemma map_ιFree_mapFree_hom :
    F.map (ιFree i) ≫ (mapFree F η I).hom = η.hom ≫ ιFree i := by
  have : η.inv ≫ η.hom ≫ ιFree i = (η.inv ≫ F.map (ιFree i)) ≫ (mapFree F η I).hom := by
    simp [← ιFree_mapFree_inv_assoc]
  rw [← Iso.hom_inv_id_assoc η (η.hom ≫ ιFree i)]
  simp [this]

end

end SheafOfModules
