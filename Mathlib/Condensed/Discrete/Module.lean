/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Light.Module
public import Mathlib.Condensed.Module
public import Mathlib.Topology.LocallyConstant.Algebra
/-!

# Discrete condensed `R`-modules

This file provides the necessary API to prove that a condensed `R`-module is discrete if and only
if the underlying condensed set is (both for light condensed and condensed).

That is, it defines the functor `CondensedMod.LocallyConstant.functor` which takes an `R`-module to
the condensed `R`-modules given by locally constant maps to it, and proves that this functor is
naturally isomorphic to the constant sheaf functor (and the analogues for light condensed modules).
-/

@[expose] public section

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

variable {P : TopCat.{u} → Prop}

namespace CompHausLike.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHausLike P` given by locally
constant maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ ModuleCat.ofHom (comapₗ R f.unop.hom.hom) }
  map f := { app := fun S ↦ ModuleCat.ofHom (mapₗ R f.hom) }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `CompHausLike.LocallyConstantModule.functorToPresheaves` lands in sheaves. -/
@[simps!]
def functor : haveI := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) :=
  ObjectProperty.lift _ (functorToPresheaves.{w, u} R) (fun X ↦ by
    have := CompHausLike.preregular hs
    apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
      (s := CategoryTheory.forget (ModuleCat R))
    exact ((CompHausLike.LocallyConstant.functor P hs).obj _).property)

end CompHausLike.LocallyConstantModule

namespace CondensedMod.LocallyConstant

open Condensed

variable (R : Type (u + 1)) [Ring R]

/-- `functorToPresheaves` in the case of `CompHaus`. -/
abbrev functorToPresheaves : ModuleCat.{u + 1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R) :=
  CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R

/-- `functorToPresheaves` as a functor to condensed modules. -/
abbrev functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  CompHausLike.LocallyConstantModule.functor.{u + 1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteAux₁ (M : ModuleCat.{u + 1} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u + 1}) M)) where
  hom := ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteAux₂ (M : ModuleCat R) :
    (discrete _).obj M ≅ (discrete _).obj
      (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u + 1}) M)) :=
  (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

instance (M : ModuleCat R) : IsIso ((forget R).map
    ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M))) := by
  dsimp [Condensed.forget, discreteUnderlyingAdj]
  rw [← constantSheafAdj_counit_w]
  refine IsIso.comp_isIso' inferInstance ?_
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
    inferInstanceAs (discrete _).Faithful
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
    inferInstanceAs (discrete _).Full
  rw [← Sheaf.isConstant_iff_isIso_counit_app]
  constructor
  change (discrete _).essImage _
  rw [essImage_eq_of_natIso CondensedSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage CondensedSet.LocallyConstant.functor M

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteComponents (M : ModuleCat R) :
    (discrete _).obj M ≅ (functor R).obj M :=
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (Condensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

/--
`CondensedMod.LocallyConstant.functor` is naturally isomorphic to the constant sheaf functor from
`R`-modules to condensed `R`-modules.
-/
noncomputable def functorIsoDiscrete : functor R ≅ discrete _ :=
  NatIso.ofComponents (fun M ↦ (functorIsoDiscreteComponents R M).symm) fun f ↦ by
    dsimp
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [assoc, ← Iso.eq_inv_comp,
      ← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

/--
`CondensedMod.LocallyConstant.functor` is left adjoint to the forgetful functor from condensed
`R`-modules to `R`-modules.
-/
noncomputable def adjunction : functor R ⊣ underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

/--
`CondensedMod.LocallyConstant.functor` is fully faithful.
-/
noncomputable def fullyFaithfulFunctor : (functor R).FullyFaithful :=
  (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux₁ R _).symm)

instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

instance : (functor R).Full := (fullyFaithfulFunctor R).full

instance : (discrete (ModuleCat R)).Faithful :=
  Functor.Faithful.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat R)).Faithful :=
  inferInstanceAs (discrete (ModuleCat R)).Faithful

instance : (discrete (ModuleCat R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat R)).Full :=
  inferInstanceAs (discrete (ModuleCat R)).Full

instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
  inferInstanceAs (discrete (Type (u + 1))).Faithful

instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
  inferInstanceAs (discrete (Type (u + 1))).Full

end CondensedMod.LocallyConstant

namespace LightCondMod.LocallyConstant

open LightCondensed

variable (R : Type u) [Ring R]

/-- `functorToPresheaves` in the case of `LightProfinite`. -/
abbrev functorToPresheaves : ModuleCat.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R) :=
  CompHausLike.LocallyConstantModule.functorToPresheaves.{u, u} R

/-- `functorToPresheaves` as a functor to light condensed modules. -/
abbrev functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  CompHausLike.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteAux₁ (M : ModuleCat.{u} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)) where
  hom := ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteAux₂ (M : ModuleCat.{u} R) :
    (discrete _).obj M ≅ (discrete _).obj
      (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)) :=
  (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

-- Not stating this explicitly causes timeouts below.
instance : HasSheafify (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R) :=
  inferInstance

instance (M : ModuleCat R) :
    IsIso ((LightCondensed.forget R).map
    ((discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  dsimp [LightCondensed.forget, discreteUnderlyingAdj]
  rw [← constantSheafAdj_counit_w]
  refine IsIso.comp_isIso' inferInstance ?_
  have : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Faithful :=
    inferInstanceAs (discrete _).Faithful
  have : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Full :=
    inferInstanceAs (discrete (Type u)).Full
  rw [← Sheaf.isConstant_iff_isIso_counit_app]
  constructor
  change (discrete _).essImage _
  rw [essImage_eq_of_natIso LightCondSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage LightCondSet.LocallyConstant.functor M

/-- Auxiliary definition for `functorIsoDiscrete`. -/
noncomputable def functorIsoDiscreteComponents (M : ModuleCat R) :
    (discrete _).obj M ≅ (functor R).obj M :=
  have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (LightCondensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

/--
`LightCondMod.LocallyConstant.functor` is naturally isomorphic to the constant sheaf functor from
`R`-modules to light condensed `R`-modules.
-/
noncomputable def functorIsoDiscrete : functor R ≅ discrete _ :=
  NatIso.ofComponents (fun M ↦ (functorIsoDiscreteComponents R M).symm) fun f ↦ by
    dsimp
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [Category.assoc, ← Iso.eq_inv_comp,
      ← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

/--
`LightCondMod.LocallyConstant.functor` is left adjoint to the forgetful functor from light condensed
`R`-modules to `R`-modules.
-/
noncomputable def adjunction : functor R ⊣ underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

/--
`LightCondMod.LocallyConstant.functor` is fully faithful.
-/
noncomputable def fullyFaithfulFunctor : (functor R).FullyFaithful :=
  (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux₁ R _).symm)

instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

instance : (functor R).Full := (fullyFaithfulFunctor R).full

instance : (discrete.{u} (ModuleCat R)).Faithful := Functor.Faithful.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Faithful :=
  inferInstanceAs (discrete.{u} (ModuleCat R)).Faithful

instance : (discrete (ModuleCat.{u} R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Full :=
  inferInstanceAs (discrete.{u} (ModuleCat.{u} R)).Full

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Faithful :=
  inferInstanceAs (discrete (Type u)).Faithful

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Full :=
  inferInstanceAs (discrete (Type u)).Full

end LightCondMod.LocallyConstant
