/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Discrete
import Mathlib.Condensed.Discrete.LocallyConstant
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.LocallyConstant.Algebra
/-!

# Discrete condensed `R`-modules

This file proves a condensed `R`-module is discrete if and only if the underlying condensed set is
(both for light condensed and condensed).
-/

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace Condensed.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHaus` given by locally constant
maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ comapₗ R f.unop }
  map f := { app := fun S ↦ mapₗ R f }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `Condensed.LocallyConstantModule.functorToPresheaves` lands in condensed modules. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) where
  obj X := {
    val := (functorToPresheaves.{w, u} R).obj X
    cond := by
      have := CompHausLike.preregular hs
      apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp (s :=
        CategoryTheory.forget (ModuleCat R))
      exact ((Condensed.LocallyConstant.functor P hs).obj _).cond }
  map f := ⟨(functorToPresheaves.{w, u} R).map f⟩

end Condensed.LocallyConstantModule

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

namespace LocallyConstant

abbrev functorToPresheaves : ModuleCat.{u+1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R) :=
  Condensed.LocallyConstantModule.functorToPresheaves.{u+1, u} R

abbrev functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u+1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

noncomputable def functorIsoDiscreteAux' (M : ModuleCat.{u+1} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) where
  hom := constₗ R
  inv := evalₗ R PUnit.unit

noncomputable def functorIsoDiscreteAux (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (Condensed.discrete _).obj
      (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) :=
  (Condensed.discrete _).mapIso (functorIsoDiscreteAux' R M)

instance (M : ModuleCat R) : IsIso ((Condensed.forget R).map
    ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  erw [← Sheaf.constantCommuteComposeApp_comp_counit]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  change Sheaf.IsDiscrete _ _ _
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
    inferInstanceAs (Condensed.discrete _).Faithful
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
    inferInstanceAs (Condensed.discrete _).Full
  rw [Sheaf.isDiscrete_iff_mem_essImage]
  change _ ∈ (Condensed.discrete _).essImage
  rw [essImage_eq_of_natIso CondensedSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage CondensedSet.LocallyConstant.functor M

noncomputable def functorIsoDiscrete_components (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (functor R).obj M := by
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  refine (functorIsoDiscreteAux R M) ≪≫ (@asIso _ _ _ _ ?_ ?_)
  · exact (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)
  · apply this.reflects

open Condensed.LocallyConstantModule in
noncomputable def functorIsoDiscrete : functor R ≅ Condensed.discrete _ := by
  refine NatIso.ofComponents (fun M ↦ (functorIsoDiscrete_components R M).symm) ?_
  intro M N f
  dsimp
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  dsimp [functorIsoDiscrete_components]
  rw [Category.assoc, ← Iso.eq_inv_comp]
  erw [← (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.naturality]
  change _ ≫ ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app (((functor R).obj N))) = _
  simp only [← assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  apply Sheaf.hom_ext
  simp only [comp_obj, Condensed.underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
    coe_of, Condensed.discrete_obj, Functor.comp_map, Condensed.underlying_map,
    functorToPresheaves_map_app, Condensed.discrete_map, functorIsoDiscreteAux, mapIso_inv,
    ← Functor.map_comp]
  rfl

noncomputable def compIsoId :
    (functor R) ⋙ (Condensed.underlying (ModuleCat R)) ≅ 𝟭 _ :=
  NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux' R _).symm

noncomputable def adjunction : functor R ⊣ Condensed.underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (Condensed.discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

noncomputable def fullyFaithfulFunctor :
    (functor R).FullyFaithful := (adjunction R).fullyFaithfulLOfCompIsoId (compIsoId R)

instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

instance : (functor R).Full := (fullyFaithfulFunctor R).full

instance : (Condensed.discrete (ModuleCat R)).Faithful :=
  Functor.Faithful.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat R)).Faithful :=
  inferInstanceAs (Condensed.discrete (ModuleCat R)).Faithful

instance : (Condensed.discrete (ModuleCat R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat R)).Full :=
  inferInstanceAs (Condensed.discrete (ModuleCat R)).Full

instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
  inferInstanceAs (Condensed.discrete (Type (u + 1))).Faithful

instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
  inferInstanceAs (Condensed.discrete (Type (u + 1))).Full

end LocallyConstant

abbrev _root_.CondensedSet.IsDiscrete (M : CondensedSet.{u}) :=
  Sheaf.IsDiscrete (coherentTopology CompHaus) CompHaus.isTerminalPUnit M

abbrev IsDiscrete (M : CondensedMod R) :=
  Sheaf.IsDiscrete (coherentTopology CompHaus) CompHaus.isTerminalPUnit M

lemma isDiscrete_iff_isDiscrete_forget (M : CondensedMod R) :
    IsDiscrete R M ↔ CondensedSet.IsDiscrete ((Condensed.forget R).obj M) :=
  Sheaf.isDiscrete_iff_forget (coherentTopology CompHaus) CompHaus.isTerminalPUnit
    (CategoryTheory.forget (ModuleCat R)) M


end CondensedMod

namespace LightCondMod

variable (R : Type u) [Ring R]

namespace LocallyConstant

abbrev functorToPresheaves : ModuleCat.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R) :=
  Condensed.LocallyConstantModule.functorToPresheaves.{u, u} R

abbrev functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

noncomputable def functorIsoDiscreteAux' (M : ModuleCat.{u} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u+1}) M)) where
  hom := constₗ R
  inv := evalₗ R PUnit.unit

noncomputable def functorIsoDiscreteAux (M : ModuleCat R) :
    (LightCondensed.discrete _).obj M ≅ (LightCondensed.discrete _).obj
      (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u+1}) M)) :=
  (LightCondensed.discrete _).mapIso (functorIsoDiscreteAux' R M)

-- Not stating this explicitly causes timeouts below.
instance : HasSheafify (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R) :=
  inferInstance

instance (M : ModuleCat R) : IsIso ((LightCondensed.forget R).map
    ((LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  erw [← Sheaf.constantCommuteComposeApp_comp_counit]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  change Sheaf.IsDiscrete _ _ _
  have : (constantSheaf (coherentTopology LightProfinite) (Type u)).Faithful :=
    inferInstanceAs (LightCondensed.discrete _).Faithful
  have : (constantSheaf (coherentTopology LightProfinite) (Type u)).Full :=
    inferInstanceAs (LightCondensed.discrete _).Full
  rw [Sheaf.isDiscrete_iff_mem_essImage]
  change _ ∈ (LightCondensed.discrete _).essImage
  rw [essImage_eq_of_natIso LightCondSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage LightCondSet.LocallyConstant.functor M

noncomputable def functorIsoDiscrete_components (M : ModuleCat R) :
    (LightCondensed.discrete _).obj M ≅ (functor R).obj M := by
  have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  refine (functorIsoDiscreteAux R M) ≪≫ (@asIso _ _ _ _ ?_ ?_)
  · exact (LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)
  · apply this.reflects

open Condensed.LocallyConstantModule in
noncomputable def functorIsoDiscrete : functor R ≅ LightCondensed.discrete _ := by
  refine NatIso.ofComponents (fun M ↦ (functorIsoDiscrete_components R M).symm) ?_
  intro M N f
  dsimp
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  dsimp [functorIsoDiscrete_components]
  rw [Category.assoc, ← Iso.eq_inv_comp]
  erw [← (LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.naturality]
  change _ ≫ ((LightCondensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
    (((functor R).obj N))) = _
  simp only [← assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  apply Sheaf.hom_ext
  simp only [comp_obj, LightCondensed.underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
    coe_of, LightCondensed.discrete_obj, Functor.comp_map, LightCondensed.underlying_map,
    functorToPresheaves_map_app, LightCondensed.discrete_map, functorIsoDiscreteAux, mapIso_inv,
    ← Functor.map_comp]
  rfl

noncomputable def compIsoId :
    (functor R) ⋙ (LightCondensed.underlying (ModuleCat R)) ≅ 𝟭 _ :=
  NatIso.ofComponents fun M ↦ (functorIsoDiscreteAux' R _).symm

noncomputable def adjunction : functor R ⊣ LightCondensed.underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (LightCondensed.discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

noncomputable def fullyFaithfulFunctor :
    (functor R).FullyFaithful := (adjunction R).fullyFaithfulLOfCompIsoId (compIsoId R)

instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

instance : (functor R).Full := (fullyFaithfulFunctor R).full

instance : (LightCondensed.discrete.{u} (ModuleCat R)).Faithful :=
  Functor.Faithful.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Faithful :=
  inferInstanceAs (LightCondensed.discrete.{u} (ModuleCat R)).Faithful

instance : (LightCondensed.discrete (ModuleCat.{u} R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Full :=
  inferInstanceAs (LightCondensed.discrete.{u} (ModuleCat.{u} R)).Full

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Faithful :=
  inferInstanceAs (LightCondensed.discrete (Type u)).Faithful

instance : (constantSheaf (coherentTopology LightProfinite) (Type u)).Full :=
  inferInstanceAs (LightCondensed.discrete (Type u)).Full

end LocallyConstant

abbrev _root_.LightCondSet.IsDiscrete (M : LightCondSet.{u}) :=
  Sheaf.IsDiscrete (coherentTopology LightProfinite) LightProfinite.isTerminalPUnit M

abbrev IsDiscrete (M : LightCondMod R) :=
  Sheaf.IsDiscrete (coherentTopology LightProfinite) LightProfinite.isTerminalPUnit M

lemma isDiscrete_iff_isDiscrete_forget (M : LightCondMod R) :
    IsDiscrete R M ↔ LightCondSet.IsDiscrete ((LightCondensed.forget R).obj M) :=
  Sheaf.isDiscrete_iff_forget (coherentTopology LightProfinite) LightProfinite.isTerminalPUnit
    (CategoryTheory.forget (ModuleCat R)) M

end LightCondMod
