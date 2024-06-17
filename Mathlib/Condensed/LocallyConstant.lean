/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.LocallyConstant
import Mathlib.Condensed.Discrete
import Mathlib.Condensed.Light.Discrete
import Mathlib.Condensed.TopComparison
/-!

# The sheaf of locally constant maps on `CompHausLike`

This file proves that the discreteness functor into (light) condensed sets is given by the sheaf
of locally constant maps, and deduces full faithfulness of these functors.
-/

universe w u

open CategoryTheory CompHausLike CompHausLike.LocallyConstant Condensed Limits Opposite

attribute [local instance] ConcreteCategory.instFunLike

namespace Condensed.LocallyConstant

variable (P : TopCat.{u} → Prop) (X : TopCat.{max u w})
    [CompHausLike.HasExplicitFiniteCoproducts.{0} P] [CompHausLike.HasExplicitPullbacks.{u} P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
noncomputable def functorToPresheavesIsoTopCatToCondensed (X : Type (max u w)) :
    functorToPresheaves.{u, w}.obj X ≅
      ((topCatToSheafCompHausLike P hs).obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

/-- `Condensed.LocallyConstant.functorToPresheaves` lands in condensed sets. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := {
    val := functorToPresheaves.{u, w}.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff
        (functorToPresheavesIsoTopCatToCondensed P hs X)]
      exact ((topCatToSheafCompHausLike P hs).obj (TopCat.discrete.obj X)).cond
  }
  map f := ⟨functorToPresheaves.{u, w}.map f⟩

/--
`Condensed.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToCondensed` to discrete topological spaces.
-/
noncomputable def functorIsoTopCatToCondensed :
    functor.{w, u} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIsoTopCatToCondensed P hs X))

variable [CompHausLike.HasProp P PUnit.{u+1}] (J : GrothendieckTopology (CompHausLike.{u} P))
  (A : Type*) [Category A]


variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]
variable [HasExplicitFiniteCoproducts.{u} P]
variable  [HasExplicitPullbacks P]

noncomputable instance {C A : Type*} [Category C] [Category A] [Preregular C] [FinitaryExtensive C]
    (F : Sheaf (coherentTopology C) A)
    [HasPullbacks C] : PreservesFiniteProducts F.val :=
  Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F.val |>.mp F.cond |>.1.some

/-- The counit is natural in both the compact Hausdorff space `S` and the condensed set `Y` -/
@[simps]
noncomputable def counit :
    have := CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ ⋙ functor.{w, u} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X :=
    have := CompHausLike.preregular hs
    ⟨counitApp.{u, w} X.val⟩
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply Sheaf.hom_ext
    simp only [underlying, functor, id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Functor.id_map]
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_comp_val]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_app]
    apply locallyConstantCondensed_ext.{u, w} (f.map (g.val.app (op
      (CompHausLike.of P PUnit.{u+1}))))
    intro a
    simp only [op_unop, functorToPresheaves_map_app]
    erw [incl_of_counitAppApp]
    rw [← hom_apply_counitAppApp]

/--
The unit of the adjunciton is given by mapping each element to the corresponding constant map.
-/
@[simps]
def unit : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  app X x := LocallyConstant.const _ x

theorem locallyConstantAdjunction_left_triangle (X : Type max u w) :
    functorToPresheaves.{u, w}.map ((unit P hs).app X) ≫
      ((counit P hs).app ((functor P hs).obj X)).val =
    𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, underlying_obj, FunctorToTypes.comp, NatTrans.id_app,
    functorToPresheaves_obj_obj, types_id_apply]
  simp only [counit, counitApp_app]
  have := CompHausLike.preregular hs
  apply locallyConstantCondensed_ext
    (X := ((functor P hs).obj X).val) (Y := ((functor.{w, u} P hs).obj X).val)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_val, functorToPresheaves_obj_obj, coe_of, Functor.id_obj,
    counitAppAppImage, LocallyConstant.map_apply, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← Aux.α.map_eq_image _ a x]
  rfl

/-- The unit of the adjunction is an iso. -/
noncomputable def unitIso : 𝟭 (Type max u w) ≅ functor.{w, u} P hs ⋙
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  hom := unit P hs
  inv := { app := fun X f ↦ f.toFun PUnit.unit }

/--
`Condensed.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
-- Note: adding `@[simps]` makes the linter complain.
noncomputable def adjunction :
    functor.{w, u} P hs ⊣ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ :=
  Adjunction.mkOfUnitCounit {
    unit := unit P hs
    counit := counit P hs
    left_triangle := by
      ext X : 2
      simp only [id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
        underlying_obj, functorToPresheaves_obj_obj, whiskerRight_app, Functor.associator_hom_app,
        whiskerLeft_app, Category.id_comp, NatTrans.id_app']
      apply Sheaf.hom_ext
      rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_id_val]
      exact locallyConstantAdjunction_left_triangle P hs X
    right_triangle := by
      ext X (x : X.val.obj _)
      simp only [Functor.comp_obj, Functor.id_obj, underlying_obj, counit, FunctorToTypes.comp,
        whiskerLeft_app, Functor.associator_inv_app, functor_obj_val, functorToPresheaves_obj_obj,
        types_id_apply, whiskerRight_app, underlying_map, counitApp_app, NatTrans.id_app']
      have := CompHausLike.preregular hs
      let _ : PreservesFiniteProducts
          ((sheafToPresheaf (coherentTopology (CompHausLike P)) (Type (max u w))).obj X) :=
        (inferInstance : PreservesFiniteProducts (Sheaf.val _))
      apply locallyConstantCondensed_ext ((unit P hs).app _ x)
      intro a
      erw [incl_of_counitAppApp]
      simp only [sheafToPresheaf_obj, unit_app, coe_of, counitAppAppImage,
        LocallyConstant.coe_const]
      have := Aux.α.map_eq_image _ a ⟨PUnit.unit, by
        simp [Aux.α.mem_iff_eq_image (a := a), ← Aux.α.map_preimage_eq_image]⟩
      erw [← this]
      simp only [coe_of, unit_app, LocallyConstant.coe_const, Function.const_apply]
      congr }

instance : IsIso (adjunction P hs).unit := (inferInstance : IsIso (unitIso P hs).hom)

end Condensed.LocallyConstant

open Condensed.LocallyConstant

/-- The functor from sets to condensed sets given by locally constant maps into the set. -/
abbrev CondensedSet.LocallyConstant.functor : Type (u+1) ⥤ CondensedSet.{u} :=
  Condensed.LocallyConstant.functor.{u+1, u} (P := fun _ ↦ True)
    (hs := fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
`CondensedSet.LocallyConstant.functor` is isomorphic to `Condensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def CondensedSet.LocallyConstant.iso :
    CondensedSet.LocallyConstant.functor ≅ discrete (Type (u+1)) :=
  (adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

/-- `CondensedSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def fullyFaithfulCondensedSetLocallyConstantFunctor :
    CondensedSet.LocallyConstant.functor.FullyFaithful :=
  (adjunction.{u+1, u} _ _).fullyFaithfulLOfIsIsoUnit

noncomputable instance : CondensedSet.LocallyConstant.functor.Faithful :=
  fullyFaithfulCondensedSetLocallyConstantFunctor.faithful

noncomputable instance : CondensedSet.LocallyConstant.functor.Full :=
  fullyFaithfulCondensedSetLocallyConstantFunctor.full

instance : (discrete (Type _)).Faithful := Functor.Faithful.of_iso
  CondensedSet.LocallyConstant.iso

noncomputable instance : (discrete (Type _)).Full := Functor.Full.of_iso
  CondensedSet.LocallyConstant.iso

/-- The functor from sets to light condensed sets given by locally constant maps into the set. -/
abbrev LightCondSet.LocallyConstant.functor : Type u ⥤ LightCondSet.{u} :=
  Condensed.LocallyConstant.functor.{u, u}
    (P := fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

instance (S : LightProfinite.{u}) (p : S → Prop) :
    HasProp (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X) (Subtype p) :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace (Subtype p)),
    (inferInstance : SecondCountableTopology {s | p s})⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is isomorphic to `LightCondensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def LightCondSet.LocallyConstant.iso :
    LightCondSet.LocallyConstant.functor ≅ LightCondensed.discrete (Type u) :=
  (adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

/-- `LightCondSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def fullyFaithfulLightCondSetLocallyConstantFunctor :
    LightCondSet.LocallyConstant.functor.{u}.FullyFaithful :=
  (adjunction _ _).fullyFaithfulLOfIsIsoUnit

instance : LightCondSet.LocallyConstant.functor.{u}.Faithful :=
  fullyFaithfulLightCondSetLocallyConstantFunctor.faithful

instance : LightCondSet.LocallyConstant.functor.Full :=
  fullyFaithfulLightCondSetLocallyConstantFunctor.full

instance : (LightCondensed.discrete (Type u)).Faithful := Functor.Faithful.of_iso
  LightCondSet.LocallyConstant.iso.{u}

instance : (LightCondensed.discrete (Type u)).Full := Functor.Full.of_iso
  LightCondSet.LocallyConstant.iso.{u}
