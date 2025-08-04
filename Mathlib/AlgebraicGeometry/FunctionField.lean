/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `AlgebraicGeometry.Scheme.functionField`: The function field of an integral scheme.
* `AlgebraicGeometry.Scheme.germToFunctionField`: The canonical map from a component into the
  function field. This map is injective.
-/

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)

/-- The restriction map from a component to the function field. -/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))

noncomputable instance [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    Algebra Γ(X, U) X.functionField :=
  (X.germToFunctionField U).hom.toAlgebra

noncomputable instance [IsIntegral X] : Field X.functionField := by
  refine .ofIsUnitOrEqZero fun a ↦ ?_
  obtain ⟨U, m, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ a
  rw [or_iff_not_imp_right, ← (X.presheaf.germ _ _ m).hom.map_zero]
  intro ha
  replace ha := ne_of_apply_ne _ ha
  have hs : genericPoint X ∈ RingedSpace.basicOpen _ s := by
    rw [← SetLike.mem_coe, (genericPoint_spec X).mem_open_set_iff,
      Set.univ_inter, Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, ← SetLike.ext'_iff]
    · erw [basicOpen_eq_bot_iff]
      exact ha
    · exact (RingedSpace.basicOpen _ _).isOpen
  have := (X.presheaf.germ _ _ hs).hom.isUnit_map (RingedSpace.isUnit_res_basicOpen _ s)
  rwa [Presheaf.germ_res_apply] at this

theorem germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e

theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _ _

theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert (genericPoint_spec X).image (show Continuous f.base by fun_prop)
  symm
  rw [← Set.univ_subset_iff]
  convert subset_closure_inter_of_isPreirreducible_of_isOpen _ H.base_open.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩

noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X] (x : X) :
    Algebra (X.presheaf.stalk x) X.functionField := by
  -- TODO: can we write this normally after the refactor finishes?
  apply RingHom.toAlgebra
  exact (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom

instance functionField_isScalarTower [IrreducibleSpace X] (U : X.Opens) (x : U)
    [Nonempty U] : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.germ U x x.2 ≫ _).hom
  rw [X.presheaf.germ_stalkSpecializes]

noncomputable instance (R : CommRingCat.{u}) [IsDomain R] :
    Algebra R (Spec R).functionField :=
  -- TODO: can we write this normally after the refactor finishes?
  RingHom.toAlgebra <| by apply CommRingCat.Hom.hom; apply StructureSheaf.toStalk

@[simp]
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) := by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl

instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  convert StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero

instance {X : Scheme} [IsIntegral X] {U : X.Opens} [Nonempty U] :
    IsIntegral U :=
  isIntegral_of_isOpenImmersion U.ι

theorem IsAffineOpen.primeIdealOf_genericPoint {X : Scheme} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X,
          ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
      genericPoint (Spec Γ(X, U)) := by
  haveI : IsAffine _ := hU
  delta IsAffineOpen.primeIdealOf
  convert
    genericPoint_eq_of_isOpenImmersion
      (U.toScheme.isoSpec.hom ≫ Spec.map (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPoint_eq_of_isOpenImmersion U.ι).symm

theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  haveI : IsAffine _ := hU
  haveI : IsIntegral U :=
    @isIntegral_of_isAffine_of_isDomain _ _ _
      (by rw [Scheme.Opens.toScheme_presheaf_obj, Opens.isOpenEmbedding_obj_top]; infer_instance)
  delta IsFractionRing Scheme.functionField
  convert hU.isLocalization_stalk ⟨genericPoint X,
    (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩ using 1
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  ext; exact mem_nonZeroDivisors_iff_ne_zero

instance (x : X) : IsAffine (X.affineCover.obj x) :=
  AlgebraicGeometry.isAffine_Spec _

instance [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : X.Opens := (X.affineCover.map x).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  -- Porting note: the following two lines were not needed.
  let _hA := Presheaf.algebra_section_stalk X.presheaf x
  have := functionField_isScalarTower X U x
  .isFractionRing_of_isDomain_of_isLocalization M ↑(Presheaf.stalk X.presheaf x)
    (Scheme.functionField X)

instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

end AlgebraicGeometry
