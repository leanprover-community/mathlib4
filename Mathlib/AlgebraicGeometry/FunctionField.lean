/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Properties

#align_import algebraic_geometry.function_field from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `AlgebraicGeometry.Scheme.functionField`: The function field of an integral scheme.
* `AlgebraicGeometry.Scheme.germToFunctionField`: The canonical map from a component into the
  function field. This map is injective.
-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

set_option linter.uppercaseLean3 false

universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)
#align algebraic_geometry.Scheme.function_field AlgebraicGeometry.Scheme.functionField

/-- The restriction map from a component to the function field. -/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : Opens X)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ
    ⟨genericPoint X,
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩
#align algebraic_geometry.Scheme.germ_to_function_field AlgebraicGeometry.Scheme.germToFunctionField

noncomputable instance [IrreducibleSpace X] (U : Opens X) [Nonempty U] :
    Algebra Γ(X, U) X.functionField :=
  (X.germToFunctionField U).toAlgebra

noncomputable instance [IsIntegral X] : Field X.functionField := by
  refine .ofIsUnitOrEqZero fun a ↦ ?_
  obtain ⟨U, m, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ a
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero]
  intro ha
  replace ha := ne_of_apply_ne _ ha
  have hs : genericPoint X ∈ RingedSpace.basicOpen _ s := by
    rw [← SetLike.mem_coe, (genericPoint_spec X).mem_open_set_iff, Set.top_eq_univ,
      Set.univ_inter, Set.nonempty_iff_ne_empty, Ne, ← Opens.coe_bot, ← SetLike.ext'_iff]
    · erw [basicOpen_eq_bot_iff]
      exact ha
    · exact (RingedSpace.basicOpen _ _).isOpen
  have := (X.presheaf.germ ⟨_, hs⟩).isUnit_map (RingedSpace.isUnit_res_basicOpen _ s)
  rwa [TopCat.Presheaf.germ_res_apply] at this

theorem germ_injective_of_isIntegral [IsIntegral X] {U : Opens X} (x : U) :
    Function.Injective (X.presheaf.germ x) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ x).map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy
  cases Subsingleton.elim iU iV
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e
#align algebraic_geometry.germ_injective_of_is_integral AlgebraicGeometry.germ_injective_of_isIntegral

theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : Opens X) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _
#align algebraic_geometry.Scheme.germ_to_function_field_injective AlgebraicGeometry.Scheme.germToFunctionField_injective

theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f.1.base (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert (genericPoint_spec X).image (show Continuous f.1.base by fun_prop)
  symm
  rw [eq_top_iff, Set.top_eq_univ, Set.top_eq_univ]
  convert subset_closure_inter_of_isPreirreducible_of_isOpen _ H.base_open.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩
#align algebraic_geometry.generic_point_eq_of_is_open_immersion AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion

noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X] (x : X) :
    Algebra (X.presheaf.stalk x) X.functionField := by
  apply RingHom.toAlgebra
  exact X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)
#align algebraic_geometry.stalk_function_field_algebra AlgebraicGeometry.stalkFunctionFieldAlgebra

instance functionField_isScalarTower [IrreducibleSpace X] (U : Opens X) (x : U)
    [Nonempty U] : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = X.presheaf.germ x ≫ _
  rw [X.presheaf.germ_stalkSpecializes]
#align algebraic_geometry.function_field_is_scalar_tower AlgebraicGeometry.functionField_isScalarTower

noncomputable instance (R : CommRingCat.{u}) [IsDomain R] :
    Algebra R (𝖲𝗉𝖾𝖼 R).functionField :=
  RingHom.toAlgebra <| by change CommRingCat.of R ⟶ _; apply StructureSheaf.toStalk

@[simp]
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (𝖲𝗉𝖾𝖼 R) = (⊥ : PrimeSpectrum R) := by
  apply (genericPoint_spec (𝖲𝗉𝖾𝖼 R).carrier).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  rw [Set.top_eq_univ, ← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl
#align algebraic_geometry.generic_point_eq_bot_of_affine AlgebraicGeometry.genericPoint_eq_bot_of_affine

instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (𝖲𝗉𝖾𝖼 R).functionField := by
  convert StructureSheaf.IsLocalization.to_stalk R (genericPoint (Scheme.Spec.obj (op R)))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero
#align algebraic_geometry.function_field_is_fraction_ring_of_affine AlgebraicGeometry.functionField_isFractionRing_of_affine

instance {X : Scheme} [IsIntegral X] {U : Opens X.carrier} [hU : Nonempty U] :
    IsIntegral (X ∣_ᵤ U) :=
  haveI : Nonempty (X ∣_ᵤ U).carrier := hU
  isIntegral_of_isOpenImmersion (Scheme.ιOpens U)

theorem IsAffineOpen.primeIdealOf_genericPoint {X : Scheme} [IsIntegral X] {U : Opens X}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X,
          ((genericPoint_spec X.carrier).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
      genericPoint (𝖲𝗉𝖾𝖼 Γ(X, U)) := by
  haveI : IsAffine _ := hU
  delta IsAffineOpen.primeIdealOf
  convert
    genericPoint_eq_of_isOpenImmersion
      ((X ∣_ᵤ U).isoSpec.hom ≫ 𝖲𝗉𝖾𝖼(X.presheaf.map (eqToHom U.openEmbedding_obj_top).op))
  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPoint_eq_of_isOpenImmersion (Scheme.ιOpens U)).symm
#align algebraic_geometry.is_affine_open.prime_ideal_of_generic_point AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint

theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : Opens X)
    (hU : IsAffineOpen U) [hU' : Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  haveI : IsAffine _ := hU
  haveI : Nonempty (X.restrict U.openEmbedding).carrier := hU'
  haveI : IsIntegral (X.restrict U.openEmbedding) :=
    @isIntegral_of_isAffine_of_isDomain _ _ _
      (by dsimp; rw [Opens.openEmbedding_obj_top]; infer_instance)
  delta IsFractionRing Scheme.functionField
  convert hU.isLocalization_stalk ⟨genericPoint X.carrier, _⟩ using 1
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  ext; exact mem_nonZeroDivisors_iff_ne_zero
#align algebraic_geometry.function_field_is_fraction_ring_of_is_affine_open AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen

instance (x : X.carrier) : IsAffine (X.affineCover.obj x) :=
  AlgebraicGeometry.isAffine_Spec _

instance [IsIntegral X] (x : X.carrier) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : Opens X.carrier :=
    ⟨Set.range (X.affineCover.map x).1.base,
      PresheafedSpace.IsOpenImmersion.base_open.isOpen_range⟩
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.map x)
  let x : U := ⟨x, X.affineCover.Covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  -- Porting note: the following two lines were not needed.
  let _hA := Presheaf.algebra_section_stalk X.presheaf x
  have := functionField_isScalarTower X U x
  .isFractionRing_of_isDomain_of_isLocalization M ↑(Presheaf.stalk X.presheaf x)
    (Scheme.functionField X)

end AlgebraicGeometry
