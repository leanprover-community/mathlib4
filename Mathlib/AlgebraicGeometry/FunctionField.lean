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
* `Algebraic_geometry.germToFunctionField`: The canonical map from a component into the function
  field. This map is injective.
-/

set_option linter.uppercaseLean3 false

universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

/-- The function field of an irreducible scheme is the local ring at its generic point.
Despite the name, this is a field only when the scheme is integral. -/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X.carrier] : CommRingCat :=
  X.presheaf.stalk (genericPoint X.carrier)
#align algebraic_geometry.Scheme.function_field AlgebraicGeometry.Scheme.functionField

/-- The restriction map from a component to the function field. -/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X.carrier] (U : Opens X.carrier)
    [h : Nonempty U] : X.presheaf.obj (op U) ⟶ X.functionField :=
  X.presheaf.germ
    ⟨genericPoint X.carrier,
      ((genericPoint_spec X.carrier).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩
                                                                        -- 🎉 no goals
#align algebraic_geometry.Scheme.germ_to_function_field AlgebraicGeometry.Scheme.germToFunctionField

noncomputable instance [IrreducibleSpace X.carrier] (U : Opens X.carrier) [Nonempty U] :
    Algebra (X.presheaf.obj (op U)) X.functionField :=
  (X.germToFunctionField U).toAlgebra

noncomputable instance [IsIntegral X] : Field X.functionField := by
  apply fieldOfIsUnitOrEqZero
  -- ⊢ ∀ (a : ↑(Scheme.functionField X)), IsUnit a ∨ a = 0
  intro a
  -- ⊢ IsUnit a ∨ a = 0
  obtain ⟨U, m, s, rfl⟩ := TopCat.Presheaf.germ_exist _ _ a
  -- ⊢ IsUnit (↑(Presheaf.germ X.presheaf { val := genericPoint ↑↑X.toPresheafedSpa …
  rw [or_iff_not_imp_right, ← (X.presheaf.germ ⟨_, m⟩).map_zero]
  -- ⊢ ¬↑(Presheaf.germ X.presheaf { val := genericPoint ↑↑X.toPresheafedSpace, pro …
  intro ha
  -- ⊢ IsUnit (↑(Presheaf.germ X.presheaf { val := genericPoint ↑↑X.toPresheafedSpa …
  replace ha := ne_of_apply_ne _ ha
  -- ⊢ IsUnit (↑(Presheaf.germ X.presheaf { val := genericPoint ↑↑X.toPresheafedSpa …
  have hs : genericPoint X.carrier ∈ RingedSpace.basicOpen _ s := by
    rw [← SetLike.mem_coe, (genericPoint_spec X.carrier).mem_open_set_iff, Set.top_eq_univ,
      Set.univ_inter, Set.nonempty_iff_ne_empty, Ne.def, ← Opens.coe_bot, ← SetLike.ext'_iff]
    erw [basicOpen_eq_bot_iff]
    exacts [ha, (RingedSpace.basicOpen _ _).isOpen]
  have := (X.presheaf.germ ⟨_, hs⟩).isUnit_map (RingedSpace.isUnit_res_basicOpen _ s)
  -- ⊢ IsUnit (↑(Presheaf.germ X.presheaf { val := genericPoint ↑↑X.toPresheafedSpa …
  rwa [TopCat.Presheaf.germ_res_apply] at this
  -- 🎉 no goals

theorem germ_injective_of_isIntegral [IsIntegral X] {U : Opens X.carrier} (x : U) :
    Function.Injective (X.presheaf.germ x) := by
  rw [injective_iff_map_eq_zero]
  -- ⊢ ∀ (a : (forget CommRingCat).obj (X.presheaf.obj (op U))), ↑(Presheaf.germ X. …
  intro y hy
  -- ⊢ y = 0
  rw [← (X.presheaf.germ x).map_zero] at hy
  -- ⊢ y = 0
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ x.prop x.prop _ _ hy
  -- ⊢ y = 0
  cases show iU = iV from Subsingleton.elim _ _
  -- ⊢ y = 0
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  -- ⊢ y = 0
  exact map_injective_of_isIntegral X iU e
  -- 🎉 no goals
#align algebraic_geometry.germ_injective_of_is_integral AlgebraicGeometry.germ_injective_of_isIntegral

theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : Opens X.carrier) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _
#align algebraic_geometry.Scheme.germ_to_function_field_injective AlgebraicGeometry.Scheme.germToFunctionField_injective

theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f]
    [hX : IrreducibleSpace X.carrier] [IrreducibleSpace Y.carrier] :
    f.1.base (genericPoint X.carrier : _) = (genericPoint Y.carrier : _) := by
  apply ((genericPoint_spec Y).eq _).symm
  -- ⊢ IsGenericPoint (↑f.val.base (genericPoint ↑↑X.toPresheafedSpace)) ⊤
  -- Porting note: the continuity argument used to be `by continuity`
  convert (genericPoint_spec X.carrier).image
    (show Continuous f.1.base from ContinuousMap.continuous_toFun _)
  symm
  -- ⊢ closure (↑f.val.base '' ⊤) = ⊤
  rw [eq_top_iff, Set.top_eq_univ, Set.top_eq_univ]
  -- ⊢ Set.univ ≤ closure (↑f.val.base '' Set.univ)
  convert subset_closure_inter_of_isPreirreducible_of_isOpen _ H.base_open.open_range _
  rw [Set.univ_inter, Set.image_univ]
  -- ⊢ IsPreirreducible Set.univ
  apply PreirreducibleSpace.isPreirreducible_univ (α := Y.carrier)
  -- ⊢ Set.Nonempty (Set.univ ∩ Set.range ↑f.val.base)
  exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩
  -- 🎉 no goals
#align algebraic_geometry.generic_point_eq_of_is_open_immersion AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion

noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X.carrier] (x : X.carrier) :
    Algebra (X.presheaf.stalk x) X.functionField := by
  apply RingHom.toAlgebra
  -- ⊢ ↑(Presheaf.stalk X.presheaf x) →+* ↑(Scheme.functionField X)
  exact X.presheaf.stalkSpecializes ((genericPoint_spec X.carrier).specializes trivial)
  -- 🎉 no goals
#align algebraic_geometry.stalk_function_field_algebra AlgebraicGeometry.stalkFunctionFieldAlgebra

instance functionField_isScalarTower [IrreducibleSpace X.carrier] (U : Opens X.carrier) (x : U)
    [Nonempty U] : IsScalarTower (X.presheaf.obj <| op U) (X.presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  -- ⊢ algebraMap ↑(X.presheaf.obj (op U)) ↑(Scheme.functionField X) = RingHom.comp …
  simp_rw [RingHom.algebraMap_toAlgebra]
  -- ⊢ Scheme.germToFunctionField X U = RingHom.comp (Presheaf.stalkSpecializes X.p …
  change _ = X.presheaf.germ x ≫ _
  -- ⊢ Scheme.germToFunctionField X U = Presheaf.germ X.presheaf x ≫ Presheaf.stalk …
  rw [X.presheaf.germ_stalkSpecializes]
  -- 🎉 no goals
#align algebraic_geometry.function_field_is_scalar_tower AlgebraicGeometry.functionField_isScalarTower

noncomputable instance (R : CommRingCat) [IsDomain R] :
    Algebra R (Scheme.Spec.obj <| op R).functionField :=
  RingHom.toAlgebra <| by change CommRingCat.of R ⟶ _; apply StructureSheaf.toStalk
                          -- ⊢ CommRingCat.of ↑R ⟶ Scheme.functionField (Scheme.Spec.obj (op R))
                                                       -- 🎉 no goals

@[simp]
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (Scheme.Spec.obj <| op R).carrier = (⟨0, Ideal.bot_prime⟩ : PrimeSpectrum R) := by
  apply (genericPoint_spec (Scheme.Spec.obj <| op R).carrier).eq
  -- ⊢ IsGenericPoint { asIdeal := 0, IsPrime := (_ : Ideal.IsPrime ⊥) } ⊤
  rw [isGenericPoint_def]
  -- ⊢ closure {{ asIdeal := 0, IsPrime := (_ : Ideal.IsPrime ⊥) }} = ⊤
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  -- ⊢ PrimeSpectrum.zeroLocus ↑{ asIdeal := 0, IsPrime := (_ : Ideal.IsPrime ⊥) }. …
  rw [Set.top_eq_univ, ← PrimeSpectrum.zeroLocus_singleton_zero]
  -- ⊢ PrimeSpectrum.zeroLocus ↑{ asIdeal := 0, IsPrime := (_ : Ideal.IsPrime ⊥) }. …
  rfl
  -- 🎉 no goals
#align algebraic_geometry.generic_point_eq_bot_of_affine AlgebraicGeometry.genericPoint_eq_bot_of_affine

instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Scheme.Spec.obj <| op R).functionField := by
  convert StructureSheaf.IsLocalization.to_stalk R (genericPoint _)
  -- ⊢ IsFractionRing ↑R ↑(Scheme.functionField (Scheme.Spec.obj (op R))) ↔ IsLocal …
  delta IsFractionRing IsLocalization.AtPrime
  -- ⊢ IsLocalization (nonZeroDivisors ↑R) ↑(Scheme.functionField (Scheme.Spec.obj  …
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  -- ⊢ IsLocalization (nonZeroDivisors ↑R) ↑(Scheme.functionField (Scheme.Spec.obj  …
  congr 1
  -- ⊢ nonZeroDivisors ↑R = Ideal.primeCompl (genericPoint ↑↑(Scheme.Spec.obj (op R …
  rw [genericPoint_eq_bot_of_affine]
  -- ⊢ nonZeroDivisors ↑R = Ideal.primeCompl { asIdeal := 0, IsPrime := (_ : Ideal. …
  ext
  -- ⊢ x✝ ∈ nonZeroDivisors ↑R ↔ x✝ ∈ Ideal.primeCompl { asIdeal := 0, IsPrime := ( …
  exact mem_nonZeroDivisors_iff_ne_zero
  -- 🎉 no goals
#align algebraic_geometry.function_field_is_fraction_ring_of_affine AlgebraicGeometry.functionField_isFractionRing_of_affine

instance {X : Scheme} [IsIntegral X] {U : Opens X.carrier} [hU : Nonempty U] :
    IsIntegral (X.restrict U.openEmbedding) :=
  haveI : Nonempty (X.restrict U.openEmbedding).carrier := hU
  isIntegralOfOpenImmersion (X.ofRestrict U.openEmbedding)

theorem IsAffineOpen.primeIdealOf_genericPoint {X : Scheme} [IsIntegral X] {U : Opens X.carrier}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X.carrier,
          ((genericPoint_spec X.carrier).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
                                                                            -- 🎉 no goals
      genericPoint (Scheme.Spec.obj <| op <| X.presheaf.obj <| op U).carrier := by
  haveI : IsAffine _ := hU
  -- ⊢ primeIdealOf hU { val := genericPoint ↑↑X.toPresheafedSpace, property := (_  …
  have e : U.openEmbedding.isOpenMap.functor.obj ⊤ = U := by
    ext1; exact Set.image_univ.trans Subtype.range_coe
  delta IsAffineOpen.primeIdealOf
  -- ⊢ ↑(Scheme.Spec.map (X.presheaf.map (eqToHom (_ : (IsOpenMap.functor (_ : IsOp …
  erw [← Scheme.comp_val_base_apply]
  -- ⊢ ↑((Scheme.isoSpec (Scheme.restrict X (_ : OpenEmbedding ↑(Opens.inclusion U) …
  convert
    genericPoint_eq_of_isOpenImmersion
      ((X.restrict U.openEmbedding).isoSpec.hom ≫
        Scheme.Spec.map (X.presheaf.map (eqToHom e).op).op)
  -- Porting note: this was `ext1`
  apply Subtype.ext
  -- ⊢ ↑{ val := genericPoint ↑↑X.toPresheafedSpace, property := (_ : genericPoint  …
  exact (genericPoint_eq_of_isOpenImmersion (X.ofRestrict U.openEmbedding)).symm
  -- 🎉 no goals
#align algebraic_geometry.is_affine_open.prime_ideal_of_generic_point AlgebraicGeometry.IsAffineOpen.primeIdealOf_genericPoint

theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : Opens X.carrier)
    (hU : IsAffineOpen U) [hU' : Nonempty U] :
    IsFractionRing (X.presheaf.obj <| op U) X.functionField := by
  haveI : IsAffine _ := hU
  -- ⊢ IsFractionRing ↑(X.presheaf.obj (op U)) ↑(Scheme.functionField X)
  haveI : Nonempty (X.restrict U.openEmbedding).carrier := hU'
  -- ⊢ IsFractionRing ↑(X.presheaf.obj (op U)) ↑(Scheme.functionField X)
  haveI : IsIntegral (X.restrict U.openEmbedding) :=
    @isIntegralOfIsAffineIsDomain _ _ _
      (by dsimp; rw [Opens.openEmbedding_obj_top]; infer_instance)
  delta IsFractionRing Scheme.functionField
  -- ⊢ IsLocalization (nonZeroDivisors ↑(X.presheaf.obj (op U))) ↑(Presheaf.stalk X …
  convert hU.isLocalization_stalk ⟨genericPoint X.carrier, _⟩ using 1
  -- ⊢ nonZeroDivisors ↑(X.presheaf.obj (op U)) = Ideal.primeCompl (IsAffineOpen.pr …
  rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  -- ⊢ nonZeroDivisors ↑(X.presheaf.obj (op U)) = Ideal.primeCompl { asIdeal := 0,  …
  ext; exact mem_nonZeroDivisors_iff_ne_zero
  -- ⊢ x✝ ∈ nonZeroDivisors ↑(X.presheaf.obj (op U)) ↔ x✝ ∈ Ideal.primeCompl { asId …
       -- 🎉 no goals
#align algebraic_geometry.function_field_is_fraction_ring_of_is_affine_open AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen

instance (x : X.carrier) : IsAffine (X.affineCover.obj x) :=
  AlgebraicGeometry.SpecIsAffine _

instance [IsIntegral X] (x : X.carrier) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : Opens X.carrier :=
    ⟨Set.range (X.affineCover.map x).1.base,
      PresheafedSpace.IsOpenImmersion.base_open.open_range⟩
  have hU : IsAffineOpen U := rangeIsAffineOpenOfOpenImmersion (X.affineCover.map x)
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
