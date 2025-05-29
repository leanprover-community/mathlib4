/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Krull dimension of polynomial ring

This file proves properties of the krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.
-/

lemma PrimeSpectrum.residueField_specComap {R : Type*} [CommRing R] (I : PrimeSpectrum R) :
    Set.range (algebraMap R I.asIdeal.ResidueField).specComap = {I} := by
  rw [Set.range_unique, Set.singleton_eq_singleton_iff]
  exact PrimeSpectrum.ext (Ideal.ext fun x ↦ Ideal.algebraMap_residueField_eq_zero)

/-- The `OrderIso` between fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal
 `p : PrimeSpectrum R` and the prime spectrum of the tensor product of `S` and the residue field of
 `p`. -/
noncomputable def PrimeSpectrum.preimageOrderIsoTensorResidueField (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p} ≃o
      PrimeSpectrum (TensorProduct R p.asIdeal.ResidueField S) := OrderIso.symm <| by
  letI : Algebra S (TensorProduct R (Localization.AtPrime p.asIdeal) S) :=
    Algebra.TensorProduct.rightAlgebra
  let f1 : S →+* (TensorProduct R (Localization.AtPrime p.asIdeal) S) :=
    Algebra.TensorProduct.includeRight.toRingHom
  let f2r := Algebra.algHom R (Localization.AtPrime p.asIdeal) p.asIdeal.ResidueField
  let f2 : (TensorProduct R (Localization.AtPrime p.asIdeal) S) →ₐ[R]
    (TensorProduct R (p.asIdeal.ResidueField) S) := Algebra.TensorProduct.map
      f2r (AlgHom.id R S)
  have hf2r_surj : Function.Surjective f2r := Ideal.Quotient.mkₐ_surjective _ _
  have hf2_surj : Function.Surjective f2 := (AlgHom.range_eq_top f2).mp <| by
    rw [← Algebra.range_id, Algebra.TensorProduct.map_id.symm, Algebra.TensorProduct.map_range,
      Algebra.TensorProduct.map_range]
    simp [AlgHom.range_comp, (AlgHom.range_eq_top _).mpr hf2r_surj]
  let f1'' := IsLocalization.orderEmbedding (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    (TensorProduct R (Localization.AtPrime p.asIdeal) S)
  let f2'' := Ideal.orderEmbeddingOfSurjective f2 hf2_surj
  let f1' : PrimeSpectrum (TensorProduct R (Localization.AtPrime p.asIdeal) S) ↪o PrimeSpectrum S :=
    OrderEmbedding.ofMapLEIff f1.specComap fun {p q} ↦
      f1''.map_rel_iff (a := p.asIdeal) (b := q.asIdeal)
  let f2' : PrimeSpectrum (TensorProduct R (p.asIdeal.ResidueField) S) ↪o
    PrimeSpectrum (TensorProduct R (Localization.AtPrime p.asIdeal) S) :=
      OrderEmbedding.ofMapLEIff f2.specComap fun {p q} ↦
        f2''.map_rel_iff (a := p.asIdeal) (b := q.asIdeal)
  suffices h : Set.range (f2'.trans f1') = (algebraMap R S).specComap ⁻¹' {p} by
    rw [← h]
    exact OrderEmbedding.orderIso
  apply subset_antisymm
  · rw [← Set.image_subset_iff, ← Set.range_comp]
    simp only [AlgHom.toRingHom_eq_coe, RelEmbedding.coe_trans, OrderEmbedding.coe_ofMapLEIff,
      Function.comp_apply, f2', f1', ← specComap_comp]
    let f3 : R →+* p.asIdeal.ResidueField := algebraMap _ _
    let f4 : p.asIdeal.ResidueField →+* TensorProduct R (p.asIdeal.ResidueField) S :=
      Algebra.TensorProduct.includeLeftRingHom
    have : ((RingHomClass.toRingHom f2).comp f1).comp (algebraMap R S) = f4.comp f3 := by
      show ((RingHomClass.toRingHom f2).comp f1).comp (algebraMap R S) =
        Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R (p.asIdeal.ResidueField))
      rw [Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
      rfl
    simp only [this, specComap_comp, f3]
    apply subset_trans (Set.range_comp_subset_range _ _)
    rw [PrimeSpectrum.residueField_specComap]
  · simp only [AlgHom.toRingHom_eq_coe, RelEmbedding.coe_trans, OrderEmbedding.coe_ofMapLEIff,
    Set.range_comp, show _ from by simpa using range_specComap_of_surjective _ _ hf2_surj, f2', f1']
    rintro ⟨q, hqp⟩ hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    have hq : Ideal.comap (algebraMap R S) q = p.asIdeal := by
      simpa using congr(PrimeSpectrum.asIdeal $hq)
    simp only [AlgHom.toRingHom_eq_coe, OrderEmbedding.coe_ofMapLEIff, Set.mem_image, mem_zeroLocus,
      SetLike.coe_subset_coe, mk.injEq, f1']
    let iso := (IsLocalization.orderIsoOfPrime (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
      (TensorProduct R (Localization.AtPrime p.asIdeal) S)).symm
    have hq' : Disjoint ((Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) : Set S) q :=
      Disjoint.symm <| by
        apply Ideal.disjoint_map_primeCompl_iff_comap_le.mpr
        rw [hq]
    let q' := iso ⟨q, ⟨hqp, hq'⟩⟩
    refine ⟨⟨q'.val, q'.prop⟩, ?_, congr($(iso.left_inv ⟨q, ⟨hqp, hq'⟩⟩).val)⟩
    have aux1 : RingHom.ker (RingHomClass.toRingHom f2) =
      Ideal.map Algebra.TensorProduct.includeLeft (RingHom.ker f2r) :=
        Algebra.TensorProduct.rTensor_ker f2r hf2r_surj
    have aux2 : RingHom.ker f2r = IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) :=
      Ideal.Quotient.mkₐ_ker R _
    rw [aux1, aux2]
    apply Ideal.map_le_of_le_comap <| le_of_eq <| Eq.symm <|
      Localization.AtPrime.eq_maximalIdeal_iff_comap_eq.mp _
    have aux3 : Ideal.comap Algebra.TensorProduct.includeRight q'.val = q :=
      congr($(iso.left_inv ⟨q, ⟨hqp, hq'⟩⟩).val)
    conv_rhs => rw [← hq, ← aux3]
    nth_rw 2 [← Ideal.comap_coe]
    nth_rw 4 [← Ideal.comap_coe]
    simp [Ideal.comap_comap]

theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim (Polynomial R) ≤ 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim, ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' C.specComap ?_ (fun p ↦ ?_)
  · exact fun {a b} h ↦ Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoTensorResidueField R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.KrullDimLE_iff_ringKrullDim_le]
    infer_instance
