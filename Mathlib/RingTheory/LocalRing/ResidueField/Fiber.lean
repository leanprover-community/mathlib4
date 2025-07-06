/-
Copyright (c) 2025 Jingting Wang, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Junyan Xu
-/
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The fiber of a ring homomorphism at a prime ideal

## Main results

* `PrimeSpectrum.preimageOrderIsoTensorResidueField` : We show that there is an `OrderIso` between
  fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal `p : PrimeSpectrum R` and
  the prime spectrum of the tensor product of `S` and the residue field of `p`.
-/

open Algebra TensorProduct in
/-- The `OrderIso` between fiber of a ring homomorphism `algebraMap R S : R →+* S` at a prime ideal
 `p : PrimeSpectrum R` and the prime spectrum of the tensor product of `S` and the residue field of
 `p`. -/
noncomputable def PrimeSpectrum.preimageOrderIsoTensorResidueField (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] (p : PrimeSpectrum R) :
    (algebraMap R S).specComap ⁻¹' {p} ≃o
      PrimeSpectrum (p.asIdeal.ResidueField ⊗[R] S) := by
  let Rp := Localization.AtPrime p.asIdeal
  refine .trans ?_ <| comapEquiv
    ((Algebra.TensorProduct.comm ..).trans <| cancelBaseChange R Rp ..).toRingEquiv
  refine .trans (.symm ((Ideal.primeSpectrumQuotientOrderIsoZeroLocus _).trans ?_)) <|
    comapEquiv (quotIdealMapEquivTensorQuot ..).toRingEquiv
  letI := rightAlgebra (R := R) (A := Rp) (B := S)
  let e := IsLocalization.primeSpectrumOrderIso
    (algebraMapSubmonoid S p.asIdeal.primeCompl) (Rp ⊗[R] S) |>.trans <|
    .setCongr _ {q | (algebraMap R S).specComap q ≤ p} <| Set.ext fun _ ↦
      disjoint_comm.trans (Ideal.disjoint_map_primeCompl_iff_comap_le ..)
  have {q : PrimeSpectrum (Rp ⊗[R] S)} :
      q ∈ zeroLocus ((IsLocalRing.maximalIdeal _).map (algebraMap Rp (Rp ⊗[R] S))) ↔
      p ≤ (algebraMap R S).specComap (e q) := by
    rw [mem_zeroLocus, SetLike.coe_subset_coe, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, Ideal.map_le_iff_le_comap, show algebraMap Rp _ = includeLeftRingHom from rfl,
      includeLeftRingHom_comp_algebraMap]; rfl
  exact
  { toFun q := ⟨e q, (e q).2.antisymm (this.mp q.2)⟩
    invFun q := ⟨e.symm ⟨q, q.2.le⟩, this.mpr <| by rw [e.apply_symm_apply]; exact q.2.ge⟩
    left_inv q := Subtype.ext (e.left_inv q)
    right_inv q := Subtype.ext <| by apply Subtype.ext_iff.mp (e.right_inv ⟨q, q.2.le⟩)
    map_rel_iff' := e.map_rel_iff }
