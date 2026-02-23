/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!

# Some Lemma About Formally Smooth Under Quotient

-/

@[expose] public section

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

lemma RingHom.FormallySmooth.of_quotient_of_flat {S : Type v} [CommRing S] (f : R →+* S)
    {I : Ideal R} (sq0 : I ^ 2 = ⊥) (flat : f.Flat)
    (smoothq : (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FormallySmooth) :
    f.FormallySmooth := by
  let _ := f.toAlgebra
  let IS := I.map f
  let _ := (Ideal.quotientMap IS f Ideal.le_comap_map).toAlgebra
  let P := (Algebra.Generators.self R S).toExtension
  let _ : Algebra.FormallySmooth R P.Ring := Algebra.mvPolynomial _
  let IP := I.map (algebraMap R P.Ring)
  let _ : Algebra (R ⧸ I) (P.Ring ⧸ IP) :=
    (Ideal.quotientMap _ (algebraMap R P.Ring) Ideal.le_comap_map).toAlgebra
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq, RingHom.algebraMap_toAlgebra]
  let _ : Algebra (P.Ring ⧸ IP) (S ⧸ IS) :=
    (Ideal.quotientMap _ (algebraMap P.Ring S) (by
      simp [← Ideal.map_le_iff_le_comap, ISeq])).toAlgebra
  have _ : IsScalarTower (R ⧸ I) (P.Ring ⧸ IP) (S ⧸ IS) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext
    simp only [IS, IP, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, Ideal.quotientMap_mk,
      ← IsScalarTower.algebraMap_apply]
  let P' : Algebra.Extension (R ⧸ I) (S ⧸ IS) := {
    Ring := P.Ring ⧸ IP
    σ := fun x ↦ Ideal.Quotient.mk _ (P.σ (Classical.choose (Ideal.Quotient.mk_surjective x)))
    algebraMap_σ x := by
      simpa [IS, IP, RingHom.algebraMap_toAlgebra] using
        Classical.choose_spec (Ideal.Quotient.mk_surjective x) }
  let _ : IsScalarTower R (R ⧸ I) P'.Ring := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower P.Ring P'.Ring (S ⧸ IS) := IsScalarTower.of_algebraMap_eq' rfl
  let e' : P'.Ring ≃ₐ[R] MvPolynomial S (R ⧸ I) :=
    (MvPolynomial.quotientEquivQuotientMvPolynomial I).symm
  let e : P'.Ring ≃ₐ[R ⧸ I] MvPolynomial S (R ⧸ I) :=
    e'.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective R I)
  let _ : Algebra.FormallySmooth (R ⧸ I) P'.Ring := Algebra.FormallySmooth.of_equiv e.symm
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring (S ⧸ IS))
  classical
  have infeq : IP ⊓ J = IP * J := by
    --this needs `S` being flat
    sorry
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x ↦ ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring (S ⧸ I.map f)) :=
    fun x ↦ ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have comapJ' : J'.comap (Ideal.Quotient.mkₐ P.Ring IP) = IP ⊔ J := by
    change J'.comap (algebraMap P.Ring P'.Ring) = _
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ S,
      ← RingHom.comap_ker]
    simp [ISeq, Ideal.comap_map_of_surjective' _ surjP, J]
  have Jle : J ≤ J'.comap (Ideal.Quotient.mkₐ P.Ring IP) := le_of_le_of_eq le_sup_right comapJ'.symm
  have exist_in_J {x : P'.Ring} (memJ' : x ∈ J') : ∃ y ∈ J, Ideal.Quotient.mkₐ P.Ring IP y = x := by
    rcases Ideal.Quotient.mkₐ_surjective P.Ring IP x with ⟨x', hx'⟩
    rw [← hx', ← Ideal.mem_comap, comapJ'] at memJ'
    rcases Submodule.mem_sup.mp memJ' with ⟨y, hy, z, hz, hyz⟩
    use z, hz
    simpa [← hx', ← hyz] using Ideal.Quotient.eq_zero_iff_mem.mpr hy
  have J'eqmap : J' = J.map (Ideal.Quotient.mkₐ P.Ring IP) := by
    refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr Jle)
    rcases exist_in_J hx with ⟨y, mem, hy⟩
    simpa [← hy] using Ideal.mem_map_of_mem _ mem
  let mapcot := Ideal.mapCotangent J J' (Ideal.Quotient.mkₐ P.Ring IP) Jle
  have cotsurj : Function.Surjective mapcot := by
    intro x
    rcases J'.toCotangent_surjective x with ⟨x', hx'⟩
    rcases exist_in_J x'.2 with ⟨y', mem, hy'⟩
    use J.toCotangent ⟨y', mem⟩
    simpa [mapcot, ← hx'] using J'.toCotangent.congr_arg (SetCoe.ext hy')
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
      simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
        Ideal.toCotangent_eq_zero, mapcot, J'eqmap] at hx
      rw [← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _
        (Ideal.Quotient.mkₐ_surjective _ _)] at hx
      rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
      have : y + z ∈ J := by simp [hyz]
      have zmemJ := (Ideal.add_mem_iff_right J (Ideal.pow_le_self (by omega) hy)).mp this
      have zmem : z ∈ IP * J := by
        simpa [← infeq, Ideal.mem_inf] using ⟨Ideal.Quotient.eq_zero_iff_mem.mp hz, zmemJ⟩
      have xeq : x = J.toCotangent ⟨z, zmemJ⟩ := by simpa [← hx', J.toCotangent_eq, ← hyz] using hy
      rw [xeq]
      exact Submodule.mem_map_of_mem (Submodule.mem_comap.mpr zmem)
    · rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp]
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, mapcot]
      convert map_zero J'.toCotangent
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_le_right hx)
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor (R ⧸ I) P'.Ring (S ⧸ IS)
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] →ₗ[P.Ring]
    TensorProduct P'.Ring (S ⧸ IS) Ω[P'.Ring⁄R ⧸ I] :=
    TensorProduct.lift ((((TensorProduct.mk P'.Ring (S ⧸ IS) Ω[P'.Ring⁄R ⧸ I]).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R (R ⧸ I) P.Ring P'.Ring)).comp
      (Ideal.Quotient.mkₐ P.Ring IS).toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    set_option backward.isDefEq.respectTransparency false in
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, hy⟩
    simp only [← hy, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, mapcot]
    change (KaehlerDifferential.kerToTensor (R ⧸ I) P'.Ring (S ⧸ IS))
      ⟨(algebraMap P.Ring P'.Ring) y.1, Jle y.2⟩ =
      mapTen ((KaehlerDifferential.kerToTensor R P.Ring S) y)
    simp [KaehlerDifferential.kerToTensor, mapTen]
  let ediff : Ω[P.Ring⁄R] ≃ₗ[P.Ring] S →₀ P.Ring := KaehlerDifferential.mvPolynomialEquiv R S
  let eTen : TensorProduct P.Ring S Ω[P.Ring⁄R] ≃ₗ[P.Ring] (S →₀ S) :=
    ((ediff.lTensor S).trans (TensorProduct.finsuppRight P.Ring P.Ring _ _ S)).trans
    (Finsupp.mapRange.linearEquiv (TensorProduct.rid P.Ring _))
  let toJ'cot : (S →₀ S) →ₗ[P.Ring] J'.Cotangent :=
    ((σ.restrictScalars P.Ring).comp mapTen).comp eTen.symm.toLinearMap
  let eS : (P.Ring ⧸ J) ≃ₗ[P.Ring] S :=
    (Submodule.quotEquivOfEq _ _ (by ext; simp [J])).trans
    ((Algebra.linearMap P.Ring S).quotKerEquivOfSurjective surjP)
  let _ : IsScalarTower P.Ring (P.Ring ⧸ J) J.Cotangent := Module.IsTorsionBySet.isScalarTower _
  let toJcot : (S →₀ S) →ₗ[P.Ring] J.Cotangent :=
    Finsupp.lsum P.Ring (fun s ↦ ((LinearMap.toSpanSingleton (P.Ring ⧸ J) J.Cotangent
      (Classical.choose (cotsurj (toJ'cot (Finsupp.single s 1))))).restrictScalars P.Ring).comp
      eS.symm.toLinearMap)
  have toJcot_spec : mapcot.comp toJcot = toJ'cot := by
    ext i s
    simp only [LinearMap.comp_assoc, toJcot, Finsupp.lsum_comp_lsingle]
    rcases Ideal.Quotient.mk_surjective (eS.symm s) with ⟨p, hp⟩
    have (x : J.Cotangent) : mapcot (eS.symm s • x) = p • mapcot x := by
      rw [← map_smul, ← hp]
      rfl
    have psmul : p • 1 = s := by simpa [Algebra.smul_def, eS] using eS.eq_symm_apply.mp hp
    simp [this, Classical.choose_spec (cotsurj (toJ'cot (Finsupp.single i 1))), ← map_smul, psmul]
  let σ' := toJcot.comp eTen.toLinearMap
  have σ'_spec' : mapcot.comp σ' = (σ.restrictScalars P.Ring).comp mapTen := by
    simp only [← LinearMap.comp_assoc, toJcot_spec, σ']
    apply LinearMap.ext (fun x ↦ ?_)
    exact ((σ.restrictScalars P.Ring).comp mapTen).congr_arg (eTen.symm_apply_apply x)
  have σ'_spec : mapcot.comp (σ'.comp cottoTen) = mapcot := by
    rw [← LinearMap.comp_assoc, σ'_spec', LinearMap.comp_assoc, ← comm, ← LinearMap.comp_assoc,
      ← LinearMap.restrictScalars_comp, hσ]
    rfl
  let Δ : J.Cotangent →ₗ[P.Ring] J.Cotangent := LinearMap.id - (σ'.comp cottoTen)
  have rΔle : Δ.range ≤ (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    rintro x ⟨y, hy⟩
    simp only [← cotker, ← hy, LinearMap.mem_ker, Δ]
    rw [LinearMap.sub_apply, map_sub, LinearMap.id_apply, ← LinearMap.comp_apply, σ'_spec, sub_self]
  have leΔk : (Submodule.comap J.subtype (IP * J)).map J.toCotangent ≤ Δ.ker := by
    have IPsq : IP * IP = ⊥ := by simp [← pow_two, IP, ← Ideal.map_pow, sq0]
    have {x : P.Ring} (h : x ∈ IP * J) : Δ (J.toCotangent ⟨x, Ideal.mul_le_left h⟩) = 0 := by
      induction h using Submodule.mul_induction_on' with
      | mem_mul_mem y hy z hz =>
        change Δ (J.toCotangent (y • ⟨z, hz⟩)) = 0
        rw [map_smul, map_smul]
        rcases Submodule.mem_map.mp (rΔle (Δ.mem_range_self (J.toCotangent ⟨z, hz⟩))) with
          ⟨w, hw, eqz⟩
        have := Ideal.mul_mem_mul hy (Submodule.mem_comap.mp hw)
        simp only [← mul_assoc, IPsq, Submodule.bot_mul, Submodule.mem_bot] at this
        have eq0 : y • w = 0 := SetCoe.ext this
        rw [← eqz, ← map_smul, eq0, map_zero]
      | add y ymem z zmem hy hz =>
        have : (⟨y + z, Ideal.mul_le_left (add_mem ymem zmem)⟩ : J) =
          ⟨y, Ideal.mul_le_left ymem⟩ + ⟨z, Ideal.mul_le_left zmem⟩ := rfl
        rw [this, map_add, map_add, hy, hz, add_zero]
    intro x hx
    rcases  Submodule.mem_map.mp hx with ⟨x', hx', eq⟩
    simpa [← eq] using this hx'
  let δ : J'.Cotangent →ₗ[P.Ring] J.Cotangent :=
    (Submodule.liftQ _ Δ (le_of_eq_of_le cotker leΔk)).comp
    (mapcot.quotKerEquivOfSurjective cotsurj).symm.toLinearMap
  have δ_spec : δ.comp mapcot = Δ := by
    ext
    simp [δ]
  use σ' + (δ.comp (σ.restrictScalars P.Ring)).comp mapTen
  change σ'.comp cottoTen + δ.comp ((σ.restrictScalars P.Ring).comp (mapTen.comp cottoTen)) = _
  rw [← comm, ← LinearMap.comp_assoc mapcot, ← LinearMap.restrictScalars_comp, hσ]
  exact add_eq_of_eq_sub' δ_spec
