/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

/-!

# Some Lemma About Formally Smooth Under Quotient

In this file, we formalize the result [Stacks 031L] : For flat ring homomorphism `f : R →+* S`,
`I` an ideal of `R` which is square zero, if `R ⧸ I →+* S ⧸ IS` is formally smooth, so do `f`.

-/

@[expose] public section

open IsLocalRing

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

section

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma IsBaseChange.surjective_of_surjective {M : Type*} [AddCommGroup M] [Module R M]
    {R' M' : Type*} [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R' M']
    [Module R M'] [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (isb : IsBaseChange R' f)
    (surj : Function.Surjective (algebraMap R R')) : Function.Surjective f := by
  rw [isb.eq_rTensor_comp]
  exact ((isb.equiv.restrictScalars R).surjective.comp (LinearMap.rTensor_surjective M surj)).comp
    (LinearEquiv.surjective _)

lemma IsBaseChange.ker_of_surjective {M : Type*} [AddCommGroup M] [Module R M]
    {R' M' : Type*} [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R' M']
    [Module R M'] [IsScalarTower R R' M'] {f : M →ₗ[R] M'} (isb : IsBaseChange R' f)
    (surj : Function.Surjective (algebraMap R R')) :
    f.ker = (RingHom.ker (algebraMap R R')) • (⊤ : Submodule R M) := by
  rw [isb.eq_rTensor_comp, LinearMap.comp_assoc, LinearEquiv.ker_comp, LinearMap.ker_comp]
  have exac : Function.Exact (RingHom.ker (algebraMap R R')).subtype _ :=
    (Algebra.linearMap R R').exact_subtype_ker_map
  rw [LinearMap.exact_iff.mp (rTensor_exact M exac surj), ← Submodule.map_equiv_eq_comap_symm,
    ← LinearMap.range_comp, Ideal.subtype_rTensor_range]

lemma LinearMap.ker_inf_smul_top_eq_smul_of_flat (I : Ideal R) (f : M →ₗ[R] N)
    (surj : Function.Surjective f) [Module.Flat R N] :
    f.ker ⊓ (I • (⊤ : Submodule R M)) = I • f.ker := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rcases (Submodule.ext_iff.mp (I.subtype_rTensor_range M) x).mpr hx.2 with ⟨y, hy⟩
    have inj : Function.Injective ((TensorProduct.lid R N).comp (I.subtype.rTensor N)) := by
      simpa using Module.Flat.iff_rTensor_injective'.mp ‹_› I
    have comm1 : ((TensorProduct.lid R N).comp (I.subtype.rTensor N)).comp (f.lTensor I) =
      f.comp ((TensorProduct.lid R M).comp (I.subtype.rTensor M)) := by
      ext
      simp
    have eq0 : f.lTensor I y = 0 := by
      apply inj
      rw [map_zero, ← LinearMap.comp_apply, comm1, LinearMap.comp_apply, hy, f.mem_ker.mp hx.1]
    rcases ((lTensor_exact I (f.exact_subtype_ker_map) surj) y).mp eq0 with ⟨z, hz⟩
    have comm2 : ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).comp
      (f.ker.subtype.lTensor I) = f.ker.subtype.comp
      ((TensorProduct.lid R f.ker).comp (I.subtype.rTensor f.ker)) := by
      ext
      simp
    apply (Submodule.mem_smul_top_iff I f.ker ⟨x, hx.1⟩).mp
    rw [← Ideal.subtype_rTensor_range]
    use z
    apply f.ker.subtype_injective
    rw [← LinearMap.comp_apply, ← comm2, LinearMap.comp_apply, hz, hy, Submodule.subtype_apply]
  · induction hx using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [LinearMap.mem_ker.mp hm] using Submodule.smul_mem_smul hr Submodule.mem_top
    | add y ymem z zmem hy hz => exact add_mem hy hz

end

/-- For flat ring homomorphism `f : R →+* S`, `I` an ideal of `R` which is square zero,
if `R ⧸ I →+* S ⧸ IS` is formally smooth, so do `f`. -/
@[stacks 031L]
lemma RingHom.FormallySmooth.of_surjective_of_isBaseChange_of_flat {S : Type v} [CommRing S]
    [Algebra R S] {R' S' : Type*} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra R' S']
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [Module.Flat R S] (surj : Function.Surjective (algebraMap R R'))
    (sq0 : (RingHom.ker (algebraMap R R')) ^ 2 = ⊥) [isp : Algebra.IsPushout R R' S S']
    (smoothq : Algebra.FormallySmooth R' S') : Algebra.FormallySmooth R S := by
  let P := (Algebra.Generators.self R S).toExtension
  let : Algebra.FormallySmooth R P.Ring := Algebra.mvPolynomial S
  let IP := (RingHom.ker (algebraMap R R')).map (algebraMap R P.Ring)
  have surjS : Function.Surjective (algebraMap S S') := isp.1.surjective_of_surjective surj
  let Gen : Algebra.Generators R' S' S := {
    val := algebraMap S S'
    σ' := fun s' ↦ MvPolynomial.X (Classical.choose (surjS s'))
    aeval_val_σ' s' := by simp [Classical.choose_spec (surjS s')] }
  let P' := Gen.toExtension
  let : Algebra.FormallySmooth R' P'.Ring := Algebra.mvPolynomial S
  let : Algebra P.Ring P'.Ring := MvPolynomial.algebraMvPolynomial
  let : IsScalarTower R P.Ring P'.Ring :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (MvPolynomial.map_C _ x).symm)
  algebraize [(algebraMap S S').comp (algebraMap P.Ring S)]
  have : IsScalarTower P.Ring P'.Ring S' := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    change (algebraMap S S') (MvPolynomial.aeval _root_.id x) =
      MvPolynomial.aeval Gen.val (MvPolynomial.map (algebraMap R R') x)
    rw [← MvPolynomial.aeval_algebraMap_apply]
    simp [MvPolynomial.aeval_map_algebraMap, Gen]
  let J := RingHom.ker (algebraMap P.Ring S)
  let J' := RingHom.ker (algebraMap P'.Ring S')
  let I := RingHom.ker (algebraMap R R')
  let IS := I.map (algebraMap R S)
  have kerS : RingHom.ker (algebraMap S S') = IS := by
    apply Submodule.restrictScalars_injective R
    rw [← Ideal.smul_top_eq_map, ← isp.1.ker_of_surjective surj]
    rfl
  let IP := I.map (algebraMap R P.Ring)
  have kerP : RingHom.ker (algebraMap P.Ring P'.Ring) = IP := MvPolynomial.ker_map _
  have surjPP' : Function.Surjective (algebraMap P.Ring P'.Ring) :=
    MvPolynomial.map_surjective _ surj
  have ISeq : IS = IP.map (algebraMap P.Ring S) := by
    simp [IP, IS, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  classical
  have surjP : Function.Surjective (algebraMap P.Ring S) := fun x ↦ ⟨P.σ x, P.algebraMap_σ x⟩
  apply (Algebra.FormallySmooth.iff_split_injection surjP).mpr
  have surjP' : Function.Surjective (algebraMap P'.Ring S') := fun x ↦ ⟨P'.σ x, P'.algebraMap_σ x⟩
  rcases (Algebra.FormallySmooth.iff_split_injection surjP').mp smoothq with ⟨σ, hσ⟩
  have infeq : IP ⊓ J = IP * J := by
    refine le_antisymm (fun x hx ↦ ?_) Ideal.mul_le_inf
    have : x ∈ I • (J.restrictScalars R) := by
      change x ∈ I • (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.ker
      rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat I _ surjP]
      simpa using ⟨hx.2, hx.1⟩
    simpa [← Ideal.smul_restrictScalars I J, Submodule.restrictScalars_mem] using this
  have comapJ' : J'.comap (algebraMap P.Ring P'.Ring) = IP ⊔ J := by
    change J'.comap (algebraMap P.Ring P'.Ring) = _
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq _ S,
      ← RingHom.comap_ker]
    simp [kerS, ISeq, Ideal.comap_map_of_surjective' _ surjP, J]
  have Jle : J ≤ J'.comap (algebraMap P.Ring P'.Ring) := le_of_le_of_eq le_sup_right comapJ'.symm
  have exist_in_J {x : P'.Ring} (memJ' : x ∈ J') : ∃ y ∈ J, (algebraMap P.Ring P'.Ring) y = x := by
    rcases surjPP' x with ⟨x', hx'⟩
    rw [← hx', ← Ideal.mem_comap, comapJ'] at memJ'
    rcases Submodule.mem_sup.mp memJ' with ⟨y, hy, z, hz, hyz⟩
    use z, hz
    simpa [← hx', ← hyz, ← RingHom.mem_ker, kerP] using hy
  have J'eqmap : J' = J.map (algebraMap P.Ring P'.Ring) := by
    refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.mpr Jle)
    rcases exist_in_J hx with ⟨y, mem, hy⟩
    simpa [← hy] using Ideal.mem_map_of_mem _ mem
  let mapcot := Ideal.mapCotangent J J' (Algebra.ofId P.Ring P'.Ring) Jle
  have cotsurj : Function.Surjective mapcot := by
    intro x
    rcases J'.toCotangent_surjective x with ⟨x', hx'⟩
    rcases exist_in_J x'.2 with ⟨y', mem, hy'⟩
    use J.toCotangent ⟨y', mem⟩
    simpa [mapcot, ← hx'] using J'.toCotangent.congr_arg (SetCoe.ext hy')
  have cotker : LinearMap.ker mapcot = (Submodule.comap J.subtype (IP * J)).map J.toCotangent := by
    refine le_antisymm (fun x hx ↦ ?_) ?_
    · rcases J.toCotangent_surjective x with ⟨x', hx'⟩
      have : Function.Surjective (Algebra.ofId P.Ring P'.Ring) := surjPP'
      simp only [← hx', LinearMap.mem_ker, Ideal.mapCotangent_toCotangent,
        Ideal.toCotangent_eq_zero, mapcot, J'eqmap, Algebra.ofId_apply] at hx
      rw [← Ideal.map_pow, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ surjPP'] at hx
      rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, hyz⟩
      have : y + z ∈ J := by simp [hyz]
      have zmemJ := (Ideal.add_mem_iff_right J (Ideal.pow_le_self (by omega) hy)).mp this
      have zmem : z ∈ IP * J := by simpa [← infeq, Ideal.mem_inf] using ⟨le_of_eq kerP hz, zmemJ⟩
      have xeq : x = J.toCotangent ⟨z, zmemJ⟩ := by simpa [← hx', J.toCotangent_eq, ← hyz] using hy
      rw [xeq]
      exact Submodule.mem_map_of_mem (Submodule.mem_comap.mpr zmem)
    · rw [Submodule.map_le_iff_le_comap, ← LinearMap.ker_comp]
      intro x hx
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, mapcot]
      convert map_zero J'.toCotangent
      exact le_of_eq kerP.symm (Ideal.mul_le_right hx)
  let cottoTen := KaehlerDifferential.kerCotangentToTensor R P.Ring S
  let cottoTen' := KaehlerDifferential.kerCotangentToTensor R' P'.Ring S'
  let mapTen : TensorProduct P.Ring S Ω[P.Ring⁄R] →ₗ[P.Ring]
    TensorProduct P'.Ring S' Ω[P'.Ring⁄R'] :=
    TensorProduct.lift ((((TensorProduct.mk P'.Ring S' Ω[P'.Ring⁄R']).restrictScalars₁₂
      P.Ring P.Ring).compl₂ (KaehlerDifferential.map R R' P.Ring P'.Ring)).comp
      (IsScalarTower.toAlgHom P.Ring S S').toLinearMap)
  have comm : (cottoTen'.restrictScalars P.Ring).comp mapcot = mapTen.comp cottoTen := by
    set_option backward.isDefEq.respectTransparency false in
    ext x
    rcases Ideal.toCotangent_surjective _ x with ⟨y, hy⟩
    simp only [← hy, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, mapcot]
    change (KaehlerDifferential.kerToTensor R' P'.Ring S')
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
    have IPsq : IP * IP = ⊥ := by simp [← pow_two, IP, ← Ideal.map_pow, I, sq0]
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
