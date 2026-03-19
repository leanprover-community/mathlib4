/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!

# Galois action on ideals

Let `L/K` be a Galois extension and let `G = Gal(L/K)` act on a ring `B` (e.g. the ring of
integers of `L`). This file collects results on the action of `G` on ideals of `B`.

## Main definitions

* `Ideal.stabilizerMapOfLiesOver`: For `F/K` a Galois subextension of `L/K`, the natural group
  homomorphism from the decomposition group of `P` in `Gal(L/K)` to the decomposition group
  of `p` in `Gal(F/K)` induced by the restriction.
* `Ideal.inertiaMapOfLiesOver`: For `F/K` a Galois subextension of `L/K`, the natural group
  homomorphism from the inertia group of `P` in `Gal(L/K)` to the inertia group
  of `p` in `Gal(F/K)` induced by the restriction.

## Main results

* `Ideal.stabilizerMapOfLiesOver_surjective`: The map `stabilizerMapOfLiesOver` is surjective.
* `Ideal.stabilizerMapOfLiesOver_ker`: The kernel of `stabilizerMapOfLiesOver` is the
  fixing subgroup of `E` intersected with the decomposition group of `P`.
* `Ideal.inertiaMapOfLiesOver_surjective`: The map `inertiaMapOfLiesOver` is surjective.
* `Ideal.inertiaMapOfLiesOver_ker`: The kernel of `inertiaMapOfLiesOver` is the fixing
  subgroup of `E` intersected with the inertia group of `P`.

-/

@[expose] public section

open Pointwise

namespace Ideal

open MulAction AlgEquiv

variable (K L : Type*) [Field K] [Field L] [Algebra K L] (F : Type*) [Field F]
  [Algebra K F] [Algebra F L] [IsScalarTower K F L]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra B L] [Algebra A L]
  [Algebra A F] [FaithfulSMul B L] [IsScalarTower A B L] [IsScalarTower A F L]
  [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L] [MulSemiringAction Gal(F/K) A]
  [SMulDistribClass Gal(F/K) A F]

variable (P : Ideal B) (p : Ideal A) [P.LiesOver p]

theorem restrictScalars_smul [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L]
    (σ : Gal(L/F)) : restrictScalars K σ • P = σ • P := by
  ext x
  have : (restrictScalars K σ)⁻¹ • x = σ⁻¹ • x := by
    apply FaithfulSMul.algebraMap_injective B L
    rw [algebraMap.smul', algebraMap.smul', AlgEquiv.smul_def, AlgEquiv.smul_def, coe_inv,
      coe_inv, restrictScalars_symm_apply]
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem, this]

variable [Normal K F]

theorem comap_smul_eq_restrictNormalHom_smul_comap (g : Gal(L/K)) :
    Ideal.comap (algebraMap A B) (g • P) =
      AlgEquiv.restrictNormalHom F g • Ideal.comap (algebraMap A B) P := by
  ext x
  rw [mem_comap, mem_pointwise_smul_iff_inv_smul_mem, mem_pointwise_smul_iff_inv_smul_mem,
    mem_comap, ← map_inv, AlgEquiv.algebraMap_restrictNormalHom_smul']

theorem smul_liesOver_of_restrictNormalHom_mem_stabilizer (σ : Gal(L/K))
    (hσ : restrictNormalHom F σ ∈ stabilizer Gal(F/K) p) :
    (σ • P).LiesOver p := by
  rw [liesOver_iff, under_def, Ideal.comap_smul_eq_restrictNormalHom_smul_comap K L F, ← under_def,
      ← over_def P p, hσ]

/--
The natural group homomorphism from the decomposition group of `P` in `Gal(L/K)` to the
decomposition group of `p` in `Gal(F/K)`, induced by the restriction homomorphism
`AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)`.
-/
@[simps! apply_coe]
noncomputable def stabilizerMapOfLiesOver :
    stabilizer Gal(L/K) P →* stabilizer Gal(F/K) p :=
  ((AlgEquiv.restrictNormalHom F).restrict _).codRestrict _
  (fun ⟨g, hg⟩ ↦ by
    have := congr_arg (Ideal.comap (algebraMap A B)) hg
    rwa [comap_smul_eq_restrictNormalHom_smul_comap K L F, ← under_def, ← over_def P p] at this)

theorem stabilizerMapOfLiesOver_surjective [IsFractionRing A F] [IsFractionRing B L]
    [IsGalois F L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B]
    [P.IsPrime] [IsGalois K L] [FiniteDimensional F L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] :
    Function.Surjective (Ideal.stabilizerMapOfLiesOver K L F P p) := by
  have : IsGaloisGroup Gal(L/F) A B := .of_isFractionRing _ _ _ F L
  intro ⟨g, hg⟩
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective L g
  have : (σ⁻¹ • P).LiesOver p := by
    apply smul_liesOver_of_restrictNormalHom_mem_stabilizer K L F P p
    rwa [map_inv, ← Subgroup.inv_mem_iff]
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P (σ⁻¹ • P) Gal(L/F)
  refine ⟨⟨σ * τ.restrictScalars K, ?_⟩, ?_⟩
  · rw [mem_stabilizer_iff, mul_smul, restrictScalars_smul, hτ, smul_inv_smul]
  · simp only [Subtype.ext_iff, stabilizerMapOfLiesOver_apply_coe, map_mul, mul_eq_left,
      AlgEquiv.ext_iff, one_apply]
    intro _
    apply FaithfulSMul.algebraMap_injective F L
    simp [restrictNormalHom]

set_option backward.isDefEq.respectTransparency false in
theorem stabilizerMapOfLiesOver_ker (E : IntermediateField K L) [Normal K E]
    [Algebra A E] [MulSemiringAction Gal(E/K) A] [SMulDistribClass Gal(E/K) A E]
    [IsScalarTower A E L] :
    (Ideal.stabilizerMapOfLiesOver K L E P p).ker =
      E.fixingSubgroup.subgroupOf (stabilizer Gal(L/K) P) := by
  unfold stabilizerMapOfLiesOver
  rw [MonoidHom.ker_codRestrict, MonoidHom.ker_restrict, IntermediateField.restrictNormalHom_ker]

/--
The natural group homomorphism from the inertia group of `P` in `Gal(L/K)` to the inertia group
of `p` in `Gal(F/K)`, induced by the restriction homomorphism
`AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K)`.
-/
@[simps! apply_coe]
noncomputable def inertiaMapOfLiesOver :
    inertia Gal(L/K) P →* inertia Gal(F/K) p :=
  ((AlgEquiv.restrictNormalHom F).restrict _).codRestrict _
  (fun ⟨g, hg⟩ ↦ fun x ↦ by
    rw [over_def P p, under_def, MonoidHom.restrict_apply, Submodule.mem_toAddSubgroup, mem_comap,
      map_sub, algebraMap_restrictNormalHom_smul']
    exact hg (algebraMap A B x))

attribute [instance] Ideal.Quotient.field

set_option backward.isDefEq.respectTransparency false in
theorem inertiaMapOfLiesOver_surjective {R : Type*} [CommRing R] [IsIntegrallyClosed R]
    [Algebra R K] [Algebra R B] [Algebra R L] [Algebra R A] [Algebra.IsIntegral R B]
    [IsFractionRing R K] [IsScalarTower R A B] [IsFractionRing A F] [IsFractionRing B L]
    [IsScalarTower R K L] [IsScalarTower R B L] [IsGalois F L] [IsGalois K L]
    [IsIntegrallyClosed A] [Algebra.IsIntegral A B] (p₀ : Ideal R) [P.IsMaximal] [P.LiesOver p₀]
    [FiniteDimensional F L] [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L] :
    Function.Surjective (Ideal.inertiaMapOfLiesOver K L F P p) := by
  have : IsGaloisGroup Gal(L/K) R B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup Gal(L/F) A B := .of_isFractionRing _ _ _ F L
  have : p.IsMaximal := IsMaximal.of_isMaximal_liesOver P p
  have : p₀.IsMaximal := IsMaximal.of_isMaximal_liesOver P p₀
  intro ⟨g, hg⟩
  obtain ⟨σ, hσ⟩ := stabilizerMapOfLiesOver_surjective K L F P p ⟨g, inertia_le_stabilizer _ hg⟩
  have hσ' : restrictNormalHom F σ.val = g := by simpa using congr_arg Subtype.val hσ
  have : p.LiesOver p₀ := LiesOver.tower_bot P p p₀
  let σ' : Gal((B ⧸ P) / (A ⧸ p)) := by
    refine AlgEquiv.ofRingEquiv
      (f := ((IsFractionRing.stabilizerHom _ p₀ P (R ⧸ p₀) (B ⧸ P) σ)).toRingEquiv) fun q ↦ ?_
    refine Quotient.inductionOn' q fun x ↦ ?_
    have := IsFractionRing.stabilizerHom_algebraMap_mk Gal(L/K) p₀ P (R ⧸ p₀) (B ⧸ P) σ
      (algebraMap A B x)
    simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at this
    rw [show Quotient.mk'' x = Quotient.mk p x by rfl, Quotient.algebraMap_mk_of_liesOver,
      coe_ringEquiv', this, Quotient.mk_eq_mk_iff_sub_mem,
      show σ.val • (algebraMap A B) x = algebraMap A B (g • x) by
        rw [← hσ', algebraMap_restrictNormalHom_smul'],
      ← map_sub, ← Ideal.mem_comap, ← under_def, ← over_def P p]
    exact hg x
  obtain ⟨⟨τ, hτ⟩, hτ'⟩ := IsFractionRing.stabilizerHom_surjective Gal(L/F) p P (A ⧸ p) (B ⧸ P) σ'⁻¹
  refine ⟨⟨σ.val * τ.restrictScalars K, fun x ↦ ?_⟩, ?_⟩
  · suffices τ • x - σ⁻¹ • x ∈ P by
      rw [Submodule.mem_toAddSubgroup, ← smul_mem_pointwise_smul_iff (a := σ⁻¹), smul_sub, mul_smul,
        ← subgroup_smul_def, inv_smul_smul]
      convert this using 2
      · exact mem_stabilizer_iff.mp <| (Subgroup.inv_mem_iff _).mpr σ.prop
      · apply FaithfulSMul.algebraMap_injective B L
        rw [algebraMap.smul', algebraMap.smul', AlgEquiv.smul_def, AlgEquiv.smul_def,
          restrictScalars_apply]
    rw [← Quotient.mk_eq_mk_iff_sub_mem]
    have := IsFractionRing.stabilizerHom_algebraMap_mk Gal(L/K) p₀ P (R ⧸ p₀) (B ⧸ P) σ⁻¹ x
    simp only [map_inv, Algebra.algebraMap_self, RingHomCompTriple.comp_apply,
      ← subgroup_smul_def] at this
    rw [← this]
    have := IsFractionRing.stabilizerHom_algebraMap_mk Gal(L/F) p P (A ⧸ p) (B ⧸ P) ⟨τ, hτ⟩ x
    simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply] at this
    rw [← this]
    exact AlgEquiv.congr_fun hτ' x
  · simp only [Subtype.ext_iff, inertiaMapOfLiesOver_apply_coe, map_mul, hσ', mul_eq_left,
      AlgEquiv.ext_iff, one_apply]
    intro _
    apply FaithfulSMul.algebraMap_injective F L
    simp [restrictNormalHom]

set_option backward.isDefEq.respectTransparency false in
theorem inertiaMapOfLiesOver_ker (E : IntermediateField K L) [Normal K E] [Algebra A E]
    [MulSemiringAction Gal(E/K) A] [SMulDistribClass Gal(E/K) A E] [IsScalarTower A E L] :
    (Ideal.inertiaMapOfLiesOver K L E P p).ker =
      E.fixingSubgroup.subgroupOf (inertia Gal(L/K) P) := by
  unfold inertiaMapOfLiesOver
  rw [MonoidHom.ker_codRestrict, MonoidHom.ker_restrict, IntermediateField.restrictNormalHom_ker]

end Ideal
