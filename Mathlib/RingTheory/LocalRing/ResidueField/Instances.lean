/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

import Mathlib.RingTheory.Finiteness.Quotient

/-! # Instances on residue fields -/

@[expose] public section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (p : Ideal A) (q : Ideal B) [q.LiesOver p]

section maximal

variable [p.IsMaximal] [q.IsMaximal] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

attribute [local instance] Ideal.Quotient.field

instance [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

instance [p.IsMaximal] [q.IsMaximal] [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ q) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  apply RingHom.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]

variable {p q} in
lemma Algebra.isSeparable_residueField_iff :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end maximal

section prime

variable [p.IsPrime] [q.IsPrime] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
  [Localization.AtPrime.IsLiesOverAlgebra p q]

instance : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

instance [Algebra.IsIntegral A B] :
    Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  letI := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  haveI : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  haveI : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  haveI : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)

end prime

namespace IsLocalRing

variable {R k : Type*} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k]

instance ResidueField.algebraOfIsIntegral [Algebra.IsIntegral R k] : Algebra (ResidueField R) k :=
  fast_instance% (Ideal.Quotient.lift (maximalIdeal R) (algebraMap R k)
    (by simp [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k)])).toAlgebra

instance ResidueField.isScalarTowerOfIsIntegral [Algebra.IsIntegral R k] :
    IsScalarTower R (ResidueField R) k :=
  .of_algebraMap_eq fun _ ↦ rfl

instance [Module.Finite R k] : Module.Finite (ResidueField R) k := .of_equiv_equiv
  (Ideal.quotEquivOfEq (show Ideal.comap (algebraMap R k) ⊥ = maximalIdeal R by
    rw [← eq_maximalIdeal (Algebra.ker_algebraMap_isMaximal_of_isIntegral R k), RingHom.ker]))
  (RingEquiv.quotientBot k) (by ext; rfl)

end IsLocalRing
