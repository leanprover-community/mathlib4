/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable

/-! # Instances on residue fields -/

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (p : Ideal A) (q : Ideal B) [q.LiesOver p]

attribute [local instance] Ideal.Quotient.field

instance [p.IsMaximal] [q.IsMaximal] [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra]

instance [p.IsMaximal] [q.IsMaximal] [Algebra.IsSeparable p.ResidueField q.ResidueField] :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ q) := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.symm <| .ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.symm <| .ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  obtain ⟨x, rfl⟩ :=
    (RingEquiv.ofBijective _ p.bijective_algebraMap_quotient_residueField).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply (RingEquiv.ofBijective _ q.bijective_algebraMap_quotient_residueField).injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.apply_symm_apply]
  simp [RingHom.algebraMap_toAlgebra]

variable {p q} in
lemma Algebra.isSeparable_residueField_iff [p.IsMaximal] [q.IsMaximal] :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

instance [p.IsPrime] : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
  IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))

instance [p.IsPrime] [q.IsPrime] [Algebra.IsIntegral A B] :
    Algebra.IsAlgebraic p.ResidueField q.ResidueField := by
  have : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) :=
    .tower_top A
  letI := ((algebraMap (B ⧸ q) q.ResidueField).comp (algebraMap (A ⧸ p) (B ⧸ q))).toAlgebra
  haveI : IsScalarTower (A ⧸ p) (B ⧸ q) q.ResidueField := .of_algebraMap_eq' rfl
  haveI : Algebra.IsAlgebraic (A ⧸ p) q.ResidueField := .trans _ (B ⧸ q) _
  haveI : IsScalarTower (A ⧸ p) p.ResidueField q.ResidueField := by
    refine .of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [RingHom.algebraMap_toAlgebra]
  refine .extendScalars (Ideal.injective_algebraMap_quotient_residueField p)
