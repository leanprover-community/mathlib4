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

variable (p : Ideal A) [p.IsMaximal] (q : Ideal B) [q.IsMaximal] [q.LiesOver p]

attribute [local instance] Ideal.Quotient.field

instance [Algebra.IsSeparable (A ⧸ p) (B ⧸ q)] :
    Algebra.IsSeparable p.ResidueField q.ResidueField := by
  refine Algebra.IsSeparable.of_equiv_equiv
    (.ofBijective _ p.bijective_algebraMap_quotient_residueField)
    (.ofBijective _ q.bijective_algebraMap_quotient_residueField) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]

instance [Algebra.IsSeparable p.ResidueField q.ResidueField] :
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
  simp [RingHom.algebraMap_toAlgebra, Algebra.ofId_apply]

lemma Algebra.isSeparable_residueField_iff
    {p : Ideal A} [p.IsMaximal] {q : Ideal B} [q.IsMaximal] [q.LiesOver p] :
    Algebra.IsSeparable p.ResidueField q.ResidueField ↔ Algebra.IsSeparable (A ⧸ p) (B ⧸ q) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩
