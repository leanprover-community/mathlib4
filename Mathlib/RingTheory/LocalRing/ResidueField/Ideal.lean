/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The residue field of a prime ideal

We define `Ideal.ResidueField I` to be the residue field of the local ring `Localization.Prime I`,
and provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.

-/

variable {R A} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R) [I.IsPrime]

/--
The residue field at a prime ideal, defined to be the residue field of the local ring
`Localization.Prime I`.
We also provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.
-/
abbrev Ideal.ResidueField : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

/-- If `I = f⁻¹(J)`, then there is an canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
abbrev Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (f : R →+* A) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

/-- If `I = f⁻¹(J)`, then there is an canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
def Ideal.ResidueField.mapₐ (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (hf : I = J.comap (algebraMap R A)) : I.ResidueField →ₐ[R] J.ResidueField where
  __ := Ideal.ResidueField.map I J (algebraMap R A) hf
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
      IsLocalRing.ResidueField.algebraMap_eq]
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
    rfl

@[simp] lemma Ideal.ResidueField.mapₐ_apply (I : Ideal R) [I.IsPrime] (J : Ideal A) [J.IsPrime]
    (hf : I = J.comap (algebraMap R A)) (x) :
    Ideal.ResidueField.mapₐ I J hf x = Ideal.ResidueField.map I J _ hf x := rfl

variable {I} in
@[simp high] -- marked `high` to override the more general `FaithfulSMul.algebraMap_eq_zero_iff`
lemma Ideal.algebraMap_residueField_eq_zero {x} :
    algebraMap R I.ResidueField x = 0 ↔ x ∈ I := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I),
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _

@[simp high] -- marked `high` to override the more general `FaithfulSMul.ker_algebraMap_eq_bot`
lemma Ideal.ker_algebraMap_residueField :
    RingHom.ker (algebraMap R I.ResidueField) = I :=
  Ideal.ext fun _ ↦ Ideal.algebraMap_residueField_eq_zero

attribute [-instance] IsLocalRing.ResidueField.field in
noncomputable instance : Algebra (R ⧸ I) I.ResidueField :=
  (Ideal.Quotient.liftₐ I (Algebra.ofId _ _)
    fun _ ↦ Ideal.algebraMap_residueField_eq_zero.mpr).toRingHom.toAlgebra

instance : IsScalarTower R (R ⧸ I) I.ResidueField :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

@[simp]
lemma algebraMap_mk (x) :
    algebraMap (R ⧸ I) I.ResidueField (Ideal.Quotient.mk _ x) =
    algebraMap R I.ResidueField x := rfl

lemma Ideal.injective_algebraMap_quotient_residueField :
    Function.Injective (algebraMap (R ⧸ I) I.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  show map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField, map_quotient_self]

instance : IsFractionRing (R ⧸ I) I.ResidueField where
  map_units' y := isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj' x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨Ideal.Quotient.mk _ s, ?_⟩⟩, ?_⟩
    · rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    · simp [IsScalarTower.algebraMap_eq R (Localization.AtPrime I) I.ResidueField, ← map_mul]
  exists_of_eq {x y} e := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero, ← map_sub, ← map_sub] at e
    simp only [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime I) I.ResidueField, algebraMap_mk,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ I, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at e
    use 1
    simp [e]

lemma Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ I) I.ResidueField) :=
  ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩

section LiesOver

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

noncomputable
instance (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    Algebra p.ResidueField q.ResidueField :=
  (Ideal.ResidueField.mapₐ p q Ideal.LiesOver.over).toAlgebra

instance (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    IsScalarTower R p.ResidueField q.ResidueField := .of_algebraMap_eq'
  ((Ideal.ResidueField.mapₐ p q Ideal.LiesOver.over).restrictScalars R).comp_algebraMap.symm

instance (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver q] [Q.LiesOver p] :
    IsScalarTower p.ResidueField q.ResidueField Q.ResidueField := by
  refine .of_algebraMap_eq fun x ↦ ?_
  simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map, IsLocalRing.ResidueField.map_map,
    ← IsLocalRing.ResidueField.map_comp, IsScalarTower.algebraMap_eq R A B,
    ← Localization.localRingHom_comp]

end LiesOver
