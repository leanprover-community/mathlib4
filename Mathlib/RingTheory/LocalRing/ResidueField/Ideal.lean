/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SurjectiveOnStalks

/-!
# The residue field of a prime ideal

We define `Ideal.ResidueField I` to be the residue field of the local ring `Localization.Prime I`,
and provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.

-/

@[expose] public section

open scoped nonZeroDivisors

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (I : Ideal R) [I.IsPrime]

/--
The residue field at a prime ideal, defined to be the residue field of the local ring
`Localization.Prime I`.
We also provide an `IsFractionRing (R ⧸ I) I.ResidueField` instance.
-/
abbrev Ideal.ResidueField : Type _ :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
abbrev Ideal.ResidueField.map (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R →+* S) (hf : I = J.comap f) : I.ResidueField →+* J.ResidueField :=
  IsLocalRing.ResidueField.map (Localization.localRingHom I J f hf)

@[simp]
lemma Ideal.ResidueField.map_algebraMap (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime]
    (f : R →+* S) (hf : I = J.comap f) (r : R) :
    ResidueField.map I J f hf (algebraMap _ _ r) = algebraMap _ _ (f r) := by
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime I)]
  simp [IsLocalRing.ResidueField.map_residue, Localization.localRingHom_to_map]
  rfl

/-- If `I = f⁻¹(J)`, then there is a canonical embedding `κ(I) ↪ κ(J)`. -/
noncomputable
def Ideal.ResidueField.mapₐ (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A →ₐ[R] B) (hf : I = J.comap f.toRingHom) : I.ResidueField →ₐ[R] J.ResidueField where
  __ := Ideal.ResidueField.map I J f hf
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R A I.ResidueField,
      IsScalarTower.algebraMap_apply R B J.ResidueField]

@[simp] lemma Ideal.ResidueField.mapₐ_apply (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime]
    (f : A →ₐ[R] B) (hf : I = J.comap f.toRingHom) (x) :
    Ideal.ResidueField.mapₐ I J f hf x = Ideal.ResidueField.map I J _ hf x := rfl

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
lemma Ideal.algebraMap_quotient_residueField_mk (x) :
    algebraMap (R ⧸ I) I.ResidueField (Ideal.Quotient.mk _ x) =
    algebraMap R I.ResidueField x := rfl

@[deprecated (since := "2025-12-02")]
alias algebraMap_mk := Ideal.algebraMap_quotient_residueField_mk

lemma Ideal.injective_algebraMap_quotient_residueField :
    Function.Injective (algebraMap (R ⧸ I) I.ResidueField) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine (Ideal.ker_quotient_lift _ _).trans ?_
  change map (Quotient.mk I) (RingHom.ker (algebraMap R I.ResidueField)) = ⊥
  rw [Ideal.ker_algebraMap_residueField, map_quotient_self]

instance : IsFractionRing (R ⧸ I) I.ResidueField where
  map_units y := isUnit_iff_ne_zero.mpr
    (map_ne_zero_of_mem_nonZeroDivisors _ I.injective_algebraMap_quotient_residueField y.2)
  surj x := by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq I.primeCompl x
    refine ⟨⟨Ideal.Quotient.mk _ x, ⟨Ideal.Quotient.mk _ s, ?_⟩⟩, ?_⟩
    · rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    · simp [IsScalarTower.algebraMap_eq R (Localization.AtPrime I) I.ResidueField, ← map_mul]
  exists_of_eq {x y} e := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← sub_eq_zero, ← map_sub, ← map_sub] at e
    simp only [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff,
      IsScalarTower.algebraMap_apply R (Localization.AtPrime I) I.ResidueField,
      Ideal.algebraMap_quotient_residueField_mk, IsLocalization.AtPrime.to_map_mem_maximal_iff _ I,
      ← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at e
    use 1
    simp [e]

lemma Ideal.bijective_algebraMap_quotient_residueField (I : Ideal R) [I.IsMaximal] :
    Function.Bijective (algebraMap (R ⧸ I) I.ResidueField) :=
  ⟨I.injective_algebraMap_quotient_residueField, IsFractionRing.surjective_iff_isField.mpr
    ((Quotient.maximal_ideal_iff_isField_quotient I).mp inferInstance)⟩

lemma Ideal.surjectiveOnStalks_residueField (I : Ideal R) [I.IsPrime] :
    (algebraMap R I.ResidueField).SurjectiveOnStalks :=
  (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective).comp
    (RingHom.surjectiveOnStalks_of_isLocalization I.primeCompl _)

instance (p : Ideal R) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
  Localization.isLocalHom_localRingHom _ _ _ (Ideal.over_def _ _)

/-- If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`. -/
noncomputable def Ideal.ResidueField.lift
    (f : R →+* S) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid S).comap f) : I.ResidueField →+* S :=
  IsLocalization.lift (M := (R ⧸ I)⁰) (g := Ideal.Quotient.lift I (f := f) hf₁) <| by
    simpa [Ideal.Quotient.mk_surjective.forall, Ideal.Quotient.eq_zero_iff_mem]

@[simp] lemma Ideal.ResidueField.lift_algebraMap
    (f : R →+* S) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid S).comap f) (r : R) :
    lift I f hf₁ hf₂ (algebraMap _ _ r) = f r := by
  rw [lift, IsScalarTower.algebraMap_apply R (R ⧸ I) I.ResidueField, IsLocalization.lift_eq]
  simp

/-- If `f` sends `I` to `0` and `Iᶜ` to units, then `f` lifts to `κ(I)`. -/
noncomputable
def Ideal.ResidueField.liftₐ (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B) (hf₁ : I ≤ RingHom.ker f)
    (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) : I.ResidueField →ₐ[R] B where
  __ := Ideal.ResidueField.lift I f.toRingHom hf₁ hf₂
  commutes' r := by simp [IsScalarTower.algebraMap_apply R A I.ResidueField]

@[simp]
lemma Ideal.ResidueField.liftₐ_algebraMap (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B)
    (hf₁ : I ≤ RingHom.ker f) (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) (r : A) :
    liftₐ I f hf₁ hf₂ (algebraMap _ _ r) = f r :=
  lift_algebraMap _ _ _ hf₂ _

@[simp] lemma Ideal.ResidueField.liftₐ_comp_toAlgHom (I : Ideal A) [I.IsPrime] (f : A →ₐ[R] B)
    (hf₁ : I ≤ RingHom.ker f) (hf₂ : I.primeCompl ≤ (IsUnit.submonoid B).comap f) :
    (liftₐ I f hf₁ hf₂).comp (IsScalarTower.toAlgHom _ A _) = f :=
  AlgHom.ext fun _ ↦ liftₐ_algebraMap _ _ _ hf₂ _

@[ext high] -- higher than `RingHom.ext`.
lemma Ideal.ResidueField.ringHom_ext {I : Ideal R} [I.IsPrime]
    {f g : I.ResidueField →+* S} (H : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g :=
  IsLocalization.ringHom_ext (R ⧸ I)⁰ (Ideal.Quotient.ringHom_ext H)

@[ext high] -- higher than `AlgHom.ext`.
lemma Ideal.ResidueField.algHom_ext {I : Ideal A} [I.IsPrime] {f g : I.ResidueField →ₐ[R] B}
    (H : f.comp (IsScalarTower.toAlgHom R A _) = g.comp (IsScalarTower.toAlgHom R A _)) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext congr($H))
