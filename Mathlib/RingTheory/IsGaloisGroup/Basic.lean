/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Defs

/-!
# Galois Groups of Rings

Given an action of a group `G` on an extension of rings `B/A`, the predicate `IsGaloisGroup G A B`
states that `G` acts faithfully on `B` with fixed field `A`. This file develops some of the theory
of this predicate without assuming Galois theory for fields.
-/

@[expose] public section

-- this file should not import any field theory beyond the contents of `FieldTheory/Fixed.lean`
-- material involving Galois theory should be placed in `FieldTheory/IsGaloisGroup.lean`
assert_not_exists IntermediateField.adjoin

open Module

section CommRing

variable (G A B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

variable {C : Type*} [CommSemiring C] [Algebra C B]

variable {G} in
protected theorem Subgroup.smul_algebraMap {H : Subgroup G} [SMulCommClass H C B] {g : G}
    (hg : g ∈ H) (x : C) :
    g • algebraMap C B x = algebraMap C B x :=
  smul_algebraMap (⟨g, hg⟩ : H) x

theorem IsGaloisGroup.smul_mem_of_normal (N : Subgroup G) [hN : N.Normal]
    [hC : IsGaloisGroup N C B] (g : G) (x : C) :
    g • algebraMap C B x ∈ Set.range (algebraMap C B) := by
  apply hC.isInvariant.isInvariant (g • algebraMap C B x)
  intro n
  rw [← inv_smul_eq_iff, Subgroup.smul_def, ← mul_smul, ← mul_smul]
  exact Subgroup.smul_algebraMap B (hN.conj_mem' n n.prop g) x

@[deprecated (since := "2026-05-28")] alias smul_eq_self := Subgroup.smul_algebraMap
@[deprecated (since := "2026-05-28")] alias smul_mem_of_normal := IsGaloisGroup.smul_mem_of_normal

end CommRing

section Field

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]
  [MulSemiringAction G L] [SMulDistribClass G B L]

instance [IsGaloisGroup G A B] : IsGaloisGroup G (algebraMap A B).range B where
  faithful := IsGaloisGroup.faithful A
  commutes := ⟨fun g ⟨a', ⟨a, ha⟩⟩ b ↦ by simp [Subring.smul_def, ← ha]⟩
  isInvariant := ⟨fun b hb ↦ by
    obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A) b hb
    exact ⟨⟨algebraMap A B a, ⟨a, rfl⟩⟩, ha⟩⟩

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
theorem IsGaloisGroup.to_isFractionRing_of_isIntegral
    [Algebra.IsIntegral A B] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L where
  faithful :=
    have := hGAB.faithful
    IsFractionRing.faithfulSMul G B L
  commutes := IsFractionRing.smulCommClass G A B K L
  isInvariant := IsFractionRing.isInvariant_of_isIntegral G A B K L

/-- `IsGaloisGroup` for rings implies `IsGaloisGroup` for their fraction fields. -/
theorem IsGaloisGroup.to_isFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L :=
  have := hGAB.isInvariant.isIntegral
  IsGaloisGroup.to_isFractionRing_of_isIntegral G A B K L

/-- If `B` is an integral extension of an integrally closed domain `A`, then `IsGaloisGroup` for
their fraction fields implies `IsGaloisGroup` for these rings. -/
theorem IsGaloisGroup.of_isFractionRing [hGKL : IsGaloisGroup G K L]
    [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGaloisGroup G A B := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp_rw [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h ↦ ?_⟩, ⟨fun g x y ↦ IsFractionRing.injective B L ?_⟩, ⟨fun x h ↦ ?_⟩⟩
  · have := hGKL.faithful
    refine eq_of_smul_eq_smul fun (y : L) ↦ ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
    simp only [smul_div₀', ← algebraMap.coe_smul', h]
  · simp [Algebra.smul_def, algebraMap.coe_smul', ← hc]
  · obtain ⟨b, hb⟩ := hGKL.isInvariant.isInvariant (algebraMap B L x)
      (by simpa [← algebraMap.coe_smul'])
    have hx : IsIntegral A (algebraMap B L x) := (Algebra.IsIntegral.isIntegral x).algebraMap
    rw [← hb, isIntegral_algebraMap_iff (algebraMap K L).injective,
      IsIntegrallyClosedIn.isIntegral_iff] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, by rwa [hc, IsFractionRing.coe_inj] at hb⟩

/-- If `G` is finite and `A` is integrally closed then `IsGaloisGroup G A B` is equivalent to `B/A`
being integral and the fields of fractions `Frac(B)/Frac(A)` being Galois with Galois group `G`. -/
theorem IsGaloisGroup.iff_isFractionRing [Finite G] [IsIntegrallyClosed A] :
    IsGaloisGroup G A B ↔ Algebra.IsIntegral A B ∧ IsGaloisGroup G K L :=
  ⟨fun h ↦ ⟨h.isInvariant.isIntegral, h.to_isFractionRing G A B K L⟩,
    fun ⟨_, h⟩ ↦ h.of_isFractionRing G A B K L⟩

@[deprecated (since := "2026-04-20")] alias FractionRing.mulSemiringAction_of_isGaloisGroup :=
  IsFractionRing.mulSemiringAction

/--
If `G` is finite and `IsGaloisGroup G A B` with `A` and `B` domains, then `G` is also
a Galois group for `FractionRing B / FractionRing A` for the action defined by
`IsFractionRing.mulSemiringAction`.
-/
instance IsGaloisGroup.toFractionRing [IsDomain A] [IsDomain B] [IsTorsionFree A B] [Finite G]
    [IsGaloisGroup G A B] [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)] :
    letI := IsFractionRing.mulSemiringAction G B (FractionRing B)
    IsGaloisGroup G (FractionRing A) (FractionRing B) := by
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  apply IsGaloisGroup.to_isFractionRing G A B _ _

end Field

variable (G G' K L : Type*) [Group G] [Group G'] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction G' L]

namespace IsGaloisGroup

section IsDomain

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B]
  [MulSemiringAction G B] [MulSemiringAction G' B] [IsGaloisGroup G A B] [IsGaloisGroup G' A B]
  [Finite G] [Finite G']

end IsDomain

variable (H : Subgroup G)

instance (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [MulSemiringAction G S] [hGKL : IsGaloisGroup G R S] :
    IsGaloisGroup H (FixedPoints.subalgebra R S H) S where
  faithful := have := hGKL.faithful; inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

section Quotient

section Semiring

variable (A B C : Type*) [CommSemiring A] [Semiring C] [Algebra A C] [MulSemiringAction G C]
variable (N : Subgroup G) [CommSemiring B] [Algebra B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B`.
For `g : G` and `x : B`, `g • x` is the unique element of `B` whose image in `C` is
`g • algebraMap B C x`, see `algebraMap_smulOfNormal`. -/
@[implicit_reducible]
noncomputable def smulOfNormal [N.Normal] [IsGaloisGroup N B C] : SMul G B where
  smul g x := (smul_mem_of_normal G C N g x).choose

@[simp]
theorem algebraMap_smulOfNormal [N.Normal] [IsGaloisGroup N B C] (g : G) (x : B) :
    letI := smulOfNormal G B C
    algebraMap B C (g • x) = g • algebraMap B C x :=
  (smul_mem_of_normal G C N g x).choose_spec

/-- If `N` is normal and `IsGaloisGroup N B C`, the action `smulOfNormal G B C` satisfies
`SMulDistribClass G B C`. -/
instance smulDistribClass_smulOfNormal [N.Normal] [IsGaloisGroup N B C] :
    letI := smulOfNormal G B C
    SMulDistribClass G B C :=
  let := smulOfNormal G B C
  ⟨fun g b c ↦ by simp [Algebra.smul_def]⟩

variable [FaithfulSMul B C]

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then `G` acts on `B` as a
`MulSemiringAction`, via the action defined in `smulOfNormal`. -/
@[implicit_reducible]
noncomputable def mulSemiringActionOfNormal [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction G B := by
  let : SMul G B := smulOfNormal G B C N
  have : SMulDistribClass G B C := smulDistribClass_smulOfNormal G B C N
  exact mulSemiringActionOfSmulDistribClass B C G

/-- If `N` is a normal subgroup of `G` and `IsGaloisGroup N B C`, then the quotient group `G ⧸ N`
acts on `B` by `(g : G ⧸ N) • x = g • x`. -/
@[implicit_reducible]
noncomputable def mulSemiringActionQuotient [IsGaloisGroup N B C] [N.Normal] :
    MulSemiringAction (G ⧸ N) B :=
  letI := mulSemiringActionOfNormal G B C N
  { smul q x :=
      Quotient.liftOn' q (· • x) fun g₁ g₂ h ↦ by
      apply FaithfulSMul.algebraMap_injective B C
      rw [algebraMap.smul', algebraMap.smul', smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul,
        Subgroup.smul_algebraMap C (by rwa [← QuotientGroup.leftRel_apply])]
    one_smul x := one_smul G x
    mul_smul q₁ q₂ x := Quotient.inductionOn₂' q₁ q₂ fun g h ↦ mul_smul g h x
    smul_add q x y := Quotient.inductionOn' q fun g ↦ smul_add g x y
    smul_zero q := Quotient.inductionOn' q fun g ↦ smul_zero g
    smul_one q := Quotient.inductionOn' q fun g ↦ smul_one g
    smul_mul q x y := Quotient.inductionOn' q fun g ↦ smul_mul' g x y }

theorem mulSemiringActionQuotient_smul_def [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] (g : G) (b : B) :
    letI := mulSemiringActionQuotient G B C N
    (g : G ⧸ N) • b = g • b := by
  let := mulSemiringActionOfNormal G B C N
  refine (Quotient.liftOn'_mk'' (· • b) _ g).trans (FaithfulSMul.algebraMap_injective B C ?_)
  rw [algebraMap.smul', algebraMap.smul']

instance isScalarTower_mulSemiringActionQuotient [MulSemiringAction G B] [SMulDistribClass G B C]
    [IsGaloisGroup N B C] [N.Normal] :
    letI := mulSemiringActionQuotient G B C N
    IsScalarTower G (G ⧸ N) B :=
  let := mulSemiringActionQuotient G B C N
  ⟨fun g q b ↦ Quotient.inductionOn' q fun h ↦ by
    simp [mul_smul, mulSemiringActionQuotient_smul_def]⟩

set_option linter.defProp false in
/-- If `G` acts on `C` commuting with `A`, then the action of `G ⧸ N` on `B` commutes with `A`. -/
@[implicit_reducible]
def smulCommClassQuotient [N.Normal] [Algebra A B] [IsScalarTower A B C] [SMulCommClass G A C]
    [MulSemiringAction G B] [MulAction (G ⧸ N) B] [SMulDistribClass G B C]
    [IsScalarTower G (G ⧸ N) B] :
    SMulCommClass (G ⧸ N) A B :=
  ⟨fun g k x ↦ Quotient.inductionOn' g fun g ↦
    FaithfulSMul.algebraMap_injective B C (by
      simp [algebraMap.smul, algebraMap.smul', smul_comm])⟩

end Semiring

variable (F : IntermediateField K L) (N : Subgroup G) [N.Normal] [IsGaloisGroup N F L]

noncomputable instance : MulSemiringAction (G ⧸ N) F :=
  letI := smulOfNormal G F L N
  haveI := smulDistribClass_smulOfNormal G F L N
  letI := mulSemiringActionOfSmulDistribClass F L G
  mulSemiringActionQuotient G F L N

instance [SMulCommClass G K L] [MulSemiringAction G F] [SMulDistribClass G F L]
    [IsScalarTower G (G ⧸ N) F] : SMulCommClass (G ⧸ N) K F :=
  smulCommClassQuotient G K F L N

end Quotient

end IsGaloisGroup
