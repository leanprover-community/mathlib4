/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Class group map induced by an extension of domains

For an extension `A → B` of commutative domains with injective algebra map (equivalently
`Module.IsTorsionFree A B`), we construct the monoid homomorphism
`ClassGroup.extendedHom : ClassGroup A →* ClassGroup B` given by pushing fractional ideals forward
along the algebra map.

## Main definitions

- `ClassGroup.extendedHom A B`: the induced map between the class groups.
-/

public section

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]

namespace ClassGroup

/-- The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
extension of domains `A → B`. -/
noncomputable def extendedHom : ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using
        (FractionalIdeal.extendedHom_spanSingleton (FractionRing B) B _).symm)

@[simp]
lemma extendedHom_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (QuotientGroup.mk α) = QuotientGroup.mk
      (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom α) := by
  rw [extendedHom]
  rfl

@[simp]
theorem extendedHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (ClassGroup.mk I) = ClassGroup.mk
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

variable [IsDedekindDomain A]

/-- `ClassGroup.mk0` factors through the canonical quotient projection
on `(FractionalIdeal A⁰ (FractionRing A))ˣ`. -/
lemma mk0_eq_quotientMk (I : (Ideal A)⁰) :
    (ClassGroup.mk0 I : ClassGroup A) =
      QuotientGroup.mk (FractionalIdeal.mk0 (FractionRing A) I) :=
  (ClassGroup.mk_mk0 (K := FractionRing A) I).symm.trans (ClassGroup.Quot_mk_eq_mk _).symm

lemma extendedHom_mk0 [IsDedekindDomain B] (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨I.1.map (algebraMap A B),
      mem_nonZeroDivisors_iff_ne_zero.mpr <|
        (Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective A B)).not.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _

theorem extendedHom_mk0' (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) =
      ClassGroup.mk (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
        (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), extendedHom_mk]

end ClassGroup

end
