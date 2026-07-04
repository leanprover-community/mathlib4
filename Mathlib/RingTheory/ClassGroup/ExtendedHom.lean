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

For an injective extension `A → B` of commutative domains (equivalently `Module.IsTorsionFree A B`),
we construct the group homomorphism `ClassGroup.extendedHom : ClassGroup A →* ClassGroup B` given by
pushing fractional ideals forward along the algebra map.

## Main definitions

- `ClassGroup.extendedHom A B`: the induced map between the class groups.
- `ClassGroup.extendedIdeal A B`: the extension of a nonzero integral ideal.

## Main results

- `ClassGroup.extendedHom_mk`: compatibility with representatives as fractional ideals.
- `ClassGroup.extendedHom_mk0`: compatibility with representatives as nonzero integral ideals.
- `ClassGroup.extendedHom_comp`: compatibility of extension in a tower `A → B → C`.
- `ClassGroup.extendedHom_eq_one_of_forall_isPrincipal`: if the extension of every ideal is
  principal, then `ClassGroup.extendedHom A B` is trivial.
-/

public section

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.IsTorsionFree A B]

namespace ClassGroup

section CommRing

variable [IsDomain A] [IsDomain B]

/-- The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
injective extension of domains `A → B`. -/
noncomputable def extendedHom : ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using!
        (FractionalIdeal.extendedHom_spanSingleton (FractionRing B) B _).symm)

@[simp]
lemma extendedHom_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (QuotientGroup.mk α) = QuotientGroup.mk
      (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom α) := by
  rfl

@[simp]
theorem extendedHom_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extendedHom A B (ClassGroup.mk _ I) = ClassGroup.mk _
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  exact extendedHom_quotientMk A B I

/-- The extension of a nonzero integral ideal along an injective extension of domains. -/
abbrev extendedIdeal (I : (Ideal A)⁰) : (Ideal B)⁰ :=
  ⟨I.1.map (algebraMap A B), mem_nonZeroDivisors_iff_ne_zero.mpr <|
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩

@[simp]
theorem extendedIdeal_extendedIdeal (C : Type*) [CommRing C] [IsDomain C] [Algebra B C]
    [Algebra A C] [IsScalarTower A B C] [Module.IsTorsionFree B C]
    [Module.IsTorsionFree A C] (I : (Ideal A)⁰) :
    extendedIdeal B C (extendedIdeal A B I) = extendedIdeal A C I := by
  simp [Ideal.map_map, IsScalarTower.algebraMap_eq A B C]

end CommRing

section DedekindDomain

variable [IsDedekindDomain A] (C : Type*) [CommRing C] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] [Module.IsTorsionFree B C] [Module.IsTorsionFree A C]
  [IsDedekindDomain C]

theorem extendedHom_mk0' [IsDomain B] (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) =
      ClassGroup.mk _ (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
      (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), extendedHom_mk]

variable [IsDedekindDomain B]

lemma extendedHom_mk0 (I : (Ideal A)⁰) :
    extendedHom A B (ClassGroup.mk0 I) = ClassGroup.mk0 (extendedIdeal A B I) := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, extendedHom_quotientMk]
  congr; ext : 1
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) _


@[simp]
theorem extendedHom_comp_apply (x : ClassGroup A) :
      extendedHom B C (extendedHom A B x) = extendedHom A C x := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0 A B I, extendedHom_mk0 B C (extendedIdeal A B I),
    extendedHom_mk0 A C I, extendedIdeal_extendedIdeal]

theorem extendedHom_comp : (extendedHom B C).comp (extendedHom A B) = extendedHom A C := by
  ext x
  exact extendedHom_comp_apply A B C x

theorem extendedHom_eq_one_of_forall_isPrincipal
    (h : ∀ I : (Ideal A), (I.map (algebraMap A B)).IsPrincipal) : extendedHom A B = 1 := by
  ext x
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
  rw [extendedHom_mk0, MonoidHom.one_apply]
  exact (ClassGroup.mk0_eq_one_iff (extendedIdeal A B I).2).mpr (by simpa using h I)

end DedekindDomain

end ClassGroup

end
