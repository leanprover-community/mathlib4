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
`ClassGroup.extensionMap : ClassGroup A →* ClassGroup B` given by pushing fractional ideals forward
along the algebra map.

## Main definitions

- `ClassGroup.extensionMap A B`: the induced map between the class groups.
-/

@[expose] public section

open scoped nonZeroDivisors

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.IsTorsionFree A B]

namespace ClassGroup

/-- The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
extension of domains `A → B`.

It descends from `Units.map (FractionalIdeal.extendedHom _ B)` via the
quotient by principal fractional ideals; the descent is well-defined by
`FractionalIdeal.extendedHom_spanSingleton`. -/
noncomputable def extensionMap : ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (IsFractionRing.map (j := algebraMap A B)
        (FaithfulSMul.algebraMap_injective _ _) (α : FractionRing A))
        (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using
        (FractionalIdeal.extendedHom_spanSingleton (FractionRing B) B _).symm)

/-- The class-group descent applied to `QuotientGroup.mk α` is
`QuotientGroup.mk` of the unit-pushforward — by definition of
`extensionMap` as a `QuotientGroup.map`. -/
@[simp]
lemma extensionMap_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extensionMap A B (QuotientGroup.mk α) =
      QuotientGroup.mk
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom α) :=
  rfl

/-- `extensionMap` sends `ClassGroup.mk I` to `ClassGroup.mk` of the
pushed-forward unit. -/
@[simp]
theorem extensionMap_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extensionMap A B (ClassGroup.mk I) =
      ClassGroup.mk
        (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  rfl

variable [IsDedekindDomain A]

/-- `ClassGroup.mk0` factors through the canonical quotient projection
on `(FractionalIdeal A⁰ (FractionRing A))ˣ`. -/
lemma mk0_eq_quotientMk (I : (Ideal A)⁰) :
    (ClassGroup.mk0 I : ClassGroup A) =
      QuotientGroup.mk (FractionalIdeal.mk0 (FractionRing A) I) := by
  change ClassGroup.mk (FractionalIdeal.mk0 _ I) = _
  change ((QuotientGroup.mk' _).comp _) (FractionalIdeal.mk0 _ I) = _
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    FractionalIdeal.canonicalEquiv_self]
  rfl

/-- Compatibility: the class-group map sends the class of a non-zero ideal
`I ∈ (Ideal A)⁰` to the class of its image `I · B = I.map (algebraMap A B)`
in `ClassGroup B`. -/
lemma extensionMap_mk0 [IsDedekindDomain B] (I : (Ideal A)⁰) :
    extensionMap A B (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map (algebraMap A B),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective
            (FaithfulSMul.algebraMap_injective A B)).not.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, extensionMap_quotientMk]
  congr 1
  apply Units.ext
  change FractionalIdeal.extendedHom (FractionRing B) B (FractionalIdeal.mk0 _ I).val =
    (FractionalIdeal.mk0 (FractionRing B) _).val
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
  exact FractionalIdeal.extendedHom_coeIdeal_eq_map (L := FractionRing B) (B := B) I.1

/-- `extensionMap` sends `ClassGroup.mk0 I` to `ClassGroup.mk` of the
pushed-forward fractional ideal. -/
theorem extensionMap_mk0' (I : (Ideal A)⁰) :
    extensionMap A B (ClassGroup.mk0 I) =
      ClassGroup.mk (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom
        (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), extensionMap_mk]

/-- Injectivity of `extensionMap` reduces to: every fractional ideal of `A`
whose pushforward to `B` is principal was already principal. -/
theorem extensionMap_injective_iff :
    Function.Injective (extensionMap A B) ↔
      ∀ I : (FractionalIdeal A⁰ (FractionRing A))ˣ,
        ClassGroup.mk
          (Units.map (FractionalIdeal.extendedHom (FractionRing B) B).toMonoidHom I) = 1 →
          ClassGroup.mk I = 1 := by
  rw [injective_iff_map_eq_one]
  constructor
  · intro h I hI
    exact h _ (by rwa [extensionMap_mk])
  · intro h x
    exact ClassGroup.induction (K := FractionRing A)
      (fun I hI => by rw [extensionMap_mk] at hI; exact h I hI) x

end ClassGroup

end
