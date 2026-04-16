/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Class group map induced by an extension of domains

For an extension `A → B` of commutative domains with injective algebra map
(equivalently `Module.IsTorsionFree A B`), we construct the monoid
homomorphism `ClassGroup.extensionMap : ClassGroup A →* ClassGroup B` given
by pushing fractional ideals forward along the algebra map.

## Main definitions

- `FractionalIdeal.extensionMap A B` — the ring homomorphism on fractional
  ideals induced by `A → B`.
- `FractionalIdeal.fractionRingMap A B` — the ring homomorphism on fraction
  rings induced by `A → B` via the universal property of localisation.
- `ClassGroup.extensionMap A B` — the descent to class groups.

## Main results

- `FractionalIdeal.extensionMap_spanSingleton` — principal fractional ideals
  push forward to principal fractional ideals. The key compatibility that
  makes the class-group-level descent well-defined.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace FractionalIdeal

variable (A : Type*) [CommRing A] [IsDomain A]
variable (B : Type*) [CommRing B] [IsDomain B]
variable [Algebra A B] [Module.IsTorsionFree A B]

/-- Non-zero divisors of `A` map into non-zero divisors of `B` under an
injective algebra map. -/
lemma algebraMap_nonZeroDivisors_le :
    A⁰ ≤ Submonoid.comap (algebraMap A B) B⁰ :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (FaithfulSMul.algebraMap_injective _ _)

/-- The ring homomorphism on fractional ideals induced by an extension of
domains `A → B`. -/
abbrev extensionMap :
    FractionalIdeal A⁰ (FractionRing A) →+*
      FractionalIdeal B⁰ (FractionRing B) :=
  FractionalIdeal.extendedHomₐ (FractionRing B) B

/-- The ring homomorphism on fraction rings induced by an extension
`A → B`. -/
abbrev fractionRingMap : FractionRing A →+* FractionRing B :=
  IsLocalization.map (FractionRing B) (algebraMap A B)
    (algebraMap_nonZeroDivisors_le A B)

/-- The fractional-ideal pushforward sends principal fractional ideals to
principal fractional ideals — the key compatibility for the class-group
descent. -/
lemma extensionMap_spanSingleton (x : FractionRing A) :
    extensionMap A B (spanSingleton _ x) =
      spanSingleton _ (fractionRingMap A B x) := by
  refine FractionalIdeal.ext fun y => ?_
  rw [show extensionMap A B = FractionalIdeal.extendedHom _
        (algebraMap_nonZeroDivisors_le A B) from rfl,
      FractionalIdeal.extendedHom_apply, FractionalIdeal.mem_extended_iff,
      FractionalIdeal.mem_spanSingleton, ← Submodule.mem_span_singleton]
  refine ⟨fun hy => Submodule.span_le.2 ?_ hy, fun hy => Submodule.span_le.2 ?_ hy⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, FractionalIdeal.mem_spanSingleton] at hw
    obtain ⟨a, rfl⟩ := hw
    rw [SetLike.mem_coe, Algebra.smul_def, map_mul, IsLocalization.map_eq, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rintro _ rfl
    exact Submodule.subset_span ⟨x, SetLike.mem_coe.mpr (mem_spanSingleton_self _ x), rfl⟩

end FractionalIdeal

namespace ClassGroup

variable (A : Type*) [CommRing A] [IsDomain A]
variable (B : Type*) [CommRing B] [IsDomain B]
variable [Algebra A B] [Module.IsTorsionFree A B]

/-- The monoid homomorphism `ClassGroup A → ClassGroup B` induced by an
extension of domains `A → B`.

It descends from `Units.map (FractionalIdeal.extensionMap A B)` via the
quotient by principal fractional ideals; the descent is well-defined by
`FractionalIdeal.extensionMap_spanSingleton`. -/
noncomputable def extensionMap : ClassGroup A →* ClassGroup B :=
  QuotientGroup.map _ _
    (Units.map (FractionalIdeal.extensionMap A B).toMonoidHom)
    (by
      rintro _ ⟨α, rfl⟩
      refine ⟨Units.mk0 (FractionalIdeal.fractionRingMap A B
        (α : FractionRing A)) (by simp [α.ne_zero]), ?_⟩
      simpa [coe_toPrincipalIdeal, Units.coe_map, Units.val_mk0] using
        (FractionalIdeal.extensionMap_spanSingleton A B _).symm)

/-- The class-group descent applied to `QuotientGroup.mk α` is
`QuotientGroup.mk` of the unit-pushforward — by definition of
`extensionMap` as a `QuotientGroup.map`. -/
@[simp]
lemma extensionMap_quotientMk (α : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extensionMap A B (QuotientGroup.mk α) =
      QuotientGroup.mk
        (Units.map (FractionalIdeal.extensionMap A B).toMonoidHom α) :=
  rfl

variable [IsDedekindDomain A] [IsDedekindDomain B]

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
lemma extensionMap_mk0 (I : (Ideal A)⁰) :
    extensionMap A B (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨I.1.map (algebraMap A B),
        mem_nonZeroDivisors_iff_ne_zero.mpr <|
          (Ideal.map_eq_bot_iff_of_injective
            (FaithfulSMul.algebraMap_injective A B)).not.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2)⟩ := by
  rw [mk0_eq_quotientMk, mk0_eq_quotientMk, extensionMap_quotientMk]
  congr 1
  apply Units.ext
  change FractionalIdeal.extensionMap A B (FractionalIdeal.mk0 _ I).val =
    (FractionalIdeal.mk0 (FractionRing B) _).val
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
  exact FractionalIdeal.extendedHomₐ_coeIdeal_eq_map (L := FractionRing B) (B := B) I.1

/-- `extensionMap` sends `ClassGroup.mk I` to `ClassGroup.mk` of the
pushed-forward unit. -/
@[simp]
theorem extensionMap_mk (I : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
    extensionMap A B (ClassGroup.mk I) =
      ClassGroup.mk (Units.map (FractionalIdeal.extensionMap A B).toMonoidHom I) := by
  rw [← ClassGroup.Quot_mk_eq_mk, ← ClassGroup.Quot_mk_eq_mk]
  rfl

/-- `extensionMap` sends `ClassGroup.mk0 I` to `ClassGroup.mk` of the
pushed-forward fractional ideal. -/
theorem extensionMap_mk0' (I : (Ideal A)⁰) :
    extensionMap A B (ClassGroup.mk0 I) =
      ClassGroup.mk (Units.map (FractionalIdeal.extensionMap A B).toMonoidHom
        (FractionalIdeal.mk0 (FractionRing A) I)) := by
  rw [← ClassGroup.mk_mk0 (FractionRing A), extensionMap_mk]

/-- Injectivity of `extensionMap` reduces to: every fractional ideal of `A`
whose pushforward to `B` is principal was already principal. -/
theorem extensionMap_injective_iff :
    Function.Injective (extensionMap A B) ↔
      ∀ I : (FractionalIdeal A⁰ (FractionRing A))ˣ,
        ClassGroup.mk (Units.map (FractionalIdeal.extensionMap A B).toMonoidHom I) = 1 →
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
