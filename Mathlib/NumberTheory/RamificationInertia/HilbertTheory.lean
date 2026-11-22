/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IntermediateField.ExtendRight
public import Mathlib.NumberTheory.RamificationInertia.Galois

import Mathlib.LinearAlgebra.Dimension.Domain

/-!
# Decomposition and inertia rings

We develop Hilbert's theory of the splitting of a prime ideal in a Galois extension, working
throughout at the level of rings.

Let `A ⊆ B` be commutative rings with `B` Galois over `A` with group `G`, let `p` be a prime of `A`
and `P` a prime of `B` lying over `p`. The *decomposition ring* `R` and the *inertia ring* `R'` of
`P` are the intermediate rings fixed by the decomposition and inertia subgroups of `P`; since the
inertia group is contained in the decomposition group, they fit into a tower `A ⊆ R ⊆ R' ⊆ B`.

## Ring predicates

For an intermediate ring `R` of `B`, we introduce two characteristic predicates:

* `Ideal.IsDecompositionRing G P R`: `B` is Galois over `R` with Galois group the *decomposition
  group* of `P`, that is the stabilizer of `P` in `G`;
* `Ideal.IsInertiaRing G P R`: `B` is Galois over `R` with Galois group the *inertia group* of `P`,
  that is the subgroup of `G` acting trivially modulo `P`.

## Main results

Writing `e`, `f` for the ramification index and inertia degree of `P` over `p`, `g` for the number
of primes of `B` above `p`, and `𝓟`, `𝓟'` for the primes of the decomposition ring `R` and the
inertia ring `R'` below `P`:
```
degree            ramif. index   inertia deg.
        B      P
  e     |      |      e               1
        R'     𝓟'
  f     |      |      1               f
        R      𝓟
  g     |      |      1               1
        A      p
```

## Relation to the classical field setting

In the classical setting `L/K` is a Galois extension of fields with `G = Gal(L/K)`, and `A`, `B` are
subrings of `K`, `L` with `K` the fraction field of `A`, `L` that of `B`, and `B` the integral
closure of `A` in `L`. The decomposition (resp. inertia) *field* is the subfield of `L` fixed by the
decomposition (resp. inertia) group of `P`, and the associated ring is the integral closure of `A`
in this field. Decomposition and inertia rings arising this way are provided by
`Ideal.IsDecompositionRing.of_isFractionRing` and `Ideal.IsInertiaRing.of_isFractionRing`, and the
degrees of the fields follow from those of the rings via `IsFractionRing.finrank_eq`.

-/

@[expose] public section

namespace Ideal

-- We fix the order of variables for the whole file
variable {A K L B : Type*}

section Ring

variable [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B]
  (P : Ideal B) (R : Type*) [CommRing R] [Algebra R B]

open MulAction Pointwise

section basic

/-- `P.IsDecompositionRing G R` states that the intermediate ring `R` of `B` is a *decomposition
ring* of the prime `P`: the ring `B` is Galois over `R` with Galois group the *decomposition group*
of `P`, that is the stabilizer of `P` under the action of `G`.

This is the ring-level characteristic predicate; the classical decomposition *field* is
recovered by passing to fraction fields. -/
@[mk_iff]
class IsDecompositionRing extends IsGaloisGroup (stabilizer G P) R B

instance [IsGaloisGroup (stabilizer G P) R B] : IsDecompositionRing G P R where

/-- `P.IsInertiaRing G R` states that the intermediate ring `R` of `B` is an *inertia ring* of the
prime `P`: the ring `B` is Galois over `R` with Galois group the *inertia group* of `P`, that is the
elements of `G` acting trivially modulo `P` (a subgroup of the decomposition group).

This is the ring-level characteristic predicate; the classical inertia *field* is recovered by
passing to fraction fields. -/
@[mk_iff]
class IsInertiaRing extends IsGaloisGroup (inertia G P) R B

instance [IsGaloisGroup (inertia G P) R B] : IsInertiaRing G P R where

variable (L) [Field L] [Algebra B L] [IsFractionRing B L]
  [MulSemiringAction G L] [SMulDistribClass G B L]

/-- If `L` is Galois over the field `D` with the decomposition group of `P` as a Galois group (so
`D` is the decomposition field of `P`), and `R` is an integrally closed subring of `D` with fraction
field `D` such that `B` is integral over `R`, then `R` is a decomposition ring of `P`. -/
theorem IsDecompositionRing.of_isFractionRing (D : Type*) [Field D]
    [Algebra R D] [Algebra R L] [Algebra D L] [IsScalarTower R D L] [IsScalarTower R B L]
    [IsFractionRing R D] [IsIntegrallyClosed R] [Algebra.IsIntegral R B]
    [IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionRing G P R where
  toIsGaloisGroup := .of_isFractionRing (stabilizer G P) R B D L

/-- If `L` is Galois over the field `E` with the inertia group of `P` as a Galois group (so `E` is
the inertia field of `P`), and `R` is an integrally closed subring of `E` with fraction field `E`
such that `B` is integral over `R`, then `R` is an inertia ring of `P`. -/
theorem IsInertiaRing.of_isFractionRing (E : Type*) [Field E]
    [Algebra R E] [Algebra R L] [Algebra E L] [IsScalarTower R E L] [IsScalarTower R B L]
    [IsFractionRing R E] [IsIntegrallyClosed R] [Algebra.IsIntegral R B]
    [IsGaloisGroup (inertia G P) E L] :
    IsInertiaRing G P R where
  toIsGaloisGroup := .of_isFractionRing (inertia G P) R B E L

end basic

section rank

/-! ## Degree formulas -/

variable [IsDomain B] [CommRing A] [IsDomain A] [Algebra A B] [Module.Finite A B]
  [Module.Flat A B] [FaithfulSMul R B] [IsGaloisGroup G A B] (p : Ideal A) [p.IsPrime]
  [P.IsPrime] [P.LiesOver p] [Algebra.HasSeparableResidueFieldsAt A B p]

/-- The degree `[B : R]` of `B` over the decomposition ring `R` equals the product of the
ramification index and the inertia degree of `p` in `B`. -/
theorem IsDecompositionRing.finrank_top [P.IsDecompositionRing G R] :
    Module.finrank R B = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← IsGaloisGroup.card_eq_finrank' (stabilizer G P) R B, card_stabilizer_eq p]

/-- The degree `[B : R]` of `B` over the inertia ring `R` equals the ramification index of `p`
in `B`. -/
theorem IsInertiaRing.finrank_top [P.IsInertiaRing G R] :
    Module.finrank R B = p.ramificationIdxIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← IsGaloisGroup.card_eq_finrank' (inertia G P) R B, card_inertia_eq_ramificationIdxIn p]

variable [Algebra A R] [IsScalarTower A R B]

/-- The degree `[R : A]` of the decomposition ring `R` over `A` equals the number of prime ideals
of `B` lying over `p`. -/
theorem IsDecompositionRing.finrank_bot [P.IsDecompositionRing G R] :
    Module.finrank A R = (p.primesOver B).ncard := by
  have := IsGaloisGroup.finite G A B
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R B).isDomain
  have : Module.Finite R B := Module.Finite.right A R B
  rw [← mul_left_inj' (c := Module.finrank R B) Module.finrank_pos.ne',
    Module.IsTorsionFree.finrank_mul_finrank, IsDecompositionRing.finrank_top G P R p,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G,
    IsGaloisGroup.card_eq_finrank' G A B]

/-- The degree `[R : A]` of the inertia ring `R` over `A` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`. -/
theorem IsInertiaRing.finrank_bot [P.IsInertiaRing G R] :
    Module.finrank A R = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R B).isDomain
  have : Module.Finite R B := Module.Finite.right A R B
  rw [← mul_left_inj' (c := Module.finrank R B) Module.finrank_pos.ne',
    Module.IsTorsionFree.finrank_mul_finrank, IsInertiaRing.finrank_top G P R p,
    ← IsGaloisGroup.card_eq_finrank' G A B, mul_assoc, mul_comm (p.inertiaDegIn B),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]

/-- The degree `[R' : R]` of the inertia ring `R'` over the decomposition ring `R` equals the
inertia degree of `p` in `B`. -/
theorem IsInertiaRing.finrank_decompositionRing (R' : Type*) [CommRing R'] [Algebra R' B]
    [FaithfulSMul R' B] [Algebra R R'] [IsScalarTower R R' B]
    [P.IsDecompositionRing G R] [P.IsInertiaRing G R'] :
    Module.finrank R R' = p.inertiaDegIn B := by
  have : IsDomain R' := (FaithfulSMul.algebraMap_injective R' B).isDomain
  have : Module.Finite R B := Module.Finite.right A R B
  have : Module.Finite R' B := Module.Finite.right R R' B
  rw [← mul_left_inj' (c := Module.finrank R' B) Module.finrank_pos.ne',
    Module.IsTorsionFree.finrank_mul_finrank, IsInertiaRing.finrank_top G P R' p,
    IsDecompositionRing.finrank_top G P R p, mul_comm]

end rank

section splitting

/-! ## Splitting of a prime in a decomposition ring -/

variable [CommRing A] [Algebra A B] [Algebra A R] [IsScalarTower A R B]
  (p : Ideal A) [P.LiesOver p] (𝓟 : Ideal R) [P.LiesOver 𝓟]

namespace IsDecompositionRing

variable [P.IsDecompositionRing G R]

/-- If `R` is a decomposition ring of `P` and `𝓟` is the prime of `R` below `P`, then any prime
of `B` above `𝓟` is equal to `P`. -/
theorem eq_of_liesOver [P.IsPrime] [Finite (stabilizer G P)] (Q : Ideal B) [Q.IsPrime]
    [Q.LiesOver 𝓟] : Q = P := by
  obtain ⟨σ, rfl⟩ := 𝓟.exists_smul_eq_of_isGaloisGroup P Q (stabilizer G P)
  exact σ.prop

/-- Let `R` be a decomposition ring of `P` and `𝓟` the prime of `R` below `P`. Then `P` is the
only prime of `B` above `𝓟`. -/
theorem primesOver_eq_singleton [P.IsPrime] [Finite (stabilizer G P)] : 𝓟.primesOver B = {P} :=
  Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩,
    fun Q ⟨_, _⟩ ↦ eq_of_liesOver G P R 𝓟 Q⟩

variable [IsGaloisGroup G A B] [IsDomain A] [IsDomain B] [FaithfulSMul R B]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat R B] [p.IsPrime]
  [Algebra.HasSeparableResidueFieldsAt A B p] [P.IsPrime]

include G P in
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq :
    𝓟.ramificationIdxIn B = p.ramificationIdxIn B ∧ 𝓟.inertiaDegIn B = p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  have : 𝓟.IsPrime := P.isPrime_of_liesOver 𝓟
  have : 𝓟.LiesOver p := LiesOver.tower_bot P 𝓟 p
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R B).isDomain
  have : Module.Finite R B := Module.Finite.right A R B
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact (ramificationIdxIn_ne_zero (stabilizer G P)).pos
  · exact (inertiaDegIn_ne_zero (stabilizer G P)).pos
  · exact ramificationIdxIn_above_le p 𝓟 B G (stabilizer G P)
  · exact inertiaDegIn_above_le p 𝓟 B G (stabilizer G P)
  · have := 𝓟.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn B (stabilizer G P)
    rw [primesOver_eq_singleton G P, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank' (stabilizer G P) R B, finrank_top G P R p]

include G P in
/-- The ramification index of `𝓟` in `B` equals the ramification index of `p` in `B`. -/
theorem ramificationIdxIn_eq : 𝓟.ramificationIdxIn B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P R p 𝓟).1

include G P in
/-- The inertia degree of `𝓟` in `B` equals the inertia degree of `p` in `B`. -/
theorem inertiaDegIn_eq : 𝓟.inertiaDegIn B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P R p 𝓟).2

include G P in
/-- The ramification index of `P` over `R` equals the ramification index of `p` in `B`. -/
theorem ramificationIdx_eq : P.ramificationIdx R = p.ramificationIdxIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← (P.under R).ramificationIdxIn_eq_ramificationIdx P (stabilizer G P),
    ramificationIdxIn_eq G P R p (P.under R)]

include G P in
/-- The inertia degree of `P` over `R` equals the inertia degree of `p` in `B`. -/
theorem inertiaDeg_eq : P.inertiaDeg R = p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← (P.under R).inertiaDegIn_eq_inertiaDeg P (stabilizer G P),
    inertiaDegIn_eq G P R p (P.under R)]

include G P p in
/-- The ramification index of `𝓟` over `A` equals `1`. -/
theorem ramificationIdx_eq_one : 𝓟.ramificationIdx A = 1 := by
  have := IsGaloisGroup.finite G A B
  have := 𝓟.ramificationIdx_tower (R := A) P
  rwa [ramificationIdx_eq G P R p, p.ramificationIdxIn_eq_ramificationIdx P G,
    right_eq_mul₀ (P.ramificationIdx_pos A).ne'] at this

include G P p in
/-- The inertia degree of `𝓟` over `A` equals `1`. -/
theorem inertiaDeg_eq_one : 𝓟.inertiaDeg A = 1 := by
  have := IsGaloisGroup.finite G A B
  have : Module.Finite R B := Module.Finite.right A R B
  have := 𝓟.inertiaDeg_tower (R := A) P
  rwa [inertiaDeg_eq G P R p, p.inertiaDegIn_eq_inertiaDeg P G,
    right_eq_mul₀ (P.inertiaDeg_pos A).ne'] at this

end IsDecompositionRing

/-! ### Splitting of a prime in an inertia ring -/

namespace IsInertiaRing

attribute [local instance] Ideal.Quotient.field

variable [P.IsInertiaRing G R]

/-- Let `R` be an inertia ring of `P` and `𝓟` the prime of `R` below `P`. Then `P` is the
only prime of `B` above `𝓟`. -/
theorem primesOver_eq_singleton [P.IsPrime] [Finite (inertia G P)] :
    primesOver 𝓟 B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, fun Q ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟 P Q (inertia G P)
  exact inertia_le_stabilizer _ σ.prop

variable [Finite G] [Ring.HasFiniteQuotients B] [P.IsMaximal]

include G P in
/-- The inertia degree of `𝓟` in `B` equals `1`. -/
theorem inertiaDegIn_eq [Algebra.IsIntegral R B] (hP : P ≠ ⊥) :
    inertiaDegIn 𝓟 B = 1 := by
  have : 𝓟.IsMaximal := .of_isMaximal_liesOver P 𝓟
  have : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  rw [inertiaDegIn_eq_inertiaDeg 𝓟 P (inertia G P), inertiaDeg_eq_of_isMaximal 𝓟 P,
    ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia G P) 𝓟 P).toEquiv]
  refine Nat.card_eq_one_iff_unique.mpr ⟨?_, inferInstance⟩
  rw [QuotientGroup.subsingleton_iff, Subgroup.eq_top_iff']
  exact fun ⟨⟨σ, hσ⟩, hσ'⟩ ↦ hσ

variable [IsGaloisGroup G A B] [Module.Finite A B]

include G P in
/-- The inertia degree of `𝓟` over `A` equals the inertia degree of `p` in `B`. -/
theorem inertiaDeg_eq (hP : P ≠ ⊥) :
    𝓟.inertiaDeg A = p.inertiaDegIn B := by
  have : Module.Finite R B := Module.Finite.right A R B
  have := inertiaDeg_tower (R := A) 𝓟 P
  rw [← inertiaDegIn_eq_inertiaDeg 𝓟 P (inertia G P), inertiaDegIn_eq G P R 𝓟 hP,
    mul_one] at this
  rw [inertiaDegIn_eq_inertiaDeg p P G, this]

variable [IsDomain A] [IsDomain B] [IsDomain R] [Module.Flat A B] [Module.Flat R B]
  [Ring.HasFiniteQuotients A]

include G P in
/-- The ramification index of `𝓟` in `B` equals the ramification index of `p` in `B`. -/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟 B = p.ramificationIdxIn B := by
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : p.IsMaximal := .of_isMaximal_liesOver P p
  have : Module.Finite R B := Module.Finite.right A R B
  have : 𝓟.IsMaximal := .of_isMaximal_liesOver P 𝓟
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟 B (inertia G P)
  rwa [primesOver_eq_singleton G P, Set.ncard_singleton, one_mul, inertiaDegIn_eq G P R 𝓟 hP,
    mul_one, card_inertia_eq_ramificationIdxIn p P] at this

include G P in
/-- `𝓟` is unramified over `A`. -/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    𝓟.ramificationIdx A = 1 := by
  have := ramificationIdx_tower (R := A) 𝓟 P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟 P (inertia G P),
    ramificationIdxIn_eq G P R p 𝓟 hp, ramificationIdxIn_eq_ramificationIdx p P G,
    right_eq_mul₀ (P.ramificationIdx_pos A).ne'] at this

end IsInertiaRing

end splitting

end Ring

section IntermediateField

open IntermediateField MulAction Pointwise

variable (K L) [Field K] [Field L] [Algebra K L] [CommRing B] (P : Ideal B)
  [MulSemiringAction Gal(L/K) B]

/-- The decomposition field of `P` in `L/K`: the subfield of `L` fixed by the decomposition
subgroup of `P`. -/
def decompositionField : IntermediateField K L :=
  fixedField (stabilizer Gal(L/K) P)

/-- The inertia field of `P` in `L/K`: the subfield of `L` fixed by the inertia subgroup of `P`. -/
def inertiaField : IntermediateField K L :=
  fixedField (inertia Gal(L/K) P)

theorem decompositionField_def :
    P.decompositionField K L = fixedField (stabilizer Gal(L/K) P) :=
  rfl

theorem inertiaField_def :
    P.inertiaField K L = fixedField (inertia Gal(L/K) P) :=
  rfl

theorem decompositionField_le_inertiaField :
    P.decompositionField K L ≤ P.inertiaField K L :=
  fun _ hx ↦ (mem_fixedField_iff _ _).mpr fun σ hσ ↦
    (mem_fixedField_iff _ _).mp hx σ (inertia_le_stabilizer P hσ)

@[simp]
theorem fixingSubgroup_decompositionField [FiniteDimensional K L] :
    (P.decompositionField K L).fixingSubgroup = stabilizer Gal(L/K) P :=
  fixingSubgroup_fixedField _

@[simp]
theorem fixingSubgroup_inertiaField [FiniteDimensional K L] :
    (P.inertiaField K L).fixingSubgroup = inertia Gal(L/K) P :=
  fixingSubgroup_fixedField _

instance [IsGalois K L] :
    IsGaloisGroup (stabilizer Gal(L/K) P) (P.decompositionField K L) L :=
  IsGaloisGroup.subgroup_iff.mpr rfl

instance [IsGalois K L] :
    IsGaloisGroup (inertia Gal(L/K) P) (P.inertiaField K L) L :=
  IsGaloisGroup.subgroup_iff.mpr rfl

theorem eq_decompositionField_iff [FiniteDimensional K L] [IsGalois K L]
    {D : IntermediateField K L} :
    D = P.decompositionField K L ↔ D.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [decompositionField_def, eq_comm, IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem eq_inertiaField_iff [FiniteDimensional K L] [IsGalois K L]
    {E : IntermediateField K L} :
    E = P.inertiaField K L ↔ E.fixingSubgroup = inertia Gal(L/K) P := by
  rw [inertiaField_def, eq_comm, IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem le_decompositionField_iff {F : IntermediateField K L} :
    F ≤ P.decompositionField K L ↔ stabilizer Gal(L/K) P ≤ F.fixingSubgroup :=
  le_fixedField_iff_le_fixingSubgroup _ _

theorem le_inertiaField_iff {F : IntermediateField K L} :
    F ≤ P.inertiaField K L ↔ inertia Gal(L/K) P ≤ F.fixingSubgroup :=
  le_fixedField_iff_le_fixingSubgroup _ _

theorem decompositionField_le_iff {F : IntermediateField K L} [FiniteDimensional K L]
    [IsGalois K L] :
    P.decompositionField K L ≤ F ↔ F.fixingSubgroup ≤ stabilizer Gal(L/K) P := by
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/K) K L F,
    IsGaloisGroup.le_fixedPoints_iff_le_fixingSubgroup, IsGaloisGroup.fixedPoints_fixingSubgroup,
    ← IntermediateField.fixingSubgroup, ← IntermediateField.fixingSubgroup,
    fixingSubgroup_decompositionField]

theorem inertiaField_le_iff {F : IntermediateField K L} [FiniteDimensional K L] [IsGalois K L] :
    P.inertiaField K L ≤ F ↔ F.fixingSubgroup ≤ inertia Gal(L/K) P := by
  rw [← IsGaloisGroup.fixedPoints_fixingSubgroup Gal(L/K) K L F,
    IsGaloisGroup.le_fixedPoints_iff_le_fixingSubgroup, IsGaloisGroup.fixedPoints_fixingSubgroup,
    ← IntermediateField.fixingSubgroup, ← IntermediateField.fixingSubgroup,
    fixingSubgroup_inertiaField]

section ring

variable [IsGalois K L] [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L]
  (R : Type*) [CommRing R] [Algebra R B] [Algebra R L] [IsScalarTower R B L] [IsIntegrallyClosed R]
  [Algebra.IsIntegral R B]

/-- A ring `R` with `R ⊆ B`, `B` integral over `R`, `R` integrally closed, and fraction field the
decomposition field of `P`, is a decomposition ring for `P`. -/
theorem isDecompositionRing_of_isFractionRing [Algebra R (P.decompositionField K L)]
    [IsScalarTower R (P.decompositionField K L) L] [IsFractionRing R (P.decompositionField K L)] :
    P.IsDecompositionRing Gal(L/K) R := {
  toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ R B (P.decompositionField K L) L }

/-- A ring `R` with `R ⊆ B`, `B` integral over `R`, `R` integrally closed, and fraction field the
inertia field of `P`, is an inertia ring for `P`. -/
theorem isInertiaRing_of_isFractionRing [Algebra R (P.inertiaField K L)]
    [IsScalarTower R (P.inertiaField K L) L] [IsFractionRing R (P.inertiaField K L)] :
    P.IsInertiaRing Gal(L/K) R := {
  toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ R B (P.inertiaField K L) L }

end ring

section rank

variable [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDomain B]
  [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L]
  [Algebra A K] [IsFractionRing A K] [Algebra A B] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [Module.Finite A B] [Module.Flat A B]
  [FiniteDimensional K L] [IsGalois K L]
  (p : Ideal A) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] [PerfectField p.ResidueField]

/-- The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`. -/
theorem finrank_decompositionField_top :
    Module.finrank (P.decompositionField K L) L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  rw [decompositionField, finrank_fixedField_eq_card, card_stabilizer_eq p P]

/-- The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p`
in `B`. -/
theorem finrank_inertiaField_top :
    Module.finrank (P.inertiaField K L) L = p.ramificationIdxIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  rw [inertiaField, finrank_fixedField_eq_card, card_inertia_eq_ramificationIdxIn p P]

/-- The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`. -/
theorem finrank_decompositionField_bot :
    Module.finrank K (P.decompositionField K L) = (p.primesOver B).ncard := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  rw [← mul_left_inj' (c := Module.finrank (P.decompositionField K L) L) Module.finrank_pos.ne',
    Module.finrank_mul_finrank, finrank_decompositionField_top K L P p,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank _ K L]

/-- The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`. -/
theorem finrank_inertiaField_bot :
    Module.finrank K (P.inertiaField K L) = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  rw [← mul_left_inj' (c := Module.finrank (P.inertiaField K L) L) Module.finrank_pos.ne',
    Module.finrank_mul_finrank, finrank_inertiaField_top K L P p,  mul_assoc,
    mul_comm (p.inertiaDegIn B), ← IsGaloisGroup.card_eq_finrank Gal(L/K),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K)]

end rank

variable (F : IntermediateField K L) [Algebra B L] [FaithfulSMul B L]
  [SMulDistribClass Gal(L/K) B L]

section restrictScalars

variable [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L]

/-- Let `F` be an intermediate field of `L/K`. The decomposition field of `P` for `L/F` is the
compositum of `F` with the decomposition field of `P` for `L/K`. -/
theorem restrictScalars_decompositionField [FiniteDimensional K L] [IsGalois K L] :
    (P.decompositionField F L).restrictScalars K = F ⊔ P.decompositionField K L := by
  let H : Subgroup Gal(L/K) := stabilizer Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↑(F ⊔ P.decompositionField K L) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, fixingSubgroup_decompositionField, inf_comm]
  let e : stabilizer Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((stabilizer F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine stabilizerEquiv P F.fixingSubgroupEquiv.symm fun σ x ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  have h : IsGaloisGroup (stabilizer Gal(L/F) P) ↑(F ⊔ P.decompositionField K L) L :=
    IsGaloisGroup.of_mulEquiv e fun _ _ ↦ rfl
  rw [decompositionField_def, fixedField,
    (IsGaloisGroup.subgroup_iff (F := extendScalars le_sup_left)).mp h,
    extendScalars_restrictScalars]

/-- Let `F` be an intermediate field of `L/K`. The inertia field of `P` for `L/F` is the
compositum of `F` with the inertia field of `P` for `L/K`. -/
theorem restrictScalars_inertiaField [FiniteDimensional K L] [IsGalois K L] :
    (P.inertiaField F L).restrictScalars K = F ⊔ P.inertiaField K L := by
  let H : Subgroup Gal(L/K) := inertia Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↑(F ⊔ P.inertiaField K L) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, fixingSubgroup_inertiaField, inf_comm]
  let e : inertia Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((inertia F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine inertiaEquiv P F.fixingSubgroupEquiv.symm fun σ x ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  have h : IsGaloisGroup (inertia Gal(L/F) P) ↑(F ⊔ P.inertiaField K L) L :=
    IsGaloisGroup.of_mulEquiv e fun _ _ ↦ rfl
  rw [inertiaField_def, fixedField,
    (IsGaloisGroup.subgroup_iff (F := extendScalars le_sup_left)).mp h,
    extendScalars_restrictScalars]

end restrictScalars

variable [IsFractionRing B L]

section lift

variable {𝓞F : Type*} [CommRing 𝓞F] [Algebra 𝓞F F] [Algebra 𝓞F B] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F F L] [IsScalarTower 𝓞F B L] [IsFractionRing 𝓞F F]
  [IsIntegrallyClosed 𝓞F] [Algebra.IsIntegral 𝓞F B]
  [MulSemiringAction Gal(F/K) 𝓞F] [SMulDistribClass Gal(F/K) 𝓞F F]
  (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F]

/-- Let `F` be an intermediate field of `L/K`. The decomposition field of the prime `𝓟F`
below `P` for `F/K` is the intersection of `F` with the decomposition field of `P` for `L/K`. -/
theorem lift_decompositionField [FiniteDimensional K L] [IsGalois K L] [Normal K F] [P.IsPrime] :
    lift (𝓟F.decompositionField K F) = P.decompositionField K L ⊓ F := by
  have : Algebra.IsInvariant 𝓞F B F.fixingSubgroup :=
    have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
    (IsGaloisGroup.of_isFractionRing F.fixingSubgroup 𝓞F B F L).isInvariant
  have h : (stabilizer Gal(L/K) P).map (AlgEquiv.restrictNormalHom F) = stabilizer Gal(F/K) 𝓟F :=
    Ideal.map_stabilizer_of_surjective _ F.fixingSubgroup 𝓟F P
      (AlgEquiv.restrictNormalHom_surjective L)
      (IntermediateField.restrictNormalHom_ker F).ge
      (fun g x ↦ AlgEquiv.algebraMap_restrictNormalHom_smul' F x g)
  rw [← IsGalois.fixedField_fixingSubgroup (lift (𝓟F.decompositionField K F)),lift,
    show F.val = IsScalarTower.toAlgHom K F L from rfl, map_fixingSubgroup,
    fixingSubgroup_decompositionField, ← h, Subgroup.comap_map_eq, restrictNormalHom_ker,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq, fixingSubgroup_inf,
    fixingSubgroup_decompositionField]

/-- Let `F` be an intermediate field of `L/K`. The inertia field of the prime `𝓟F`
below `P` for `F/K` is the intersection of `F` with the inertia field of `P` for `L/K`. -/
theorem lift_inertiaField [FiniteDimensional K L] [IsGalois K L] [Normal K F] [P.IsPrime] :
    lift (𝓟F.inertiaField K F) = P.inertiaField K L ⊓ F := by
  have : Algebra.IsInvariant 𝓞F B F.fixingSubgroup :=
    have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
    (IsGaloisGroup.of_isFractionRing F.fixingSubgroup 𝓞F B F L).isInvariant
  have h : (inertia Gal(L/K) P).map (AlgEquiv.restrictNormalHom F) = inertia Gal(F/K) 𝓟F :=
    Ideal.map_inertia_of_surjective _ F.fixingSubgroup 𝓟F P
      (AlgEquiv.restrictNormalHom_surjective L)
      (IntermediateField.restrictNormalHom_ker F).ge
      (fun g x ↦ AlgEquiv.algebraMap_restrictNormalHom_smul' F x g)
  rw [← IsGalois.fixedField_fixingSubgroup (lift (𝓟F.inertiaField K F)),lift,
    show F.val = IsScalarTower.toAlgHom K F L from rfl, map_fixingSubgroup,
    fixingSubgroup_inertiaField, ← h, Subgroup.comap_map_eq, restrictNormalHom_ker,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq, fixingSubgroup_inf,
    fixingSubgroup_inertiaField]

end lift

section arithmetic

variable (A) {𝓞F : Type*} [CommRing 𝓞F] [Algebra 𝓞F F] [Algebra 𝓞F B] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F F L] [IsScalarTower 𝓞F B L] [IsFractionRing 𝓞F F]
  [IsIntegrallyClosed 𝓞F] [Algebra.IsIntegral 𝓞F B]
  [FiniteDimensional K L] [IsGalois K L] (𝓟F : Ideal 𝓞F) [P.IsPrime] [P.LiesOver 𝓟F]

omit [FaithfulSMul B L] in
/-- `D ≤ F` iff `P` is the unique prime of `L` above the prime `𝓟F` of `F` below `P`. -/
theorem decompositionField_le_iff_primesOver [SMulCommClass Gal(L/K) 𝓞F B] :
    P.decompositionField K L ≤ F ↔ 𝓟F.primesOver B = {P} := by
  have : IsGaloisGroup F.fixingSubgroup F L := .intermediateField _ _ _ _
  have : IsGaloisGroup F.fixingSubgroup 𝓞F B := .of_isFractionRing F.fixingSubgroup 𝓞F B F L
  have hP : P ∈ 𝓟F.primesOver B := ⟨inferInstance, inferInstance⟩
  simp only [decompositionField_le_iff, Set.eq_singleton_iff_unique_mem, hP, true_and]
  refine ⟨fun h Q ⟨_, _⟩ ↦ ?_, fun h σ hσ ↦ ?_⟩
  · obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟F P Q F.fixingSubgroup
    exact h σ.prop
  · exact h (σ • P) ⟨IsPrime.smul σ, LiesOver.smul σ⟩

variable [MulSemiringAction Gal(L/F) B] [SMulDistribClass Gal(L/F) B L] [CommRing A]
  [IsIntegrallyClosed A] [Algebra A B] [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [Algebra A 𝓞F] [IsScalarTower A 𝓞F B] (p : Ideal A)
  [P.LiesOver p] [𝓟F.LiesOver p] [Module.Finite A B] [Module.Flat A B] [Module.Flat 𝓞F B]
  [p.IsMaximal] [PerfectField p.ResidueField] [IsDomain B]

include 𝓟F in
/-- `E ≤ F` iff `P` is totally ramified over the prime `𝓟F` of `F` below `P`. -/
theorem inertiaField_le_iff_ramificationIdx_eq_finrank [Module.Finite 𝓞F B] [P.IsMaximal]
    [𝓟F.IsPrime] [PerfectField 𝓟F.ResidueField] :
    P.inertiaField K L ≤ F ↔ P.ramificationIdx 𝓞F = Module.finrank F L := by
  have : IsDomain 𝓞F := Function.Injective.isDomain _ (IsFractionRing.injective 𝓞F F)
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  have : 𝓟F.IsMaximal := IsMaximal.of_isMaximal_liesOver P 𝓟F
  rw [← sup_eq_right, eq_comm, eq_iff_finrank_eq_of_le' le_sup_right]
  have : Module.finrank (inertiaField F L P) L = Module.finrank ↑(F ⊔ inertiaField K L P) L :=
    Algebra.finrank_eq_of_equiv_equiv
      (equivOfEq (restrictScalars_inertiaField K L P F)).toRingEquiv (RingEquiv.refl L) rfl
  rw [sup_comm, ← this, finrank_inertiaField_top F L P 𝓟F,
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), eq_comm]

include p in
/-- `F ≤ E` iff `p` is unramified in `F`. -/
theorem le_inertiaField_iff_ramificationIdx_eq_one :
    F ≤ P.inertiaField K L ↔ 𝓟F.ramificationIdx A = 1 := by
  have : IsDomain A := Function.Injective.isDomain _ (IsFractionRing.injective A K)
  have : IsDomain 𝓞F := Function.Injective.isDomain _ (IsFractionRing.injective 𝓞F F)
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  have : Module.Finite 𝓞F B := .right A 𝓞F B
  have : P.IsMaximal := .of_liesOver_isMaximal P p
  have : 𝓟F.IsMaximal := IsMaximal.of_isMaximal_liesOver P 𝓟F
  have : Algebra.IsIntegral A 𝓞F := Algebra.IsIntegral.tower_bot B
  let := Localization.AtPrime.algebraOfLiesOver p 𝓟F
  have : PerfectField 𝓟F.ResidueField := Algebra.IsAlgebraic.perfectField p.ResidueField
  have : Module.finrank (inertiaField F L P) L = Module.finrank ↑(F ⊔ inertiaField K L P) L :=
    Algebra.finrank_eq_of_equiv_equiv
      (equivOfEq (restrictScalars_inertiaField K L P F)).toRingEquiv (RingEquiv.refl L) rfl
  rw [← sup_eq_right, eq_comm, eq_iff_finrank_eq_of_le' le_sup_right,
    finrank_inertiaField_top K L P p, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    ramificationIdx_tower 𝓟F, ← ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F),
    ← finrank_inertiaField_top F L P, this, mul_eq_right₀ Module.finrank_pos.ne']

variable [P.IsMaximal] [IsDomain 𝓞F]

include p in
/-- `F ≤ D` iff `p` is totally split in `F`. -/
theorem le_decompositionField_iff_ramificationIdx_inertiaDeg_eq_one [IsDomain A] :
    F ≤ P.decompositionField K L ↔ 𝓟F.ramificationIdx A = 1 ∧ 𝓟F.inertiaDeg A = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  have : Module.Finite 𝓞F B := .right A 𝓞F B
  have : 𝓟F.IsMaximal := IsMaximal.of_isMaximal_liesOver P 𝓟F
  have : Algebra.IsIntegral A 𝓞F := Algebra.IsIntegral.tower_bot B
  let := Localization.AtPrime.algebraOfLiesOver p 𝓟F
  have : PerfectField 𝓟F.ResidueField := Algebra.IsAlgebraic.perfectField p.ResidueField
  have : Module.finrank (decompositionField F L P) L =
      Module.finrank ↑(F ⊔ decompositionField K L P) L :=
    Algebra.finrank_eq_of_equiv_equiv
      (equivOfEq (restrictScalars_decompositionField K L P F)).toRingEquiv (RingEquiv.refl L) rfl
  rw [← sup_eq_right, sup_comm, eq_comm, eq_iff_finrank_eq_of_le' le_sup_left,
    finrank_decompositionField_top K L P p, sup_comm, ← this,
    finrank_decompositionField_top F L P 𝓟F, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F),
    inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F), ramificationIdx_tower 𝓟F P,
    mul_comm (𝓟F.ramificationIdx A), mul_assoc, mul_right_inj' (Ideal.ramificationIdx_pos _ _).ne',
    inertiaDeg_tower 𝓟F P,  ← mul_assoc, mul_eq_right₀ (Ideal.inertiaDeg_pos _ _).ne',  mul_eq_one]

include p in
/-- An intermediate field `F` of `L/K` is the decomposition field of `P` iff `p` is totally split
in `F` and there is only one prime ideal above `𝓟F` in `L`. -/
theorem eq_decompositionField_iff' [IsDomain A] [SMulCommClass Gal(L/K) 𝓞F B] :
    F = P.decompositionField K L ↔
      𝓟F.primesOver B = {P} ∧ 𝓟F.ramificationIdx A = 1 ∧ 𝓟F.inertiaDeg A = 1 := by
  rw [le_antisymm_iff,
    le_decompositionField_iff_ramificationIdx_inertiaDeg_eq_one A K L P F 𝓟F p,
    decompositionField_le_iff_primesOver K L P F 𝓟F, and_comm]

include p in
/-- An intermediate field `F` of `L/K` is the inertia field of `P` iff the prime `𝓟F` of `F` below
`P` is unramified over `p`, and `P` is totally ramified over `𝓟F`. -/
theorem eq_inertiaField_iff' :
    F = P.inertiaField K L ↔
      P.ramificationIdx 𝓞F = Module.finrank F L ∧ 𝓟F.ramificationIdx A = 1 := by
  have : Module.Finite 𝓞F B := .right A 𝓞F B
  have : 𝓟F.IsMaximal := IsMaximal.of_isMaximal_liesOver P 𝓟F
  have : Algebra.IsIntegral A 𝓞F := Algebra.IsIntegral.tower_bot B
  let := Localization.AtPrime.algebraOfLiesOver p 𝓟F
  have : PerfectField 𝓟F.ResidueField := Algebra.IsAlgebraic.perfectField p.ResidueField
  rw [le_antisymm_iff, le_inertiaField_iff_ramificationIdx_eq_one A K L P F 𝓟F p,
    inertiaField_le_iff_ramificationIdx_eq_finrank K L P F 𝓟F, and_comm]

end arithmetic

section compositum

variable [CommRing A] [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] [Algebra A B] [IsScalarTower A B L] [IsDedekindDomain B]
  [FiniteDimensional K L] [Module.Finite A B]
  {p : Ideal A} [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [PerfectField p.ResidueField]
  (F₁ F₂ : IntermediateField K L) {B₁ B₂ : Type*}
  [CommRing B₁] [IsDedekindDomain B₁] [Algebra A B₁] [Algebra B₁ F₁] [IsFractionRing B₁ F₁]
  [Algebra B₁ B] [Algebra B₁ L] [IsScalarTower B₁ F₁ L] [IsScalarTower B₁ B L]
  [IsScalarTower A B₁ B] [Module.Flat B₁ B]
  [CommRing B₂] [IsDedekindDomain B₂] [Algebra A B₂] [Algebra B₂ F₂] [IsFractionRing B₂ F₂]
  [Algebra B₂ B] [Algebra B₂ L] [IsScalarTower B₂ F₂ L] [IsScalarTower B₂ B L]
  [IsScalarTower A B₂ B] [Module.Flat B₂ B]
  {P₁ : Ideal B₁} {P₂ : Ideal B₂} [P.LiesOver P₁] [P.LiesOver P₂] [P₁.LiesOver p] [P₂.LiesOver p]
  (C : Type*) [CommRing C] [IsIntegrallyClosed C] [Algebra A C] [Algebra C B] [Algebra C L]
  [IsScalarTower C B L] [IsScalarTower A C B] [Algebra C ↑(F₁ ⊔ F₂)] [IsFractionRing C ↑(F₁ ⊔ F₂)]
  [IsScalarTower C ↑(F₁ ⊔ F₂) L] [Module.Flat C B]
  (𝓟 : Ideal C) [P.LiesOver 𝓟] [𝓟.LiesOver p]

section Galois

variable (p) [IsGalois K L]
  [MulSemiringAction Gal(L/F₁) B] [SMulDistribClass Gal(L/F₁) B L]
  [MulSemiringAction Gal(L/F₂) B] [SMulDistribClass Gal(L/F₂) B L]
  [MulSemiringAction Gal(L/↑(F₁ ⊔ F₂)) B] [SMulDistribClass Gal(L/↑(F₁ ⊔ F₂)) B L]

include F₁ F₂ P p in
/-- If `p` is unramified in both `F₁/K` and `F₂/K`, then `p` is unramified in `(F₁ ⊔ F₂)/K`,
assuming `L/K` is Galois. -/
theorem ramificationIdx_sup_eq_one_of_isGalois
    (h₁ : P₁.ramificationIdx A = 1) (h₂ : P₂.ramificationIdx A = 1) :
    𝓟.ramificationIdx A = 1 := by
  have : FaithfulSMul A L := FaithfulSMul.trans A K L
  have : FaithfulSMul A B := FaithfulSMul.tower_bot A B L
  have : Algebra.IsIntegral B₁ B := Algebra.IsIntegral.tower_top A
  have : Algebra.IsIntegral B₂ B := Algebra.IsIntegral.tower_top A
  have : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top A
  rw [← le_inertiaField_iff_ramificationIdx_eq_one A K L P F₁ P₁ p] at h₁
  rw [← le_inertiaField_iff_ramificationIdx_eq_one A K L P F₂ P₂ p] at h₂
  rw [← le_inertiaField_iff_ramificationIdx_eq_one A K L P (F₁ ⊔ F₂) 𝓟 p]
  exact sup_le h₁ h₂

include F₁ F₂ P p in
/-- If `p` totally splits in both `F₁/K` and `F₂/K`, then `p` totally splits in `(F₁ ⊔ F₂)/K`,
assuming `L/K` is Galois. -/
theorem ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois [IsDomain C]
    (h₁ : P₁.ramificationIdx A = 1 ∧ P₁.inertiaDeg A = 1)
    (h₂ : P₂.ramificationIdx A = 1 ∧ P₂.inertiaDeg A = 1) :
    𝓟.ramificationIdx A = 1 ∧ 𝓟.inertiaDeg A = 1 := by
  have : FaithfulSMul A L := FaithfulSMul.trans A K L
  have : FaithfulSMul A B := FaithfulSMul.tower_bot A B L
  have : Algebra.IsIntegral B₁ B := Algebra.IsIntegral.tower_top A
  have : Algebra.IsIntegral B₂ B := Algebra.IsIntegral.tower_top A
  have : Algebra.IsIntegral C B := Algebra.IsIntegral.tower_top A
  rw [← le_decompositionField_iff_ramificationIdx_inertiaDeg_eq_one A K L P F₁ P₁ p] at h₁
  rw [← le_decompositionField_iff_ramificationIdx_inertiaDeg_eq_one A K L P F₂ P₂ p] at h₂
  rw [← le_decompositionField_iff_ramificationIdx_inertiaDeg_eq_one A K L P (F₁ ⊔ F₂) 𝓟 p]
  exact sup_le h₁ h₂

end Galois

omit [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]

include F₁ F₂ P p in
/-- If `p` is unramified in both `F₁/K` and `F₂/K`, then `p` is unramified in `(F₁ ⊔ F₂)/K`. -/
theorem ramificationIdx_sup_eq_one [Algebra.IsSeparable K L]
    (h₁ : P₁.ramificationIdx A = 1) (h₂ : P₂.ramificationIdx A = 1) :
    𝓟.ramificationIdx A = 1 := by
  let N := normalClosure K L (AlgebraicClosure L)
  have : IsGalois K N := ⟨⟩
  let F₁' := F₁.extendRight N
  let F₂' := F₂.extendRight N
  algebraize [((algebraMap L N).comp (algebraMap B L))]
  algebraize [((algebraMap F₁ N).comp (algebraMap B₁ F₁))]
  algebraize [((algebraMap F₂ N).comp (algebraMap B₂ F₂))]
  let D := integralClosure B N
  have : FiniteDimensional L N := Module.Finite.right K L N
  have : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  have : IsDedekindDomain D := integralClosure.isDedekindDomain B L N
  have : IsFractionRing D N := integralClosure.isFractionRing_of_finite_extension L N
  have : Module.Finite B D := IsIntegralClosure.finite B L N D
  algebraize [(algebraMap B D).comp (algebraMap A B)]
  algebraize [(algebraMap B D).comp (algebraMap C B)]
  algebraize [(algebraMap B D).comp (algebraMap B₁ B)]
  algebraize [(algebraMap B D).comp (algebraMap B₂ B)]
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  have : Module.Finite A D := Module.Finite.trans B D
  have : Algebra.IsIntegral A D := Algebra.IsIntegral.trans B
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A B N := IsScalarTower.to₁₂₄ A B L N
  have : IsScalarTower A D N := IsScalarTower.to₁₃₄ A B D N
  have : IsIntegralClosure D A N := IsIntegralClosure.of_isIntegrallyClosedIn
  let : MulSemiringAction Gal(N/K) D := IsIntegralClosure.MulSemiringAction A K N D
  have : IsScalarTower C B N := IsScalarTower.to₁₂₄ C B L N
  have : IsScalarTower C D N := IsScalarTower.to₁₃₄ C B D N
  have : IsScalarTower A C D := IsScalarTower.to₁₂₄ A C B D
  have : IsScalarTower A B₁ D := IsScalarTower.to₁₂₄ A B₁ B D
  have : IsScalarTower A B₂ D := IsScalarTower.to₁₂₄ A B₂ B D
  have : IsScalarTower B₁ L N := IsScalarTower.to₁₃₄ B₁ F₁ L N
  have : IsScalarTower B₁ B N := IsScalarTower.to₁₂₄ B₁ B L N
  have : IsScalarTower B₁ D N := IsScalarTower.to₁₃₄ B₁ B D N
  have : IsScalarTower B₂ L N := IsScalarTower.to₁₃₄ B₂ F₂ L N
  have : IsScalarTower B₂ B N := IsScalarTower.to₁₂₄ B₂ B L N
  have : IsScalarTower B₂ D N := IsScalarTower.to₁₃₄ B₂ B D N
  have : FaithfulSMul B N := FaithfulSMul.trans B L N
  have : Module.IsTorsionFree B D := Subalgebra.instIsTorsionFree (integralClosure B N)
  have : Module.Flat C D := Module.Flat.trans C B D
  have : Module.Flat B₁ D := Module.Flat.trans B₁ B D
  have : Module.Flat B₂ D := Module.Flat.trans B₂ B D
  have hsup : (F₁ ⊔ F₂).extendRight N = F₁' ⊔ F₂' :=
    IntermediateField.map_sup F₁ F₂ (Algebra.algHom K L N)
  have : IsScalarTower C ↑(F₁ ⊔ F₂) N := IsScalarTower.to₁₂₄ C ↑(F₁ ⊔ F₂) L N
  algebraize [(IntermediateField.equivOfEq hsup).toRingHom.comp
    (algebraMap C ↥((F₁ ⊔ F₂).extendRight N))]
  have : IsFractionRing C ↑(F₁' ⊔ F₂') :=
    IsFractionRing.of_algEquiv
      (AlgEquiv.ofCommutes (IntermediateField.equivOfEq hsup).toRingEquiv fun _ ↦ rfl :
        ↑((F₁ ⊔ F₂).extendRight N) ≃ₐ[C] ↑(F₁' ⊔ F₂'))
  have : IsScalarTower C ↑(F₁' ⊔ F₂') N := IsScalarTower.of_algebraMap_eq' rfl
  -- the Galois actions relative to the intermediate fields
  let : MulSemiringAction Gal(N/F₁') D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/F₁') D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  let : MulSemiringAction Gal(N/F₂') D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/F₂') D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  let : MulSemiringAction Gal(N/↑(F₁' ⊔ F₂')) D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/↑(F₁' ⊔ F₂')) D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  obtain ⟨Q, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := D) P
  have : Q.LiesOver p := LiesOver.trans Q P p
  have : Q.LiesOver P₁ := LiesOver.trans Q P P₁
  have : Q.LiesOver P₂ := LiesOver.trans Q P P₂
  have : Q.LiesOver 𝓟 := LiesOver.trans Q P 𝓟
  exact ramificationIdx_sup_eq_one_of_isGalois K N Q p F₁' F₂' C 𝓟 h₁ h₂

include F₁ F₂ P p in
/-- If `p` is unramified in both `F₁/K` and `F₂/K`, then `p` is unramified in `(F₁ ⊔ F₂)/K`. -/
theorem ramificationIdx_inertiaDeg_sup_eq_one [IsDomain C] [Algebra.IsSeparable K L]
    (h₁ : P₁.ramificationIdx A = 1 ∧ P₁.inertiaDeg A = 1)
    (h₂ : P₂.ramificationIdx A = 1 ∧ P₂.inertiaDeg A = 1) :
    𝓟.ramificationIdx A = 1 ∧ 𝓟.inertiaDeg A = 1 := by
  let N := normalClosure K L (AlgebraicClosure L)
  have : IsGalois K N := ⟨⟩
  let F₁' := F₁.extendRight N
  let F₂' := F₂.extendRight N
  algebraize [((algebraMap L N).comp (algebraMap B L))]
  algebraize [((algebraMap F₁ N).comp (algebraMap B₁ F₁))]
  algebraize [((algebraMap F₂ N).comp (algebraMap B₂ F₂))]
  let D := integralClosure B N
  have : FiniteDimensional L N := Module.Finite.right K L N
  have : Algebra.IsSeparable L N := Algebra.isSeparable_tower_top_of_isSeparable K L N
  have : IsDedekindDomain D := integralClosure.isDedekindDomain B L N
  have : IsFractionRing D N := integralClosure.isFractionRing_of_finite_extension L N
  have : Module.Finite B D := IsIntegralClosure.finite B L N D
  algebraize [(algebraMap B D).comp (algebraMap A B)]
  algebraize [(algebraMap B D).comp (algebraMap C B)]
  algebraize [(algebraMap B D).comp (algebraMap B₁ B)]
  algebraize [(algebraMap B D).comp (algebraMap B₂ B)]
  algebraize [(algebraMap L N).comp (algebraMap C L)]
  have : Module.Finite A D := Module.Finite.trans B D
  have : Algebra.IsIntegral A D := Algebra.IsIntegral.trans B
  have : IsScalarTower A L N := IsScalarTower.to₁₃₄ A K L N
  have : IsScalarTower A B N := IsScalarTower.to₁₂₄ A B L N
  have : IsScalarTower A D N := IsScalarTower.to₁₃₄ A B D N
  have : IsIntegralClosure D A N := IsIntegralClosure.of_isIntegrallyClosedIn
  let : MulSemiringAction Gal(N/K) D := IsIntegralClosure.MulSemiringAction A K N D
  have : IsScalarTower C B N := IsScalarTower.to₁₂₄ C B L N
  have : IsScalarTower C D N := IsScalarTower.to₁₃₄ C B D N
  have : IsScalarTower A C D := IsScalarTower.to₁₂₄ A C B D
  have : IsScalarTower A B₁ D := IsScalarTower.to₁₂₄ A B₁ B D
  have : IsScalarTower A B₂ D := IsScalarTower.to₁₂₄ A B₂ B D
  have : IsScalarTower B₁ L N := IsScalarTower.to₁₃₄ B₁ F₁ L N
  have : IsScalarTower B₁ B N := IsScalarTower.to₁₂₄ B₁ B L N
  have : IsScalarTower B₁ D N := IsScalarTower.to₁₃₄ B₁ B D N
  have : IsScalarTower B₂ L N := IsScalarTower.to₁₃₄ B₂ F₂ L N
  have : IsScalarTower B₂ B N := IsScalarTower.to₁₂₄ B₂ B L N
  have : IsScalarTower B₂ D N := IsScalarTower.to₁₃₄ B₂ B D N
  have : FaithfulSMul B N := FaithfulSMul.trans B L N
  have : Module.IsTorsionFree B D := Subalgebra.instIsTorsionFree (integralClosure B N)
  have : Module.Flat C D := Module.Flat.trans C B D
  have : Module.Flat B₁ D := Module.Flat.trans B₁ B D
  have : Module.Flat B₂ D := Module.Flat.trans B₂ B D
  have hsup : (F₁ ⊔ F₂).extendRight N = F₁' ⊔ F₂' :=
    IntermediateField.map_sup F₁ F₂ (Algebra.algHom K L N)
  have : IsScalarTower C ↑(F₁ ⊔ F₂) N := IsScalarTower.to₁₂₄ C ↑(F₁ ⊔ F₂) L N
  algebraize [(IntermediateField.equivOfEq hsup).toRingHom.comp
    (algebraMap C ↥((F₁ ⊔ F₂).extendRight N))]
  have : IsFractionRing C ↑(F₁' ⊔ F₂') :=
    IsFractionRing.of_algEquiv
      (AlgEquiv.ofCommutes (IntermediateField.equivOfEq hsup).toRingEquiv fun _ ↦ rfl :
        ↑((F₁ ⊔ F₂).extendRight N) ≃ₐ[C] ↑(F₁' ⊔ F₂'))
  have : IsScalarTower C ↑(F₁' ⊔ F₂') N := IsScalarTower.of_algebraMap_eq' rfl
  -- the Galois actions relative to the intermediate fields
  let : MulSemiringAction Gal(N/F₁') D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/F₁') D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  let : MulSemiringAction Gal(N/F₂') D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/F₂') D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  let : MulSemiringAction Gal(N/↑(F₁' ⊔ F₂')) D :=
    MulSemiringAction.compHom D (AlgEquiv.restrictScalarsHom K)
  have : SMulDistribClass Gal(N/↑(F₁' ⊔ F₂')) D N :=
    ⟨fun g d n ↦ smul_distrib_smul (AlgEquiv.restrictScalarsHom K g) d n⟩
  obtain ⟨Q, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := D) P
  have : Q.LiesOver p := LiesOver.trans Q P p
  have : Q.LiesOver P₁ := LiesOver.trans Q P P₁
  have : Q.LiesOver P₂ := LiesOver.trans Q P P₂
  have : Q.LiesOver 𝓟 := LiesOver.trans Q P 𝓟
  exact ramificationIdx_inertiaDeg_sup_eq_one_of_isGalois K N Q p F₁' F₂' C 𝓟 h₁ h₂

end compositum

end IntermediateField

end Ideal

section deprecated

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] (p : Ideal A) (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.

Superseded by the ring-level `Ideal.IsDecompositionRing`.
-/
@[mk_iff, deprecated "Replaced by the ring-level predicate `Ideal.IsDecompositionRing`. \
A decomposition field is recovered as the fraction field of a decomposition ring."
(since := "2026-07-10")]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

@[deprecated "Superseded by the ring-level predicate `Ideal.IsDecompositionRing`."
(since := "2026-07-10")]
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D := { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed by the inertia
subgroup of `P` in `Gal(L/K)`.

Superseded by the ring-level `Ideal.IsInertiaRing`.
-/
@[mk_iff, deprecated "Replaced by the ring-level predicate `Ideal.IsInertiaRing`. \
An inertia field is recovered as the fraction field of an inertia ring." (since := "2026-07-10")]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

@[deprecated "Superseded by the ring-level predicate `Ideal.IsInertiaRing`."
(since := "2026-07-10")]
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaField K L P E := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

@[deprecated "Superseded by the ring-level predicate `Ideal.IsDecompositionRing`."
(since := "2026-07-10")]
instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

@[deprecated "Superseded by the ring-level predicate `Ideal.IsInertiaRing`."
(since := "2026-07-10")]
instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B]

section of_isGaloisGroup

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]

@[deprecated "No longer needed with the abstract-group predicate \
`Ideal.IsDecompositionRing`." (since := "2026-07-10")]
theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

@[deprecated "No longer needed with the abstract-group predicate \
`Ideal.IsInertiaRing`." (since := "2026-07-10")]
theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) E L] :
    IsInertiaField K L P E := by
  refine (isInertiaField_iff K L P E).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end of_isGaloisGroup

variable (D' : Type*) [Field D'] [Algebra D' L] (E' : Type*) [Field E'] [Algebra E' L]

/-- Two decomposition fields are isomorphic. Superseded by
`IsGaloisGroup.ringEquiv`. -/
@[deprecated "Use the ring-level `IsGaloisGroup.ringEquiv`." (since := "2026-07-10")]
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[deprecated "Use the ring-level \
`IsGaloisGroup.algebraMap_ringEquiv_apply`." (since := "2026-07-10")]
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[deprecated "Use the ring-level \
`IsGaloisGroup.algebraMap_ringEquiv_symm_apply`." (since := "2026-07-10")]
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia fields are isomorphic. Superseded by `IsGaloisGroup.ringEquiv`. -/
@[deprecated "Use the ring-level `IsGaloisGroup.ringEquiv`." (since := "2026-07-10")]
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[deprecated "Use the ring-level \
`IsGaloisGroup.algebraMap_ringEquiv_apply`." (since := "2026-07-10")]
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[deprecated "Use the ring-level \
`IsGaloisGroup.algebraMap_ringEquiv_symm_apply`." (since := "2026-07-10")]
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E') :
    algebraMap E L ((IsInertiaField.ringEquiv K L P E E').symm x) = algebraMap E' L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [p.IsPrime] [Algebra.HasSeparableResidueFieldsAt A B p] [P.IsPrime]

variable (D : Type*) [Field D] [Algebra D L]

include K P

/--
The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`.
-/
@[deprecated "Use the ring-level `Ideal.IsDecompositionRing.finrank_top`." (since := "2026-07-10")]
theorem IsDecompositionField.rank_left [IsDecompositionField K L P D] :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p]

/--
The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`.
-/
@[deprecated "Use the ring-level `Ideal.IsDecompositionRing.finrank_bot`." (since := "2026-07-10")]
theorem IsDecompositionField.rank_right [IsDecompositionField K L P D] [IsGalois K L]
    [Algebra K D] [IsScalarTower K D L] :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L p P D,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L]

/--
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p` in `B`.
-/
@[deprecated "Use the ring-level `Ideal.IsInertiaRing.finrank_top`." (since := "2026-07-10")]
theorem IsInertiaField.rank_left [IsInertiaField K L P E] :
    Module.finrank E L = p.ramificationIdxIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L, card_inertia_eq_ramificationIdxIn p]

/--
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
@[deprecated "Use the ring-level `Ideal.IsInertiaRing.finrank_bot`." (since := "2026-07-10")]
theorem IsInertiaField.rank_right [IsInertiaField K L P E] [IsGalois K L] [Algebra K E]
    [IsScalarTower K E L] :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L p P E, mul_assoc, mul_comm (p.inertiaDegIn B),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/--
The degree `[E : D]` of the inertia field `E` over the decomposition field `D` equals the
inertia degree of `p` in `B`.
-/
@[deprecated "Use the ring-level \
`Ideal.IsInertiaRing.finrank_decompositionRing`." (since := "2026-07-10")]
theorem IsInertiaField.rank_decompositionField [IsDecompositionField K L P D]
    [IsInertiaField K L P E] [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] :
    Module.finrank D E = p.inertiaDegIn B := by
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L p P E, IsDecompositionField.rank_right A K L p P D,
    mul_right_inj'] at this
  obtain ⟨⟨Q, hQ⟩⟩ : Nonempty (p.primesOver B) := inferInstance
  exact Set.ncard_ne_zero_of_mem hQ (Algebra.QuasiFinite.finite_primesOver p)

end rank

section splitting

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

namespace IsDecompositionField

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D]

include K L D in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `P` is the only prime of `L` above `𝓟D`.
-/
@[deprecated Ideal.IsDecompositionRing.primesOver_eq_singleton +typeChanged (since := "2026-11-14")]
theorem primesOver_eq_singleton [IsDecompositionField K L P D] [hP : P.IsPrime]
    [Finite (stabilizer Gal(L/K) P)] [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} :=
  have := IsDecompositionRing.of_isFractionRing L Gal(L/K) P 𝓞D D
  IsDecompositionRing.primesOver_eq_singleton Gal(L/K) P 𝓞D 𝓟D

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B]
  [IsDedekindDomain 𝓞D]

omit [P.LiesOver p] hD in
include K L D P in
@[deprecated "Only used by deprecated lemmas." (since := "2026-11-14")]
private lemma instances [IsDecompositionField K L P D] :
    Module.Finite 𝓞D B ∧ Module.IsTorsionFree 𝓞D B ∧ FaithfulSMul 𝓞D B ∧
      Module.IsTorsionFree A 𝓞D ∧ IsGaloisGroup Gal(L/K) A B ∧
      P.IsDecompositionRing Gal(L/K) 𝓞D := by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : FaithfulSMul 𝓞D B := Module.isTorsionFree_iff_faithfulSMul.mp inst₂
  have inst₄ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₅ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅,
    IsDecompositionRing.of_isFractionRing L Gal(L/K) P 𝓞D D⟩

variable [p.IsPrime] [Algebra.HasSeparableResidueFieldsAt A B p] [P.IsMaximal]

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of `p` in `L`.
-/
@[deprecated Ideal.IsDecompositionRing.ramificationIdxIn_eq +typeChanged (since := "2026-11-14")]
theorem ramificationIdxIn_eq [IsDecompositionField K L P D] :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.ramificationIdxIn_eq Gal(L/K) P 𝓞D p 𝓟D

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in `L`.
-/
@[deprecated Ideal.IsDecompositionRing.inertiaDegIn_eq +typeChanged (since := "2026-11-14")]
theorem inertiaDegIn_eq [IsDecompositionField K L P D] :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.inertiaDegIn_eq Gal(L/K) P 𝓞D p 𝓟D

include K L D p P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
@[deprecated Ideal.IsDecompositionRing.ramificationIdx_eq_one +typeChanged (since := "2026-11-14")]
theorem ramificationIdx_eq [IsDecompositionField K L P D] :
    𝓟D.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.ramificationIdx_eq_one Gal(L/K) P 𝓞D p 𝓟D

include K L D p P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
@[deprecated Ideal.IsDecompositionRing.inertiaDeg_eq_one +typeChanged (since := "2026-11-14")]
theorem inertiaDeg_eq [IsDecompositionField K L P D] :
    𝓟D.inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.inertiaDeg_eq_one Gal(L/K) P 𝓞D p 𝓟D

end IsDecompositionField

end splitting

end deprecated
