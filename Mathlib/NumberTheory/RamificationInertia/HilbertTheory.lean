/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

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

The field-level predicates `IsDecompositionField` and `IsInertiaField` defined below will be
deprecated in favor of the ring-level predicates `Ideal.IsDecompositionRing` and
`Ideal.IsInertiaRing`.

-/

@[expose] public section

namespace Ideal

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B]
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

variable (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
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

variable [IsDomain B] {A : Type*} [CommRing A] [IsDomain A] [Algebra A B] [Module.Finite A B]
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

variable {A : Type*} [CommRing A] [Algebra A B] [Algebra A R] [IsScalarTower A R B]
  (p : Ideal A) [P.LiesOver p] (𝓟 : Ideal R) [P.LiesOver 𝓟] [P.IsDecompositionRing G R]

namespace IsDecompositionRing

/-- Let `R` be a decomposition ring of `P` and `𝓟` the prime of `R` below `P`. Then `P` is the
only prime of `B` above `𝓟`. -/
theorem primesOver_eq_singleton [P.IsPrime] [Finite (stabilizer G P)] :
    𝓟.primesOver B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, fun Q ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := 𝓟.exists_smul_eq_of_isGaloisGroup P Q (stabilizer G P)
  exact σ.prop

include G P in
/-- If `R` is a decomposition ring of `P` and `𝓟` is the prime of `R` below `P`, then any prime
of `B` above `𝓟` is equal to `P`. -/
theorem eq_of_liesOver [P.IsPrime] [Finite (stabilizer G P)] (Q : Ideal B) [Q.IsPrime]
    [Q.LiesOver 𝓟] : Q = P := by
  have := primesOver_eq_singleton G P R 𝓟
  rw [Set.eq_singleton_iff_unique_mem] at this
  exact this.2 Q ⟨inferInstance, inferInstance⟩

variable [IsGaloisGroup G A B] [IsDomain A] [IsDomain B] [FaithfulSMul R B]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat R B] [p.IsPrime]
  [Algebra.HasSeparableResidueFieldsAt A B p] [P.IsPrime]

include G P in
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq :
    𝓟.ramificationIdxIn B = p.ramificationIdxIn B ∧ 𝓟.inertiaDegIn B = p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  have : 𝓟.IsPrime := P.isPrime_of_liesOver 𝓟
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R B).isDomain
  have : Module.Finite R B := Module.Finite.right A R B
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero (stabilizer G P)
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero (stabilizer G P)
  · rw [p.ramificationIdxIn_eq_ramificationIdx P G,
      𝓟.ramificationIdxIn_eq_ramificationIdx P (stabilizer G P)]
    exact 𝓟.ramificationIdx_above_le P
  · rw [p.inertiaDegIn_eq_inertiaDeg P G, 𝓟.inertiaDegIn_eq_inertiaDeg P (stabilizer G P)]
    exact 𝓟.inertiaDeg_above_le P
  · have := 𝓟.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn B (stabilizer G P)
    rw [primesOver_eq_singleton G P, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank' (stabilizer G P) R B, finrank_top G P R p]

include G P in
/-- The ramification index of `𝓟` in `B` equals the ramification index of `p` in `B`. -/
theorem ramificationIdxIn_eq :
    𝓟.ramificationIdxIn B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P R p 𝓟).1

include G P in
/-- The inertia degree of `𝓟` in `B` equals the inertia degree of `p` in `B`. -/
theorem inertiaDegIn_eq :
    𝓟.inertiaDegIn B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P R p 𝓟).2

include G P in
/-- The ramification index of `P` over `R` equals the ramification index of `p` in `B`. -/
theorem ramificationIdx_eq :
    P.ramificationIdx R = p.ramificationIdxIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← (P.under R).ramificationIdxIn_eq_ramificationIdx P (stabilizer G P),
    ramificationIdxIn_eq G P R p (P.under R)]

include G P in
/-- The inertia degree of `P` over `R` equals the inertia degree of `p` in `B`. -/
theorem inertiaDeg_eq :
    P.inertiaDeg R = p.inertiaDegIn B := by
  have := IsGaloisGroup.finite G A B
  rw [← (P.under R).inertiaDegIn_eq_inertiaDeg P (stabilizer G P),
    inertiaDegIn_eq G P R p (P.under R)]

include G P p in
/-- The ramification index of `𝓟` over `A` equals `1`. -/
theorem ramificationIdx_eq_one :
    𝓟.ramificationIdx A = 1 := by
  have := IsGaloisGroup.finite G A B
  have := 𝓟.ramificationIdx_tower (R := A) P
  rwa [← 𝓟.ramificationIdxIn_eq_ramificationIdx P (stabilizer G P),
    ramificationIdxIn_eq G P R p 𝓟, p.ramificationIdxIn_eq_ramificationIdx P G,
    right_eq_mul₀ (P.ramificationIdx_pos A).ne'] at this

include G P p in
/-- The inertia degree of `𝓟` over `A` equals `1`. -/
theorem inertiaDeg_eq_one :
    𝓟.inertiaDeg A = 1 := by
  have := IsGaloisGroup.finite G A B
  have : 𝓟.IsPrime := P.isPrime_of_liesOver 𝓟
  have : Module.Finite R B := Module.Finite.right A R B
  have := 𝓟.inertiaDeg_tower (R := A) P
  rwa [← p.inertiaDegIn_eq_inertiaDeg P G, ← inertiaDegIn_eq G P R p 𝓟,
    ← 𝓟.inertiaDegIn_eq_inertiaDeg P (stabilizer G P),
    right_eq_mul₀ <| inertiaDegIn_ne_zero (stabilizer G P)] at this

end IsDecompositionRing

end splitting

end Ideal

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] (p : Ideal A) (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D := { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed by the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaField K L P E := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B]

section of_isGaloisGroup

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]

/--
If `G` is a Galois group for `L/K` and the stabilizer of `P` in `G` is a Galois group for
`L/D`, then `D` is a decomposition field for `P`.
-/
theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

/--
If `G` is a Galois group for `L/K` and the inertia group of `P` in `G` is a Galois group for
`L/E`, then `E` is an inertia field for `P`.
-/
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

/-- Two decomposition fields are isomorphic. -/
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia fields are isomorphic. -/
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
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

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P

/--
The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`.
-/
theorem IsDecompositionField.rank_left :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p]

/--
The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`.
-/
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L] :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L p P D,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

/--
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p` in `B`.
-/
theorem IsInertiaField.rank_left :
    Module.finrank E L = p.ramificationIdxIn B := by
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L, card_inertia_eq_ramificationIdxIn p]

/--
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] :
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
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
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

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D]

include K L D in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `P` is the only prime of `L` above `𝓟D`.
-/
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} :=
  have := IsDecompositionRing.of_isFractionRing Gal(L/K) P 𝓞D L D
  IsDecompositionRing.primesOver_eq_singleton Gal(L/K) P 𝓞D 𝓟D

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B]
  [IsDedekindDomain 𝓞D]

omit [P.LiesOver p] hD in
include K L D P in
private lemma instances :
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
    IsDecompositionRing.of_isFractionRing Gal(L/K) P 𝓞D L D⟩

variable [p.IsPrime] [Algebra.HasSeparableResidueFieldsAt A B p] [P.IsMaximal]

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of `p` in `L`.
-/
theorem ramificationIdxIn_eq :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.ramificationIdxIn_eq Gal(L/K) P 𝓞D p 𝓟D

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in `L`.
-/
theorem inertiaDegIn_eq :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.inertiaDegIn_eq Gal(L/K) P 𝓞D p 𝓟D

include K L D p P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
theorem ramificationIdx_eq :
    𝓟D.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.ramificationIdx_eq_one Gal(L/K) P 𝓞D p 𝓟D

include K L D p P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
theorem inertiaDeg_eq :
    𝓟D.inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D
  exact IsDecompositionRing.inertiaDeg_eq_one Gal(L/K) P 𝓞D p 𝓟D

end IsDecompositionField

end splitting
