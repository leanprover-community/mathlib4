/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!

# Decomposition and inertia rings

We develop Hilbert's theory of the splitting of a prime ideal in a Galois extension, working at the
level of rings.

## Ring predicates

Let `G` be a group acting on a commutative ring `B` and let `P` be a prime ideal of `B`. For an
intermediate ring `C` of `B`, we introduce two characteristic predicates:

* `Ideal.IsDecompositionRing G P C`: `B` is Galois over `C` with Galois group the *decomposition
  group* of `P`, that is the stabilizer of `P` in `G`;
* `Ideal.IsInertiaRing G P C`: `B` is Galois over `C` with Galois group the *inertia group* of `P`,
  that is the subgroup of `G` acting trivially modulo `P`.

## Decomposition and inertia fields

In the classical setting, `L/K` is a Galois extension of fields with `G = Gal(L/K)`, and `A`, `B`
are subrings of `K` and `L` with `K` the fraction field of `A`, `L` that of `B`, and `B` the
integral closure of `A` in `L`. For `P` a prime of `B` lying over `p` of `A`, the *decomposition
field* `D` (resp. *inertia field* `E`) is the subfield of `L` fixed by the decomposition (resp.
inertia) group of `P`. The corresponding decomposition (resp. inertia) ring is the integral closure
of `A` in `D` (resp. `E`), and one passes between the ring and field statements through the fraction
fields (see `Ideal.IsDecompositionRing.of_isFractionRing`).

Writing `e`, `f` for the ramification index and inertia degree of `P` over `p`, `g` for the number
of primes of `B` above `p`, and `𝓟D`, `𝓟E` for the primes of `D`, `E` below `P`:
```
degree            ramif. index   inertia deg.
        L      P
  e     |      |      e               1
        E      𝓟E
  f     |      |      1               f
        D      𝓟D
  g     |      |      1               1
        K      p
```

-/

@[expose] public section

namespace Ideal

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B]
  (P : Ideal B) (C : Type*) [CommRing C] [Algebra C B]

open MulAction Pointwise

section basic

/-- `P.IsDecompositionRing G C` states that the intermediate ring `C` of `B` is a *decomposition
ring* of the prime `P`: the ring `B` is Galois over `C` with Galois group the *decomposition group*
of `P`, that is the stabilizer of `P` under the action of `G`.

This is the ring-level characteristic predicate; the classical decomposition *field* is
recovered by passing to fraction fields. -/
@[mk_iff]
class IsDecompositionRing extends IsGaloisGroup (stabilizer G P) C B

instance [h : IsGaloisGroup (stabilizer G P) C B] : IsDecompositionRing G P C where
  toIsGaloisGroup := h

/-- `P.IsInertiaRing G C` states that the intermediate ring `C` of `B` is an *inertia ring* of the
prime `P`: the ring `B` is Galois over `C` with Galois group the *inertia group* of `P`, that is the
elements of `G` acting trivially modulo `P` (a subgroup of the decomposition group).

This is the ring-level characteristic predicate; the classical inertia *field* is recovered by
passing to fraction fields. -/
@[mk_iff]
class IsInertiaRing extends IsGaloisGroup (inertia G P) C B

instance [h : IsGaloisGroup (inertia G P) C B] : IsInertiaRing G P C where
  toIsGaloisGroup := h

variable (C' : Type*) [CommRing C'] [Algebra C' B]

/-- Two decomposition rings are isomorphic. -/
noncomputable def IsDecompositionRing.ringEquiv [IsDecompositionRing G P C]
    [IsDecompositionRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] :
    C ≃+* C' :=
  IsGaloisGroup.ringEquiv (stabilizer G P) C C' B

@[simp]
theorem IsDecompositionRing.algebraMap_ringEquiv_apply [IsDecompositionRing G P C]
    [IsDecompositionRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] (x : C) :
    algebraMap C' B (IsDecompositionRing.ringEquiv G P C C' x) = algebraMap C B x := by
  simp [IsDecompositionRing.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
theorem IsDecompositionRing.algebraMap_ringEquiv_symm_apply [IsDecompositionRing G P C]
    [IsDecompositionRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] (x : C') :
    algebraMap C B ((IsDecompositionRing.ringEquiv G P C C').symm x) = algebraMap C' B x := by
  simp [IsDecompositionRing.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia rings are isomorphic. -/
noncomputable def IsInertiaRing.ringEquiv [IsInertiaRing G P C]
    [IsInertiaRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] :
    C ≃+* C' :=
  IsGaloisGroup.ringEquiv (inertia G P) C C' B

@[simp]
theorem IsInertiaRing.algebraMap_ringEquiv_apply [IsInertiaRing G P C]
    [IsInertiaRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] (x : C) :
    algebraMap C' B (IsInertiaRing.ringEquiv G P C C' x) = algebraMap C B x := by
  simp [IsInertiaRing.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
theorem IsInertiaRing.algebraMap_ringEquiv_symm_apply [IsInertiaRing G P C]
    [IsInertiaRing G P C'] [FaithfulSMul C B] [FaithfulSMul C' B] (x : C') :
    algebraMap C B ((IsInertiaRing.ringEquiv G P C C').symm x) = algebraMap C' B x := by
  simp [IsInertiaRing.ringEquiv, IsGaloisGroup.ringEquiv]

variable (A K L : Type*) [CommRing A] [Field K] [Field L] [Algebra B L] [IsFractionRing B L]
  [Algebra A B] [Algebra A L] [IsScalarTower A B L] [Algebra K L]
  [MulSemiringAction Gal(L/K) B] [SMulDistribClass Gal(L/K) B L]

/-- If `L` is Galois over the field `D` with the decomposition group of `P` (so `D` is the
decomposition field of `P`), and `C` is an integrally closed subring of `D` with fraction field `D`
such that `B` is integral over `C`, then `C` is a decomposition ring of `P`. -/
theorem IsDecompositionRing.of_isFractionRing (C D : Type*) [CommRing C] [Algebra C B] [Field D]
    [Algebra C D] [Algebra C L] [Algebra D L] [IsScalarTower C D L] [IsScalarTower C B L]
    [IsFractionRing C D] [IsIntegrallyClosed C] [Algebra.IsIntegral C B]
    [IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionRing Gal(L/K) P C :=
  {toIsGaloisGroup := .of_isFractionRing (stabilizer Gal(L/K) P) C B D L}

/-- If `L` is Galois over the field `E` with the inertia group of `P` (so `E` is the inertia field
of `P`), and `C` is an integrally closed subring of `E` with fraction field `E` such that `B` is
integral over `C`, then `C` is an inertia ring of `P`. -/
theorem IsInertiaRing.of_isFractionRing (C E : Type*) [CommRing C] [Algebra C B] [Field E]
    [Algebra C E] [Algebra C L] [Algebra E L] [IsScalarTower C E L] [IsScalarTower C B L]
    [IsFractionRing C E] [IsIntegrallyClosed C] [Algebra.IsIntegral C B]
    [IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaRing Gal(L/K) P C :=
  {toIsGaloisGroup := .of_isFractionRing (inertia Gal(L/K) P) C B E L}

end basic

section rank

variable [IsDomain B] [Finite G] {A : Type*} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
  [Algebra A B] [Module.Finite A B] [Module.Flat A B] [IsGaloisGroup G A B] {p : Ideal A}
  [P.LiesOver p]

/-! ### Ring-level degree formulas -/

/-- The degree `[B : C]` of `B` over the decomposition ring `C` equals the product of the
ramification index and the inertia degree of `p` in `B`. -/
-- TODO: this should also hold for `p = ⊥`, then `P = ⊥`, `A` and `B` are fields and `C = B`.
theorem IsDecompositionRing.finrank_eq [FaithfulSMul C B] [P.IsMaximal]
    [P.IsDecompositionRing G C] (hp : p ≠ ⊥) :
    Module.finrank C B = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank' (stabilizer G P) C B, card_stabilizer_eq p]

/-- The degree `[B : C]` of `B` over the inertia ring `C` equals the ramification index of `p`
in `B`. -/
theorem IsInertiaRing.finrank_eq [FaithfulSMul C B] [P.IsMaximal] [P.IsInertiaRing G C]
    (hp : p ≠ ⊥) :
    Module.finrank C B = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank' (inertia G P) C B, card_inertia_eq_ramificationIdxIn p]

/-! ### Fraction-field degree formulas -/

variable [FaithfulSMul C B] (K L : Type*) [Field K] [Field L] [Algebra A C] [IsScalarTower A C B]
  [Algebra B L] [IsFractionRing B L] [Algebra C L] [IsScalarTower C B L]

/-- The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`. -/
theorem IsDecompositionRing.rank_left (D : Type*) [Field D] [Algebra C D]
    [IsFractionRing C D] [Algebra D L] [IsScalarTower C D L] [P.IsMaximal]
    [P.IsDecompositionRing G C] (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : Module.Finite C B := Module.Finite.right A C B
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing C D B L, finrank_eq G P C hp]

/-- The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p`
in `B`. -/
theorem IsInertiaRing.rank_left (E : Type*) [Field E] [Algebra C E]
    [IsFractionRing C E] [Algebra E L] [IsScalarTower C E L] [P.IsMaximal] [P.IsInertiaRing G C]
    (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : Module.Finite C B := Module.Finite.right A C B
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing C E B L, finrank_eq G P C hp]

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [IsScalarTower A B L] [MulSemiringAction G L] [SMulDistribClass G B L]

/-- The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`. -/
theorem IsDecompositionRing.rank_right (D : Type*) [Field D]
    [Algebra C D] [IsFractionRing C D] [Algebra K D] [Algebra D L] [IsScalarTower C D L]
    [IsScalarTower K D L] [P.IsMaximal] [P.IsDecompositionRing G C] (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : IsGaloisGroup (stabilizer G P) D L := .to_isFractionRing (stabilizer G P) C B D L
  have : IsGaloisGroup G K L := IsGaloisGroup.to_isFractionRing G A B K L
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  rw [← mul_left_inj' (c := Module.finrank D L) Module.finrank_pos.ne', Module.finrank_mul_finrank,
    IsDecompositionRing.rank_left G P C L D hp, ← IsGaloisGroup.card_eq_finrank G,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]

/-- The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`. -/
theorem IsInertiaRing.rank_right (E : Type*) [Field E] [Algebra C E]
    [IsFractionRing C E] [Algebra K E] [Algebra E L] [IsScalarTower C E L] [IsScalarTower K E L]
    [P.IsMaximal] [P.IsInertiaRing G C] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : IsGaloisGroup (inertia G P) E L := .to_isFractionRing (inertia G P) C B E L
  have : IsGaloisGroup G K L := IsGaloisGroup.to_isFractionRing G A B K L
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional K L := IsGaloisGroup.finiteDimensional G K L
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  rw [← mul_left_inj' (c := Module.finrank E L) Module.finrank_pos.ne', Module.finrank_mul_finrank,
    IsInertiaRing.rank_left G P C L E hp, ← IsGaloisGroup.card_eq_finrank G, mul_assoc,
    mul_comm (p.inertiaDegIn B), ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]

/-- The degree `[E : D]` of the inertia field `E` over the decomposition field `D` equals the
inertia degree of `p` in `B`. Here `C` is a decomposition ring (fraction field `D`) and `C'` an
inertia ring (fraction field `E`). -/
theorem IsInertiaRing.rank_decompositionRing (C' D E : Type*)
    [CommRing C'] [Algebra C' B] [Field D] [Field E]
    [Algebra A C'] [Algebra C D] [Algebra C' E] [Algebra C' L] [Algebra K D] [Algebra K E]
    [Algebra D L] [Algebra E L] [Algebra D E]
    [IsFractionRing C D] [IsFractionRing C' E]
    [IsScalarTower A C' B] [IsScalarTower C D L] [IsScalarTower C' B L] [IsScalarTower C' E L]
    [IsScalarTower K D L] [IsScalarTower K E L] [IsScalarTower K D E]
    [FaithfulSMul C' B] [IsDedekindRing B] [P.IsMaximal]
    [P.IsDecompositionRing G C] [P.IsInertiaRing G C'] (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaRing.rank_right G P C' K L E hp, IsDecompositionRing.rank_right G P C K L D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero _ _

end rank

section splitting

/-! ### Splitting of a prime in a decomposition ring -/

variable {A : Type*} [CommRing A] [Algebra A B] [Algebra A C] [IsScalarTower A C B]
  {p : Ideal A} [P.LiesOver p] (𝓟 : Ideal C) [P.LiesOver 𝓟] [P.IsDecompositionRing G C]

namespace IsDecompositionRing

/-- Let `C` be a decomposition ring of `P` and `𝓟` the prime of `C` below `P`. Then `P` is the
only prime of `B` above `𝓟`. -/
theorem primesOver_eq_singleton [P.IsPrime] [Finite (stabilizer G P)] :
    primesOver 𝓟 B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, fun Q ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟 P Q (stabilizer G P)
  exact σ.prop

variable [Finite G] [IsGaloisGroup G A B] [IsDomain A] [IsDomain B] [FaithfulSMul C B]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat C B] [Ring.HasFiniteQuotients A]
  [𝓟.IsMaximal] [P.IsMaximal]

include G P in
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟 B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟 B = p.inertiaDegIn B := by
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  have : Module.Finite C B := Module.Finite.right A C B
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero (stabilizer G P)
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero (stabilizer G P)
  · rw [ramificationIdxIn_eq_ramificationIdx p P G,
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer G P)]
    exact 𝓟.ramificationIdx_above_le P
  · rw [inertiaDegIn_eq_inertiaDeg p P G, inertiaDegIn_eq_inertiaDeg _ P (stabilizer G P)]
    exact 𝓟.inertiaDeg_above_le P
  · have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟 B (stabilizer G P)
    rw [primesOver_eq_singleton G P, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank' (stabilizer G P) C B,
      IsDecompositionRing.finrank_eq G P C hp]

include G P in
/-- The ramification index of `𝓟` in `B` equals the ramification index of `p` in `B`. -/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟 B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P C 𝓟 hp).1

include G P in
/-- The inertia degree of `𝓟` in `B` equals the inertia degree of `p` in `B`. -/
theorem inertiaDegIn_eq (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟 B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq G P C 𝓟 hp).2

include G P in
/-- `𝓟` is unramified over `A`. -/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    𝓟.ramificationIdx A = 1 := by
  have := ramificationIdx_tower (R := A) 𝓟 P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟 P (stabilizer G P), ramificationIdxIn_eq G P C 𝓟 hp,
    ramificationIdxIn_eq_ramificationIdx p P G, right_eq_mul₀ (ramificationIdx_pos P A).ne'] at this

include G P in
/-- The inertia degree of `𝓟` over `A` equals `1`. -/
theorem inertiaDeg_eq (hp : p ≠ ⊥) :
    𝓟.inertiaDeg A = 1 := by
  have : Module.Finite C B := Module.Finite.right A C B
  have := inertiaDeg_tower (R := A) 𝓟 P
  rwa [← inertiaDegIn_eq_inertiaDeg p P G, ← inertiaDegIn_eq G P C 𝓟 hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟 P (stabilizer G P),
    right_eq_mul₀ <| inertiaDegIn_ne_zero (stabilizer G P)] at this

end IsDecompositionRing

end splitting

end Ideal

section deprecated

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

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
`Ideal.IsDecompositionRing.ringEquiv`. -/
@[deprecated Ideal.IsDecompositionRing.ringEquiv (since := "2026-07-10")]
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[deprecated Ideal.IsDecompositionRing.algebraMap_ringEquiv_apply (since := "2026-07-10")]
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[deprecated Ideal.IsDecompositionRing.algebraMap_ringEquiv_symm_apply (since := "2026-07-10")]
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia fields are isomorphic. Superseded by `Ideal.IsInertiaRing.ringEquiv`. -/
@[deprecated Ideal.IsInertiaRing.ringEquiv (since := "2026-07-10")]
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[deprecated Ideal.IsInertiaRing.algebraMap_ringEquiv_apply (since := "2026-07-10")]
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[deprecated Ideal.IsInertiaRing.algebraMap_ringEquiv_symm_apply (since := "2026-07-10")]
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E') :
    algebraMap E L ((IsInertiaField.ringEquiv K L P E E').symm x) = algebraMap E' L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L]

include K P

@[deprecated "Use the ring-level `Ideal.IsDecompositionRing.rank_left`." (since := "2026-07-10")]
theorem IsDecompositionField.rank_left [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p]

@[deprecated "Use the ring-level `Ideal.IsDecompositionRing.rank_right`." (since := "2026-07-10")]
theorem IsDecompositionField.rank_right [IsDecompositionField K L P D] [IsGalois K L]
    [Algebra K D] [IsScalarTower K D L] (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L]

@[deprecated "Use the ring-level `Ideal.IsInertiaRing.rank_left`." (since := "2026-07-10")]
theorem IsInertiaField.rank_left [IsInertiaField K L P E] (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L, card_inertia_eq_ramificationIdxIn p]

@[deprecated "Use the ring-level `Ideal.IsInertiaRing.rank_right`." (since := "2026-07-10")]
theorem IsInertiaField.rank_right [IsInertiaField K L P E] [IsGalois K L] [Algebra K E]
    [IsScalarTower K E L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

@[deprecated "Use the ring-level \
`Ideal.IsInertiaRing.rank_decompositionRing`." (since := "2026-07-10")]
theorem IsInertiaField.rank_decompositionField [IsDecompositionField K L P D]
    [IsInertiaField K L P E] [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

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
@[deprecated "Use the ring-level \
`Ideal.IsDecompositionRing.primesOver_eq_singleton`." (since := "2026-07-10")]
theorem primesOver_eq_singleton [IsDecompositionField K L P D] [hP : P.IsPrime]
    [Finite (stabilizer Gal(L/K) P)] [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B]
  [IsDedekindDomain 𝓞D] [𝓟D.LiesOver p]

omit [P.LiesOver p] hD in
include K L D P in
@[deprecated "Superseded by the ring-level splitting results." (since := "2026-07-10")]
private lemma instances [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    Module.Finite 𝓞D B ∧ Module.IsTorsionFree 𝓞D B ∧ Module.IsTorsionFree A 𝓞D ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B ∧ 𝓟D ≠ ⊥ := by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₄ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have inst₅ : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅, Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D⟩

variable [FiniteDimensional K L] [Ring.HasFiniteQuotients A] [𝓟D.IsMaximal] [P.IsMaximal]

include K L D P in
@[deprecated "Superseded by the ring-level splitting results." (since := "2026-07-10")]
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq [IsDecompositionField K L P D]
    (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact 𝓟D.ramificationIdx_above_le P
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_above_le 𝓟D P
  · have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟D B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]

include K L D P in
@[deprecated "Use the ring-level \
`Ideal.IsDecompositionRing.ramificationIdxIn_eq`." (since := "2026-07-10")]
theorem ramificationIdxIn_eq [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in
@[deprecated "Use the ring-level \
`Ideal.IsDecompositionRing.inertiaDegIn_eq`." (since := "2026-07-10")]
theorem inertiaDegIn_eq [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in
@[deprecated "Use the ring-level \
`Ideal.IsDecompositionRing.ramificationIdx_eq`." (since := "2026-07-10")]
theorem ramificationIdx_eq [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    𝓟D.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx_pos P A).ne'] at this

include K L D P in
@[deprecated "Use the ring-level \
`Ideal.IsDecompositionRing.inertiaDeg_eq`." (since := "2026-07-10")]
theorem inertiaDeg_eq [IsDecompositionField K L P D] (hp : p ≠ ⊥) :
    𝓟D.inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
    right_eq_mul₀ <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)] at this

end IsDecompositionField

end splitting
