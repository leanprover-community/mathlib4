/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!

# Decomposition and inertia rings

We develop Hilbert's theory of the splitting of a prime ideal in a Galois extension, working
throughout at the level of rings.

Let `A ⊆ B` be commutative rings with `B` Galois over `A` with group `G`, let `p` be a prime of `A`
and `P` a prime of `B` lying over `p`. The *decomposition ring* `C` and the *inertia ring* `C'` of
`P` are the intermediate rings fixed by the decomposition and inertia subgroups of `P`; since the
inertia group is contained in the decomposition group, they fit into a tower `A ⊆ C ⊆ C' ⊆ B`.

## Ring predicates

For an intermediate ring `C` of `B`, we introduce two characteristic predicates:

* `Ideal.IsDecompositionRing G P C`: `B` is Galois over `C` with Galois group the *decomposition
  group* of `P`, that is the stabilizer of `P` in `G`;
* `Ideal.IsInertiaRing G P C`: `B` is Galois over `C` with Galois group the *inertia group* of `P`,
  that is the subgroup of `G` acting trivially modulo `P`.

## Main results

Writing `e`, `f` for the ramification index and inertia degree of `P` over `p`, `g` for the number
of primes of `B` above `p`, and `𝓟`, `𝓟'` for the primes of the decomposition ring `C` and the
inertia ring `C'` below `P`:
```
degree            ramif. index   inertia deg.
        B      P
  e     |      |      e               1
        C'     𝓟'
  f     |      |      1               f
        C      𝓟
  g     |      |      1               1
        A      p
```

## Relation to the classical field setting

In the classical setting `L/K` is a Galois extension of fields with `G = Gal(L/K)`, and `A`, `B` are
subrings of `K`, `L` with `K` the fraction field of `A`, `L` that of `B`, and `B` the integral
closure of `A` in `L`. The decomposition (resp. inertia) *field* is the subfield of `L` fixed by the
decomposition (resp. inertia) group of `P`, and the associated ring is its integral closure over
`A`. Decomposition and inertia rings arising this way are provided by
`Ideal.IsDecompositionRing.of_isFractionRing` and `Ideal.IsInertiaRing.of_isFractionRing`, and the
degrees of the fields follow from those of the rings via
`Algebra.IsAlgebraic.finrank_of_isFractionRing`.

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
theorem IsDecompositionRing.finrank_top [FaithfulSMul C B] [P.IsMaximal]
    [P.IsDecompositionRing G C] (hp : p ≠ ⊥) :
    Module.finrank C B = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank' (stabilizer G P) C B, card_stabilizer_eq p]

/-- The degree `[B : C]` of `B` over the inertia ring `C` equals the ramification index of `p`
in `B`. -/
theorem IsInertiaRing.finrank_top [FaithfulSMul C B] [P.IsMaximal] [P.IsInertiaRing G C]
    (hp : p ≠ ⊥) :
    Module.finrank C B = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank' (inertia G P) C B, card_inertia_eq_ramificationIdxIn p]

variable [Algebra A C] [IsScalarTower A C B]

/-- The degree `[C : A]` of the decomposition ring `C` over `A` equals the number of prime ideals
of `B` lying over `p`. -/
theorem IsDecompositionRing.finrank_bot [FaithfulSMul A C] [Module.Finite A C] [FaithfulSMul C B]
    [P.IsMaximal] [P.IsDecompositionRing G C] (hp : p ≠ ⊥) :
    Module.finrank A C = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  have : Module.Finite C B := Module.Finite.right A C B
  have : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A C B, RingHom.coe_comp]
    exact (FaithfulSMul.algebraMap_injective C B).comp (FaithfulSMul.algebraMap_injective A C)
  rw [← mul_left_inj' (c := Module.finrank C B) Module.finrank_pos.ne',
    Module.finrank_mul_finrank' A C B, IsDecompositionRing.finrank_top G P C hp,
    ← IsGaloisGroup.card_eq_finrank' G A B,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]

/-- The degree `[C : A]` of the inertia ring `C` over `A` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`. -/
theorem IsInertiaRing.finrank_bot [FaithfulSMul A C] [Module.Finite A C] [FaithfulSMul C B]
    [P.IsMaximal] [P.IsInertiaRing G C] (hp : p ≠ ⊥) :
    Module.finrank A C = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  have : Module.Finite C B := Module.Finite.right A C B
  have : FaithfulSMul A B := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A C B, RingHom.coe_comp]
    exact (FaithfulSMul.algebraMap_injective C B).comp (FaithfulSMul.algebraMap_injective A C)
  rw [← mul_left_inj' (c := Module.finrank C B) Module.finrank_pos.ne',
    Module.finrank_mul_finrank' A C B, IsInertiaRing.finrank_top G P C hp,
    ← IsGaloisGroup.card_eq_finrank' G A B, mul_assoc, mul_comm (p.inertiaDegIn B),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G]

/-- The degree `[C' : C]` of the inertia ring `C'` over the decomposition ring `C` equals the
inertia degree of `p` in `B`. -/
theorem IsInertiaRing.finrank_decompositionRing (C' : Type*) [CommRing C'] [Algebra C' B]
    [FaithfulSMul C B] [FaithfulSMul C' B] [Algebra C C'] [IsScalarTower C C' B]
    [Module.Finite C C']
    [P.IsMaximal] [P.IsDecompositionRing G C] [P.IsInertiaRing G C'] (hp : p ≠ ⊥) :
    Module.finrank C C' = p.inertiaDegIn B := by
  have : IsDomain C := (FaithfulSMul.algebraMap_injective C B).isDomain
  have : IsDomain C' := (FaithfulSMul.algebraMap_injective C' B).isDomain
  have : Module.Finite C B := Module.Finite.right A C B
  have : Module.Finite C' B := Module.Finite.right C C' B
  have : FaithfulSMul C C' := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h := FaithfulSMul.algebraMap_injective C B
    rw [IsScalarTower.algebraMap_eq C C' B, RingHom.coe_comp] at h
    exact h.of_comp
  rw [← mul_left_inj' (c := Module.finrank C' B) Module.finrank_pos.ne',
    Module.finrank_mul_finrank' C C' B, IsInertiaRing.finrank_top G P C' hp,
    IsDecompositionRing.finrank_top G P C hp, mul_comm (p.ramificationIdxIn B)]

end rank

section splitting

/-! ### Splitting of a prime in a decomposition ring -/

variable {A : Type*} [CommRing A] [Algebra A B] [Algebra A C] [IsScalarTower A C B]
  {p : Ideal A} [P.LiesOver p] (𝓟 : Ideal C) [P.LiesOver 𝓟]

namespace IsDecompositionRing

variable [P.IsDecompositionRing G C]

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
      IsDecompositionRing.finrank_top G P C hp]

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

/-! ### Splitting of a prime in an inertia ring -/

namespace IsInertiaRing

attribute [local instance] Ideal.Quotient.field

variable [P.IsInertiaRing G C]

/-- Let `C` be an inertia ring of `P` and `𝓟` the prime of `C` below `P`. Then `P` is the
only prime of `B` above `𝓟`. -/
theorem primesOver_eq_singleton [P.IsPrime] [Finite (inertia G P)] :
    primesOver 𝓟 B = {P} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, fun Q ⟨_, _⟩ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟 P Q (inertia G P)
  exact inertia_le_stabilizer _ σ.prop

variable [Finite G] [Ring.HasFiniteQuotients B] [P.IsMaximal]

include G P in
/-- The inertia degree of `𝓟` in `B` equals `1`. -/
theorem inertiaDegIn_eq [Algebra.IsIntegral C B] (hP : P ≠ ⊥) :
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
  have : Module.Finite C B := Module.Finite.right A C B
  have := inertiaDeg_tower (R := A) 𝓟 P
  rw [← inertiaDegIn_eq_inertiaDeg 𝓟 P (inertia G P), inertiaDegIn_eq G P C 𝓟 hP,
    mul_one] at this
  rw [inertiaDegIn_eq_inertiaDeg p P G, this]

variable [IsDomain A] [IsDomain B] [IsDomain C] [Module.Flat A B] [Module.Flat C B]
  [Ring.HasFiniteQuotients A]

include G P in
/-- The ramification index of `𝓟` in `B` equals the ramification index of `p` in `B`. -/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟 B = p.ramificationIdxIn B := by
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : p.IsMaximal := .of_isMaximal_liesOver P p
  have : Module.Finite C B := Module.Finite.right A C B
  have : 𝓟.IsMaximal := .of_isMaximal_liesOver P 𝓟
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟 B (inertia G P)
  rwa [primesOver_eq_singleton G P, Set.ncard_singleton, one_mul, inertiaDegIn_eq G P C 𝓟 hP,
    mul_one, card_inertia_eq_ramificationIdxIn p P] at this

include G P in
/-- `𝓟` is unramified over `A`. -/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    𝓟.ramificationIdx A = 1 := by
  have := ramificationIdx_tower (R := A) 𝓟 P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟 P (inertia G P),
    ramificationIdxIn_eq G P C 𝓟 hp, ramificationIdxIn_eq_ramificationIdx p P G,
    right_eq_mul₀ <| (ramificationIdx_pos P A).ne'] at this

end IsInertiaRing

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

namespace IntermediateField

variable [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] [IsGalois K L]
  {F : IntermediateField K L}

/--
An intermediate field `F` of `L/K` is the decomposition field of `P` if and only if its fixing
subgroup is the decomposition group of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
theorem isDecompositionField_iff_fixingSubgroup :
    IsDecompositionField K L P F ↔ F.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [isDecompositionField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

/--
An intermediate field `F` of `L/K` is the inertia field of `P` if and only if its fixing
subgroup is the inertia group of `P` in `Gal(L/K)`.
-/
theorem isInertiaField_iff_fixingSubgroup :
    IsInertiaField K L P F ↔ F.fixingSubgroup = inertia Gal(L/K) P := by
  rw [isInertiaField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

variable (D E : IntermediateField K L) [Algebra B L]
  [hSD : SMulDistribClass Gal(L/K) B L]

variable (F)

/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, the decomposition field of `P` in `L/F` is the compositum `DF`.
-/
instance isDecompositionField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] [hD : IsDecompositionField K L P D] :
    IsDecompositionField F L P (D ⊔ F : IntermediateField K L) := by
  let H : Subgroup Gal(L/K) := stabilizer Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(D ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isDecompositionField_iff_fixingSubgroup K L P).mp hD]
  let e : stabilizer Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((stabilizer F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine stabilizerEquiv P F.fixingSubgroupEquiv.symm fun σ x ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact (isDecompositionField_iff _ _ P _).mpr <| IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, the inertia field of `P` in `L/F` is the compositum `EF`.
-/
instance isInertiaField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
    [SMulDistribClass Gal(L/F) B L] [hE : IsInertiaField K L P E] :
    IsInertiaField F L P (E ⊔ F : IntermediateField K L) := by
  let H : Subgroup Gal(L/K) := inertia Gal(L/K) P ⊓ F.fixingSubgroup
  have : IsGaloisGroup H ↥(E ⊔ F) L := by
    rw [IsGaloisGroup.subgroup_iff, ← fixedField, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixingSubgroup_sup, (isInertiaField_iff_fixingSubgroup K L P).mp hE]
  let e : inertia Gal(L/F) P ≃* H := by
    refine (MulEquiv.trans ?_ ((inertia F.fixingSubgroup P).equivMapOfInjective _
      F.fixingSubgroup.subtype_injective)).trans <| MulEquiv.subgroupCongr <| by ext; simp [H]
    refine inertiaEquiv P F.fixingSubgroupEquiv.symm fun _ _ ↦ ?_
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul', fixingSubgroupEquiv_symm_apply_apply]
  exact (isInertiaField_iff _ _ P _).mpr <| IsGaloisGroup.of_mulEquiv e fun g x ↦ rfl

variable [IsFractionRing B L] (𝓞F : Type*) [CommRing 𝓞F] [Algebra 𝓞F F]
  [Algebra 𝓞F B] [Algebra.IsIntegral 𝓞F B] [Algebra 𝓞F L] [IsScalarTower 𝓞F F L]
  [IsScalarTower 𝓞F B L] (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F]

/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `D` is a subfield of `F` iff `P` is the only prime ideal above the prime `𝓟F` of `F`
below `P`.
-/
theorem isDecompositionField_le_iff [hD : IsDecompositionField K L P D] [IsFractionRing 𝓞F F]
    [IsIntegrallyClosed 𝓞F] [P.IsPrime] :
    D ≤ F ↔ primesOver 𝓟F B = {P} := by
  have : IsGaloisGroup F.fixingSubgroup 𝓞F B := by
      have : IsGaloisGroup F.fixingSubgroup F L := IsGaloisGroup.intermediateField _ _ _ _
      exact IsGaloisGroup.of_isFractionRing _ 𝓞F B F L
  have : P ∈ 𝓟F.primesOver B := ⟨inferInstance, inferInstance⟩
  simp only [← IsGalois.intermediateFieldEquivSubgroup.le_iff_le,
    IsGalois.intermediateFieldEquivSubgroup_apply, OrderDual.toDual_le_toDual,
    (isDecompositionField_iff_fixingSubgroup K L P).mp hD, Set.eq_singleton_iff_unique_mem,
    SetLike.le_def, this, true_and]
  refine ⟨fun h Q ⟨hQ₁, hQ₂⟩ ↦ ?_, fun h σ hσ ↦ h (σ • P) ⟨IsPrime.smul σ, ?_⟩⟩
  · obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝓟F P Q F.fixingSubgroup
    exact h σ.prop
  · exact Ideal.LiesOver.smul (⟨σ, hσ⟩ : F.fixingSubgroup)

variable [IsDedekindDomain 𝓞F] [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra A 𝓞F]
  [IsIntegralClosure B 𝓞F L] [IsScalarTower A 𝓞F B] [FaithfulSMul 𝓞F B]

omit [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] hSD in
include A in
/-- The instances shared by the proofs comparing `F` to the decomposition or inertia field:
`𝓞F` is a Galois group setup for `B` over `F`, and the relevant finiteness/torsion-freeness. -/
private lemma instances [IsFractionRing 𝓞F F] :
    letI := IsIntegralClosure.MulSemiringAction 𝓞F F L B
    IsGaloisGroup Gal(L/F) 𝓞F B ∧ Module.Finite 𝓞F B ∧ Module.IsTorsionFree A 𝓞F :=
  letI := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  ⟨.of_isFractionRing _ _ _ F L, Module.Finite.right A 𝓞F B,
    Module.IsTorsionFree.of_faithfulSMul _ _ B⟩

variable [IsDedekindDomain A] [IsDedekindDomain B] [Ring.HasFiniteQuotients 𝓞F]

include A in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `E` is a subfield of `F` iff `𝓟F` is totally ramified in `L` where `𝓟F` is the
prime of `F` below `P`.
-/
theorem isInertiaField_le_iff [IsFractionRing 𝓞F F] [P.IsMaximal] [IsInertiaField K L P E]
    (hp : p ≠ ⊥) :
    E ≤ F ↔ P.ramificationIdx' 𝓞F = Module.finrank F L := by
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  obtain ⟨_, _, _⟩ := instances (B := B) A K L F 𝓞F
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(E ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have hPF : P.under 𝓞F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, eq_comm, eq_iff_finrank_eq_of_le' le_sup_right,
    IsInertiaField.rank_left 𝓞F F L P ↥(E ⊔ F) hPF,
    ramificationIdxIn_eq_ramificationIdx (P.under 𝓞F) P Gal(L/F), eq_comm]

variable [Ring.HasFiniteQuotients A] [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

include P in
/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `D` iff `p` is totally split in `F`.
-/
theorem le_isDecompositionField_iff [IsFractionRing 𝓞F F] [IsDecompositionField K L P D]
    [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ D ↔ 𝓟F.ramificationIdx' A = 1 ∧ 𝓟F.inertiaDeg' A = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  obtain ⟨_, _, _⟩ := instances (B := B) A K L F 𝓞F
  let : Algebra F ↥(D ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(D ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_iff_finrank_eq_of_le' le_sup_left,
    IsDecompositionField.rank_left A K L P D hp, IsDecompositionField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K), inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F),
    ramificationIdx'_tower (R := A) 𝓟F P, inertiaDeg'_tower (R := A) 𝓟F P, mul_rotate, mul_assoc,
    mul_right_inj' (ramificationIdx'_pos P 𝓞F).ne', mul_rotate,
    mul_assoc, mul_eq_left₀ (inertiaDeg'_pos P 𝓞F).ne', mul_eq_one]

include P in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `E` iff `p` is unramified in `F`.
-/
theorem le_isInertiaField_iff [IsFractionRing 𝓞F F] [IsInertiaField K L P E] [P.IsMaximal]
    (hp : p ≠ ⊥) :
    F ≤ E ↔ 𝓟F.ramificationIdx' A = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  obtain ⟨_, _, _⟩ := instances (B := B) A K L F 𝓞F
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_iff_finrank_eq_of_le' le_sup_left,
    IsInertiaField.rank_left A K L P E hp, IsInertiaField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), ramificationIdx'_tower (R := A) 𝓟F P,
    mul_eq_right₀ (ramificationIdx'_pos P 𝓞F).ne']

/--
An intermediate field `F` of `L/K` is the decomposition field of `P` if and only if `p` is totally
split in `F`, that is `P` is the only prime of `L` above the prime `𝓟F` of `F` below `P`, and `𝓟F`
is unramified over `p` with inertia degree `1`.
-/
theorem isDecompositionField_iff [IsFractionRing 𝓞F F] [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal]
    (hp : p ≠ ⊥) :
    IsDecompositionField K L P F ↔ primesOver 𝓟F B = {P} ∧
      𝓟F.ramificationIdx' A = 1 ∧ 𝓟F.inertiaDeg' A = 1 := by
  let D := (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L)
  convert_to D = F ↔ _
  · rw [isDecompositionField_iff_fixingSubgroup, ← IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixedField]
  rw [le_antisymm_iff, le_isDecompositionField_iff A K L P F D 𝓞F 𝓟F hp,
    isDecompositionField_le_iff K L P F D 𝓞F 𝓟F]

/--
An intermediate field `F` of `L/K` is the inertia field of `P` if and only if the prime `𝓟F` of
`F` below `P` is unramified over `p`, and `P` is totally ramified over `𝓟F`, that is the
ramification index of `P` over `𝓞F` equals `[L : F]`.
-/
theorem isInertiaField_iff [IsFractionRing 𝓞F F] [P.IsMaximal] (hp : p ≠ ⊥) :
    IsInertiaField K L P F ↔ P.ramificationIdx' 𝓞F = Module.finrank F L
      ∧ 𝓟F.ramificationIdx' A = 1 := by
  let E := (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L)
  convert_to E = F ↔ _
  · rw [isInertiaField_iff_fixingSubgroup, ← IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
      fixedField]
  rw [le_antisymm_iff, le_isInertiaField_iff A K L P F E 𝓞F 𝓟F hp,
    isInertiaField_le_iff A K L P F E 𝓞F hp]

end IntermediateField
