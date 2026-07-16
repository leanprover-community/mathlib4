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

-- We fix the order of variables for the whole file
variable {A K L B : Type*}

section Ring

variable [CommRing B] (G : Type*) [Group G] [MulSemiringAction G B]
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

variable (K L) [Field K] [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
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

variable [IsDomain B] [Finite G] [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
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

variable [CommRing A] [Algebra A B] [Algebra A C] [IsScalarTower A C B]
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
  IsGaloisGroup.of_fixedPoints_eq _ _ _ _ _ rfl

instance [IsGalois K L] :
    IsGaloisGroup (inertia Gal(L/K) P) (P.inertiaField K L) L :=
  IsGaloisGroup.of_fixedPoints_eq _ _ _ _ _ rfl

theorem eq_decompositionField_iff [FiniteDimensional K L] [IsGalois K L]
    {D : IntermediateField K L} :
    D = P.decompositionField K L ↔ D.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [decompositionField, eq_comm, IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem eq_inertiaField_iff [FiniteDimensional K L] [IsGalois K L]
    {E : IntermediateField K L} :
    E = P.inertiaField K L ↔ E.fixingSubgroup = inertia Gal(L/K) P := by
  rw [inertiaField, eq_comm, IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

theorem le_decompositionField_iff {F : IntermediateField K L} :
    F ≤ P.decompositionField K L ↔ stabilizer Gal(L/K) P ≤ F.fixingSubgroup :=
  le_iff_le _ _

theorem le_inertiaField_iff {F : IntermediateField K L} :
    F ≤ P.inertiaField K L ↔ inertia Gal(L/K) P ≤ F.fixingSubgroup :=
  le_iff_le _ _

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
  (C : Type*) [CommRing C] [Algebra C B] [Algebra C L] [IsScalarTower C B L] [IsIntegrallyClosed C]
  [Algebra.IsIntegral C B]

/-- A ring `C` with `C ⊆ B`, `B` integral over `C`, `C` integrally closed, and fraction field the
decomposition field of `P`, is a decomposition ring for `P`. -/
theorem isDecompositionRing_of_isFractionRing [Algebra C (P.decompositionField K L)]
    [IsScalarTower C (P.decompositionField K L) L] [IsFractionRing C (P.decompositionField K L)] :
    P.IsDecompositionRing Gal(L/K) C := {
  toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ C B (P.decompositionField K L) L }

/-- A ring `C` with `C ⊆ B`, `B` integral over `C`, `C` integrally closed, and fraction field the
inertia field of `P`, is an inertia ring for `P`. -/
theorem isInertiaRing_of_isFractionRing [Algebra C (P.inertiaField K L)]
    [IsScalarTower C (P.inertiaField K L) L] [IsFractionRing C (P.inertiaField K L)] :
    P.IsInertiaRing Gal(L/K) C := {
  toIsGaloisGroup := IsGaloisGroup.of_isFractionRing _ C B (P.inertiaField K L) L }

end ring

section rank

variable [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDomain B]
  [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L]
  [Algebra A K] [IsFractionRing A K] [Algebra A B] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [Algebra.IsIntegral A B] [Module.Finite A B] [Module.Flat A B]
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

variable (F : IntermediateField K L) [Algebra B L] [IsFractionRing B L]
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
  rw [decompositionField, fixedField,
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
  rw [inertiaField, fixedField, (IsGaloisGroup.subgroup_iff (F := extendScalars le_sup_left)).mp h,
    extendScalars_restrictScalars]

end restrictScalars

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

end IntermediateField

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

end deprecated
