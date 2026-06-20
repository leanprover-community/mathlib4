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

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`K` fraction field of `A`, `L` fraction field of `B` and `B` the integral closure of `A` in `L`.

For `P` a prime ideal of `B` lying over the prime ideal `p` of `A`, the decomposition field `D` of
`P` in `L/K` is the subfield of elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and
the inertia field `E` of `P` in `L/K` is the subfield of elements of `L` fixed by the inertia
group of `P` in `Gal(L/K)`.

Let `e` and `f` the ramification index and inertia degree of `P` over `p` and let `g`
be the number of prime ideals above `p` in `L`. Denote by `𝓟D`, resp. `𝓟E`, the prime ideal of `D`,
resp. `E`, below `P`. Then we have the following properties
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

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

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
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P

/--
The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`.
-/
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p]

/--
The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`.
-/
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

/--
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p` in `B`.
-/
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L, card_inertia_eq_ramificationIdxIn p]

/--
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/--
The degree `[E : D]` of the inertia field `E` over the decomposition field `D` equals the
inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
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
private lemma instances (hp : p ≠ ⊥) :
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
  [p.IsMaximal]

include K L D P in
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    rw [← ramificationIdx_eq_ramificationIdx' p _ hp,
      ← ramificationIdx_eq_ramificationIdx' 𝓟D _ h𝓟]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    rw [← inertiaDeg_eq_inertiaDeg' p, ← inertiaDeg_eq_inertiaDeg' 𝓟D]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P
  · have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟D B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of `p` in `L`.
-/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in `L`.
-/
theorem inertiaDegIn_eq (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    𝓟D.ramificationIdx' A = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx'_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx'_pos P A).ne'] at this

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
theorem inertiaDeg_eq (hp : p ≠ ⊥) :
    𝓟D.inertiaDeg' A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg'_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
    right_eq_mul₀ <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)] at this

end IsDecompositionField

namespace IsInertiaField

attribute [local instance] Ideal.Quotient.field

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E] [CommRing 𝓞E]
  [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L] (𝓟E : Ideal 𝓞E) [P.LiesOver 𝓟E]

include L K E in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then `P` is the only prime of `L` above `𝓟E`.
-/
theorem primesOver_eq_singleton [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B] [P.IsPrime]
    [Finite (inertia Gal(L/K) P)] :
    primesOver 𝓟E B = {P} := by
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟E P Q (inertia Gal(L/K) P)
  exact inertia_le_stabilizer _ σ.prop

variable [Ring.HasFiniteQuotients B] [P.IsMaximal] [𝓟E.IsMaximal]

include K L P E in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the inertia degree of `𝓟E` in `L` is equal to `1`.
-/
theorem inertiaDegIn_eq [IsIntegrallyClosed 𝓞E] [Algebra.IsIntegral 𝓞E B]
    [Finite (inertia Gal(L/K) P)] (hP : P ≠ ⊥) :
    inertiaDegIn 𝓟E B = 1 := by
  have : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  rw [inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), ← inertiaDeg_eq_inertiaDeg' 𝓟E,
    inertiaDeg_algebraMap, ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia Gal(L/K) P) 𝓟E P).toEquiv]
  refine Nat.card_eq_one_iff_unique.mpr ⟨?_, inferInstance⟩
  rw [QuotientGroup.subsingleton_iff, Subgroup.eq_top_iff']
  exact fun ⟨⟨σ, hσ⟩, hσ'⟩ ↦ hσ

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsIntegral A B] [Algebra.IsIntegral 𝓞E B]
  [p.IsMaximal]

include K L E P in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the inertia degree of `𝓟E` over `K` is equal to the inertia degree of `p` in `L`.
-/
theorem inertiaDeg_eq [IsIntegrallyClosed A] [IsIntegrallyClosed 𝓞E]
    [Algebra A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p] (hP : P ≠ ⊥) :
    inertiaDeg p 𝓟E = p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := inertiaDeg'_tower (R := A) 𝓟E P
  rw [← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDegIn_eq K L P E 𝓞E 𝓟E hP,
    mul_one] at this
  rwa [inertiaDeg_eq_inertiaDeg' p, inertiaDegIn_eq_inertiaDeg p P Gal(L/K), eq_comm]

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [IsDedekindDomain 𝓞E] [Module.Finite 𝓞E B] [Module.IsTorsionFree 𝓞E B] [Ring.HasFiniteQuotients A]

include L K P E in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the ramification index of `𝓟E` in `L` is equal to the ramification index of `p` in `L`.
-/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟E B (inertia Gal(L/K) P)
  rwa [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul,
    inertiaDegIn_eq K L P E _ _ hP, mul_one, card_inertia_eq_ramificationIdxIn p P] at this

variable [Algebra A 𝓞E] [Module.IsTorsionFree A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p]

include K L E P in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then `𝓟E` is unramified over `K`.
-/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    ramificationIdx p 𝓟E = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  rw [ramificationIdx_eq_ramificationIdx' p 𝓟E hp]
  have := ramificationIdx'_tower (R := A) 𝓟E P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
    ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx'_pos P A).ne'] at this

end IsInertiaField

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
theorem isDecompositionField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
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
theorem isInertiaField_sup [FaithfulSMul B L] [MulSemiringAction Gal(L/F) B]
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
  haveI : IsInertiaField F L P ↥(E ⊔ F) := isInertiaField_sup K L P F E
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
  haveI : IsDecompositionField F L P ↥(D ⊔ F) := isDecompositionField_sup K L P F D
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
  haveI : IsInertiaField F L P ↥(E ⊔ F) := isInertiaField_sup K L P F E
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
An intermediate field `F` of `L/K` is the inertia field of `P` if and only if `𝓟F` is totally
ramified in `L` (the ramification index of `P` over `𝓟F` equals `[L : F]`) and `𝓟F` is unramified
over `p`, where `𝓟F` is the prime of `F` below `P`.
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
