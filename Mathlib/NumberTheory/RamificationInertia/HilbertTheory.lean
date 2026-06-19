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
