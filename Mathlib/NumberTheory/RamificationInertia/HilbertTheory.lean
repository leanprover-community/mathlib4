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
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed the
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
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L

instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) D L] :
    IsInertiaField K L P D := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]

set_option backward.isDefEq.respectTransparency false in
instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)

set_option backward.isDefEq.respectTransparency false in
instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] (G : Type*) [Group G]
    [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L] [MulSemiringAction G B]
    [SMulDistribClass G B L]

theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) D L] :
    IsInertiaField K L P D := by
  refine (isInertiaField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P in
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p hp]

include P in
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

include K P in
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_inertia_eq_ramificationIdxIn p hp]

include P in
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) ?_ ?_
  · exact Nat.pos_iff_ne_zero.mp <| Module.finrank_pos
  · dsimp only
    rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hp B Gal(L/K),
      IsGalois.card_aut_eq_finrank]

include P in
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact primesOver_ncard_ne_zero p B

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

variable [FiniteDimensional K L] [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B]
  [Ring.HasFiniteQuotients A] [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra A 𝓞D]
  [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B] [IsDedekindDomain 𝓞D] [𝓟D.IsMaximal]
  [P.IsMaximal] [p.IsMaximal]

include K L P D in
private theorem ramficationIdxIn_eq_inertiaDegIn_eq (hp : p ≠ ⊥) (hP : 𝓟D ≠ ⊥)
    (h₀ : 𝓟D.ramificationIdxIn B ≤ p.ramificationIdxIn B)
    (h₁ : 𝓟D.inertiaDegIn B ≤ p.inertiaDegIn B) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have : p.ramificationIdxIn B * p.inertiaDegIn B ≤ 𝓟D.ramificationIdxIn B * 𝓟D.inertiaDegIn B := by
    have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hP B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]
  refine ⟨le_antisymm h₀ ?_, le_antisymm h₁ ?_⟩
  · refine Nat.le_of_mul_le_mul_right (this.trans (Nat.mul_le_mul_left _ h₁)) ?_
    exact Nat.pos_iff_ne_zero.mpr <| inertiaDegIn_ne_zero Gal(L/K)
  · refine Nat.le_of_mul_le_mul_left (this.trans (Nat.mul_le_mul_right _ h₀)) ?_
    exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero Gal(L/K) hp

variable [𝓟D.LiesOver p]

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of `p` in `L`.
-/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  refine (ramficationIdxIn_eq_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp ?_ ?_ ?_).1
  · exact Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in `L`.
-/
theorem inertiaDegIn_eq (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  refine (ramficationIdxIn_eq_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp ?_ ?_ ?_).2
  · exact Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact IsDedekindDomain.ramificationIdx_le_ramificationIdx _ _ _ hp
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_le_inertiaDeg p 𝓟D P

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞D) p 𝓟D = 1 := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟D) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
      ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D
  · exact map_ne_bot_of_ne_bot hp
  · exact map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟D).mp inferInstance

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
theorem inertiaDeg_eq (hp : p ≠ ⊥) :
    inertiaDeg p 𝓟D = 1 := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  have := inertiaDeg_algebra_tower p 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P), right_eq_mul₀] at this
  exact inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)

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

include K L P E in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the inertia degree of `𝓟E` in `L` is equal to `1`.
-/
theorem inertiaDegIn_eq [Ring.HasFiniteQuotients B] [IsIntegrallyClosed 𝓞E]
    [Algebra.IsIntegral 𝓞E B] [P.IsMaximal] [𝓟E.IsMaximal] [Finite (inertia Gal(L/K) P)]
    (hP : P ≠ ⊥) :
    inertiaDegIn 𝓟E B = 1 := by
  have : Finite (B ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  rw [inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDeg_algebraMap,
    ← IsGalois.card_aut_eq_finrank,
    ← Nat.card_congr (Quotient.stabilizerQuotientInertiaEquiv (inertia Gal(L/K) P) 𝓟E P).toEquiv]
  simp

variable [FiniteDimensional K L] [IsGalois K L] [Algebra.IsIntegral A B] [Algebra.IsIntegral 𝓞E B]

include K L E P in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the inertia degree of `𝓟E` over `K` is equal to the inertia degree of `p` in `L`.
-/
theorem inertiaDeg_eq [IsIntegrallyClosed A] [Ring.HasFiniteQuotients B] [IsIntegrallyClosed 𝓞E]
    [Algebra A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p] [P.IsMaximal] [𝓟E.IsMaximal]
    [p.IsMaximal] (hP : P ≠ ⊥) :
    inertiaDeg p 𝓟E = p.inertiaDegIn B := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := inertiaDeg_algebra_tower p 𝓟E P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ← inertiaDegIn_eq_inertiaDeg 𝓟E P (inertia Gal(L/K) P), inertiaDegIn_eq K L P E 𝓞E _ hP,
    mul_one, eq_comm] at this

variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [IsDedekindDomain 𝓞E] [Module.Finite 𝓞E B] [Module.IsTorsionFree 𝓞E B]

include L K P E in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then the ramification index of `𝓟E` in `L` is equal to the ramification index of `p` in `L`.
-/
theorem ramificationIdxIn_eq [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B] [p.IsMaximal]
    [P.IsMaximal] [𝓟E.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟E B = p.ramificationIdxIn B := by
  have hP : P ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have : 𝓟E ≠ ⊥ := by
    rw [over_def P 𝓟E]
    exact under_ne_bot 𝓞E <| ne_bot_of_liesOver_of_ne_bot hp _
  have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this B (inertia Gal(L/K) P)
  rwa [primesOver_eq_singleton K L P E 𝓞E, Set.ncard_singleton, one_mul,
    inertiaDegIn_eq K L P E _ _ hP, mul_one, card_inertia_eq_ramificationIdxIn p hp] at this

variable [Algebra A 𝓞E] [Module.IsTorsionFree A 𝓞E] [IsScalarTower A 𝓞E B] [𝓟E.LiesOver p]

include K L E P in
/--
Let `E` be the inertia field of `P` in `L/K`. Let `𝓟E` be a prime ideal of `E` below `P`,
then `𝓟E` is unramified over `K`.
-/
theorem ramificationIdx_eq [Ring.HasFiniteQuotients A] [Ring.HasFiniteQuotients B] [𝓟E.IsMaximal]
    [P.IsMaximal] [p.IsMaximal] (hp : p ≠ ⊥) :
    ramificationIdx (algebraMap A 𝓞E) p 𝓟E = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have : IsGaloisGroup (inertia Gal(L/K) P) 𝓞E B := .of_isFractionRing _ _ _ E L
  have := ramificationIdx_algebra_tower (p := p) (P := 𝓟E) (Q := P) ?_ ?_ ?_
  · rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟E P (inertia Gal(L/K) P),
      ramificationIdxIn_eq A K L P E 𝓞E 𝓟E hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      right_eq_mul₀] at this
    exact IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
  · exact map_ne_bot_of_ne_bot <| Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟E
  · exact map_ne_bot_of_ne_bot hp
  · exact map_le_iff_le_comap.mpr <| le_of_eq <| (liesOver_iff P 𝓟E).mp inferInstance

end IsInertiaField

end splitting

section IntermediateField

open IntermediateField

variable [MulSemiringAction Gal(L/K) B] [FiniteDimensional K L] [IsGalois K L]
  {F : IntermediateField K L}

set_option backward.isDefEq.respectTransparency false in
theorem isDecompositionField_iff_fixingSubgroup :
    IsDecompositionField K L P F ↔ F.fixingSubgroup = stabilizer Gal(L/K) P := by
  rw [isDecompositionField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

set_option backward.isDefEq.respectTransparency false in
theorem isInertiaField_iff_fixingSubgroup :
    IsInertiaField K L P F ↔ F.fixingSubgroup = inertia Gal(L/K) P := by
  rw [isInertiaField_iff, IsGaloisGroup.subgroup_iff, ← IntermediateField.fixedField,
    IsGalois.fixedField_eq_iff_fixingSubgroup_eq]

variable (D E : IntermediateField K L) (𝓞D 𝓞E : Type*) [Algebra B L]
  [hSD : SMulDistribClass Gal(L/K) B L]

variable (F)

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

variable [IsFractionRing B L] (𝓞F : Type*) [CommRing 𝓞F] [IsIntegrallyClosed 𝓞F] [Algebra 𝓞F F]
  [Algebra 𝓞F B] [Algebra.IsIntegral 𝓞F B] [Algebra 𝓞F L]
  [IsScalarTower 𝓞F F L] [IsScalarTower 𝓞F B L] (𝓟F : Ideal 𝓞F) [P.LiesOver 𝓟F]

set_option backward.isDefEq.respectTransparency false in
/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `D` is a subfield of `F` iff `P` is the only prime ideal above the prime `𝓟F` of `F`
below `P`.
-/
theorem isDecompositionField_le_iff [hD : IsDecompositionField K L P D] [IsFractionRing 𝓞F F]
    [P.IsPrime] :
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

variable [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain 𝓞F] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞F] [IsIntegralClosure B 𝓞F L] [IsScalarTower A 𝓞F B]
  [FaithfulSMul 𝓞F B] [Ring.HasFiniteQuotients 𝓞F]

include A in
set_option backward.isDefEq.respectTransparency false in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `E` is a subfield of `F` iff `𝓟F` is totally ramified in `L` where `𝓟F` is the
prime of `F` below `P`.
-/
theorem isInertiaField_le_iff [IsFractionRing 𝓞F F] [P.IsMaximal] [IsInertiaField K L P E]
    (hp : p ≠ ⊥) :
    E ≤ F ↔ ramificationIdx (algebraMap 𝓞F B) 𝓟F P = Module.finrank F L := by
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(E ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, eq_comm, eq_of_le_iff_finrank_eq' le_sup_right,
    IsInertiaField.rank_left 𝓞F F L P ↥(E ⊔ F) hPF,
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), eq_comm]

variable [Ring.HasFiniteQuotients A] [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

include P in
set_option backward.isDefEq.respectTransparency false in
/--
Let `D` be the decomposition field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `D` iff `p` is totally split in `F`.
-/
theorem le_isDecompositionField_iff [IsFractionRing 𝓞F F] [IsDecompositionField K L P D]
    [p.IsMaximal] [P.IsMaximal] [𝓟F.IsMaximal] (hp : p ≠ ⊥) :
    F ≤ D ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 ∧ inertiaDeg p 𝓟F = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  let : Algebra F ↥(D ⊔ F) := (inclusion le_sup_right).toAlgebra
  have : IsScalarTower F ↥(D ⊔ F) L := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_of_le_iff_finrank_eq' le_sup_left,
    IsDecompositionField.rank_left A K L P D hp, IsDecompositionField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K), inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), inertiaDegIn_eq_inertiaDeg 𝓟F P Gal(L/F),
    ramificationIdx_algebra_tower' p 𝓟F P, inertiaDeg_algebra_tower p 𝓟F P, mul_rotate, mul_assoc,
    mul_right_inj' (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hPF), mul_rotate,
    mul_assoc, mul_eq_left₀ (inertiaDeg_ne_zero 𝓟F P), mul_eq_one]

include P in
set_option backward.isDefEq.respectTransparency false in
/--
Let `E` be the inertia field of `P` in `L/K` and let `F` be a subextension of `L/K`.
Then, `F` is a subfield of `E` iff `p` is unramified in `F`.
-/
theorem le_isInertiaField_iff [IsFractionRing 𝓞F F] [IsInertiaField K L P E] [P.IsMaximal]
    (hp : p ≠ ⊥) :
    F ≤ E ↔ ramificationIdx (algebraMap A 𝓞F) p 𝓟F = 1 := by
  have : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  let := IsIntegralClosure.MulSemiringAction 𝓞F F L B
  have : IsGaloisGroup Gal(L/F) 𝓞F B := .of_isFractionRing _ _ _ F L
  have : Module.Finite 𝓞F B := Module.Finite.right A 𝓞F B
  have : Module.IsTorsionFree A 𝓞F := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have : 𝓟F.LiesOver p := LiesOver.tower_bot P 𝓟F p
  have hPF : 𝓟F ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
  rw [← sup_eq_right, sup_comm, eq_comm, eq_of_le_iff_finrank_eq' le_sup_left,
    IsInertiaField.rank_left A K L P E hp, IsInertiaField.rank_left 𝓞F F L P _ hPF,
    ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    ramificationIdxIn_eq_ramificationIdx 𝓟F P Gal(L/F), ramificationIdx_algebra_tower' p 𝓟F P,
    mul_eq_right₀ (IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hPF)]

end IntermediateField
