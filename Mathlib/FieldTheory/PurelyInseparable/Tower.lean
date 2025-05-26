/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!

# Tower law for purely inseparable extensions

This file contains results related to `Field.sepDegree`, `Field.insepDegree` and the tower law.

## Main results

- `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`: the separable degrees satisfy the
  tower law: $[E:F]_s [K:E]_s = [K:F]_s$.

- `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`:
  `Field.finInsepDegree_mul_finInsepDegree_of_isAlgebraic`: the inseparable degrees satisfy the
  tower law: $[E:F]_i [K:E]_i = [K:F]_i$.

- `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable`,
  `IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'`:
  if `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
  for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
  the same separable degree. In particular, if `S` is an intermediate field of `K / F` such that
  `S / F` is algebraic, the `E(S) / E` and `S / F` have the same separable degree.

- `minpoly.map_eq_of_isSeparable_of_isPurelyInseparable`: if `K / E / F` is a field extension tower,
  such that `E / F` is purely inseparable, then for any element `x` of `K` separable over `F`,
  it has the same minimal polynomials over `F` and over `E`.

- `Polynomial.Separable.map_irreducible_of_isPurelyInseparable`: if `E / F` is purely inseparable,
  `f` is a separable irreducible polynomial over `F`, then it is also irreducible over `E`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

open Polynomial IntermediateField Field

noncomputable section

universe u v w

section TowerLaw

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

variable [Algebra E K] [IsScalarTower F E K]

variable {F K} in
/-- If `K / E / F` is a field extension tower such that `E / F` is purely inseparable,
if `{ u_i }` is a family of separable elements of `K` which is `F`-linearly independent,
then it is also `E`-linearly independent. -/
theorem LinearIndependent.map_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι → K} (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl ↦ Finsupp.ext fun i ↦ ?_
  choose f hf using fun i ↦ (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  have := (expChar_pow_pos F q n).ne'
  replace hf (i : ι) : l i ^ q ^ n ∈ (algebraMap F E).range := by
    by_cases hs : i ∈ l.support
    · convert pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.notMem_support_iff.1 hs, zero_pow this]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i ↦ by
    contrapose!
    refine fun hs ↦ (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF, Finsupp.notMem_support_iff.1 hs, zero_pow this]
  replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_isSeparable' q n hsep) lF₀ <| by
    replace hl := congr($hl ^ q ^ n)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_pow_char_pow, zero_pow this] at hl
    rw [← hl, Finsupp.linearCombination_apply,
      Finsupp.onFinset_sum _ (fun _ ↦ by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine pow_eq_zero ((hlF _).symm.trans ?_)
  convert map_zero (algebraMap F E)
  exact congr($h i)

variable {F K} in
/-- If `K / E / F` is a field extension tower such that `E / F` is purely inseparable,
if `S` is an intermediate field of `K / F` which is separable over `F`, then `S` and `E` are
linearly disjoint over `F`. -/
theorem IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] (S : IntermediateField F K) [Algebra.IsSeparable F S] :
    S.LinearDisjoint E :=
  have ⟨ι, ⟨b⟩⟩ := Basis.exists_basis F S
  .of_basis_left b <| b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective)
    |>.map_of_isPurelyInseparable_of_isSeparable E fun i ↦ by
      simpa only [IsSeparable, minpoly_eq] using Algebra.IsSeparable.isSeparable F (b i)

namespace Field

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable and `K / E`
is separable, then the separable degree of `K / F` is equal to the degree of `K / E`.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable E K] : sepDegree F K = Module.rank E K := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.adjoin_rank_eq_rank_left_of_isAlgebraic_left |>.symm
  rwa [separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable K, rank_top'] at h

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[E:F] [K:E]_s = [K:F]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma lift_rank_mul_lift_sepDegree_of_isSeparable [Algebra.IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree, sepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

/-- The same-universe version of `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`. -/
lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[K:F]_i = [K:E]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma insepDegree_eq_of_isSeparable [Algebra.IsSeparable F E] :
    insepDegree F K = insepDegree E K := by
  rw [insepDegree, insepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  rfl

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable,
then $[K:F]_s = [K:E]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  haveI : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree, ← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
    (IsScalarTower.toAlgHom F (separableClosure E K) K) |>.symm.toLinearEquiv.rank_eq

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable,
then $[E:F] [K:E]_i = [K:F]_i$.
It is a special case of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma lift_rank_mul_lift_insepDegree_of_isPurelyInseparable [IsPurelyInseparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := (separableClosure F K).linearDisjoint_of_isPurelyInseparable_of_isSeparable E
    |>.lift_rank_right_mul_lift_adjoin_rank_eq_of_isAlgebraic_left
  rwa [separableClosure.adjoin_eq_of_isAlgebraic] at h

/-- The same-universe version of `Field.lift_rank_mul_lift_insepDegree_of_isPurelyInseparable`. -/
lemma rank_mul_insepDegree_of_isPurelyInseparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [IsPurelyInseparable F E] :
    Module.rank F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_insepDegree_of_isPurelyInseparable F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$. -/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

/-- The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 1"]
theorem sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    sepDegree F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
inseparable degrees satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$. -/
theorem lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    Cardinal.lift.{w} (insepDegree F E) * Cardinal.lift.{v} (insepDegree E K) =
    Cardinal.lift.{v} (insepDegree F K) := by
  have h := lift_rank_mul_lift_insepDegree_of_isPurelyInseparable (separableClosure F E) E K
  rwa [← insepDegree_eq_of_isSeparable F (separableClosure F E) K] at h

/-- The same-universe version of `Field.lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic`. -/
@[stacks 09HK "Part 2"]
theorem insepDegree_mul_insepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [Algebra.IsAlgebraic F E] :
    insepDegree F E * insepDegree E K = insepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
inseparable degrees, as natural numbers, satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$. -/
@[stacks 09HK "Part 2, `finInsepDegree` variant"]
theorem finInsepDegree_mul_finInsepDegree_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    finInsepDegree F E * finInsepDegree E K = finInsepDegree F K := by
  simpa only [map_mul, Cardinal.toNat_lift] using
    congr(Cardinal.toNat $(lift_insepDegree_mul_lift_insepDegree_of_isAlgebraic F E K))

end Field

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any subset `S` of `K` such that `F(S) / F` is algebraic, the `E(S) / E` and `F(S) / F` have
the same separable degree. -/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable
    (S : Set K) [Algebra.IsAlgebraic F (adjoin F S)] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E S) = sepDegree F (adjoin F S) := by
  set M := adjoin F S
  set L := adjoin E S
  let E' := (IsScalarTower.toAlgHom F E K).fieldRange
  let j : E ≃ₐ[F] E' := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K)
  have hi : M ≤ L.restrictScalars F := by
    rw [restrictScalars_adjoin_of_algEquiv (E := K) j rfl, restrictScalars_adjoin]
    exact adjoin.mono _ _ _ Set.subset_union_right
  let i : M →+* L := Subsemiring.inclusion hi
  letI : Algebra M L := i.toAlgebra
  letI : SMul M L := Algebra.toSMul
  haveI : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsPurelyInseparable M L := by
    change IsPurelyInseparable M (extendScalars hi)
    obtain ⟨q, _⟩ := ExpChar.exists F
    have : extendScalars hi = adjoin M (E' : Set K) := restrictScalars_injective F <| by
      conv_lhs => rw [extendScalars_restrictScalars, restrictScalars_adjoin_of_algEquiv
        (E := K) j rfl, ← adjoin_self F E', adjoin_adjoin_comm]
    rw [this, isPurelyInseparable_adjoin_iff_pow_mem _ _ q]
    rintro x ⟨y, hy⟩
    obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q y
    refine ⟨n, algebraMap F M z, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E K, hz, ← hy, map_pow,
      AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom]
  have h := lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E L
  rw [IsPurelyInseparable.sepDegree_eq_one F E, Cardinal.lift_one, one_mul] at h
  rw [Cardinal.lift_injective h, ← sepDegree_mul_sepDegree_of_isAlgebraic F M L,
    IsPurelyInseparable.sepDegree_eq_one M L, mul_one]

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any intermediate field `S` of `K / F` such that `S / F` is algebraic, the `E(S) / E` and
`S / F` have the same separable degree. -/
theorem IntermediateField.sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable'
    (S : IntermediateField F K) [Algebra.IsAlgebraic F S] [IsPurelyInseparable F E] :
    sepDegree E (adjoin E (S : Set K)) = sepDegree F S := by
  have : Algebra.IsAlgebraic F (adjoin F (S : Set K)) := by rwa [adjoin_self]
  have := sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E (S : Set K)
  rwa [adjoin_self] at this

variable {F K} in
/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
for any element `x` of `K` separable over `F`, it has the same minimal polynomials over `F` and
over `E`. -/
theorem minpoly.map_eq_of_isSeparable_of_isPurelyInseparable (x : K)
    (hsep : IsSeparable F x) [IsPurelyInseparable F E] :
    (minpoly F x).map (algebraMap F E) = minpoly E x := by
  have hi := IsSeparable.isIntegral hsep
  have hi' : IsIntegral E x := IsIntegral.tower_top hi
  refine eq_of_monic_of_dvd_of_natDegree_le (monic hi') ((monic hi).map (algebraMap F E))
    (dvd_map_of_isScalarTower F E x) (le_of_eq ?_)
  have hsep' := IsSeparable.tower_top E hsep
  haveI := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep
  haveI := (isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsep'
  have := Algebra.IsSeparable.isAlgebraic F F⟮x⟯
  have := Algebra.IsSeparable.isAlgebraic E E⟮x⟯
  rw [Polynomial.natDegree_map, ← adjoin.finrank hi, ← adjoin.finrank hi',
    ← finSepDegree_eq_finrank_of_isSeparable F _, ← finSepDegree_eq_finrank_of_isSeparable E _,
    finSepDegree_eq, finSepDegree_eq,
    sepDegree_adjoin_eq_of_isAlgebraic_of_isPurelyInseparable (F := F) E]

variable {F} in
/-- If `E / F` is a purely inseparable field extension, `f` is a separable irreducible polynomial
over `F`, then it is also irreducible over `E`. -/
theorem Polynomial.Separable.map_irreducible_of_isPurelyInseparable {f : F[X]} (hsep : f.Separable)
    (hirr : Irreducible f) [IsPurelyInseparable F E] : Irreducible (f.map (algebraMap F E)) := by
  let K := AlgebraicClosure E
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K f
    (natDegree_pos_iff_degree_pos.1 hirr.natDegree_pos).ne'
  have ha : Associated f (minpoly F x) := by
    have := isUnit_C.2 (leadingCoeff_ne_zero.2 hirr.ne_zero).isUnit.inv
    exact ⟨this.unit, by rw [IsUnit.unit_spec, minpoly.eq_of_irreducible hirr hx]⟩
  have ha' : Associated (f.map (algebraMap F E)) ((minpoly F x).map (algebraMap F E)) :=
    ha.map (mapRingHom (algebraMap F E)).toMonoidHom
  have heq := minpoly.map_eq_of_isSeparable_of_isPurelyInseparable E x (ha.separable hsep)
  rw [ha'.irreducible_iff, heq]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral x)

end TowerLaw
