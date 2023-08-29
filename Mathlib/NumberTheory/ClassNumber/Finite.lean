/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Norm

#align_import number_theory.class_number.finite from "leanprover-community/mathlib"@"ea0bcd84221246c801a6f8fbe8a4372f6d04b176"

/-!
# Class numbers of global fields
In this file, we use the notion of "admissible absolute value" to prove
finiteness of the class group for number fields and function fields.

## Main definitions
 - `ClassGroup.fintypeOfAdmissibleOfAlgebraic`: if `R` has an admissible absolute value,
   its integral closure has a finite class group
-/

open scoped BigOperators

open scoped nonZeroDivisors

namespace ClassGroup

open Ring

open scoped BigOperators

section EuclideanDomain

variable {R S : Type*} (K L : Type*) [EuclideanDomain R] [CommRing S] [IsDomain S]

variable [Field K] [Field L]

variable [Algebra R K] [IsFractionRing R K]

variable [Algebra K L] [FiniteDimensional K L] [IsSeparable K L]

variable [algRL : Algebra R L] [IsScalarTower R K L]

variable [Algebra R S] [Algebra S L]

variable [ist : IsScalarTower R S L] [iic : IsIntegralClosure S R L]

variable (abv : AbsoluteValue R ℤ)

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (bS : Basis ι R S)

/-- If `b` is an `R`-basis of `S` of cardinality `n`, then `normBound abv b` is an integer
such that for every `R`-integral element `a : S` with coordinates `≤ y`,
we have algebra.norm a ≤ norm_bound abv b * y ^ n`. (See also `norm_le` and `norm_lt`). -/
noncomputable def normBound : ℤ :=
  let n := Fintype.card ι
  let i : ι := Nonempty.some bS.index_nonempty
  let m : ℤ :=
    Finset.max'
      (Finset.univ.image fun ijk : ι × ι × ι =>
        abv (Algebra.leftMulMatrix bS (bS ijk.1) ijk.2.1 ijk.2.2))
      ⟨_, Finset.mem_image.mpr ⟨⟨i, i, i⟩, Finset.mem_univ _, rfl⟩⟩
  Nat.factorial n • (n • m) ^ n
#align class_group.norm_bound ClassGroup.normBound

theorem normBound_pos : 0 < normBound abv bS := by
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k, Algebra.leftMulMatrix bS (bS i) j k ≠ 0 := by
    by_contra' h
    obtain ⟨i⟩ := bS.index_nonempty
    apply bS.ne_zero i
    apply
      (injective_iff_map_eq_zero (Algebra.leftMulMatrix bS)).mp (Algebra.leftMulMatrix_injective bS)
    ext j k
    simp [h, DMatrix.zero_apply]
  simp only [normBound, Algebra.smul_def, eq_natCast]
  -- ⊢ 0 < ↑(Nat.factorial (Fintype.card ι)) * (↑(Fintype.card ι) * Finset.max' (Fi …
  refine' mul_pos (Int.coe_nat_pos.mpr (Nat.factorial_pos _)) _
  -- ⊢ 0 < (↑(Fintype.card ι) * Finset.max' (Finset.image (fun ijk => ↑abv (↑(Algeb …
  refine' pow_pos (mul_pos (Int.coe_nat_pos.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)) _) _
  -- ⊢ 0 < Finset.max' (Finset.image (fun ijk => ↑abv (↑(Algebra.leftMulMatrix bS)  …
  refine' lt_of_lt_of_le (abv.pos hijk) (Finset.le_max' _ _ _)
  -- ⊢ ↑abv (↑(Algebra.leftMulMatrix bS) (↑bS i) j k) ∈ Finset.image (fun ijk => ↑a …
  exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩
  -- 🎉 no goals
#align class_group.norm_bound_pos ClassGroup.normBound_pos

/-- If the `R`-integral element `a : S` has coordinates `≤ y` with respect to some basis `b`,
its norm is less than `normBound abv b * y ^ dim S`. -/
theorem norm_le (a : S) {y : ℤ} (hy : ∀ k, abv (bS.repr a k) ≤ y) :
    abv (Algebra.norm R a) ≤ normBound abv bS * y ^ Fintype.card ι := by
  conv_lhs => rw [← bS.sum_repr a]
  -- ⊢ ↑abv (↑(Algebra.norm R) (∑ i : ι, ↑(↑bS.repr a) i • ↑bS i)) ≤ normBound abv  …
  rw [Algebra.norm_apply, ← LinearMap.det_toMatrix bS]
  -- ⊢ ↑abv (↑(Algebra.norm R) (∑ i : ι, ↑(↑bS.repr a) i • ↑bS i)) ≤ normBound abv  …
  simp only [Algebra.norm_apply, AlgHom.map_sum, AlgHom.map_smul, LinearEquiv.map_sum,
    LinearEquiv.map_smul, Algebra.toMatrix_lmul_eq, normBound, smul_mul_assoc, ← mul_pow]
  --Porting note: rest of proof was
  -- convert Matrix.det_sum_smul_le Finset.univ _ hy using 3
  -- · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
  -- · intro i j k
  --   apply Finset.le_max'
  --   exact finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩
  rw [← LinearMap.det_toMatrix bS]
  -- ⊢ ↑abv (Matrix.det (↑(LinearMap.toMatrix bS bS) (∑ x : ι, ↑(↑bS.repr a) x • ↑( …
  convert Matrix.det_sum_smul_le (n := ι) Finset.univ _ hy using 3
  · simp; rfl
    -- ⊢ ∑ x : ι, ↑(↑bS.repr a) x • ↑(LinearMap.toMatrix bS bS) (↑(LinearMap.mul R S) …
          -- 🎉 no goals
  · rw [Finset.card_univ, smul_mul_assoc, mul_comm]
    -- 🎉 no goals
  · intro i j k
    -- ⊢ ↑abv (↑(LinearMap.toMatrix bS bS) (↑(LinearMap.mul R S) (↑bS i)) j k) ≤ Fins …
    apply Finset.le_max'
    -- ⊢ ↑abv (↑(LinearMap.toMatrix bS bS) (↑(LinearMap.mul R S) (↑bS i)) j k) ∈ Fins …
    exact Finset.mem_image.mpr ⟨⟨i, j, k⟩, Finset.mem_univ _, rfl⟩
    -- 🎉 no goals
#align class_group.norm_le ClassGroup.norm_le

/-- If the `R`-integral element `a : S` has coordinates `< y` with respect to some basis `b`,
its norm is strictly less than `normBound abv b * y ^ dim S`. -/
theorem norm_lt {T : Type*} [LinearOrderedRing T] (a : S) {y : T}
    (hy : ∀ k, (abv (bS.repr a k) : T) < y) :
    (abv (Algebra.norm R a) : T) < normBound abv bS * y ^ Fintype.card ι := by
  obtain ⟨i⟩ := bS.index_nonempty
  -- ⊢ ↑(↑abv (↑(Algebra.norm R) a)) < ↑(normBound abv bS) * y ^ Fintype.card ι
  have him : (Finset.univ.image fun k => abv (bS.repr a k)).Nonempty :=
    ⟨_, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  set y' : ℤ := Finset.max' _ him with y'_def
  -- ⊢ ↑(↑abv (↑(Algebra.norm R) a)) < ↑(normBound abv bS) * y ^ Fintype.card ι
  have hy' : ∀ k, abv (bS.repr a k) ≤ y' := by
    intro k
    exact @Finset.le_max' ℤ _ _ _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
  have : (y' : T) < y := by
    rw [y'_def, ←
      Finset.max'_image (show Monotone (_ : ℤ → T) from fun x y h => Int.cast_le.mpr h)]
    apply (Finset.max'_lt_iff _ (him.image _)).mpr
    simp only [Finset.mem_image, exists_prop]
    rintro _ ⟨x, ⟨k, -, rfl⟩, rfl⟩
    exact hy k
  have y'_nonneg : 0 ≤ y' := le_trans (abv.nonneg _) (hy' i)
  -- ⊢ ↑(↑abv (↑(Algebra.norm R) a)) < ↑(normBound abv bS) * y ^ Fintype.card ι
  apply (Int.cast_le.mpr (norm_le abv bS a hy')).trans_lt
  -- ⊢ ↑(normBound abv bS * y' ^ Fintype.card ι) < ↑(normBound abv bS) * y ^ Fintyp …
  simp only [Int.cast_mul, Int.cast_pow]
  -- ⊢ ↑(normBound abv bS) * ↑(Finset.max' (Finset.image (fun k => ↑abv (↑(↑bS.repr …
  apply mul_lt_mul' le_rfl
  · exact pow_lt_pow_of_lt_left this (Int.cast_nonneg.mpr y'_nonneg) (Fintype.card_pos_iff.mpr ⟨i⟩)
    -- 🎉 no goals
  · exact pow_nonneg (Int.cast_nonneg.mpr y'_nonneg) _
    -- 🎉 no goals
  · exact Int.cast_pos.mpr (normBound_pos abv bS)
    -- 🎉 no goals
#align class_group.norm_lt ClassGroup.norm_lt


/-- A nonzero ideal has an element of minimal norm. -/
-- porting note: port of Int.exists_least_of_bdd requires DecidablePred, so we use classical
theorem exists_min (I : (Ideal S)⁰) :
    ∃ b ∈ (I : Ideal S),
      b ≠ 0 ∧ ∀ c ∈ (I : Ideal S), abv (Algebra.norm R c) < abv (Algebra.norm R b) → c =
      (0 : S) := by
  classical
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ := @Int.exists_least_of_bdd
      (fun a => ∃ b ∈ (I : Ideal S), b ≠ (0 : S) ∧ abv (Algebra.norm R b) = a) _
    (by
      use 0
      rintro _ ⟨b, _, _, rfl⟩
      apply abv.nonneg)
    (by
      obtain ⟨b, b_mem, b_ne_zero⟩ := (I : Ideal S).ne_bot_iff.mp (nonZeroDivisors.coe_ne_zero I)
      exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩)
  · refine' ⟨b, b_mem, b_ne_zero, _⟩
    intro c hc lt
    contrapose! lt with c_ne_zero
    exact min _ ⟨c, hc, c_ne_zero, rfl⟩
#align class_group.exists_min ClassGroup.exists_min

section IsAdmissible

variable {abv} (adm : abv.IsAdmissible)

/-- If we have a large enough set of elements in `R^ι`, then there will be a pair
whose remainders are close together. We'll show that all sets of cardinality
at least `cardM bS adm` elements satisfy this condition.

The value of `cardM` is not at all optimal: for specific choices of `R`,
the minimum cardinality can be exponentially smaller.
-/
noncomputable def cardM : ℕ :=
  adm.card (normBound abv bS ^ (-1 / Fintype.card ι : ℝ)) ^ Fintype.card ι
set_option linter.uppercaseLean3 false in
#align class_group.cardM ClassGroup.cardM

variable [Infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
noncomputable def distinctElems : Fin (cardM bS adm).succ ↪ R :=
  Fin.valEmbedding.trans (Infinite.natEmbedding R)
#align class_group.distinct_elems ClassGroup.distinctElems

variable [DecidableEq R]

/-- `finsetApprox` is a finite set such that each fractional ideal in the integral closure
contains an element close to `finsetApprox`. -/
noncomputable def finsetApprox : Finset R :=
  (Finset.univ.image fun xy : _ × _ => distinctElems bS adm xy.1 - distinctElems bS adm xy.2).erase
    0
#align class_group.finset_approx ClassGroup.finsetApprox

theorem finsetApprox.zero_not_mem : (0 : R) ∉ finsetApprox bS adm :=
  Finset.not_mem_erase _ _
#align class_group.finset_approx.zero_not_mem ClassGroup.finsetApprox.zero_not_mem

@[simp]
theorem mem_finsetApprox {x : R} :
    x ∈ finsetApprox bS adm ↔ ∃ i j, i ≠ j ∧ distinctElems bS adm i - distinctElems bS adm j =
    x := by
  simp only [finsetApprox, Finset.mem_erase, Finset.mem_image]
  -- ⊢ (x ≠ 0 ∧ ∃ a, a ∈ Finset.univ ∧ ↑(distinctElems bS adm) a.fst - ↑(distinctEl …
  constructor
  -- ⊢ (x ≠ 0 ∧ ∃ a, a ∈ Finset.univ ∧ ↑(distinctElems bS adm) a.fst - ↑(distinctEl …
  · rintro ⟨hx, ⟨i, j⟩, _, rfl⟩
    -- ⊢ ∃ i_1 j_1, i_1 ≠ j_1 ∧ ↑(distinctElems bS adm) i_1 - ↑(distinctElems bS adm) …
    refine' ⟨i, j, _, rfl⟩
    -- ⊢ i ≠ j
    rintro rfl
    -- ⊢ False
    simp at hx
    -- 🎉 no goals
  · rintro ⟨i, j, hij, rfl⟩
    -- ⊢ ↑(distinctElems bS adm) i - ↑(distinctElems bS adm) j ≠ 0 ∧ ∃ a, a ∈ Finset. …
    refine' ⟨_, ⟨i, j⟩, Finset.mem_univ _, rfl⟩
    -- ⊢ ↑(distinctElems bS adm) i - ↑(distinctElems bS adm) j ≠ 0
    rw [Ne.def, sub_eq_zero]
    -- ⊢ ¬↑(distinctElems bS adm) i = ↑(distinctElems bS adm) j
    exact fun h => hij ((distinctElems bS adm).injective h)
    -- 🎉 no goals
#align class_group.mem_finset_approx ClassGroup.mem_finsetApprox

section Real

open Real

attribute [-instance] Real.decidableEq

set_option maxHeartbeats 800000 in
/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finsetApprox (a : S) {b} (hb : b ≠ (0 : R)) :
    ∃ q : S,
      ∃ r ∈ finsetApprox bS adm, abv (Algebra.norm R (r • a - b • q)) <
      abv (Algebra.norm R (algebraMap R S b)) := by
  have dim_pos := Fintype.card_pos_iff.mpr bS.index_nonempty
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  set ε : ℝ := normBound abv bS ^ (-1 / Fintype.card ι : ℝ) with ε_eq
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have hε : 0 < ε := Real.rpow_pos_of_pos (Int.cast_pos.mpr (normBound_pos abv bS)) _
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have ε_le : (normBound abv bS : ℝ) * (abv b • ε) ^ Fintype.card ι ≤ abv b ^ Fintype.card ι := by
    have := normBound_pos abv bS
    have := abv.nonneg b
    rw [ε_eq, Algebra.smul_def, eq_intCast, mul_rpow, ← rpow_mul, div_mul_cancel, rpow_neg_one,
      mul_left_comm, mul_inv_cancel, mul_one, rpow_nat_cast] <;>
      try norm_cast; linarith
    · exact Iff.mpr Int.cast_nonneg this
    · linarith
  set μ : Fin (cardM bS adm).succ ↪ R := distinctElems bS adm with hμ
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  let s : ι →₀ R := bS.repr a
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have s_eq : ∀ i, s i = bS.repr a i := fun i => rfl
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  let qs : Fin (cardM bS adm).succ → ι → R := fun j i => μ j * s i / b
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  let rs : Fin (cardM bS adm).succ → ι → R := fun j i => μ j * s i % b
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have r_eq : ∀ j i, rs j i = μ j * s i % b := fun i j => rfl
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have μ_eq : ∀ i j, μ j * s i = b * qs j i + rs j i := by
    intro i j
    rw [r_eq, EuclideanDomain.div_add_mod]
  have μ_mul_a_eq : ∀ j, μ j • a = b • ∑ i, qs j i • bS i + ∑ i, rs j i • bS i := by
    intro j
    rw [← bS.sum_repr a]
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine'
      Finset.sum_congr rfl fun i _ => _
-- Porting note `← hμ, ← r_eq` and the final `← μ_eq` were not needed.
    rw [← hμ, ← r_eq, ← s_eq, ← mul_smul, μ_eq, add_smul, mul_smul, ← μ_eq]
  obtain ⟨j, k, j_ne_k, hjk⟩ := adm.exists_approx hε hb fun j i => μ j * s i
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  have hjk' : ∀ i, (abv (rs k i - rs j i) : ℝ) < abv b • ε := by simpa only [r_eq] using hjk
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  let q := ∑ i, (qs k i - qs j i) • bS i
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  set r := μ k - μ j with r_eq
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - b • q)) <  …
  refine' ⟨q, r, (mem_finsetApprox bS adm).mpr _, _⟩
  -- ⊢ ∃ i j, i ≠ j ∧ ↑(distinctElems bS adm) i - ↑(distinctElems bS adm) j = r
  · exact ⟨k, j, j_ne_k.symm, rfl⟩
    -- 🎉 no goals
  have : r • a - b • q = ∑ x : ι, (rs k x • bS x - rs j x • bS x) := by
    simp only [r_eq, sub_smul, μ_mul_a_eq, Finset.smul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, smul_sub]
    refine' Finset.sum_congr rfl fun x _ => _
    ring
  rw [this, Algebra.norm_algebraMap_of_basis bS, abv.map_pow]
  -- ⊢ ↑abv (↑(Algebra.norm R) (∑ x : ι, (rs k x • ↑bS x - rs j x • ↑bS x))) < ↑abv …
  refine' Int.cast_lt.mp ((norm_lt abv bS _ fun i => lt_of_le_of_lt _ (hjk' i)).trans_le _)
  -- ⊢ ↑(↑abv (↑(↑bS.repr (∑ x : ι, (rs k x • ↑bS x - rs j x • ↑bS x))) i)) ≤ ↑(↑ab …
  · apply le_of_eq
    -- ⊢ ↑(↑abv (↑(↑bS.repr (∑ x : ι, (rs k x • ↑bS x - rs j x • ↑bS x))) i)) = ↑(↑ab …
    congr
    -- ⊢ ↑(↑bS.repr (∑ x : ι, (rs k x • ↑bS x - rs j x • ↑bS x))) i = rs k i - rs j i
    simp_rw [LinearEquiv.map_sum, LinearEquiv.map_sub, LinearEquiv.map_smul, Finset.sum_apply',
      Finsupp.sub_apply, Finsupp.smul_apply, Finset.sum_sub_distrib, Basis.repr_self_apply,
      smul_eq_mul, mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · exact_mod_cast ε_le
    -- 🎉 no goals
#align class_group.exists_mem_finset_approx ClassGroup.exists_mem_finsetApprox

/-- We can approximate `a / b : L` with `q / r`, where `r` has finitely many options for `L`. -/
theorem exists_mem_finset_approx' (h : Algebra.IsAlgebraic R L) (a : S) {b : S} (hb : b ≠ 0) :
    ∃ q : S,
      ∃ r ∈ finsetApprox bS adm, abv (Algebra.norm R (r • a - q * b)) < abv (Algebra.norm R b) := by
  have inj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R S L]
    exact (IsIntegralClosure.algebraMap_injective S R L).comp bS.algebraMap_injective
  obtain ⟨a', b', hb', h⟩ := IsIntegralClosure.exists_smul_eq_mul h inj a hb
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - q * b)) <  …
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finsetApprox bS adm a' hb'
  -- ⊢ ∃ q r, r ∈ finsetApprox bS adm ∧ ↑abv (↑(Algebra.norm R) (r • a - q * b)) <  …
  refine' ⟨q, r, hr, _⟩
  -- ⊢ ↑abv (↑(Algebra.norm R) (r • a - q * b)) < ↑abv (↑(Algebra.norm R) b)
  refine'
    lt_of_mul_lt_mul_left _ (show 0 ≤ abv (Algebra.norm R (algebraMap R S b')) from abv.nonneg _)
  refine'
    lt_of_le_of_lt (le_of_eq _)
      (mul_lt_mul hqr le_rfl (abv.pos ((Algebra.norm_ne_zero_iff_of_basis bS).mpr hb))
        (abv.nonneg _))
  rw [← abv.map_mul, ← MonoidHom.map_mul, ← abv.map_mul, ← MonoidHom.map_mul, ← Algebra.smul_def,
    smul_sub b', sub_mul, smul_comm, h, mul_comm b a', Algebra.smul_mul_assoc r a' b,
    Algebra.smul_mul_assoc b' q b]
#align class_group.exists_mem_finset_approx' ClassGroup.exists_mem_finset_approx'

end Real

theorem prod_finsetApprox_ne_zero : algebraMap R S (∏ m in finsetApprox bS adm, m) ≠ 0 := by
  refine' mt ((injective_iff_map_eq_zero _).mp bS.algebraMap_injective _) _
  -- ⊢ ¬∏ m in finsetApprox bS adm, m = 0
  simp only [Finset.prod_eq_zero_iff, not_exists]
  -- ⊢ ∀ (x : R), ¬(x ∈ finsetApprox bS adm ∧ x = 0)
  rintro x ⟨hx, rfl⟩
  -- ⊢ False
  exact finsetApprox.zero_not_mem bS adm hx
  -- 🎉 no goals
#align class_group.prod_finset_approx_ne_zero ClassGroup.prod_finsetApprox_ne_zero

theorem ne_bot_of_prod_finsetApprox_mem (J : Ideal S)
    (h : algebraMap _ _ (∏ m in finsetApprox bS adm, m) ∈ J) : J ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨_, h, prod_finsetApprox_ne_zero _ _⟩
#align class_group.ne_bot_of_prod_finset_approx_mem ClassGroup.ne_bot_of_prod_finsetApprox_mem

/-- Each class in the class group contains an ideal `J`
such that `M := Π m ∈ finsetApprox` is in `J`. -/
theorem exists_mk0_eq_mk0 [IsDedekindDomain S] (h : Algebra.IsAlgebraic R L) (I : (Ideal S)⁰) :
    ∃ J : (Ideal S)⁰,
      ClassGroup.mk0 I = ClassGroup.mk0 J ∧
        algebraMap _ _ (∏ m in finsetApprox bS adm, m) ∈ (J : Ideal S) := by
  set M := ∏ m in finsetApprox bS adm, m
  -- ⊢ ∃ J, ↑mk0 I = ↑mk0 J ∧ ↑(algebraMap R S) M ∈ ↑J
  have hM : algebraMap R S M ≠ 0 := prod_finsetApprox_ne_zero bS adm
  -- ⊢ ∃ J, ↑mk0 I = ↑mk0 J ∧ ↑(algebraMap R S) M ∈ ↑J
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min abv I
  -- ⊢ ∃ J, ↑mk0 I = ↑mk0 J ∧ ↑(algebraMap R S) M ∈ ↑J
  suffices Ideal.span {b} ∣ Ideal.span {algebraMap _ _ M} * I.1 by
    obtain ⟨J, hJ⟩ := this
    refine' ⟨⟨J, _⟩, _, _⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.mul_bot] at hJ
      exact hM (Ideal.span_singleton_eq_bot.mp (I.2 _ hJ))
    · rw [ClassGroup.mk0_eq_mk0_iff]
      exact ⟨algebraMap _ _ M, b, hM, b_ne_zero, hJ⟩
    rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Ideal.span_le, ← Ideal.dvd_iff_le]
    refine' (mul_dvd_mul_iff_left _).mp _
    swap; · exact mt Ideal.span_singleton_eq_bot.mp b_ne_zero
    rw [Subtype.coe_mk, Ideal.dvd_iff_le, ← hJ, mul_comm]
    apply Ideal.mul_mono le_rfl
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact b_mem
  rw [Ideal.dvd_iff_le, Ideal.mul_le]
  -- ⊢ ∀ (r : (fun x => S) M), r ∈ Ideal.span {↑(algebraMap R S) M} → ∀ (s : (fun x …
  intro r' hr' a ha
  -- ⊢ r' * a ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton] at hr' ⊢
  -- ⊢ b ∣ r' * a
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' L bS adm h a b_ne_zero
  -- ⊢ b ∣ r' * a
  apply @dvd_of_mul_left_dvd _ _ q
  -- ⊢ q * b ∣ r' * a
  simp only [Algebra.smul_def] at lt
  -- ⊢ q * b ∣ r' * a
  rw [←
    sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left _ ha) (I.1.mul_mem_left _ b_mem)) lt)]
  refine' mul_dvd_mul_right (dvd_trans (RingHom.map_dvd _ _) hr') _
  -- ⊢ r ∣ M
  exact Multiset.dvd_prod (Multiset.mem_map.mpr ⟨_, r_mem, rfl⟩)
  -- 🎉 no goals
#align class_group.exists_mk0_eq_mk0 ClassGroup.exists_mk0_eq_mk0

/-- `ClassGroup.mkMMem` is a specialization of `ClassGroup.mk0` to (the finite set of)
ideals that contain `M := ∏ m in finsetApprox L f abs, m`.
By showing this function is surjective, we prove that the class group is finite. -/
noncomputable def mkMMem [IsDedekindDomain S]
    (J : { J : Ideal S // algebraMap _ _ (∏ m in finsetApprox bS adm, m) ∈ J }) : ClassGroup S :=
  ClassGroup.mk0
    ⟨J.1, mem_nonZeroDivisors_iff_ne_zero.mpr (ne_bot_of_prod_finsetApprox_mem bS adm J.1 J.2)⟩
set_option linter.uppercaseLean3 false in
#align class_group.mk_M_mem ClassGroup.mkMMem

theorem mkMMem_surjective [IsDedekindDomain S] (h : Algebra.IsAlgebraic R L) :
    Function.Surjective (ClassGroup.mkMMem bS adm) := by
  intro I'
  -- ⊢ ∃ a, mkMMem bS adm a = I'
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective I'
  -- ⊢ ∃ a, mkMMem bS adm a = ↑mk0 { val := I, property := hI }
  obtain ⟨J, mk0_eq_mk0, J_dvd⟩ := exists_mk0_eq_mk0 L bS adm h ⟨I, hI⟩
  -- ⊢ ∃ a, mkMMem bS adm a = ↑mk0 { val := I, property := hI }
  exact ⟨⟨J, J_dvd⟩, mk0_eq_mk0.symm⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align class_group.mk_M_mem_surjective ClassGroup.mkMMem_surjective

open scoped Classical

/-- The main theorem: the class group of an integral closure `S` of `R` in an
algebraic extension `L` is finite if there is an admissible absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfFinite` where `L` is a finite
extension of `K = Frac(R)`, supplying most of the required assumptions automatically.
-/
noncomputable def fintypeOfAdmissibleOfAlgebraic [IsDedekindDomain S]
    (h : Algebra.IsAlgebraic R L) : Fintype (ClassGroup S) :=
  @Fintype.ofSurjective _ _ _
    (@Fintype.ofEquiv _
      { J // J ∣ Ideal.span ({algebraMap R S (∏ m : R in finsetApprox bS adm, m)} : Set S) }
      (UniqueFactorizationMonoid.fintypeSubtypeDvd _
        (by
          rw [Ne.def, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
          -- ⊢ ¬↑(algebraMap R S) (∏ m in finsetApprox bS adm, m) = 0
          exact prod_finsetApprox_ne_zero bS adm))
          -- 🎉 no goals
      ((Equiv.refl _).subtypeEquiv fun I =>
        Ideal.dvd_iff_le.trans (by
          rw [Equiv.refl_apply, Ideal.span_le, Set.singleton_subset_iff]; rfl)))
          -- ⊢ ↑(algebraMap R S) (∏ m in finsetApprox bS adm, m) ∈ ↑I ↔ ↑(algebraMap R S) ( …
                                                                          -- 🎉 no goals
    (ClassGroup.mkMMem bS adm) (ClassGroup.mkMMem_surjective L bS adm h)
#align class_group.fintype_of_admissible_of_algebraic ClassGroup.fintypeOfAdmissibleOfAlgebraic

/-- The main theorem: the class group of an integral closure `S` of `R` in a
finite extension `L` of `K = Frac(R)` is finite if there is an admissible
absolute value.

See also `ClassGroup.fintypeOfAdmissibleOfAlgebraic` where `L` is an
algebraic extension of `R`, that includes some extra assumptions.
-/
noncomputable def fintypeOfAdmissibleOfFinite : Fintype (ClassGroup S) := by
  letI := Classical.decEq L
  -- ⊢ Fintype (ClassGroup S)
  letI := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  -- ⊢ Fintype (ClassGroup S)
  letI := IsIntegralClosure.isDedekindDomain R K L S
  -- ⊢ Fintype (ClassGroup S)
  choose s b hb_int using FiniteDimensional.exists_is_basis_integral R K L
  -- ⊢ Fintype (ClassGroup S)
-- Porting note: `this` and `f` below where solved at the end rather than being defined at first.
  have : LinearIndependent R ((Algebra.traceForm K L).dualBasis
      (traceForm_nondegenerate K L) b) := by
    refine' (Basis.linearIndependent _).restrict_scalars _
    simp only [Algebra.smul_def, mul_one]
    apply IsFractionRing.injective
  obtain ⟨n, b⟩ :=
    Submodule.basisOfPidOfLESpan this (IsIntegralClosure.range_le_span_dualBasis S b hb_int)
  let f : (S ⧸ LinearMap.ker (LinearMap.restrictScalars R (Algebra.linearMap S L))) ≃ₗ[R] S := by
    rw [LinearMap.ker_eq_bot.mpr]
    · exact Submodule.quotEquivOfEqBot _ rfl
    · exact IsIntegralClosure.algebraMap_injective _ R _
  let bS := b.map ((LinearMap.quotKerEquivRange _).symm ≪≫ₗ f)
  -- ⊢ Fintype (ClassGroup S)
  exact fintypeOfAdmissibleOfAlgebraic L bS adm (fun x =>
    (IsFractionRing.isAlgebraic_iff R K L).mpr (Algebra.isAlgebraic_of_finite K _ x))
#align class_group.fintype_of_admissible_of_finite ClassGroup.fintypeOfAdmissibleOfFinite

end IsAdmissible

end EuclideanDomain

end ClassGroup
