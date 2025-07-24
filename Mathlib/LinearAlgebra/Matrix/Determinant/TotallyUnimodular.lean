/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Vladimir Kolmogorov, Ivan Sergeev, Bhavik Mehta
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Sign
import Mathlib.Data.Sum.Decompose

/-!
# Totally unimodular matrices

This file defines totally unimodular matrices and provides basic API for them.

## Main definitions

- `Matrix.IsTotallyUnimodular`: a matrix is totally unimodular iff every square submatrix
  (not necessarily contiguous) has determinant `0` or `1` or `-1`.

## Main results

- `Matrix.isTotallyUnimodular_iff`: a matrix is totally unimodular iff every square submatrix
  (possibly with repeated rows and/or repeated columns) has determinant `0` or `1` or `-1`.
- `Matrix.IsTotallyUnimodular.apply`: entry in a totally unimodular matrix is `0` or `1` or `-1`.

-/

namespace Matrix

variable {m m' n n' R : Type*} [CommRing R]

/-- `A.IsTotallyUnimodular` means that every square submatrix of `A` (not necessarily contiguous)
has determinant `0` or `1` or `-1`; that is, the determinant is in the range of `SignType.cast`. -/
def IsTotallyUnimodular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ∈ Set.range SignType.cast

lemma isTotallyUnimodular_iff (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  constructor <;> intro hA
  · intro k f g
    by_cases hfg : f.Injective ∧ g.Injective
    · exact hA k f g hfg.1 hfg.2
    · use 0
      rw [SignType.coe_zero, eq_comm]
      simp_rw [not_and_or, Function.not_injective_iff] at hfg
      obtain ⟨i, j, hfij, hij⟩ | ⟨i, j, hgij, hij⟩ := hfg
      · rw [← det_transpose, transpose_submatrix]
        apply det_zero_of_column_eq hij.symm
        simp [hfij]
      · apply det_zero_of_column_eq hij
        simp [hgij]
  · intro _ _ _ _ _
    apply hA

lemma isTotallyUnimodular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyUnimodular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι], ∀ f : ι → m, ∀ g : ι → n,
      (A.submatrix f g).det ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff]
  constructor
  · intro hA ι _ _ f g
    specialize hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA
  · intro hA k f g
    specialize hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
    rwa [←submatrix_submatrix, det_submatrix_equiv_self] at hA

lemma IsTotallyUnimodular.apply {A : Matrix m n R} (hA : A.IsTotallyUnimodular) (i : m) (j : n) :
    A i j ∈ Set.range SignType.cast := by
  rw [isTotallyUnimodular_iff] at hA
  simpa using hA 1 (fun _ => i) (fun _ => j)

lemma IsTotallyUnimodular.submatrix {A : Matrix m n R} (f : m' → m) (g : n' → n)
    (hA : A.IsTotallyUnimodular) :
    (A.submatrix f g).IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, submatrix_submatrix] at hA ⊢
  intro _ _ _
  apply hA

lemma IsTotallyUnimodular.transpose {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    Aᵀ.IsTotallyUnimodular := by
  simp only [isTotallyUnimodular_iff, ← transpose_submatrix, det_transpose] at hA ⊢
  intro _ _ _
  apply hA

lemma transpose_isTotallyUnimodular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  constructor <;> apply IsTotallyUnimodular.transpose

lemma IsTotallyUnimodular.reindex {A : Matrix m n R} (em : m ≃ m') (en : n ≃ n')
    (hA : A.IsTotallyUnimodular) :
    (A.reindex em en).IsTotallyUnimodular :=
  hA.submatrix _ _

lemma reindex_isTotallyUnimodular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨fun hA => by simpa [Equiv.symm_apply_eq] using hA.reindex em.symm en.symm,
   fun hA => hA.reindex _ _⟩

/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1` or
a single `-1` then `fromRows A B` is totally unimodular. -/
lemma IsTotallyUnimodular.fromRows_unitlike [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hA : A.IsTotallyUnimodular)
    (hB : Nonempty n → ∀ i : m', ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    specialize hB ⟨g 0⟩
    -- Either `f` is `inr` somewhere or `inl` everywhere
    obtain ⟨i, j, hfi⟩ | ⟨f', rfl⟩ : (∃ i j, f i = .inr j) ∨ (∃ f', f = .inl ∘ f') := by
      simp_rw [← Sum.isRight_iff, or_iff_not_imp_left, not_exists, Bool.not_eq_true,
        Sum.isRight_eq_false, Sum.isLeft_iff]
      intro hfr
      choose f' hf' using hfr
      exact ⟨f', funext hf'⟩
    · have hAB := det_succ_row ((fromRows A B).submatrix f g) i
      simp only [submatrix_apply, hfi, fromRows_apply_inr] at hAB
      obtain ⟨j', s, hj'⟩ := hB j
      · simp only [hj'] at hAB
        by_cases hj'' : ∃ x, g x = j'
        · obtain ⟨x, rfl⟩ := hj''
          rw [Fintype.sum_eq_single x fun y hxy => ?_, Pi.single_eq_same] at hAB
          · rw [hAB]
            change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ (Set.mem_range_self s)) ?_
            · apply pow_mem
              exact ⟨-1, by simp⟩
            · exact ih _ _
                (hf.comp Fin.succAbove_right_injective)
                (hg.comp Fin.succAbove_right_injective)
          · simp [Pi.single_eq_of_ne, hg.ne_iff.mpr hxy]
        · rw [not_exists] at hj''
          use 0
          simpa [hj''] using hAB.symm
    · rw [isTotallyUnimodular_iff] at hA
      apply hA

/-- If `A` is totally unimodular and each row of `B` is all zeros except for at most a single `1`,
then `fromRows A B` is totally unimodular. -/
lemma fromRows_isTotallyUnimodular_iff_rows [DecidableEq n] {A : Matrix m n R} {B : Matrix m' n R}
    (hB : Nonempty n → ∀ i : m', ∃ j : n, ∃ s : SignType, B i = Pi.single j s.cast) :
    (fromRows A B).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  ⟨.submatrix Sum.inl id, fun hA => hA.fromRows_unitlike hB⟩

lemma fromRows_one_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows A (1 : Matrix n n R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  fromRows_isTotallyUnimodular_iff_rows <| fun h i ↦
    ⟨i, 1, funext fun j ↦ by simp [one_apply, Pi.single_apply, eq_comm]⟩

lemma one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA, reindex_isTotallyUnimodular, fromRows_one_isTotallyUnimodular_iff]

lemma fromCols_one_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols A (1 : Matrix m m R)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [←transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    fromRows_one_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

@[deprecated (since := "2024-12-11")]
alias fromColumns_one_isTotallyUnimodular_iff := fromCols_one_isTotallyUnimodular_iff

lemma one_fromCols_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [←transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    one_fromRows_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

@[deprecated (since := "2024-12-11")]
alias one_fromColumns_isTotallyUnimodular_iff := one_fromCols_isTotallyUnimodular_iff

alias ⟨_, IsTotallyUnimodular.fromRows_one⟩ := fromRows_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromRows⟩ := one_fromRows_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.fromCols_one⟩ := fromCols_one_isTotallyUnimodular_iff
alias ⟨_, IsTotallyUnimodular.one_fromCols⟩ := one_fromCols_isTotallyUnimodular_iff

lemma fromRows_replicateRow0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromRows A (replicateRow m' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  classical
  refine fromRows_isTotallyUnimodular_iff_rows <| fun _ _ => ?_
  inhabit n
  refine ⟨default, 0, ?_⟩
  ext x
  simp [Pi.single_apply]

@[deprecated (since := "2024-12-11")]
alias fromRows_row0_isTotallyUnimodular_iff := fromRows_replicateRow0_isTotallyUnimodular_iff

lemma fromCols_replicateCol0_isTotallyUnimodular_iff (A : Matrix m n R) :
    (fromCols A (replicateCol n' 0)).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_replicateCol,
    fromRows_replicateRow0_isTotallyUnimodular_iff, transpose_isTotallyUnimodular_iff]

@[deprecated (since := "2024-12-11")]
alias fromColumns_col0_isTotallyUnimodular_iff := fromCols_replicateCol0_isTotallyUnimodular_iff

@[deprecated (since := "2024-12-11")]
alias fromCols_col0_isTotallyUnimodular_iff := fromCols_replicateCol0_isTotallyUnimodular_iff

-- TODO maybe rename and certainly move
lemma in_set_range_singType_cast_mul_in_set_range_singType_cast {a b : R}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  sorry

variable {R : Type*} [LinearOrderedCommRing R] -- TODO reorganize

-- TODO maybe rename and certainly move
lemma in_set_range_singType_cast_iff_abs (a : R) :
    a ∈ Set.range SignType.cast ↔ |a| ∈ Set.range SignType.cast := by
  sorry

-- TODO maybe rename and certainly move; do not require `R` to be algebraic structure
lemma fromBlocks_submatrix (A₁ : Matrix m n R) (A₂ : Matrix m' n' R)
    {α : Type*} (f : α → m ⊕ m') (g : α → n ⊕ n') :
    (fromBlocks A₁ 0 0 A₂).submatrix f g =
    (Matrix.fromBlocks
      (A₁.submatrix
        ((·.val.snd) : { x₁ : α × m // f x₁.fst = Sum.inl x₁.snd } → m)
        ((·.val.snd) : { y₁ : α × n // g y₁.fst = Sum.inl y₁.snd } → n)
      ) 0 0
      (A₂.submatrix
        ((·.val.snd) : { x₂ : α × m' // f x₂.fst = Sum.inr x₂.snd } → m')
        ((·.val.snd) : { y₂ : α × n' // g y₂.fst = Sum.inr y₂.snd } → n')
      )
     ).submatrix f.decomposeSum g.decomposeSum := by
  rw [f.eq_comp_decomposeSum, g.eq_comp_decomposeSum, ←Matrix.submatrix_submatrix]
  aesop

attribute [-simp] Fintype.card_ofIsEmpty Fintype.card_ofSubsingleton -- major performance issue

lemma fromBlocks_isTotallyUnimodular
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {A₁ : Matrix m n R} {A₂ : Matrix m' n' R}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  intro k f g hf hg
  rw [isTotallyUnimodular_iff_fintype] at hA₁ hA₂
  rw [fromBlocks_submatrix]
  -- look at sizes of submatrices in blocks
  if hxy : Fintype.card { x₁ : Fin k × m // f x₁.fst = Sum.inl x₁.snd }
         = Fintype.card { y₁ : Fin k × n // g y₁.fst = Sum.inl y₁.snd }
         ∧ Fintype.card { x₂ : Fin k × m' // f x₂.fst = Sum.inr x₂.snd }
         = Fintype.card { y₂ : Fin k × n' // g y₂.fst = Sum.inr y₂.snd }
  then -- square case
    -- equivalences between canonical indexing types of given cardinality and current indexing types
    -- (domains of parts of indexing functions)
    let e₁ := Fintype.equivOfCardEq hxy.1
    let e₂ := Fintype.equivOfCardEq hxy.2
    -- relating submatrices in blocks to submatrices of `A₁` and `A₂`
    have hAfg' :
      (Matrix.fromBlocks
        (A₁.submatrix
          ((·.val.snd) : { x₁ : Fin k × m // f x₁.fst = Sum.inl x₁.snd } → m)
          ((·.val.snd) : { y₁ : Fin k × n // g y₁.fst = Sum.inl y₁.snd } → n)
        ) 0 0
        (A₂.submatrix
          ((·.val.snd) : { x₂ : Fin k × m' // f x₂.fst = Sum.inr x₂.snd } → m')
          ((·.val.snd) : { y₂ : Fin k × n' // g y₂.fst = Sum.inr y₂.snd } → n')
        )).submatrix
          f.decomposeSum
          g.decomposeSum
      =
      (Matrix.fromBlocks
        (A₁.submatrix (·.val.snd)
          (((·.val.snd) : { y₁ : Fin k × n // g y₁.fst = Sum.inl y₁.snd } → n) ∘ e₁)
        ) 0 0
        (A₂.submatrix (·.val.snd)
          (((·.val.snd) : { y₂ : Fin k × n' // g y₂.fst = Sum.inr y₂.snd } → n') ∘ e₂)
        )).submatrix
          f.decomposeSum
          (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm)) := by
      ext
      simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply,
        Function.comp_apply, Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply]
      split
      · split
        · simp
        · rfl
      · split
        · rfl
        · simp
    -- absolute value of determinant was preserved by previous mappings,
    -- and we now express it as a product of determinants of submatrices in blocks
    rw [hAfg', in_set_range_singType_cast_iff_abs, abs_det_submatrix_equiv_equiv,
      Matrix.det_fromBlocks_zero₁₂, ← in_set_range_singType_cast_iff_abs]
    -- determinants of submatrices in blocks are `0` or `±1` by TUness of `A₁` and `A₂`
    apply in_set_range_singType_cast_mul_in_set_range_singType_cast
    · apply hA₁
    · apply hA₂
  else -- the submatrix of `A₁` or the submatrix of `A₂` is non-square
    -- actually both submatrices of `A₁` and of `A₂` are non-square
    obtain ⟨cardine₁, cardine₂⟩ :
        Fintype.card { x₁ : Fin k × m // f x₁.fst = Sum.inl x₁.snd } ≠
        Fintype.card { y₁ : Fin k × n // g y₁.fst = Sum.inl y₁.snd } ∧
        Fintype.card { x₂ : Fin k × m' // f x₂.fst = Sum.inr x₂.snd } ≠
        Fintype.card { y₂ : Fin k × n' // g y₂.fst = Sum.inr y₂.snd }
    · rw [not_and_or] at hxy
      have hk₁ := Fintype.card_fin k ▸ Fintype.card_congr f.decomposeSum
      have hk₂ := Fintype.card_fin k ▸ Fintype.card_congr g.decomposeSum
      rw [Fintype.card_sum] at hk₁ hk₂
      cases hxy <;> omega
    clear hxy
    -- goal: prove that `det` = `0`
    if hxy₁ :
        Fintype.card { x₁ : Fin k × m // f x₁.fst = Sum.inl x₁.snd } <
        Fintype.card { y₁ : Fin k × n // g y₁.fst = Sum.inl y₁.snd } then
      sorry -- the bottom half of our submatrix is singular
    else
      sorry -- the top half of our submatrix is singular

end Matrix
