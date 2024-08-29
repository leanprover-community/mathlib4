import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Combinatorics.Hall.Basic

/-!
# Doubly stochastic matrices and Birkhoff's theorem

## Main definitions

* `doublyStochastic`

## Main statements

* `doublyStochastic_eq_convexHull_perm`

## Tags

Doubly stochastic, Birkhoff's theorem, Birkhoff-von Neumann theorem
-/

variable {n R : Type*} [Fintype n]

open Matrix BigOperators

/--
A square matrix is doubly stochastic if all entries are nonnegative, all column sums are 1, and
all row sums are 1.
-/
def doublyStochastic (n : Type*) [Fintype n] :
    Set (Matrix n n ℝ) :=
  {M : Matrix n n ℝ | (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1}

lemma mem_doublyStochastic {M : Matrix n n ℝ} :
    M ∈ doublyStochastic n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1 := by
  rfl

/--
A square matrix is doubly stochastic iff all entries are nonnegative, and left or right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
lemma mem_doublyStochastic_iff_mul {M : Matrix n n ℝ} :
    M ∈ doublyStochastic n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 ∧ 1 ᵥ* M = 1 := by
  simp [Function.funext_iff, mem_doublyStochastic, mulVec, vecMul, dotProduct]

lemma prod_doublyStochastic {M N : Matrix n n ℝ}
    (hM : M ∈ doublyStochastic n) (hN : N ∈ doublyStochastic n) :
    M * N ∈ doublyStochastic n := by
  rw [mem_doublyStochastic_iff_mul] at hM hN ⊢
  refine ⟨fun i j => ?_, ?_, ?_⟩
  next =>
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _)
  next => rw [←mulVec_mulVec, hN.2.1, hM.2.1]
  next => rw [←vecMul_vecMul, hM.2.2, hN.2.2]

lemma nonneg_doublyStochastic {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic n)
    (i j : n) : 0 ≤ M i j :=
  (mem_doublyStochastic.1 hM).1 _ _

lemma row_sum_doublyStochastic {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic n)
    (i : n) : ∑ j, M i j = 1 :=
  (mem_doublyStochastic.1 hM).2.1 _

lemma col_sum_doublyStochastic {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic n)
    (j : n) : ∑ i, M i j = 1 :=
  (mem_doublyStochastic.1 hM).2.2 _

lemma one_mem_doublyStochastic [DecidableEq n] : 1 ∈ doublyStochastic n := by
  simp [mem_doublyStochastic_iff_mul, zero_le_one_elem]

lemma doublyStochastic_nonempty [DecidableEq n] : (doublyStochastic n).Nonempty :=
  ⟨_, one_mem_doublyStochastic⟩

lemma doublyStochastic_le_one {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic n) {i j : n} :
    M i j ≤ 1 := by
  rw [←hM.2.1 (i := i)]
  exact Finset.single_le_sum (fun k _ => hM.1 _ k) (Finset.mem_univ j)

lemma convex_doublyStochastic : Convex ℝ (doublyStochastic n) := by
  intro x hx y hy a b ha hb h
  simp only [mem_doublyStochastic, add_apply, smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ←Finset.sum_mul, ←Finset.mul_sum, row_sum_doublyStochastic, hx, hy,
    col_sum_doublyStochastic, h, mul_one, implies_true, and_self, and_true]
  intro i j
  have := nonneg_doublyStochastic hx i j
  have := nonneg_doublyStochastic hy i j
  positivity

lemma permMatrix_doublyStochastic [DecidableEq n] {σ : Equiv.Perm n} :
    σ.permMatrix ℝ ∈ doublyStochastic n := by
  refine ⟨fun i j => ?g1, ?g2, ?g3⟩
  case g1 => aesop
  case g2 =>
    intro i
    simp only [PEquiv.toMatrix_apply, Nat.cast_eq_one, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  case g3 =>
    intro j
    simp only [PEquiv.toMatrix_apply, Nat.cast_eq_one, Option.mem_def, Equiv.toPEquiv_apply,
      Option.some.injEq, ←Equiv.eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma scalar_multiple_of_doublyStochastic_iff {M : Matrix n n ℝ} {s : ℝ} (hs : 0 ≤ s) :
    (∃ M' ∈ doublyStochastic n, M = s • M') ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = s) ∧ (∀ j, ∑ i, M i j = s) := by
  classical
  constructor
  case mp =>
    rintro ⟨M', hM', rfl⟩
    rw [mem_doublyStochastic] at hM'
    simp only [smul_apply, smul_eq_mul, ←Finset.mul_sum]
    exact ⟨fun i j => mul_nonneg hs (hM'.1 _ _), by simp [hM']⟩
  rcases eq_or_lt_of_le hs with rfl | hs
  case inl =>
    simp only [zero_smul, exists_and_right, and_imp]
    intro h₁ h₂ _
    refine ⟨doublyStochastic_nonempty, ?_⟩
    ext i j
    specialize h₂ i
    rw [Finset.sum_eq_zero_iff_of_nonneg (by simp [h₁ i])] at h₂
    rw [Pi.zero_apply, Pi.zero_apply, h₂ _ (by simp)]
  rintro ⟨hM₁, hM₂, hM₃⟩
  refine ⟨s⁻¹ • M, ?_, by simp [hs.ne']⟩
  rw [mem_doublyStochastic]
  simp only [smul_apply, smul_eq_mul, ←Finset.mul_sum, hM₂, hM₃, inv_mul_cancel₀ hs.ne',
    implies_true, and_self, and_true]
  intro i j
  exact mul_nonneg (by simp [hs.le]) (hM₁ _ _)

lemma doublyStochastic_sum_perm''' [DecidableEq n] [Nonempty n] {M : Matrix n n ℝ}
    {s : ℝ} (hs : 0 < s)
    (hM : ∃ M' ∈ doublyStochastic n, M = s • M') :
    ∃ σ : Equiv.Perm n, ∀ i j, M i j = 0 → σ.permMatrix ℝ i j = 0 := by
  rw [scalar_multiple_of_doublyStochastic_iff hs.le] at hM
  let f (i : n) : Finset n := Finset.univ.filter (M i · ≠ 0)
  have hf : ∀ (A : Finset n), A.card ≤ (A.biUnion f).card := by
    intro A
    have : ∀ i, ∑ j ∈ f i, M i j = s := by
      intro i
      simp only [f]
      rw [Finset.sum_subset (Finset.filter_subset _ _), hM.2.1]
      simp
    have h₁ : ∑ i ∈ A, ∑ j ∈ f i, M i j = A.card * s := by simp [this]
    have h₂ : ∑ i, ∑ j ∈ A.biUnion f, M i j = (A.biUnion f).card * s := by
      rw [Finset.sum_comm]
      simp only [hM.2.2, Finset.sum_const, nsmul_eq_mul, mul_comm s]
    suffices A.card * s ≤ (A.biUnion f).card * s by
      exact_mod_cast le_of_mul_le_mul_right this hs
    rw [←h₁, ←h₂]
    trans ∑ i ∈ A, ∑ j ∈ A.biUnion f, M i j
    · refine Finset.sum_le_sum ?_
      intro i hi
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem f hi) ?_
      simp [hM]
    · refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
      intro i _ _
      exact Finset.sum_nonneg fun j _ => hM.1 _ _
  obtain ⟨g, hg, hg'⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective f).1 hf
  rw [Finite.injective_iff_bijective] at hg
  refine ⟨Equiv.ofBijective g hg, ?_⟩
  intro i j hij
  simp only [PEquiv.toMatrix_apply, Option.mem_def, ite_eq_right_iff, one_ne_zero, imp_false,
    Equiv.toPEquiv_apply, Equiv.ofBijective_apply, Option.some.injEq]
  rintro rfl
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, f] at hg'
  exact hg' _ hij

/--
If M is a scalar multiple of a doubly stochastic matrix, then it is an conical combination of
permutation matrices. This is most useful when M is a doubly stochastic matrix, in which case
the combination is convex.
-/
lemma doublyStochastic_sum_perm'' [DecidableEq n] (M : Matrix n n ℝ)
    (s : ℝ) (hs : 0 ≤ s)
    (hM : ∃ M' ∈ doublyStochastic n, M = s • M') :
    ∃ (w : Equiv.Perm n → ℝ), (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ • σ.permMatrix ℝ = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨1, by simp, Subsingleton.elim _ _⟩
  set d : ℕ := (Finset.univ.filter fun i : n × n => M i.1 i.2 ≠ 0).card with ←hd
  clear_value d
  induction d using Nat.strongInductionOn generalizing M s
  case ind d ih =>
  rcases eq_or_lt_of_le hs with rfl | hs'
  case inl =>
    simp only [zero_smul, exists_and_right] at hM
    simp only [hM]
    exact ⟨0, by simp⟩
  obtain ⟨σ, hσ⟩ := doublyStochastic_sum_perm''' hs' hM
  have : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty
  obtain ⟨i, hi, hi'⟩ := Finset.exists_min_image _ (fun i => M i (σ i)) Finset.univ_nonempty
  rw [scalar_multiple_of_doublyStochastic_iff hs] at hM
  let N := M - M i (σ i) • σ.permMatrix ℝ
  let d' : ℕ := (Finset.univ.filter fun i : n × n => N i.1 i.2 ≠ 0).card
  have hMi : 0 ≤ M i (σ i) := by
    exact hM.1 _ _
  have hMi' : 0 < M i (σ i) := by
    refine lt_of_le_of_ne' hMi ?_
    intro h
    have := hσ _ _ h
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, ↓reduceIte,
      one_ne_zero] at this
  let s' : ℝ := s - M i (σ i)
  have hs' : 0 ≤ s' := by
    simp only [s', sub_nonneg, ←hM.2.1 i]
    exact Finset.single_le_sum (fun j _ => hM.1 i j) (by simp)
  have : ∃ M' ∈ doublyStochastic n, N = s' • M' := by
    rw [scalar_multiple_of_doublyStochastic_iff hs']
    simp only [sub_apply, smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, sub_nonneg,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, N]
    refine ⟨?_, by simp [hM.2.1], by simp [←σ.eq_symm_apply, hM]⟩
    intro i' j
    split
    case isTrue h =>
      cases h
      exact hi' _ (by simp)
    case isFalse h => exact hM.1 _ _
  have hd' : d' < d := by
    rw [←hd]
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ _)]
    · simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Decidable.not_not,
        Prod.exists]
      refine ⟨i, σ i, hMi'.ne', ?_⟩
      simp [N, Equiv.toPEquiv_apply]
    · rintro ⟨i', j'⟩ hN' hM'
      dsimp at hN' hM'
      simp only [sub_apply, hM', smul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero, zero_sub,
        neg_eq_zero, ite_eq_right_iff, Classical.not_imp, N] at hN'
      obtain ⟨rfl, _⟩ := hN'
      have := hi' i' (by simp)
      linarith
  obtain ⟨w, hw, hw'⟩ := ih _ hd' _ s' hs' this rfl
  refine ⟨w + fun σ' => if σ' = σ then M i (σ i) else 0, ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hw', ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, N, sub_add_cancel, and_true]
  intro σ'
  split
  case isTrue => exact add_nonneg (hw _) hMi
  case isFalse => simp [hw]

lemma doublyStochastic_sum_perm [DecidableEq n] {M : Matrix n n ℝ} (hM : M ∈ doublyStochastic n) :
    ∃ (w : Equiv.Perm n → ℝ), (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧ ∑ σ, w σ • σ.permMatrix ℝ = M := by
  rcases isEmpty_or_nonempty n
  case inl => exact ⟨fun _ => 1, by simp, by simp, Subsingleton.elim _ _⟩
  obtain ⟨w, hw1, hw3⟩ := doublyStochastic_sum_perm'' M 1 (by simp) ⟨M, hM, by simp⟩
  refine ⟨w, hw1, ?_, hw3⟩
  inhabit n
  have : ∑ j, ∑ σ : Equiv.Perm n, w σ • Equiv.Perm.permMatrix ℝ σ default j = 1 := by
    simp only [←smul_apply (m := n), ←Finset.sum_apply, hw3]
    rw [row_sum_doublyStochastic hM]
  simp only [PEquiv.toMatrix_apply, Option.mem_def, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Equiv.toPEquiv_apply, Option.some.injEq, Finset.sum_comm (γ := n), Finset.sum_ite_eq,
    Finset.mem_univ] at this
  exact this

/-- The set of doubly stochastic matrices is the convex hull of the permutation matrices. -/
theorem doublyStochastic_eq_convexHull_perm [DecidableEq n] :
    doublyStochastic n = convexHull ℝ {σ.permMatrix ℝ | σ : Equiv.Perm n} := by
  refine (convexHull_min ?g1 convex_doublyStochastic).antisymm' ?g2
  case g1 =>
    rintro x ⟨h, rfl⟩
    exact permMatrix_doublyStochastic
  case g2 =>
    intro M hM
    rcases isEmpty_or_nonempty n
    case inl => simp [Unique.exists_iff, Subsingleton.elim M ((Equiv.Perm.permMatrix ℝ 1))]
    obtain ⟨w, hw1, hw2, hw3⟩ := doublyStochastic_sum_perm hM
    exact mem_convexHull_of_exists_fintype w (·.permMatrix ℝ) hw1 hw2 (by simp) hw3
