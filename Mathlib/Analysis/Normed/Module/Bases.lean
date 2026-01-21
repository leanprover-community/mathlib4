/-
Copyright (c) 2023 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Tactic

@[expose] public section

noncomputable section

open Filter Topology LinearMap Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A Schauder basis is a sequence (e n) of vectors in X such that there exists a sequence of
    continuous linear functionals (f n) (the coordinate functionals) satisfying:
    1) f i (e j) = δ_{ij} (the Kronecker delta)
    2) for every x : X, the series ∑_{n=0}^∞ f n (x) e n converges to x.

    In other words, every vector in X can be uniquely represented as a convergent series of basis
    vectors, with coefficients given by the coordinate functionals. -/
structure SchauderBasis (𝕜 : Type*) (X : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] (e : ℕ → X) where
  coord : ℕ → StrongDual 𝕜 X
  -- Biorthogonality
  ortho : ∀ i j, coord i (e j) = if i = j then 1 else 0
  -- Convergence of partial sums (Standard Schauder Basis definition)
  basis_expansion : ∀ x : X, Tendsto (fun n ↦ ∑ i ∈ Finset.range n, coord i x • e i)
    atTop (𝓝 x)

namespace SchauderBasis

variable {e : ℕ → X} (b : SchauderBasis 𝕜 X e)

/-- The basis vectors are linearly independent. -/
theorem linearIndependent (h : SchauderBasis 𝕜 X e) : LinearIndependent 𝕜 e := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have hsum : ∑ i ∈ l.support, l i • e i = 0 := hl
  -- Apply the i-th coordinate functional to the linear combination
  have h_app : h.coord i (∑ j ∈ l.support, l j • e j) = 0 := by rw [hsum, map_zero]
  rw [map_sum] at h_app
  -- The sum collapses to just the i-th term
  simp_rw [ContinuousLinearMap.map_smul] at h_app
  rw [Finset.sum_eq_single i, h.ortho i i] at h_app
  · simpa using h_app
  · intro j _ hji; rw [h.ortho i j, if_neg hji.symm]; simp
  · intro hi; simp [Finsupp.notMem_support_iff.mp hi]

/-- A canonical projection P_n associated to a Schauder basis given by coordinate functionals f_i:
    P_n x = ∑_{i < n} f_i(x) e_i -/
def proj (n : ℕ) : X →L[𝕜] X :=
  ∑ i ∈ Finset.range n, (b.coord i).smulRight (e i)

/-- The action of the canonical projection on a vector x. -/
theorem proj_apply (n : ℕ) (x : X) :
    b.proj n x = ∑ i ∈ Finset.range n, b.coord i x • e i := by
  simp [proj, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]

/-- The action of the canonical projection on a basis element e i. -/
@[simp]
theorem proj_basis_element (n i : ℕ) :
  b.proj n (e i) = if i < n then e i else 0 := by
    rw [proj_apply]
    by_cases hin : i < n
    · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin)]
      · simp [b.ortho, if_pos hin]
      · intro j _ hji; rw [b.ortho j i, if_neg hji, zero_smul]
    rw [if_neg hin, Finset.sum_eq_zero]
    intro j hj
    push_neg at hin
    rw [b.ortho j i, if_neg, zero_smul]
    exact (Finset.mem_range.mp hj).trans_le hin |>.ne

/-- The range of the canonical projection is the span of the first n basis elements. -/
theorem range_canonicalProjection (n : ℕ) :
    LinearMap.range (b.proj n) =
        Submodule.span 𝕜 (Set.range (fun i : Fin n => e i)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [proj_apply b]
    apply Submodule.sum_mem
    intros i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    use e i
    rw [proj_basis_element b]
    rw [if_pos i.is_lt]

/-- The dimension of the range of the canonical projection P n is n. -/
theorem dim_of_range (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (b.proj n)) = n := by
  rw [range_canonicalProjection]
  -- The dimension of the span of linearly independent vectors is the cardinality of the set
  rw [finrank_span_eq_card]
  · exact Fintype.card_fin n
  · -- The subfamily is linearly independent because the whole family is
    exact b.linearIndependent.comp (fun (i : Fin n) => (i : ℕ)) Fin.val_injective


/-- The canonical projections converge pointwise to the identity map. -/
theorem proj_tendsto_id (x : X) : Tendsto (fun n ↦ b.proj n x) atTop (𝓝 x) := by
  simp_rw [proj_apply]
  exact b.basis_expansion x

/-- The canonical projections are uniformly bounded (Banach-Steinhaus). -/
theorem uniform_bound [CompleteSpace X] :  ∃ C : ℝ, ∀ n : ℕ, ‖b.proj n‖ ≤ C := by
  apply banach_steinhaus
  intro x
  let f: ℕ → X := fun n => b.proj n x
  have : ∃ M : ℝ, ∀ x ∈ Set.range f, ‖x‖ ≤ M :=
      isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ (proj_tendsto_id b x ))
  rcases this with ⟨M, hM⟩
  rw [Set.forall_mem_range] at hM
  use M

/-- The basis constant is the infimum of the bounds on the canonical projections. -/
def basis_constant : ℝ := sInf { C : ℝ | ∀ n : ℕ, ‖b.proj n‖ ≤ C }

/-- Q_n = P_{n+1} - P_n. -/
def Q (P : ℕ → X →L[𝕜] X) (n : ℕ) : X →L[𝕜] X := P (n + 1) - P n

@[simp]
lemma Q_sum (P : ℕ → X →L[𝕜] X) (h0 : P 0 = 0) (n : ℕ) :
    ∑ i ∈ Finset.range n, Q P i = P n := by
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Finset.sum_range_succ, ih, Q]; abel

lemma Q_ortho {P : ℕ → X →L[𝕜] X} (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
  (i j : ℕ) (x : X) : (Q P i) (Q P j x) = if i = j then Q P j x else 0 := by
  simp only [Q, ContinuousLinearMap.sub_apply, map_sub, hcomp, Nat.add_min_add_right]
  split_ifs with h
  · rw [h, min_self, min_eq_right (Nat.le_succ j), Nat.min_eq_left (Nat.le_succ j)]
    abel
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · rw [min_eq_left_of_lt h', min_eq_left (Nat.succ_le_of_lt h'),
        min_eq_left_of_lt (Nat.lt_succ_of_lt h')]
      abel
    · rw [min_eq_right_of_lt h', min_eq_right (Nat.succ_le_of_lt h'),
        min_eq_right_of_lt (Nat.lt_succ_of_lt h')]
      abel

/-- The rank of Q n is 1, given appropriate properties of P. -/
lemma Q_rank_one {P : ℕ → X →L[𝕜] X}
    (h_rank : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n)) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)  (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (Q P n)) = 1 := by
  let Q := Q P
  let U := LinearMap.range (Q n)
  let V := LinearMap.range (P n)
  have h_range_Pn_succ : LinearMap.range (P (n + 1)) = U ⊔ V := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; rw [← sub_add_cancel (P (n + 1) y) (P n y)]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
    · rw [sup_le_iff]; constructor
      · rintro x ⟨y, rfl⟩; exact Submodule.sub_mem _ (LinearMap.mem_range_self _ _)
          -- (by rw [h_comp]; use y; simp)
          sorry
      -- · rintro x ⟨y, rfl⟩; rw [← h_comp n (n+1)]; exact LinearMap.mem_range_self _ _
      · sorry
  have h_disjoint : U ⊓ V = ⊥ := by
    rw [Submodule.eq_bot_iff]; rintro x ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
    -- have : Q P n (P n z) = 0 := by simp [Q, h_comm, Nat.min_succ_self, min_self]
    have : Q n (P n z) = 0 := by sorry
    rw [← hz, ← this, hz, Q_ortho hcomp, if_pos rfl]

  -- have h_fin_Pn : ∀ n, FiniteDimensional 𝕜 (LinearMap.range (P n)) := by
  --     intro n
  --     apply FiniteDimensional.of_finrank_pos
  --     rw [hdim n]
  --     exact Nat.succ_pos n
  -- have : FiniteDimensional 𝕜 V := by simp only [V]; exact h_fin_Pn (n-1)
  have : FiniteDimensional 𝕜 U := by sorry
  have : FiniteDimensional 𝕜 V := by sorry
  have := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [h_disjoint, finrank_bot, add_zero, ← h_range_Pn_succ, h_rank, h_rank] at this
  rw [Nat.add_comm] at this
  exact Nat.add_right_cancel this.symm

/-- Constructs a Schauder basis from a sequence of canonical projections
    satisfying appropriate properties. -/
theorem basis_of_canonical_projections {P : ℕ → X →L[𝕜] X}
    (h0 : P 0 = 0)
    (hdim : ∀ n, Module.finrank 𝕜 (LinearMap.range (P n)) = n)
    (hcomp : ∀ n m, ∀ x : X, P n (P m x) = P (min n m) x)
    (hlim : ∀ x, Tendsto (fun n ↦ P n x) atTop (𝓝 x)) :
    ∃ e : ℕ → X, Nonempty (SchauderBasis 𝕜 X e) := by
  let Q := Q P
  have hrankQ := Q_rank_one hdim hcomp
  have : ∀ n, ∃ v, v ∈ LinearMap.range (Q n) ∧ v ≠ 0 := by
      intro n
      refine exists_mem_ne_zero_of_rank_pos ?_
      apply Module.lt_rank_of_lt_finrank
      rw [hrankQ n]
      exact Nat.zero_lt_one
  choose e he_in_range he_ne using this
  have h_range_eq_span : ∀ n, LinearMap.range (Q n) = Submodule.span 𝕜 {e n} := by
    intro n
    symm
    have : FiniteDimensional 𝕜 ↥(LinearMap.range (Q n)) := by
      apply FiniteDimensional.of_finrank_pos
      rw [hrankQ n]
      exact Nat.succ_pos 0
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact he_in_range n
    · rw [hrankQ n, finrank_span_singleton (he_ne n)]
  let f_fun : ℕ → X → 𝕜 := fun n x =>
    Classical.choose (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n) x))
  have hQf : ∀ n x, Q n x = f_fun n x • e n := fun n x =>
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (by
      rw [← h_range_eq_span]
      exact LinearMap.mem_range_self (Q n) x))).symm
  let f (n : ℕ) : StrongDual 𝕜 X := LinearMap.mkContinuous (IsLinearMap.mk' (f_fun n) (by
    constructor
    · intro x y; apply smul_left_injective 𝕜 (he_ne n); dsimp only [smul_eq_mul];
      rw [← hQf, map_add, add_smul, hQf, hQf]
    · intro c x; apply smul_left_injective 𝕜 (he_ne n);dsimp  only [smul_eq_mul];
      rw [← hQf, map_smul, mul_smul, hQf]
    )) (‖Q n‖ / ‖e n‖) (by
      intro x; rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (he_ne n))]
      calc ‖f_fun n x‖ * ‖e n‖ = ‖f_fun n x • e n‖ := (norm_smul _ _).symm
        _ = ‖Q n x‖ := by rw [hQf]
        _ ≤ ‖Q n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _)
  have ortho : ∀ i j, f i (e j) = if i = j then 1 else 0 := by
    intro i j
    apply smul_left_injective 𝕜 (he_ne i)
    dsimp only [smul_eq_mul]
    simp only [mkContinuous_apply, IsLinearMap.mk'_apply, ite_smul, one_smul, zero_smul, f]
    have : Q i (e j) = if i = j then e j else 0 := by
      obtain ⟨x, hx⟩ := he_in_range j
      rw [← hx, Q_ortho hcomp i j x]
    rw [← hQf, this]
    split_ifs with hij
    · subst hij; simp
    · simp
  have lim : ∀ x, Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i x • e i) atTop (𝓝 x) := by
    intro x
    apply Tendsto.congr _ (hlim x)
    intro n
    simp_rw [f]
    dsimp only [mkContinuous_apply, IsLinearMap.mk'_apply]
    simp_rw [← hQf, Q]
    simp only [← Q_sum P h0 n, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  use e
  exact ⟨SchauderBasis.mk f ortho lim⟩

end SchauderBasis
