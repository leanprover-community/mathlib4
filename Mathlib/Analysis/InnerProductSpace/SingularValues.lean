module

public import Mathlib

namespace LinearMap
open NNReal InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

-- This cluster of theorems should be moved to other files.
recall LinearMap.isPositive_self_comp_adjoint
recall LinearMap.isPositive_adjoint_comp_self

public theorem isSymmetric_self_comp_adjoint
  : (T ∘ₗ adjoint T).IsSymmetric := T.isPositive_self_comp_adjoint.isSymmetric

-- LinearMap.isSymmetric_adjoint_mul_self but domain and range can be different
public theorem isSymmetric_adjoint_comp_self
  : (adjoint T ∘ₗ T).IsSymmetric := T.isPositive_adjoint_comp_self.isSymmetric

public theorem eigenvalues_adjoint_comp_self_nonneg
  {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : 0 ≤ (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn i := by
  apply LinearMap.IsPositive.nonneg_eigenvalues
  exact T.isPositive_adjoint_comp_self

/--
The singular values of a finite dimensional linear map, ordered in descending order.
This definition accounts for the multiplicity of a singular value.

This definition is not public, but there are different characterizations depending on the use-case:
- `LinearMap.singularValues_fin` and `LinearMap.singularValues_of_finrank_le` for
a characterization similar in spirit to `LinearMap.IsSymmetric.eigenvalues`.

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero.
This is the approach taken in LADR 4th edition (TODO: Check if this is accurate)
- Countably infinitely many singular values, with, all but finitely many of them being zero.

We take the last approach for the following reasons:
- It avoid unnecessary dependent typing.
- You can easily convert this definition to the other three by composing with `Fin.val`, but
converting between any two of the other definitions is more inconvenient because it involves
multiple `Fin` types.
- If you prefer a definition where there are `k` singular values, you can treat the singular values
after `k` as junk values.
Not having to prove that `i < k` when getting the `i`th singular value has similar advantages to
not having to prove that `y ≠ 0` when calculating `x / y`.
- This API coincides with a potential future API for approximation numbers, which are a
generalization of singular values to continuous linear maps between possibly-infinite-dimensional
normed vector spaces.
-/
public noncomputable def singularValues : ℕ →₀ ℝ≥0 :=
  Finsupp.embDomain Fin.valEmbedding <|
    Finsupp.ofSupportFinite
      (fun i ↦ Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i))
      (Set.toFinite _)

/--
Connection between `LinearMap.singularValues` and `LinearMap.IsSymmetric.eigenvalues`.
Together with `LinearMap.singularValues_of_finrank_le`, this characterizes the singular values.

You probably need to use `LinearMap.eigenvalues_adjoint_comp_self_nonneg` to make effective use
of this.
-/
public theorem singularValues_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i


/--
`LinearMap.singularValues_fin` when combined with this characterizes the singular values.

This theorem is strictly weaker than (TODO: A theorem which states that the singular values after
rank(T) are 0).
-/
public theorem singularValues_of_finrank_le {i : ℕ}
  (hi : Module.finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  -- Unlike the `rank(T)` lemma, this should follow directly from the definition.
  -- You shouldn't have to do anything with eigenvalues, just the way the `Finsupp.embDomain` works.
  apply Finsupp.embDomain_notin_range
  simp [hi]

/- `T.singularValues i ^ 2` means `(↑(T.singularValues i)) ^ 2`, which  complies with the simp lemma
`NNReal.coe_pow`. -/

public theorem sq_singularValues_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  -- Should follow from `LinearMap.singularValues_fin` and
  -- `LinearMap.eigenvalues_adjoint_comp_self_nonneg`.
  simp [T.singularValues_fin hn i, Real.sq_sqrt (T.eigenvalues_adjoint_comp_self_nonneg hn i)]



public theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
  {n : ℕ} (hn : n < Module.finrank 𝕜 E)
  : Module.End.HasEigenvalue (adjoint T ∘ₗ T) ((T.singularValues n).toReal ^ 2) := by
  -- Can use `LinearMap.IsSymmetric.hasEigenvalue_eigenvalues`, or maybe this easily is provable
  -- from `hasEigenvector_adjoint_comp_self_rightSingularVectors`.
  sorry

public theorem singularValues_antitone : Antitone T.singularValues := by
  -- Use `LinearMap.IsSymmetric.eigenvalues_antitone`, and either
  -- a) both of `LinearMap.singularValues_fin` and `LinearMap.eigenvalues_adjoint_comp_self_nonneg`
  -- or b) `LinearMap.sq_singularValues_fin` and some order lemmas about squaring and `NNReal`
  intro i j hij
  by_cases hi : Module.finrank 𝕜 E ≤ i
  · rw [T.singularValues_of_finrank_le hi, T.singularValues_of_finrank_le (hi.trans hij)]
  by_cases hj : Module.finrank 𝕜 E ≤ j
  · simp [T.singularValues_of_finrank_le hj, zero_le _]
  push_neg at hi hj
  have : (T.singularValues j : ℝ) ^ 2 ≤ (T.singularValues i : ℝ) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j, hj⟩, T.sq_singularValues_fin rfl ⟨i, hi⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  have h1 := Real.sqrt_le_sqrt this
  simp only [Real.sqrt_sq (NNReal.coe_nonneg _)] at h1
  exact NNReal.coe_le_coe.1 h1


public theorem singularValues_lt_rank {n : ℕ}
  (hn : n < Module.finrank 𝕜 (range T)) : 0 < T.singularValues n := by
  -- I think this is one of the hard ones. Might want to hold off on it until the theory of left
  -- and right singular vectors has been developed.
  sorry

-- It's unclear what the right way to state "The rank of T, as a natural number" is,
-- I went with this approach simply because it appeared more times in Loogle, but maybe
-- `Cardinal.toNat T.rank` is better.
public theorem singularValues_rank
  : T.singularValues (Module.finrank 𝕜 (range T)) = 0 := by
  -- I think this is one of the hard ones. Might want to hold off on it until the theory of left
  -- and right singular vectors has been developed.
  sorry

public theorem singularValues_le_rank {n : ℕ}
  (hn : Module.finrank 𝕜 (range T) ≤ n) : T.singularValues n = 0 :=
  -- This should follow directly from `LinearMap.singularValues_rank`,
  -- `LinearMap.singularValues_antitone`, and order properties of `ℝ≥0`.
  le_antisymm (T.singularValues_rank ▸ T.singularValues_antitone hn) (zero_le _)

@[simp]
public theorem support_singularValues
  : T.singularValues.support = Finset.range (Module.finrank 𝕜 (range T)) := by
  -- Follows from `singularValues_lt_rank` and `singularValues_le_rank`.
  ext n
  simp only [Finsupp.mem_support_iff, Finset.mem_range, ne_eq]
  constructor
  · intro hn
    by_contra h
    push_neg at h
    exact hn (T.singularValues_le_rank h)
  · intro hn
    exact (T.singularValues_lt_rank hn).ne'

public noncomputable def rightSingularVectors : ℕ →₀ E :=
  Finsupp.embDomain Fin.valEmbedding <|
    Finsupp.ofSupportFinite
      (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
      (Set.toFinite _)

public noncomputable def leftSingularVectors : ℕ →₀ F :=
  (adjoint T).rightSingularVectors

@[simp]
public theorem rightSingularVectors_adjoint
  : (adjoint T).rightSingularVectors = T.leftSingularVectors := (rfl)

@[simp]
public theorem leftSingularVectors_adjoint
  : (adjoint T).leftSingularVectors = T.rightSingularVectors := by simp [leftSingularVectors]

public theorem rightSingularVectors_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.rightSingularVectors i = T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn i := sorry

public theorem leftSingularVectors_fin {n : ℕ} (hn : Module.finrank 𝕜 F = n) (i : Fin n)
  : T.leftSingularVectors i = T.isSymmetric_self_comp_adjoint.eigenvectorBasis hn i := by
  simpa using (adjoint T).rightSingularVectors_fin hn i

public theorem rightSingularVectors_of_finrank_le {i : ℕ} (hi : Module.finrank 𝕜 E ≤ i)
  : T.rightSingularVectors i = 0 := sorry

public theorem leftSingularVectors_of_finrank_le {i : ℕ} (hi : Module.finrank 𝕜 F ≤ i)
  : T.leftSingularVectors i = 0 := by
  -- As seen in `leftSingularVectors_fin`, the proofs of the corresponding left singular vector
  -- lemmas should be very short (usually one-liners) following directly from the corresponding
  -- right singular vector lemma.
  sorry

@[simp]
public theorem support_rightSingularVectors
  : T.rightSingularVectors.support = Finset.range (Module.finrank 𝕜 E) := sorry

@[simp]
public theorem support_leftSingularVectors
  : T.leftSingularVectors.support = Finset.range (Module.finrank 𝕜 F) := sorry

public theorem hasEigenvector_adjoint_comp_self_rightSingularVectors
  {i : ℕ} (hi : i < Module.finrank 𝕜 E)
  : Module.End.HasEigenvector (adjoint T ∘ₗ T) ((T.singularValues i).toReal ^ 2)
    (T.rightSingularVectors i) := by
  -- Prove from `LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis`
  sorry

public theorem hasEigenvector_self_comp_adjoint_leftSingularVectors
  {i : ℕ} (hi : i < Module.finrank 𝕜 F)
  : Module.End.HasEigenvector (T ∘ₗ adjoint T) ((T.singularValues i).toReal ^ 2)
    (T.leftSingularVectors i) := by
  sorry

public theorem orthonormal_rightSingularVectors_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n)
  : Orthonormal 𝕜 (fun i : Fin n ↦ T.rightSingularVectors i) := by
  -- Need to somehow use the fact that the `eigenvectorBasis` is an `OrthonormalBasis`.
  sorry

public theorem orthonormal_leftSingularVectors_fin {n : ℕ} (hn : Module.finrank 𝕜 F = n)
  : Orthonormal 𝕜 (fun i : Fin n ↦ T.leftSingularVectors i) := by
  sorry

/--
The infinite sequence of right singular vectors is orthogonal.

The first `dim(E)` right singular vectors are also unit vectors and thus orthonormal: see
`orthonormal_rightSingularVectors_fin`

TODO: Not sure if the name `orthogonal_rightSingularVectors` is better.
-/
public theorem pairwise_inner_rightSingularVectors_eq_zero
  : Pairwise fun (i j : ℕ) ↦ ⟪T.rightSingularVectors i, T.rightSingularVectors j⟫_𝕜 = 0 := sorry

public theorem pairwise_inner_leftSingularVectors_eq_zero
  : Pairwise fun (i j : ℕ) ↦ ⟪T.leftSingularVectors i, T.leftSingularVectors j⟫_𝕜 = 0 := sorry

/--
Equation 7.73 in LADR 4th edition.

TODO: Is this actually true, given our definition of leftSingularVectors?
-/
public theorem apply_rightSingularVectors {i : ℕ} (hi : i < Module.finrank 𝕜 (range T))
  : T (T.rightSingularVectors i) =
    ((T.singularValues i).toReal : 𝕜) • T.leftSingularVectors i := sorry

/-
These are lemmas that don't necessarily fit into any category, but need to be established
eventually. They will need to be moved around later.
-/

@[simp]
public theorem singularValues_zero (i : ℕ) : (0 : E →ₗ[𝕜] F).singularValues i = 0 := by
  -- Might be able to prove this from `singularValues_smul`.
  sorry

/--
Use `LinearMap.singularValues_of_finrank_le` for the rest of the characterization of the singular
values of the identity map.

TODO: Not sure if should be phrased in terms of `1` or `id` or `LinearEquiv.refl`.
-/
public theorem singularValues_one_of_lt_finrank {i : ℕ} (hi : i < Module.finrank 𝕜 E)
  : (1 : E →ₗ[𝕜] E).singularValues i = 1 := sorry

@[simp]
public theorem singularValues_smul (c : 𝕜) (i : ℕ)
  : (c • T).singularValues i = ‖c‖ * T.singularValues i := by
  -- This one might require some facts about complex numbers
  sorry

-- We might need one which states that the first singular value equals the operator norm.

end LinearMap
