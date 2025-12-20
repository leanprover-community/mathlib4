module

public import Mathlib

open NNReal

recall LinearMap.isPositive_adjoint_comp_self

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

-- LinearMap.isSymmetric_adjoint_mul_self but domain and range can be different
public theorem LinearMap.isSymmetric_adjoint_comp_self
  (T : E →ₗ[𝕜] F)
  : (adjoint T ∘ₗ T).IsSymmetric := T.isPositive_adjoint_comp_self.isSymmetric

public theorem LinearMap.eigenvalues_adjoint_comp_self_nonneg
  (T : E →ₗ[𝕜] F)
  {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : 0 ≤ (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn i := by
  apply LinearMap.IsPositive.nonneg_eigenvalues
  exact T.isPositive_adjoint_comp_self

-- TODO: prove from the fact that the set of nonzero eigenvectors forms a basis for T
noncomputable def LinearMap.IsSymmetric.defa
  {T : E →ₗ[𝕜] E} (h : T.IsSymmetric)
  {n : ℕ} (hn : Module.finrank 𝕜 E = n)
  : OrthonormalBasis {i : Fin n // h.eigenvalues hn i ≠ 0} 𝕜 (LinearMap.range T)
  := sorry
  --:= OrthonormalBasis.mk (v := h.eigenvectorBasis hn) sorry sorry

theorem LinearMap.adjoint_comp_self_eq_id_iff_isometry
  (T : E →ₗ[𝕜] F)
  : adjoint T ∘ₗ T = LinearMap.id ↔ Isometry T := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  sorry

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
public noncomputable def LinearMap.singularValues (T : E →ₗ[𝕜] F) : ℕ →₀ ℝ≥0 :=
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
public theorem LinearMap.singularValues_fin (T : E →ₗ[𝕜] F) {n : ℕ}
  (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  sorry

/--
`LinearMap.singularValues_fin` when combined with this characterizes the singular values.

This theorem is strictly weaker than (TODO: A theorem which states that the singular values after
rank(T) are 0).
-/
public theorem LinearMap.singularValues_of_finrank_le (T : E →ₗ[𝕜] F) {i : ℕ}
  (hi : Module.finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  -- Unlike the `rank(T)` lemma, this should follow directly from the definition.
  -- You shouldn't have to do anything with eigenvalues, just the way the `Finsupp.embDomain` works.
  sorry

/- `T.singularValues i ^ 2` means `(↑(T.singularValues i)) ^ 2`, which  complies with the simp lemma
`NNReal.coe_pow`. -/
public theorem LinearMap.sq_singularValues_fin (T : E →ₗ[𝕜] F) {n : ℕ}
  (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  -- Should follow from `LinearMap.singularValues_fin` and
  -- `LinearMap.eigenvalues_adjoint_comp_self_nonneg`.
  sorry

public theorem LinearMap.singularValues_antitone (T : E →ₗ[𝕜] F) : Antitone T.singularValues := by
  -- Use `LinearMap.IsSymmetric.eigenvalues_antitone`, and either
  -- a) both of `LinearMap.singularValues_fin` and `LinearMap.eigenvalues_adjoint_comp_self_nonneg`
  -- or b) `LinearMap.sq_singularValues_fin` and some order lemmas about squaring and `NNReal`
  sorry

public theorem LinearMap.singularValues_lt_rank (T : E →ₗ[𝕜] F) {n : ℕ}
  (hn : n < Module.finrank 𝕜 (LinearMap.range T)) : 0 < T.singularValues n := by
  -- I think this is one of the hard ones
  sorry

-- It's unclear what the right way to state "The rank of T, as a natural number" is,
-- I went with this approach simply because it appeared more times in Loogle, but maybe
-- `Cardinal.toNat T.rank` is better.
public theorem LinearMap.singularValues_rank (T : E →ₗ[𝕜] F)
  : T.singularValues (Module.finrank 𝕜 (LinearMap.range T)) = 0 := by
  -- I think this is one of the hard ones
  sorry

public theorem LinearMap.singularValues_le_rank (T : E →ₗ[𝕜] F) {n : ℕ}
  (hn : Module.finrank 𝕜 (LinearMap.range T) ≤ n) : T.singularValues n = 0 := by
  -- This should follow directly from `LinearMap.singularValues_rank`,
  -- `LinearMap.singularValues_antitone`, and order properties of `ℝ≥0`.
  sorry
