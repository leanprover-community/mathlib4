module

public import Mathlib

open NNReal

recall LinearMap.isPositive_adjoint_comp_self

-- LinearMap.isSymmetric_adjoint_mul_self but domain and range can be different
theorem LinearMap.isSymmetric_adjoint_comp_self {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (T : E →ₗ[𝕜] F) [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  : (adjoint T ∘ₗ T).IsSymmetric := T.isPositive_adjoint_comp_self.isSymmetric

theorem LinearMap.eigenvalues_adjoint_comp_self_nonneg {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (T : E →ₗ[𝕜] F) [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : 0 ≤ (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn i := by
  apply LinearMap.IsPositive.nonneg_eigenvalues
  exact T.isPositive_adjoint_comp_self

-- TODO: prove from the fact that the set of nonzero eigenvectors forms a basis for T
noncomputable def LinearMap.IsSymmetric.defa {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {T : E →ₗ[𝕜] E} [FiniteDimensional 𝕜 E] (h : T.IsSymmetric)
  {n : ℕ} (hn : Module.finrank 𝕜 E = n)
  : OrthonormalBasis {i : Fin n // h.eigenvalues hn i ≠ 0} 𝕜 (LinearMap.range T)
  := sorry
  --:= OrthonormalBasis.mk (v := h.eigenvectorBasis hn) sorry sorry

theorem LinearMap.adjoint_comp_self_eq_id_iff_isometry {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  (T : E →ₗ[𝕜] F) [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  : adjoint T ∘ₗ T = LinearMap.id ↔ Isometry T := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  sorry

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/--
The singular values of a finite dimensional linear map, ordered in descending order.
Singular values may appear multiple times in this list.

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
