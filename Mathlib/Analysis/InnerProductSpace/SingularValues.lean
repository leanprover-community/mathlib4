module

public import Mathlib

/-!
# Singular values for finite-dimensional linear maps

This file defines the singular values for finite-dimensional linear maps (but not the singular
value decomposition). It is set up in a way that allows for generalization to continuous linear maps
between possibly-infinite-dimensional normed vector spaces; please see the docstring of
`LinearMap.singularValues`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
-/

open NNReal

namespace LinearMap
open InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

-- TODO: I might have a more elementary proof somewhere of this
public theorem isSymmetric_self_comp_adjoint :
    (T ∘ₗ adjoint T).IsSymmetric := T.isPositive_self_comp_adjoint.isSymmetric

-- LinearMap.isSymmetric_adjoint_mul_self but domain and range can be different
public theorem isSymmetric_adjoint_comp_self
  : (adjoint T ∘ₗ T).IsSymmetric := T.isPositive_adjoint_comp_self.isSymmetric

-- TODO: Rewrite statement using one of the above
public theorem eigenvalues_adjoint_comp_self_nonneg
  {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : 0 ≤ (LinearMap.isPositive_adjoint_comp_self T).isSymmetric.eigenvalues hn i := by
  apply LinearMap.IsPositive.nonneg_eigenvalues
  exact T.isPositive_adjoint_comp_self

/--
7.64(b) in [axler2024].
-/
lemma ker_adjoint_comp_self : ker (adjoint T ∘ₗ T) = ker T := by
  apply le_antisymm
  · intro v hv
    have := calc
      ‖T v‖ ^ 2 = ⟪T v, T v⟫_𝕜 := (inner_self_eq_norm_sq_to_K (T v)).symm
      _ = ⟪(adjoint T ∘ₗ T) v, v⟫_𝕜 := (adjoint_inner_left T v (T v)).symm
      _ = ⟪0, v⟫_𝕜 := by rw [hv]
      _ = 0 := inner_zero_left v
    simp_all
  · intro v hv
    simp_all

lemma injective_adjoint_comp_self_iff
  : Function.Injective (adjoint T ∘ₗ T) ↔ Function.Injective T := by
  repeat rw [←LinearMap.ker_eq_bot]
  rw [ker_adjoint_comp_self]

-- TODO: Prove using ContinuousLinearMap.orthogonal_range
lemma orthogonal_ker : (ker T)ᗮ = range (adjoint T) := by
  sorry

-- TODO: Place after LinearMap.IsSymmetric.orthogonal_ker
lemma IsSymmetric.orthogonal_ker {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : (ker T)ᗮ = range T := by
  simp [←hT.orthogonal_range]

/--
7.64(c) in [axler2024].
-/
lemma range_adjoint_comp_self : range (adjoint T ∘ₗ T) = range (adjoint T) :=
  calc
    range (adjoint T ∘ₗ T) = (ker (adjoint T ∘ₗ T))ᗮ :=
      T.isSymmetric_adjoint_comp_self.orthogonal_ker.symm
    _ = (ker T)ᗮ := by rw [ker_adjoint_comp_self]
    _ = range (adjoint T) := T.orthogonal_ker

/--
Part of 7.64(d) from [axler2024]. See also `Module.finrank_range_adjoint_comp_self`.
-/
theorem _root_.Module.finrank_range_adjoint
  : Module.finrank 𝕜 (range (adjoint T)) = Module.finrank 𝕜 (range T) := sorry

/--
The singular values of a finite dimensional linear map, ordered in descending order.
This definition accounts for the multiplicity of a singular value.

Suppose `T : E →ₗ[𝕜] F` where `dim(E) = n`, `dim(F) = m`.
In mathematical literature, the number of singular values varies, with popular choices including
- `rank(T)` singular values, all of which are positive.
- `min(n,m)` singular values, some of which might be zero.
- `n` singular values, some of which might be zero.
  This is the approach taken in [axler2024].
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
      -- TODO: Consider using `NNReal.sqrt` and pushing the coercion inside.
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

public theorem singularValues_of_finrank_le {i : ℕ}
  (hi : Module.finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_notin_range
  simp [hi]

public theorem sq_singularValues_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.eigenvalues_adjoint_comp_self_nonneg hn]

public theorem sq_singularValues_lt {n : ℕ} (hn : Module.finrank 𝕜 E = n) {i : ℕ} (hi : i < n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ := by
  exact T.sq_singularValues_fin hn ⟨i, hi⟩

public theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
  {n : ℕ} (hn : n < Module.finrank 𝕜 E)
  : Module.End.HasEigenvalue (adjoint T ∘ₗ T) ((T.singularValues n).toReal ^ 2) := by
  have hT := T.isSymmetric_adjoint_comp_self
  convert hT.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

public theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hi : Module.finrank 𝕜 E ≤ i
  · rw [T.singularValues_of_finrank_le hi, T.singularValues_of_finrank_le (hi.trans hij)]
  by_cases! hj : Module.finrank 𝕜 E ≤ j
  · simp [T.singularValues_of_finrank_le hj]
  have : (T.singularValues j : ℝ) ^ 2 ≤ (T.singularValues i : ℝ) ^ 2 := by
    rw [T.sq_singularValues_fin rfl ⟨j, hj⟩, T.sq_singularValues_fin rfl ⟨i, hi⟩]
    exact T.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij
  simpa using Real.sqrt_le_sqrt this

/--
7.68(a) from [axler2024]. Note that we have countably infinitely many singular values whereas there
are only dim(domain(T)) singular values in [axler2024], so we modify the statement to account for
this.
-/
public theorem injective_theorem
  : Function.Injective T
    ↔ 0 ∉ Finset.image T.singularValues (Finset.range (Module.finrank 𝕜 (range T))) := by
  rw [←injective_adjoint_comp_self_iff]
  rw [←ker_eq_bot]
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 0 4
  rw [←this]
  rw [not_iff_not]
  constructor <;> intro h
  · -- Plan: If 0 is an eigenvalue, then it equals (T*T).eigenvalues i for some i
    sorry
  · sorry

public theorem singularValues_lt_rank {n : ℕ}
  (hn : n < Module.finrank 𝕜 (range T)) : 0 < T.singularValues n := by
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
  le_antisymm (T.singularValues_rank ▸ T.singularValues_antitone hn) (zero_le _)

@[simp]
public theorem support_singularValues
  : T.singularValues.support = Finset.range (Module.finrank 𝕜 (range T)) := by
  ext n
  simp only [Finsupp.mem_support_iff, Finset.mem_range]
  constructor
  · intro hn
    by_contra! h
    exact hn (T.singularValues_le_rank h)
  · intro hn
    exact (T.singularValues_lt_rank hn).ne'

@[simp]
theorem singularValues_zero (i : ℕ) : (0 : E →ₗ[𝕜] F).singularValues i = 0 := by
  apply singularValues_le_rank
  trans 0 <;> simp

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

end LinearMap
