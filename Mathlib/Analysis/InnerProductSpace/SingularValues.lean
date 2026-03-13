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

public section

open NNReal Module

namespace LinearMap
open InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  (T : E →ₗ[𝕜] F)

-- Will become available in #35174
theorem isSymmetric_self_comp_adjoint :
    (T ∘ₗ adjoint T).IsSymmetric := sorry

-- Will become available in #35174
theorem isSymmetric_adjoint_comp_self :
    (adjoint T ∘ₗ T).IsSymmetric := by sorry

/--
7.64(b) in [axler2024].
-/
lemma ker_adjoint_comp_self : ker (adjoint T ∘ₗ T) = ker T := by
  apply le_antisymm <;> intro v hv
  · rw [mem_ker, comp_apply] at hv
    rw [mem_ker, ← inner_self_eq_zero (𝕜 := 𝕜), ← adjoint_inner_left, hv, inner_zero_left]
  · aesop

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
lemma range_adjoint_comp_self' : range (adjoint T ∘ₗ T) = range (adjoint T) :=
  calc
    range (adjoint T ∘ₗ T) = (ker (adjoint T ∘ₗ T))ᗮ :=
      T.isSymmetric_adjoint_comp_self.orthogonal_ker.symm
    _ = (ker T)ᗮ := by rw [ker_adjoint_comp_self]
    _ = range (adjoint T) := T.orthogonal_ker

/--
Part of 7.64(d) from [axler2024]. See also `Module.finrank_range_adjoint_comp_self`.
-/
theorem _root_.Module.finrank_range_adjoint :
    finrank 𝕜 (range (adjoint T)) = finrank 𝕜 (range T) := sorry

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
noncomputable def singularValues : ℕ →₀ ℝ≥0 :=
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
theorem singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

theorem singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n)
    : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩)
    := T.singularValues_fin hn ⟨i, hi⟩

theorem singularValues_of_finrank_le {i : ℕ}
  (hi : finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_notin_range
  simp [hi]

theorem sq_singularValues_fin {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

theorem sq_singularValues_of_lt {n : ℕ} (hn : finrank 𝕜 E = n) {i : ℕ} (hi : i < n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ := by
  exact T.sq_singularValues_fin hn ⟨i, hi⟩

theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
  {n : ℕ} (hn : n < finrank 𝕜 E)
  : End.HasEigenvalue (adjoint T ∘ₗ T) ((T.singularValues n).toReal ^ 2) := by
  have hT := T.isSymmetric_adjoint_comp_self
  convert hT.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

theorem singularValues_antitone : Antitone T.singularValues := by
  intro i j hij
  by_cases! hi : finrank 𝕜 E ≤ i
  · rw [T.singularValues_of_finrank_le hi, T.singularValues_of_finrank_le (hi.trans hij)]
  by_cases! hj : finrank 𝕜 E ≤ j
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
theorem injective_theorem : Function.Injective T
    ↔ 0 ∉ (Finset.range (finrank 𝕜 E)).image T.singularValues  := by
  have := (adjoint T ∘ₗ T).not_hasEigenvalue_zero_tfae.out 0 4
  rw [←injective_adjoint_comp_self_iff, ←ker_eq_bot, ←this, not_iff_not, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := T.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl h
    use i, Finset.mem_range.mpr i.isLt
    simp [RCLike.ofReal_eq_zero.mp hi, T.singularValues_fin rfl]
  · intro ⟨i, h, hz⟩
    rw [show (0 : 𝕜) = T.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨i, Finset.mem_range.mp h⟩ by
      simp [hz, ←T.sq_singularValues_of_lt rfl (Finset.mem_range.mp h)]]
    exact T.isSymmetric_adjoint_comp_self.hasEigenvalue_eigenvalues rfl ⟨i, Finset.mem_range.mp h⟩

theorem card_support_singularValues : T.singularValues.support.card = finrank 𝕜 T.range := by
  have hS : ∀ m ∈ T.singularValues.support, m < finrank 𝕜 E := by
    grind [singularValues_of_finrank_le]
  have hT := T.isSymmetric_adjoint_comp_self
  rw [← T.singularValues.support.card_attachFin hS]
  have (i : Fin _) : T.isSymmetric_adjoint_comp_self.eigenvalues rfl i = 0 ↔
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl i ≤ 0 := by
    grind [T.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i]
  calc
    (T.singularValues.support.attachFin hS).card =
      ({i | ↑(hT.eigenvalues rfl i) = (0 : 𝕜)} : Finset _)ᶜ.card := by
      congr with i
      simp [T.singularValues_fin rfl, this]
    _ = finrank 𝕜 E - Finset.card {i | hT.eigenvalues rfl i = (0 : 𝕜)} := by
      rw [Finset.card_compl]; simp
    _ = finrank 𝕜 E - finrank 𝕜 (T.adjoint ∘ₗ T).ker := by
      rw [hT.card_filter_eigenvalues_eq rfl (μ := 0) sorry, End.eigenspace_zero]
    _ = finrank 𝕜 (T.adjoint ∘ₗ T).range := by
      simp [← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker]
    _ = finrank 𝕜 T.range := by
      rw [T.range_adjoint_comp_self', finrank_range_adjoint]

theorem isLowerSet_support_singularValues
  : IsLowerSet (T.singularValues.support : Set ℕ) := by
  intro a b hl ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← zero_lt_iff] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]
theorem support_singularValues
  : T.singularValues.support = Finset.range (finrank 𝕜 (range T)) := by
  obtain h | ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio
  · have : (Set.univ : Set ℕ).Finite := h ▸ Finset.finite_toSet _
    have : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
    contradiction
  · rw [← Finset.coe_Iio, Finset.coe_inj, Nat.Iio_eq_range] at hn
    convert hn
    apply_fun Finset.card at hn
    simpa [card_support_singularValues] using hn

theorem singularValues_lt_rank {n : ℕ} (hn : n < finrank 𝕜 (range T))
    : 0 < T.singularValues n := by
  rwa [zero_lt_iff, ← Finsupp.mem_support_iff, support_singularValues, Finset.mem_range]

theorem singularValues_rank : T.singularValues (finrank 𝕜 (range T)) = 0 := by
  rw [← Finsupp.notMem_support_iff, support_singularValues]
  exact Finset.notMem_range_self

theorem singularValues_le_rank {n : ℕ}
  (hn : finrank 𝕜 (range T) ≤ n) : T.singularValues n = 0 := by
  rw [← Finsupp.notMem_support_iff, support_singularValues, Finset.mem_range]
  order

@[simp]
theorem singularValues_zero (i : ℕ) : (0 : E →ₗ[𝕜] F).singularValues i = 0 := by
  apply singularValues_le_rank
  trans 0 <;> simp

theorem singularValues_id_apply_of_lt_finrank {i : ℕ} (hi : i < finrank 𝕜 E)
  : (LinearMap.id : E →ₗ[𝕜] E).singularValues i = 1 := sorry

theorem singularValues_id_apply {i : ℕ} :
  (LinearMap.id : E →ₗ[𝕜] E).singularValues i = if i < finrank 𝕜 E then 1 else 0 := by
  split_ifs with h
  · exact singularValues_id_apply_of_lt_finrank h
  · push_neg at h
    exact singularValues_of_finrank_le id h

@[simp]
theorem singularValues_smul (c : 𝕜) (i : ℕ)
  : (c • T).singularValues i = ‖c‖ * T.singularValues i := by
  -- This one might require some facts about complex numbers
  sorry

end LinearMap
