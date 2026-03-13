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

open NNReal

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
    Module.finrank 𝕜 (range (adjoint T)) = Module.finrank 𝕜 (range T) := sorry

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
theorem singularValues_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  exact Finsupp.embDomain_apply_self _ _ i

theorem singularValues_of_lt {n : ℕ} (hn : Module.finrank 𝕜 E = n) {i : ℕ} (hi : i < n)
    : T.singularValues i = Real.toNNReal √(T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩)
    := T.singularValues_fin hn ⟨i, hi⟩

theorem singularValues_of_finrank_le {i : ℕ}
  (hi : Module.finrank 𝕜 E ≤ i) : T.singularValues i = 0 := by
  apply Finsupp.embDomain_notin_range
  simp [hi]

theorem sq_singularValues_fin {n : ℕ} (hn : Module.finrank 𝕜 E = n) (i : Fin n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  simp [T.singularValues_fin hn, T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i]

theorem sq_singularValues_of_lt {n : ℕ} (hn : Module.finrank 𝕜 E = n) {i : ℕ} (hi : i < n)
  : T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn ⟨i, hi⟩ := by
  exact T.sq_singularValues_fin hn ⟨i, hi⟩

theorem hasEigenvalue_adjoint_comp_self_sq_singularValues
  {n : ℕ} (hn : n < Module.finrank 𝕜 E)
  : Module.End.HasEigenvalue (adjoint T ∘ₗ T) ((T.singularValues n).toReal ^ 2) := by
  have hT := T.isSymmetric_adjoint_comp_self
  convert hT.hasEigenvalue_eigenvalues rfl ⟨n, hn⟩ using 1
  simp [← T.sq_singularValues_fin]

theorem singularValues_antitone : Antitone T.singularValues := by
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
theorem injective_theorem : Function.Injective T
    ↔ 0 ∉ (Finset.range (Module.finrank 𝕜 E)).image T.singularValues  := by
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

-- 3. From 2., 0 appears as a singular value `dim(ker(T*T))` (= `n - rank(T*T)`) times
theorem finrank_ker_adjoint_comp_self {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
  Module.finrank 𝕜 (ker (adjoint T ∘ₗ T)) = n - Module.finrank 𝕜 (range (adjoint T ∘ₗ T)) := by
    rw [← hn, ← LinearMap.finrank_range_add_finrank_ker (adjoint T ∘ₗ T)]
    omega


omit [FiniteDimensional 𝕜 F] in
theorem finrank_comp_self {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
  Module.finrank 𝕜 (ker T) = n - Module.finrank 𝕜 (range T) := by
    rw [← hn, ← LinearMap.finrank_range_add_finrank_ker T]
    omega

-- 4. From 3., the number of positive singular values is `rank(T*T) = rank(T)`
theorem finrank_range_adjoint_comp_self :
  Module.finrank 𝕜 (range (adjoint T ∘ₗ T)) = Module.finrank 𝕜 (range T) := by
    rw [range_adjoint_comp_self', Module.finrank_range_adjoint]

-- TODO: Move to Mathlib.Analysis.InnerProductSpace.Spectrum
theorem IsSymmetric.card_filter_eigenvalues_eq_zero
  {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank 𝕜 E = n)
  : Finset.card {i : Fin n | ↑(hT.eigenvalues hn i) = (0 : 𝕜)} = Module.finrank 𝕜 (ker T) := by
  rw [hT.card_filter_eigenvalues_eq hn (μ := 0) sorry]
  rw [Module.End.eigenspace_zero]


theorem test {n : ℕ} (hn : Module.finrank 𝕜 E = n)
    : T.singularValues.support.card
      = (T.singularValues.support.preimage (@Fin.val n) Fin.val_injective.injOn).card := by
  rw [Finset.card_preimage]
  congr
  ext i
  simp only [Finsupp.mem_support_iff, ne_eq, Fin.range_val, Set.mem_Iio, Finset.mem_filter,
    iff_self_and]
  intro h
  push_neg at h
  contrapose h
  push_neg at h
  rw [←hn] at h
  exact singularValues_of_finrank_le T h

theorem test₂₅ {n : ℕ} (hn : Module.finrank 𝕜 E = n)
  : (T.singularValues.support.preimage (@Fin.val n) Fin.val_injective.injOn)
    = ({i : Fin n | ↑(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) = (0 : 𝕜)} : Finset (Fin n))ᶜ := by
  ext i
  have : 0 ≤ T.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
    T.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i
  have : T.isSymmetric_adjoint_comp_self.eigenvalues hn i = 0 ↔
    T.isSymmetric_adjoint_comp_self.eigenvalues hn i ≤ 0 := by constructor <;> order
  simp [T.singularValues_fin hn, this]

theorem test₃ : T.singularValues.support.card = Module.finrank 𝕜 T.range := by
  rw [← Module.finrank_range_adjoint, ← T.range_adjoint_comp_self']
  rw [T.test rfl]
  rw [T.test₂₅ rfl]
  rw [Finset.card_compl]
  rw [T.isSymmetric_adjoint_comp_self.card_filter_eigenvalues_eq_zero rfl]
  rw [← (T.adjoint ∘ₗ T).finrank_range_add_finrank_ker]
  simp

theorem singularValues_lt_rank {n : ℕ}
  (hn : n < Module.finrank 𝕜 (range T)) : 0 < T.singularValues n := by
    contrapose! hn
    have : T.singularValues.support ⊆ Finset.range n := by
      intro i hi
      rw [Finset.mem_range]
      have hi₂ : 0 < T.singularValues i := pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      contrapose! hi₂
      rw [←nonpos_iff_eq_zero.mp hn]
      apply singularValues_antitone T
      exact hi₂
    calc
      Module.finrank 𝕜 T.range = T.singularValues.support.card := T.test₃.symm
      _ ≤ Finset.card (Finset.range n) := Finset.card_le_card this
      _ = n := by simp


-- It's unclear what the right way to state "The rank of T, as a natural number" is,
-- I went with this approach simply because it appeared more times in Loogle, but maybe
-- `Cardinal.toNat T.rank` is better.
theorem singularValues_rank
  : T.singularValues (Module.finrank 𝕜 (range T)) = 0 := by
  -- Potentially requires proof by cases on whether T is full-rank?
  sorry

theorem singularValues_le_rank {n : ℕ}
  (hn : Module.finrank 𝕜 (range T) ≤ n) : T.singularValues n = 0 :=
  le_antisymm (T.singularValues_rank ▸ T.singularValues_antitone hn) (zero_le _)

theorem isLowerSet_support_singularValues
  : IsLowerSet (T.singularValues.support : Set ℕ) := by
  intro a b hl ha
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← zero_lt_iff] at ⊢ ha
  order [T.singularValues_antitone hl]

@[simp]
theorem support_singularValues
  : T.singularValues.support = Finset.range (Module.finrank 𝕜 (range T)) := by
  obtain h | ⟨n, hn⟩ := T.isLowerSet_support_singularValues.eq_univ_or_Iio
  · have : (Set.univ : Set ℕ).Finite := h ▸ Finset.finite_toSet _
    have : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
    contradiction
  · rw [← Finset.coe_Iio, Finset.coe_inj, Nat.Iio_eq_range] at hn
    convert hn
    apply_fun Finset.card at hn
    simpa [test₃] using hn

@[simp]
theorem singularValues_zero (i : ℕ) : (0 : E →ₗ[𝕜] F).singularValues i = 0 := by
  apply singularValues_le_rank
  trans 0 <;> simp

theorem singularValues_id_apply_of_lt_finrank {i : ℕ} (hi : i < Module.finrank 𝕜 E)
  : (LinearMap.id : E →ₗ[𝕜] E).singularValues i = 1 := sorry

theorem singularValues_id_apply {i : ℕ} :
  (LinearMap.id : E →ₗ[𝕜] E).singularValues i = if i < Module.finrank 𝕜 E then 1 else 0 := by
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
