import Mathlib

-- Definition of the singular values.

open NNReal

/--
When the vector spaces are not necessarily finite, these are called the approximation numbers.
Note: we use ≤ n instead of < n because we start the singular values at 0, not 1, so if we did
< n the first singular value would be repeated.
-/
noncomputable def ContinuousLinearMap.singularValue {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (T : X →L[𝕜] Y) (n : ℕ) : ℝ≥0 :=
  -- NOTE: We can't use `⨅ H ∈ {...}` because of
  -- https://leanprover-community.github.io/extras/pitfalls.html#accidental-double-iinf-or-isup
  ⨅ H : {S : X →L[𝕜] Y // S.rank ≤ n}, ‖T - H‖₊

section arbitrary_dimensional_not_necessarily_complete_normed_space

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  (T : X →L[𝕜] Y)

theorem ContinuousLinearMap.singularValue_le {n : ℕ} {H : X →L[𝕜] Y} (h : H.rank ≤ n)
  : T.singularValue n ≤ ‖T - H‖₊ :=
  ciInf_le' (fun S : {S : X →L[𝕜] Y // S.rank ≤ n} ↦ ‖T - S‖₊) ⟨H, h⟩

theorem ContinuousLinearMap.le_singularValue {n : ℕ} (x : ℝ≥0)
  (h : ∀ (S : X →L[𝕜] Y), S.rank ≤ n → x ≤ ‖T - S‖₊)
  : x ≤ T.singularValue n := by
  have : Nonempty {S : X →L[𝕜] Y // S.rank ≤ n} := ⟨⟨0, by simp [LinearMap.rank_zero]⟩⟩
  apply le_ciInf
  intro ⟨S, hS⟩
  exact h S hS

theorem ContinuousLinearMap.singularValue_eq {n : ℕ} {H : X →L[𝕜] Y} (h₁ : H.rank ≤ n)
  (h₂ : ∀ (S : X →L[𝕜] Y), S.rank ≤ n → ‖T - H‖₊ ≤ ‖T - S‖₊)
  : T.singularValue n = ‖T - H‖₊ := by
  apply le_antisymm
  · apply singularValue_le
    exact h₁
  · apply le_singularValue
    exact h₂

@[simp]
theorem ContinuousLinearMap.singularValue_zero : T.singularValue 0 = ‖T‖₊ := by
  suffices h : T.singularValue 0 = ‖T - 0‖₊ by simpa using h
  apply singularValue_eq
  · simp
  · intro S hS
    apply le_of_eq
    congr
    symm
    simpa [LinearMap.range_eq_bot, ←ContinuousLinearMap.coe_zero, ContinuousLinearMap.coe_inj]
      using hS

/--
Part of axiom S1 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/
theorem ContinuousLinearMap.antitone_singularValue : Antitone T.singularValue := by
  intro n m hnm
  apply le_singularValue
  intro S hS
  apply singularValue_le
  exact le_trans hS (Nat.cast_le.mpr hnm)

/--
Part of axiom S1 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/
theorem ContinuousLinearMap.singularValue_eq_zero_of_le
  {n : ℕ} (hn : T.singularValue n = 0) {m : ℕ} (h : n ≤ m) : T.singularValue m = 0 := by
  have := T.antitone_singularValue h
  have := zero_le (T.singularValue m)
  order

theorem ContinuousLinearMap.support_singularValue
  : T.singularValue.support = {n : ℕ | n < T.rank} := sorry

theorem ContinuousLinearMap.support_singularValue_of_eq {m : ℕ} (h : T.rank = m)
  : T.singularValue.support = Set.Iio m := sorry

theorem ContinuousLinearMap.support_singularValue_of_aleph0_le_rank (h : Cardinal.aleph0 ≤ T.rank)
  : T.singularValue.support = Set.univ := sorry

theorem ContinuousLinearMap.encard_support_singularValue
  : T.singularValue.support.encard = T.rank.toENat := sorry

theorem ContinuousLinearMap.ncard_support_singularValue
  : T.singularValue.support.ncard = T.rank.toNat := by
  have := T.encard_support_singularValue
  apply_fun ENat.toNat at this
  simpa using this

-- Should be able to prove this fairly easily from the previous theorems about support
open Cardinal in
theorem ContinuousLinearMap.finite_support_singularValue_iff_aleph0_le_rank
  : T.singularValue.support.Finite ↔ ℵ₀ ≤ T.rank := sorry

/--
Axiom S5 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/
-- Should be easily provable from the above theorems
theorem ContinuousLinearMap.singularValue_rank_lt {m : ℕ} (h : T.rank < m)
  : T.singularValue m = 0 := sorry

open Filter
open Topology

open Cardinal in
theorem ContinuousLinearMap.iInf_singularValue
  : ⨅ n : ℕ, T.singularValue n = ⨅ H : {S : X →L[𝕜] Y // S.rank < ℵ₀}, ‖T - H‖₊ := by
  sorry

-- Look into Mathlib.Topology.Order.MonotoneConvergence to prove the following
open Cardinal in
theorem ContinuousLinearMap.tendsto_atTop_singularValue
  : Tendsto T.singularValue (atTop : Filter ℕ)
    (𝓝 (⨅ H : {S : X →L[𝕜] Y // S.rank < ℵ₀}, ‖T - H‖₊)) := by
  apply tendsto_atTop_isGLB (antitone_singularValue T)
  rw [←ContinuousLinearMap.iInf_singularValue]
  apply isGLB_ciInf
  exact OrderBot.bddBelow (Set.range T.singularValue)

/--
Axiom S2 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/
-- You might be able to find a proof linked in one of the references there
theorem ContinuousLinearMap.singularValue_add_le (S : X →L[𝕜] Y) (n : ℕ)
  : (S + T).singularValue n ≤ S.singularValue n + ‖T‖ := sorry

/--
Part of axiom S3 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
See also `ContinuousLinearMap.singularValue_comp_left_le`
-/
-- You might be able to find a proof linked in one of the references there
theorem ContinuousLinearMap.singularValue_comp_right_le
  {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
  (A : W →L[𝕜] X) (n : ℕ)
  : (T ∘L A).singularValue n ≤ (T.singularValue n) * ‖A‖ := sorry

/--
Part of axiom S3 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
See also `ContinuousLinearMap.singularValue_comp_right_le`
-/
-- You might be able to find a proof linked in one of the references there
theorem ContinuousLinearMap.singularValue_comp_left_le
  {Z : Type*} [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  (B : Y →L[𝕜] Z) (n : ℕ)
  : (B ∘L T).singularValue n ≤ ‖B‖ * (T.singularValue n) := sorry

/--
Axiom S3 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/
theorem ContinuousLinearMap.singularValue_comp_comp_le
  {W : Type*} [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
  {Z : Type*} [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
  (A : W →L[𝕜] X) (B : Y →L[𝕜] Z) (n : ℕ)
  : (B ∘L T ∘L A).singularValue n ≤ ‖B‖ * (T.singularValue n) * ‖A‖ := by
  grw [singularValue_comp_left_le]
  grw [singularValue_comp_right_le]
  rw [mul_assoc]

/-
We still need axiom S4 for s-numbers as defined by
https://link.springer.com/article/10.1007/s43036-024-00386-x
-/

-- In every Banach Space, every operator that is the limit of finite-rank operators is compact.
-- Spaces for which the converse hold are said to have the "Approximation Property".
-- https://en.wikipedia.org/wiki/Approximation_property
-- All Hilbert spaces have the approximation property.

-- Note: might require space to be complete (i.e. a Banach space instead of just a normed space)
-- Probably want to use ContinuousLinearMap.iInf_singularValue in the proof
theorem ContinuousLinearMap.isCompactOperator_of_iInf_singularValue_eq_zero
  (h : ⨅ n : ℕ, T.singularValue n = 0) : IsCompactOperator T := sorry

end arbitrary_dimensional_not_necessarily_complete_normed_space

-- Banach Spaces
section arbitrary_dimensional_complete_normed_space

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →L[𝕜] Y)

end arbitrary_dimensional_complete_normed_space

section arbitrary_dimensional_not_necessarily_complete_inner_product_space

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  {Y : Type*} [SeminormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
  (T : X →L[𝕜] Y)

-- In the future, can be upgraded to spaces which satisfy the approximation property.
-- Note: might require space to be complete
-- (i.e. a Hilbert space instead of just an inner product space).
-- Probably want to use ContinuousLinearMap.iInf_singularValue in the proof
theorem ContinuousLinearMap.iInf_singularValue_eq_zero_of_isCompactOperator
  (h : IsCompactOperator T) : ⨅ n : ℕ, T.singularValue n = 0 := sorry

theorem ContinuousLinearMap.iInf_singularValue_eq_zero_iff_isCompactOperator
  : ⨅ n : ℕ, T.singularValue n = 0 ↔ IsCompactOperator T :=
  Iff.intro
    T.isCompactOperator_of_iInf_singularValue_eq_zero
    T.iInf_singularValue_eq_zero_of_isCompactOperator

end arbitrary_dimensional_not_necessarily_complete_inner_product_space

-- Hilbert Spaces
section arbitrary_dimensional_complete_inner_product_space

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [SeminormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  (T : X →L[𝕜] Y)

end arbitrary_dimensional_complete_inner_product_space

-- Eventually, we want to show that the range of T.singularValue is the square root of the set of
-- eigenvalues of T*T,  and that T.singularValue equals the square root of list of eigenvalues
-- produced by the spectral theorem.

section finite_dimensional_normed_space

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
  (T : X →L[𝕜] Y)

end finite_dimensional_normed_space

section finite_dimensional_inner_product_space

variable {𝕜 : Type*} [RCLike 𝕜]
  {X : Type*} [SeminormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
  {Y : Type*} [SeminormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
  (T : X →L[𝕜] Y)

end finite_dimensional_inner_product_space
