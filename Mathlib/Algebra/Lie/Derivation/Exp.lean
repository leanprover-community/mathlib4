import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup

namespace LieDerivation

universe u v w

open algebraMap

section general_expSum

variable (A : Type w) [Ring A] [Algebra ℚ A]

noncomputable def expSum : A → A := fun x ↦
  ∑ n in Finset.range (nilpotencyClass x), (1 / n.factorial : ℚ) • (x ^ n)

variable {A}

@[simp]
lemma expSum_zero : expSum A 0 = 1 := by
  by_cases hA : Nontrivial A
  · simp [expSum]
  · rw [not_nontrivial_iff_subsingleton] at hA
    exact Subsingleton.elim _ _

lemma expSum_eq_sum_range_ge {x : A} (hx : IsNilpotent x) {n : ℕ} (hn : nilpotencyClass x ≤ n) :
    expSum A x = ∑ i in Finset.range n, (1 / i.factorial : ℚ) • (x ^ i) := by
  rw [← Finset.sum_range_add_sum_Ico _ hn, expSum, self_eq_add_right]
  apply Finset.sum_eq_zero
  rintro i hi
  apply smul_eq_zero_of_right
  apply pow_eq_zero_of_nilpotencyClass_le hx (Finset.mem_Ico.1 hi).1

lemma expSum_eq_range_add {x : A} (hx : IsNilpotent x) {n : ℕ} :
    expSum A x = ∑ i in Finset.range (nilpotencyClass x + n),
      (1 / i.factorial : ℚ) • (x ^ i) := by
  rw [expSum_eq_sum_range_ge hx]
  exact Nat.le_add_right (nilpotencyClass x) n

lemma expSum_eq_one_add {a : A} (ha : IsNilpotent a) : expSum A a =
    1 + ∑ n in Finset.Ico 1 (nilpotencyClass a), (1 / n.factorial : ℚ) • (a ^ n) := by
  by_cases hA : Nontrivial A
  · simp [expSum, ← Finset.sum_range_add_sum_Ico _ (nilpotencyClass_pos ha)]
  · rw [not_nontrivial_iff_subsingleton] at hA
    exact Subsingleton.elim _ _

end general_expSum

section choose

open scoped Nat

theorem Nat.choose_div_factorial_eq_div_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    (Nat.choose n k / n ! : ℚ)  = 1 / (k ! * (n - k)!) := by
  rw [Nat.choose_eq_factorial_div_factorial hk,
    Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hk) (by positivity),
    div_div_cancel_left' (by positivity)]
  simp


end choose

section

variable {A : Type w} [CommRing A] [Algebra ℚ A]

lemma expSum_add_of_comm {a b : A} (ha : IsNilpotent a) (hb : IsNilpotent b) (hab : Commute a b) :
    expSum A (a + b) = expSum A a * expSum A b := by
  -- Let N be large enough so that `a^N = b^N = (a + b)^(2*N) = 0`
  let N := max (nilpotencyClass a) (nilpotencyClass b)
  have han : nilpotencyClass a ≤ N := le_max_left _ _
  have hbn : nilpotencyClass b ≤ N := le_max_right _ _
  have habn : nilpotencyClass (a + b) ≤ 2*N := (hab.nilpotencyClass_add_le ha hb).trans (by omega)
  -- We apply the binomial theorem to write `expSum A (a + b)` as a double sum
  simp only [expSum_eq_sum_range_ge (hab.isNilpotent_add ha hb) habn, hab.add_pow, Finset.smul_sum]
  /- Let `S` be the set of integers `(k, l)` such that `0 ≤ k, l ≤ 2*N` and `l < k + 1`. We can
  rewrite the double sum as a sum indexed by `S`. -/
  let S := (Finset.range (2*N) ×ˢ Finset.range (2*N + 1)).filter (fun ⟨k, l⟩ => l < k + 1)
  have hS : ∀ (p : ℕ × ℕ), p ∈ S ↔ p.1 ∈ Finset.range (2 * N) ∧ p.2 ∈ Finset.range (p.1 + 1) := by
    intro ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_congr_left_iff,
      and_iff_left_iff_imp, S]
    intro hxy hx
    exact hxy.trans <| Nat.add_lt_add_right hx 1
  rw [← Finset.sum_finset_product' S _ _ hS]
  /- Next, we reparametrize the sum. Let `S'` be the set of integers `(k, l)` such that
  `0 ≤ k, l ≤ 2*N` and `k + l < 2*N`. We also define a function `i : S' → ℕ × ℕ` which induces
  a bijection from `S'` to `S`. -/
  let S' := (Finset.range (2*N) ×ˢ Finset.range (2*N + 1)).filter (fun ⟨a, b⟩ => a + b < 2*N)
  let i : ∀ x ∈ S', ℕ × ℕ := fun ⟨x, y⟩ _ => ⟨x + y, y⟩
  have hi : ∀ x hx, i x hx ∈ S := by simp [S, S']; omega
  have hi_inj : ∀ x₁ hx₁ x₂ hx₂, i x₁ hx₁ = i x₂ hx₂ → x₁ = x₂ := by
    intro x₁ hx₁ x₂ hx₂ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    apply Prod.ext (by omega) h₂
  have hi_surj : ∀ y ∈ S, ∃ x hx, i x hx = y := by
    intro ⟨a, b⟩ hab
    refine ⟨⟨a - b, b⟩, by simp [S, S'] at hab ⊢; omega, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Prod.mk.injEq, and_true, S,
      i] at hab ⊢
    exact Nat.sub_add_cancel (Nat.le_of_lt_add_one hab.2)
  /- During this reparametrization, we can also rearrange the function we are summing over so that
  we sum over `((1 / x.factorial : ℚ) • b ^ x) * (1 / y.factorial : ℚ) • a ^ y` gives `(x, y) ∈ S'`.
  -/
  let f : ℕ × ℕ → A := fun ⟨x, y⟩ => ((1 / x.factorial : ℚ) • b ^ x) * (1 / y.factorial : ℚ) • a ^ y
  have hf : ∀ (x : ℕ × ℕ) (hx : x ∈ S'), f x = (1 / (i x hx).1.factorial : ℚ) •
      (a ^ (i x hx).2 * b ^ ((i x hx).1 - (i x hx).2) * (i x hx).1.choose (i x hx).2) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, S'] at hx
    rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul (R := ℚ), smul_smul, one_div_mul_eq_div]
    rw [Nat.choose_div_factorial_eq_div_factorial_div_factorial (Nat.le_add_left _ _)]
    rw [← one_div_mul_one_div, mul_smul_mul_comm, mul_comm, Nat.add_sub_cancel]
  rw [← Finset.sum_bij (f := f) i hi hi_inj hi_surj hf]
  /- Next, we write the sum over the subset `S'' := [0, N) × [0, N)`, as whenever `N ≤ k` or
  `N ≤ l`, the term corresponding to `(k, l)` will vanishes. -/
  let S'' := Finset.range N ×ˢ Finset.range N
  have hS''₀ : S'' ⊆ S' := by
    intro x hx
    simp only [S', S'', Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hx ⊢
    omega
  have hS''₁ : ∀ x ∈ S', x ∉ S'' → f x = 0 := by
    intro ⟨x, y⟩ hx₀ hx₁
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, S'] at hx₀
    obtain hx | hy := by simpa [not_and_or, -not_and, S''] using hx₁
    · apply mul_eq_zero_of_left (smul_eq_zero_of_right _ _)
      exact pow_eq_zero_of_nilpotencyClass_le hb (le_trans hbn hx)
    · apply mul_eq_zero_of_right _ (smul_eq_zero_of_right _ _)
      exact pow_eq_zero_of_nilpotencyClass_le ha (le_trans (le_max_left _ _) hy)
  rw [← Finset.sum_subset (s₁ := S'') hS''₀ hS''₁]
  -- Now it is clear that this sum is the product of `expSum A a` and `expSum A b`
  rw [Finset.sum_product]
  simp only [← Finset.sum_mul_sum]
  rw [expSum_eq_sum_range_ge ha han, expSum_eq_sum_range_ge hb hbn, mul_comm]

@[simp]
lemma expSum_mul_neg_self {a : A} (ha : IsNilpotent a) : expSum A a * expSum A (-a) = 1 := by
  rw [← expSum_add_of_comm ha ha.neg (by simp)]
  rw [add_neg_cancel, expSum_zero]

@[simp]
lemma expSum_neg_self_mul {a : A} (ha : IsNilpotent a) : expSum A (-a) * expSum A a = 1 := by
  rw [← expSum_add_of_comm ha.neg ha (by simp)]
  rw [neg_add_cancel, expSum_zero]

protected noncomputable def IsNilpotent.expSum {a : A} (ha : IsNilpotent a) : Aˣ where
  val := expSum A a
  inv := expSum A (-a)
  val_inv := expSum_mul_neg_self ha
  inv_val := expSum_neg_self_mul ha

lemma expSum_isUnit {a : A} (ha : IsNilpotent a) : IsUnit (expSum A a) :=
  ⟨IsNilpotent.expSum ha, rfl⟩

end

section

theorem Finset.range_prod_eq_biUnion_of_sums (n : ℕ) : Finset.range n ×ˢ Finset.range n =
    (Finset.range (2*n - 1)).biUnion (fun i ↦
      (Finset.range (min i n) ×ˢ Finset.range (min i n)).filter (fun ⟨a, b⟩ ↦ a + b = i)) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_biUnion, Finset.mem_filter,
    exists_eq_right_right', iff_and_self, and_imp]
  refine ⟨?_, ?_⟩
  intro ⟨ha, hb⟩
  refine ⟨by omega, ?_, ?_⟩
  sorry
  sorry
  intro ⟨hn, ha, hb⟩
  refine ⟨lt_of_lt_of_le ha (min_le_right _ _), lt_of_lt_of_le hb (min_le_right _ _)⟩

theorem Finset.sum_range_sum_range_eq {α : Type*} [NonUnitalNonAssocSemiring α] (f : ℕ → α)
    (g : ℕ → α) (n : ℕ) : ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, f i * g j =
      ∑ i ∈ Finset.range (2*n - 1), ∑ j ∈ Finset.Ico (i - n) (min i n), f j * g (i - j) := by
  rw [← Finset.sum_product', Finset.range_prod_eq_biUnion_of_sums, Finset.sum_biUnion] -- TODO: pairwise disjoint!
  apply Finset.sum_congr rfl
  intro i hi
  let f : Finset.Ioo (i - n) (min i n) ≃
      (Finset.range (min i n) ×ˢ Finset.range (min i n)).filter (fun ⟨a, b⟩ ↦ a + b = i) := {
    toFun :=
      fun ⟨x, hx⟩ ↦ ⟨⟨x, i - x⟩, by
        obtain ⟨hx₁, hx₂⟩ := Finset.mem_Ioo.1 hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          tsub_lt_self_iff]
        omega⟩
    invFun := fun ⟨⟨a, b⟩, hab⟩ ↦ ⟨a, sorry⟩
    left_inv := fun x ↦ rfl
    right_inv := by
      intro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      suffices i - x.1 = x.2 by rw [this]
      simp only [Finset.mem_filter] at hx
      omega -- TODO: fix?
  }
  --apply Finset.sum_equiv f
  sorry

theorem Finset.sum_range_mul_sum_range {α : Type*} [NonUnitalNonAssocSemiring α] (f : ℕ → α)
    (g : ℕ → α) (n : ℕ) : (∑ i ∈ Finset.range n, f i) * ∑ j ∈ Finset.range n, g j =
      ∑ i ∈ Finset.range (2*n - 1), ∑ j ∈ Finset.Ico (i - n) (min i n), f j * g (i - j) := by
  rw [Finset.sum_mul_sum, Finset.sum_range_sum_range_eq]

end

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra ℚ L]

-- TODO: 2 options here..
-- 1. Go with Humphreys proof (annoying with sum rewrites...)
-- -- -- Now it might actually be ok!
-- 2. Go with clean derivation proof (annoying w tensor products)


noncomputable def exp : (LieDerivation ℚ L L) → L →ₗ⁅ℚ⁆ L := fun δ ↦ {
  toLinearMap := expSum (L →ₗ[ℚ] L) δ
  map_lie' := by
    intro x y
    simp [expSum]
    simp only [sum_lie ℚ, lie_sum ℚ]
    rw [Finset.sum_range_sum_range_eq] -- TODO: need to be able to apply this..

    -- Then: apply Leibniz (should be immediate)
    sorry -- need to simplify once more...
}

/-
Next:
- Define inner automorphisms of a lie algebra (?)

-/


end LieDerivation
