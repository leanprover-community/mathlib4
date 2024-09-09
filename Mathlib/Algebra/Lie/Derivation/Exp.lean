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

lemma expSum_eq_ge_range {x : A} (hx : IsNilpotent x) {n : ℕ} (hn : nilpotencyClass x ≤ n) :
    expSum A x = ∑ i in Finset.range n, (1 / i.factorial : ℚ) • (x ^ i) := by
  rw [← Finset.sum_range_add_sum_Ico _ hn, expSum, self_eq_add_right]
  apply Finset.sum_eq_zero
  rintro i hi
  apply smul_eq_zero_of_right
  apply pow_eq_zero_of_nilpotencyClass_le hx (Finset.mem_Ico.1 hi).1

lemma expSum_eq_range_add {x : A} (hx : IsNilpotent x) {n : ℕ} :
    expSum A x = ∑ i in Finset.range (nilpotencyClass x + n),
      (1 / i.factorial : ℚ) • (x ^ i) := by
  rw [expSum_eq_ge_range hx]
  exact Nat.le_add_right (nilpotencyClass x) n

variable [Nontrivial A]

lemma expSum_eq_one_add {a : A} (ha : IsNilpotent a) : expSum A a =
    1 + ∑ n in Finset.Ico 1 (nilpotencyClass a), (1 / n.factorial : ℚ) • (a ^ n) := by
  simp [expSum, ← Finset.sum_range_add_sum_Ico _ (nilpotencyClass_pos ha)]

end general_expSum

section choose

open scoped Nat

theorem Nat.choose_div_factorial_eq_div_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    Nat.choose n k  = n ! / (k ! * (n - k)!) := sorry


end choose

section

variable {A : Type w} [CommRing A] [Algebra ℚ A] [Nontrivial A]

lemma expSum_add_of_comm {a b : A} (ha : IsNilpotent a) (hb : IsNilpotent b) (hab : Commute a b) :
    expSum A (a + b) = expSum A a * expSum A b := by
  let n := max (max (nilpotencyClass (a + b)) (nilpotencyClass a)) (nilpotencyClass b)
  have han : nilpotencyClass a ≤ n := le_max_of_le_left (le_max_right _ _)
  have hbn : nilpotencyClass b ≤ n := le_max_right _ _
  have habn : nilpotencyClass (a + b) ≤ 2*n :=
    (le_max_of_le_left (le_max_left _ _)).trans (Nat.le_mul_of_pos_left _ (show 0 < 2 by norm_num))
  let S := (Finset.range (2*n) ×ˢ Finset.range (2*n + 1)).filter (fun ⟨a, b⟩ => b < a + 1)
  rw [expSum_eq_ge_range (hab.isNilpotent_add ha hb) habn]
  simp only [hab.add_pow, Finset.smul_sum]
  rw [← Finset.sum_finset_product' S]

  have : ∀ p ∈ S, (1 / p.1.factorial : ℚ) • (a ^ p.2 * b ^ (p.1 - p.2) * p.1.choose p.2) =
    (1 / (p.1 - p.2).factorial : ℚ) • b ^ (p.1 - p.2) * (1 / p.2.factorial : ℚ) • a ^ p.2 := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    rw [mul_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul (R := ℚ)]
    rw [smul_smul, Nat.choose_eq_factorial_div_factorial (Nat.le_of_lt_add_one hp.2)]
    sorry -- cast issues, this should be a separate lemma somewhere...!
  rw [Finset.sum_congr rfl this]

  let S' := (Finset.range (2*n) ×ˢ Finset.range (2*n + 1)).filter (fun ⟨a, b⟩ => a + b < 2*n)

  -- CAN IMPROVE BIJECTION YET AGAIN!

  let i : ∀ x ∈ S', ℕ × ℕ := fun ⟨x, y⟩ hxy => ⟨x + y, y⟩
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
  let f : ℕ × ℕ → A := fun ⟨x, y⟩ =>
     ((1 / x.factorial : ℚ) • b ^ x) * (1 / y.factorial : ℚ) • a ^ y
  rw [← Finset.sum_bij (f := f) i hi hi_inj hi_surj (by intros; simp only [Nat.add_sub_cancel])]
  simp only [S', f] -- TODO: f is wrong....

  let S'' := Finset.range n ×ˢ Finset.range n
  rw [← Finset.sum_subset (s₁ := S'') sorry sorry] -- nontrivial sorries
  rw [Finset.sum_product]
  simp only [← Finset.sum_mul_sum]
  rw [expSum_eq_ge_range ha han, expSum_eq_ge_range hb hbn, mul_comm]
  -- NEW GOAL
  intro ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_congr_left_iff,
    and_iff_left_iff_imp, S]
  intro hxy hx
  exact hxy.trans <| Nat.add_lt_add_right hx 1

lemma expSum_isUnit {a : A} (ha : IsNilpotent a) : IsUnit (expSum A a) := by
  rw [expSum_eq_one_add ha]
  apply IsNilpotent.isUnit_one_add
  apply isNilpotent_sum
  intro n hn
  apply IsNilpotent.smul
  apply IsNilpotent.pow_of_pos ha (Nat.not_eq_zero_of_lt (Finset.mem_Ico.1 hn).1)

end

section

theorem Finset.range_prod (n : ℕ) : Finset.range n ×ˢ Finset.range n =
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

theorem Finset.sum_range_mul_sum_range {α : Type*} [NonUnitalNonAssocSemiring α]
    (f : ℕ → α) (g : ℕ → α) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) * ∑ j ∈ Finset.range n, g j =
    ∑ i ∈ Finset.range (2*n - 1), ∑ j ∈ Finset.Ico (i - n) (min i n), f j * g (i - j) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.range_prod, Finset.sum_biUnion] -- TODO: pairwise disjoint!
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


end

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra ℚ L]

-- TODO: ℚ vs R???
noncomputable def exp : (LieDerivation ℚ L L) → L →ₗ⁅ℚ⁆ L := fun δ ↦ {
  toLinearMap := expSum (L →ₗ[ℚ] L) δ
  map_lie' := by
    intro x y
    simp [expSum]
    simp only [sum_lie ℚ, lie_sum ℚ]
    rw [Finset.sum_range_mul_sum_range]

    -- need to do inner bij here!
    sorry -- need to simplify once more...


    sorry -- need sum and ⁅⁆ interaction
    -- Then need some sort of "Finset.sum prod" interaction (probably have to do it manually)
    -- Need sum_range_mul_sum_range variant

    -- NOTE: maybe other proof is better (yes as it avoids general Leibniz, but thats good to have)!


}

/-
Next:
- Define inner automorphisms of a lie algebra (?)

-/


end LieDerivation
