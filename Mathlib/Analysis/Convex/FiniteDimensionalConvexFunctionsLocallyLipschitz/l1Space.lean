/-
Copyright (c) 2024 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
/-!
# l₁ Space and Continuous Linear Maps between l₁ Space and Finite Dimensional Space

In this file, we introduce the concept of the `l₁` space,
specifically constructed over finite-dimensional real vector spaces,
using the `PiLp` type with p = 1.
This file contains several key definitions and theorems that involve continuous linear maps and their properties in this space.

## Main Definitions

- `l₁ (n : ℕ)` : The `l₁` space on `Fin n → ℝ`, defined using the `PiLp` construction.

- `f` : A noncomputable function mapping basis vectors to the `l₁` space.

- `σ` : A noncomputable map constructed using `Basis.constrL` which is shown to be continuous.

## Main Theorems

- `continuous_map_sigma` : The continuity of the map `σ`.

- `sigma_orthogonal_same_index` : The orthogonality property when indices are equal.

- `sigma_orthogonal_diff_index` : The orthogonality property when indices are different.

- `sigma_apply_basis` : An explicit formula for the map `σ` applied to basis vectors.

- `sigma_norm_apply` : A theorem relating the norm of an application of `σ` to a basis element.

- `sigma_decompose_apply` : A theorem showing the decomposition of an application of `σ`.

- `l1_norm_eq` :Assume {bᵢ} is a basis for finite dimensional space α ,
∀ x ∈ α , x = ∑ aᵢbᵢ ,then we get l₁ norm by map σ which is ‖σ(x)‖=∑ ‖aᵢ‖ * ‖bᵢ‖
-/

/--The `l₁` space on `Fin n → ℝ`, defined using the `PiLp` construction.-/
def l₁ (n : ℕ):= PiLp 1 (fun _ : Fin n => ℝ)

variable {α : Type*}
  [NormedAddCommGroup α] [InnerProductSpace ℝ α] [FiniteDimensional ℝ α]

open FiniteDimensional

open scoped Pointwise

/--A noncomputable function mapping basis vectors to the `l₁` space.-/
noncomputable def f : Fin (finrank ℝ α) → PiLp 1 (fun _ : Fin (finrank ℝ α) => ℝ) :=
  fun i j => if i = j then ‖(finBasis ℝ α) i‖ else 0

noncomputable def σ := Basis.constrL (finBasis ℝ α) f

theorem continuous_map_sigma : Continuous (σ (α := α)):= by exact ContinuousLinearMap.continuous σ

theorem sigma_orthogonal_same_index {i j : Fin (finrank ℝ α)} (h : i = j) :
    (σ ((finBasis ℝ α) i)) j = ‖(finBasis ℝ α) i‖ := by simp[σ,f,h]

theorem sigma_orthogonal_diff_index {i j : Fin (finrank ℝ α)} (h : i ≠ j) :
    (σ ((finBasis ℝ α) i)) j = 0 := by simp[σ,f,h]

theorem sigma_apply_basis (i : Fin (finrank ℝ α)) :
    σ ((finBasis ℝ α) i) = fun j => if i = j then ‖(finBasis ℝ α) i‖ else 0 := by
  ext j
  simp[σ,f];

theorem sigma_norm_apply : ∀ x , ∀ j , ∑ i  , (((finBasis ℝ α).repr x) i) • σ ((finBasis ℝ α) i) j
    = (((finBasis ℝ α).repr x) j) * ‖(finBasis ℝ α) j‖ := by
  intro x j
  nth_rw 2 [pi_eq_sum_univ ((finBasis ℝ α).repr x)]
  repeat rw[Finset.sum_apply];
  rw[Finset.sum_mul]
  congr;ext u
  rw[sigma_apply_basis];
  simp only [smul_eq_mul, mul_ite, mul_zero, Pi.smul_apply, mul_one, ite_mul, zero_mul]
  exact
    ite_congr rfl
      (fun a ↦
        congrArg (HMul.hMul (((finBasis ℝ α).repr x) u))
          (congrArg norm (congrArg (⇑(finBasis ℝ α)) a)))
      (congrFun rfl)

theorem sigma_decompose_apply : ∀ x , ∀ j , (σ x) j =
    ∑ i , (((finBasis ℝ α).repr x) i) • σ ((finBasis ℝ α) i) j:= by
  intro x
  rw[← PiLp.ext_iff]
  calc
    _ = σ (∑ i , (((finBasis ℝ α).repr x) i) • (finBasis ℝ α) i):= by
      congr;exact Eq.symm (Basis.sum_repr (finBasis ℝ α) x)
    _ = ∑ i , σ ((((finBasis ℝ α).repr x) i) • (finBasis ℝ α) i):= by
      simp only [map_sum, map_smul]
    _ = _ := by
      ext j;
      repeat rw[Finset.sum_apply]
      congr
      ext x
      simp only [map_smul, PiLp.smul_apply, smul_eq_mul]

/--
For any element x in the vector space α, the norm of the image of x
under the map σ can be expressed as a weighted sum.
Specifically, it is the sum of the norms of the coefficients
in the finite basis representation of x, each multiplied by the norm of the corresponding basis vector.
-/
theorem l1_norm_eq : ∀ x , ‖σ x‖ =  ∑ i , ‖((finBasis ℝ α).repr x) i‖ * ‖(finBasis ℝ α) i‖ := by
  intro x
  rw[PiLp.norm_eq_of_nat 1 (by norm_num)]
  simp only [pow_one, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, Real.rpow_one]
  congr
  ext i
  rw[sigma_decompose_apply x i,← norm_smul,sigma_norm_apply,norm_smul]
  simp;

/--
For a given point x in the vector space α, a positive radius r,
and the condition that the finite dimension of α over ℝ is non-zero,
the preimage under the map σ of the metric ball centered at （σ x） with radius r
is contained within the convex hull of a set.
This set is the Minkowski sum of {x} and the union of scaled basis vectors
b i, including both positive and negative scalings.
-/
local notation "b" => (finBasis ℝ α)
theorem l1Ball_sub_convexHull{x : α}{r : ℝ}(hr : r > 0)(hn : finrank ℝ α ≠ 0):
    σ.toFun ⁻¹' (Metric.ball (σ.toFun x) r) ⊆
    convexHull ℝ (({x} : Set α) + ((⋃ i , {(r / ‖b i‖) • (b i)})  ∪  (⋃ i ,{- (r / ‖b i‖) • (b i)}))):= by
  intro x₀ hx₀
  simp[dist_eq_norm] at hx₀
  rw[← map_sub] at hx₀
  have sum_le_r :  ∑ i , ‖(b).equivFun (x₀ - x)  i‖ * ‖(b) i‖ / r ≤  1 := by --sorry
    rw[← Finset.sum_div]
    simp only [Basis.equivFun_apply, Pi.sub_apply]
    rw[← l1_norm_eq (x₀ - x)]
    apply le_of_lt
    apply Bound.div_lt_one_of_pos_of_lt hr hx₀
  let n := finrank ℝ α
  let ι := Fin n
  let ι₀ := Fin (n + 2)
  let w₀ := (b).equivFun (x₀ - x)
  have repr : ∑ i , w₀ i • b i = x₀ - x := Basis.sum_equivFun b (x₀ - x)

  let w₁  : ι → ℝ := fun i => |(b).equivFun (x₀ - x) i| * ‖b i‖ / r
  let sum := ∑ i : ι, w₁ i

  have sum_pos : 1 - sum ≥ 0 := by
    simp only [sum,w₁,ge_iff_le, gt_iff_lt,sub_pos,Pi.sub_apply, sub_nonneg]
    apply sum_le_r

  let w  : ι₀ → ℝ
    | ⟨i, hi⟩ =>
        if h : i < n then w₁ ⟨i , h⟩ else (1 - sum) / 2

  have lem_i {i : ℕ}(hi : i < n + 2)(h₁ : ¬i = n + 1)(h₂ : ¬i = n) : i < n:= by
      by_contra h₃;
      push_neg at h₁ h₂ h₃;
      have : n ≤ i ∧ i ≤ n + 1 := ⟨h₃ , by linarith[hi]⟩
      rw[Nat.le_and_le_add_one_iff] at this
      rcases this with h | h
      · apply h₂ h
      · apply h₁ h
  have n_pos : n > 0 := Nat.zero_lt_of_ne_zero hn
  let fin0 : ι := ⟨0, n_pos⟩
  let z : ι₀ → α
    | ⟨i, hi⟩ =>
      if h₁ : i = n + 1 then - (r / ‖b fin0‖) • (b fin0)
      else if h₂ : i = n then  (r / ‖b fin0‖) • (b fin0)
      else if _h₃ : (b).equivFun (x₀ - x) ⟨i , lem_i hi h₁ h₂⟩ = 0 then
        (r / ‖b ⟨i, lem_i hi h₁ h₂⟩‖) • (b ⟨i, lem_i hi h₁ h₂⟩)
      else ((SignType.sign ((b).equivFun (x₀ - x) ⟨i , lem_i hi h₁ h₂⟩))
      * (r / ‖b ⟨i, lem_i hi h₁ h₂⟩‖)) • (b ⟨i, lem_i hi h₁ h₂⟩)

  have hw₀ : ∀ (i : ι₀), 0 ≤ w i := by
    intro ⟨i,hi⟩
    by_cases h : i < n
    · simp only [Pi.sub_apply, h, ↓reduceDIte, ge_iff_le, w, w₁]
      apply div_nonneg _ (le_of_lt hr)
      apply mul_nonneg
      apply abs_nonneg
      apply norm_nonneg
    · simp[w,h];linarith[sum_pos];
  have hw₁ : ∑ i : ι₀, w i = 1 :=by
    simp[w , ι₀]
    have : n + 1 + 1 = n + 2 := by norm_num
    rw[← this]
    rw[Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.is_lt, ↓reduceDIte, Fin.eta, Fin.val_last, lt_self_iff_false,
      add_lt_iff_neg_left, not_lt_zero']
    have : ∑ x : Fin n, w₁ x = sum := rfl
    rw[this]
    linarith

  have hz : ∀ (i : ι₀), z i ∈ ((⋃ i , {(r / ‖b i‖) • (b i)})  ∪  (⋃ i ,{- (r / ‖b i‖) • (b i)})) := by --sorry
    intro i
    simp only [dite_eq_ite, z]
    by_cases h₁ : (i : ℕ) = n + 1
    · simp[h₁]
    simp only [h₁, ↓reduceIte]
    by_cases h₂ : (i : ℕ) = n
    · simp[h₂]
    simp only [h₂, ↓reduceIte, add_right_inj]
    let use_i : ι := ⟨i ,lem_i i.2 h₁ h₂⟩
    simp only [↓reduceDIte]
    let a := (b).equivFun (x₀ - x) use_i
    rcases lt_trichotomy a 0 with ha | ha | ha
    · right
      have : (b).equivFun (x₀ - x) use_i ≠ 0 := by linarith
      simp at this
      rw[sign_neg ha]
      simp[this, ↓reduceIte]
    · left;
      simp only [a] at ha
      rw[ha,sign_zero]
      simp;
    · left
      rw[sign_pos ha]
      simp
  have bi_pos : ∀ i : ι , ‖b i‖ ≠ 0 := by
    intro i
    refine norm_ne_zero_iff.mpr ?_
    exact Basis.ne_zero b i

  have hx : ∑ i : ι₀, w i • z i = x₀ - x := by
    rw[Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp[w]
    have : ((1 - sum) / 2) • z (Fin.last n).castSucc +
        ((1 - sum) / 2) • z (Fin.last (n + 1)) = 0 := by
      simp[z];
    rw[add_assoc, this]
    simp;
    rw[← repr]
    congr
    ext i
    have h₁ : (i : ℕ) ≠ n + 1 := by
      refine Nat.ne_of_lt ?h
      refine Nat.lt_succ_of_lt i.2
    have h₂ : (i : ℕ) ≠ n  := Ne.symm (Nat.ne_of_lt' i.2)
    simp only [neg_smul, dite_eq_ite, Fin.coe_castSucc, h₁, ↓reduceIte, h₂,
      Fin.eta, z]
    have : w₁ i • ((SignType.sign ((b).equivFun (x₀ - x) i)) * (r / ‖b i‖)) = w₀ i := by
      simp only [Pi.sub_apply, smul_eq_mul, w₁, w₀]
      calc
        _ = |(b).equivFun (x₀ - x) i| * (‖b i‖ / r) * (SignType.sign ((b).equivFun (x₀ - x) i)) * (r / ‖b i‖) := by
          rw[← mul_div]
          linarith
        _ = ((SignType.sign ((b).equivFun (x₀ - x) i)) * |(b).equivFun (x₀ - x) i|) * ((‖b i‖ / r) * (r / ‖b i‖)) := by
          linarith
        _ = _ :=by
          rw[sign_mul_abs]
          field_simp [bi_pos i]
    by_cases h : (b).equivFun (x₀ - x) i = 0
    · simp[h]
      rw[← smul_assoc]
      simp only [smul_eq_mul, w₁,w₀,h];simp
    simp only [h, ↓reduceIte]
    simp only [w₁,w₀]
    rw[← smul_assoc]
    apply congrFun (congrArg HSMul.hSMul this) (b i)
  rw[convexHull_add]
  have sub_in₁:=mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz hx
  have x_in₂ :x ∈ (convexHull ℝ) {x} := mem_convexHull_iff.mpr fun t a _ => a rfl
  have : x₀ = x + (x₀ - x):= by simp only [add_sub_cancel]
  rw[this]
  apply Set.add_mem_add x_in₂ sub_in₁

theorem sigma_is_injective : Function.Injective σ (α := α) := by
  intro x y h
  rw[← sub_eq_zero]
  rw[← sub_eq_zero, ← map_sub] at h
  let z := x - y
  let n := finrank ℝ α
  let bs := finBasis ℝ α
  have hz : z = ∑ i : Fin n , (bs.repr z i)• bs i := Eq.symm (Basis.sum_repr bs z)
  change σ z = 0 at h
  rw[hz] at h
  simp at h
  have hi :∀ i , (∑ x : Fin n, (bs.repr z) x • σ (bs x)) i = (bs.repr z) i * ‖(finBasis ℝ α) i‖:= by
    intro i
    repeat rw[Finset.sum_apply];
    simp only [PiLp.smul_apply]
    rw[sigma_norm_apply]
  show z = 0
  rw[hz]
  apply Fintype.sum_eq_zero (fun a => (bs.repr z) a • bs a)
  intro i
  rw[smul_eq_zero]
  left
  have : ‖(finBasis ℝ α) i‖ ≠ 0:= norm_ne_zero_iff.mpr $ Basis.ne_zero (finBasis ℝ α) i
  have h1 : (bs.repr z) i * ‖(finBasis ℝ α) i‖ = 0 := by
    rw[← hi , h, PiLp.zero_apply]
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero this h1
