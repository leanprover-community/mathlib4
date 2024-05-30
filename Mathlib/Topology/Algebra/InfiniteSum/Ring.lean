/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

#align_import topology.algebra.infinite_sum.ring from "leanprover-community/mathlib"@"9a59dcb7a2d06bf55da57b9030169219980660cd"

/-!
# Infinite sum in a ring

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
-/


open Filter Finset Function

open scoped Classical

variable {ι κ R α : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f g : ι → α}
  {a a₁ a₂ : α}

theorem HasSum.mul_left (a₂) (h : HasSum f a₁) : HasSum (fun i ↦ a₂ * f i) (a₂ * a₁) := by
  simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)
#align has_sum.mul_left HasSum.mul_left

theorem HasSum.mul_right (a₂) (hf : HasSum f a₁) : HasSum (fun i ↦ f i * a₂) (a₁ * a₂) := by
  simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)
#align has_sum.mul_right HasSum.mul_right

theorem Summable.mul_left (a) (hf : Summable f) : Summable fun i ↦ a * f i :=
  (hf.hasSum.mul_left _).summable
#align summable.mul_left Summable.mul_left

theorem Summable.mul_right (a) (hf : Summable f) : Summable fun i ↦ f i * a :=
  (hf.hasSum.mul_right _).summable
#align summable.mul_right Summable.mul_right

section tsum

variable [T2Space α]

theorem Summable.tsum_mul_left (a) (hf : Summable f) : ∑' i, a * f i = a * ∑' i, f i :=
  (hf.hasSum.mul_left _).tsum_eq
#align summable.tsum_mul_left Summable.tsum_mul_left

theorem Summable.tsum_mul_right (a) (hf : Summable f) : ∑' i, f i * a = (∑' i, f i) * a :=
  (hf.hasSum.mul_right _).tsum_eq
#align summable.tsum_mul_right Summable.tsum_mul_right

theorem Commute.tsum_right (a) (h : ∀ i, Commute a (f i)) : Commute a (∑' i, f i) :=
  if hf : Summable f then
    (hf.tsum_mul_left a).symm.trans ((congr_arg _ <| funext h).trans (hf.tsum_mul_right a))
  else (tsum_eq_zero_of_not_summable hf).symm ▸ Commute.zero_right _
#align commute.tsum_right Commute.tsum_right

theorem Commute.tsum_left (a) (h : ∀ i, Commute (f i) a) : Commute (∑' i, f i) a :=
  (Commute.tsum_right _ fun i ↦ (h i).symm).symm
#align commute.tsum_left Commute.tsum_left

end tsum

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f g : ι → α}
  {a a₁ a₂ : α}

theorem HasSum.div_const (h : HasSum f a) (b : α) : HasSum (fun i ↦ f i / b) (a / b) := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]
#align has_sum.div_const HasSum.div_const

theorem Summable.div_const (h : Summable f) (b : α) : Summable fun i ↦ f i / b :=
  (h.hasSum.div_const _).summable
#align summable.div_const Summable.div_const

theorem hasSum_mul_left_iff (h : a₂ ≠ 0) : HasSum (fun i ↦ a₂ * f i) (a₂ * a₁) ↔ HasSum f a₁ :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSum.mul_left _⟩
#align has_sum_mul_left_iff hasSum_mul_left_iff

theorem hasSum_mul_right_iff (h : a₂ ≠ 0) : HasSum (fun i ↦ f i * a₂) (a₁ * a₂) ↔ HasSum f a₁ :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSum.mul_right _⟩
#align has_sum_mul_right_iff hasSum_mul_right_iff

theorem hasSum_div_const_iff (h : a₂ ≠ 0) : HasSum (fun i ↦ f i / a₂) (a₁ / a₂) ↔ HasSum f a₁ := by
  simpa only [div_eq_mul_inv] using hasSum_mul_right_iff (inv_ne_zero h)
#align has_sum_div_const_iff hasSum_div_const_iff

theorem summable_mul_left_iff (h : a ≠ 0) : (Summable fun i ↦ a * f i) ↔ Summable f :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H ↦ H.mul_left _⟩
#align summable_mul_left_iff summable_mul_left_iff

theorem summable_mul_right_iff (h : a ≠ 0) : (Summable fun i ↦ f i * a) ↔ Summable f :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H ↦ H.mul_right _⟩
#align summable_mul_right_iff summable_mul_right_iff

theorem summable_div_const_iff (h : a ≠ 0) : (Summable fun i ↦ f i / a) ↔ Summable f := by
  simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)
#align summable_div_const_iff summable_div_const_iff

theorem tsum_mul_left [T2Space α] : ∑' x, a * f x = a * ∑' x, f x :=
  if hf : Summable f then hf.tsum_mul_left a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsum_eq_zero_of_not_summable hf,
              tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).mp hf), mul_zero]
#align tsum_mul_left tsum_mul_left

theorem tsum_mul_right [T2Space α] : ∑' x, f x * a = (∑' x, f x) * a :=
  if hf : Summable f then hf.tsum_mul_right a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsum_eq_zero_of_not_summable hf,
              tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).mp hf), zero_mul]
#align tsum_mul_right tsum_mul_right

theorem tsum_div_const [T2Space α] : ∑' x, f x / a = (∑' x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsum_mul_right
#align tsum_div_const tsum_div_const

end DivisionSemiring

/-!
### Multiplying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `fun x : ι × κ ↦ f x.1 * g x.2` is summable, since there is no way to
deduce this from the summabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `Analysis/NormedSpace/Basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [TopologicalSemiring α]
  {f : ι → α} {g : κ → α} {s t u : α}

theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i ↦ f i * t) (s * t) := hf.mul_right t
  have this : ∀ i : ι, HasSum (fun c : κ ↦ f i * g c) (f i * t) := fun i ↦ hg.mul_left (f i)
  have key₂ : HasSum (fun i ↦ f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂
#align has_sum.mul_eq HasSum.mul_eq

theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 * g x.2) (s * t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu
#align has_sum.mul HasSum.mul

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are absolutely summable. -/
theorem tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.hasSum.mul_eq hg.hasSum hfg.hasSum
#align tsum_mul_tsum tsum_mul_tsum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `Finset.range (n+1)`
involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`.
This in fact allows us to generalize to any type satisfying `[Finset.HasAntidiagonal A]`
-/


section CauchyProduct

section HasAntidiagonal
variable {A : Type*} [AddCommMonoid A] [HasAntidiagonal A]
variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : A → α}

/-- The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), antidiagonal n ↦ f k * g l` is summable. -/
theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
    (Summable fun x : A × A ↦ f x.1 * g x.2) ↔
      Summable fun x : Σn : A, antidiagonal n ↦ f (x.2 : A × A).1 * g (x.2 : A × A).2 :=
  Finset.sigmaAntidiagonalEquivProd.summable_iff.symm
#align summable_mul_prod_iff_summable_mul_sigma_antidiagonal summable_mul_prod_iff_summable_mul_sigma_antidiagonal

variable [T3Space α] [TopologicalSemiring α]

theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : A × A ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  exact h.sigma' fun n ↦ (hasSum_fintype _).summable
#align summable_sum_mul_antidiagonal_of_summable_mul summable_sum_mul_antidiagonal_of_summable_mul

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `Finset.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g` are absolutely
summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : A × A ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  rw [tsum_mul_tsum hf hg hfg, ← sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A → α)]
  exact
    tsum_sigma' (fun n ↦ (hasSum_fintype _).summable)
      (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)
#align tsum_mul_tsum_eq_tsum_sum_antidiagonal tsum_mul_tsum_eq_tsum_sum_antidiagonal

end HasAntidiagonal

section Nat

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : ℕ → α}
variable [T3Space α] [TopologicalSemiring α]

theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h
#align summable_sum_mul_range_of_summable_mul summable_sum_mul_range_of_summable_mul

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `Finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are absolutely summable.
-/
theorem tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg
#align tsum_mul_tsum_eq_tsum_sum_range tsum_mul_tsum_eq_tsum_sum_range

end Nat

end CauchyProduct
