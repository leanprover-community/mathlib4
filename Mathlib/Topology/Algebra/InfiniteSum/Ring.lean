/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Infinite sum in a ring

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
-/

open Filter Finset Function

variable {ι κ α : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α] {f : ι → α}
  {a₁ : α} {L : Filter (Finset ι)}

theorem HasSumFilter.mul_left (a₂) (h : HasSumFilter L f a₁) :
    HasSumFilter L (fun i ↦ a₂ * f i) (a₂ * a₁) := by
  simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

theorem HasSumFilter.mul_right (a₂) (hf : HasSumFilter L f a₁) :
    HasSumFilter L (fun i ↦ f i * a₂) (a₁ * a₂) := by
  simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

--make alias
theorem SummableFilter.mul_left (a) (hf : SummableFilter L f) : SummableFilter L fun i ↦ a * f i :=
  (hf.hasSumFilter.mul_left _).summableFilter

theorem SummableFilter.mul_right (a) (hf : SummableFilter L f) : SummableFilter L fun i ↦ f i * a :=
  (hf.hasSumFilter.mul_right _).summableFilter

section tsumFilter

variable [T2Space α]

protected theorem SummableFilter.tsumFilter_mul_left [L.NeBot] (a) (hf : SummableFilter L f) :
    ∑'[L] i, a * f i = a * ∑'[L] i, f i :=
  (hf.hasSumFilter.mul_left _).tsumFilter_eq

protected theorem SummableFilter.tsumFilter_mul_right [L.NeBot] (a) (hf : SummableFilter L f) :
    ∑'[L] i, f i * a = (∑'[L] i, f i) * a :=
  (hf.hasSumFilter.mul_right _).tsumFilter_eq

theorem Commute.tsumFilter_right [L.NeBot] (a) (h : ∀ i, Commute a (f i)) :
    Commute a (∑'[L] i, f i) := by
  classical
  by_cases hf : SummableFilter L f
  · exact (hf.tsumFilter_mul_left a).symm.trans
      ((congr_arg _ <| funext h).trans (hf.tsumFilter_mul_right a))
  · exact (tsumFilter_eq_zero_of_not_summableFilter hf).symm ▸ Commute.zero_right _

theorem Commute.tsumFilter_left [L.NeBot] (a) (h : ∀ i, Commute (f i) a) :
    Commute (∑'[L] i, f i) a :=
  (Commute.tsumFilter_right _ fun i ↦ (h i).symm).symm

end tsumFilter

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [IsTopologicalSemiring α]
    {f : ι → α} {a a₁ a₂ : α} {L : Filter (Finset ι)}

theorem HasSumFilter.div_const (h : HasSumFilter L f a) (b : α) :
    HasSumFilter L (fun i ↦ f i / b) (a / b) := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]

theorem SummableFilter.div_const (h : SummableFilter L f) (b : α) :
    SummableFilter L fun i ↦ f i / b :=
  (h.hasSumFilter.div_const _).summableFilter

theorem hasSumFilter_mul_left_iff (h : a₂ ≠ 0) :
    HasSumFilter L (fun i ↦ a₂ * f i) (a₂ * a₁) ↔ HasSumFilter L f a₁ :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, HasSumFilter.mul_left _⟩

theorem hasSumFilter_mul_right_iff (h : a₂ ≠ 0) :
    HasSumFilter L (fun i ↦ f i * a₂) (a₁ * a₂) ↔ HasSumFilter L f a₁ :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, HasSumFilter.mul_right _⟩

theorem hasSumFilter_div_const_iff (h : a₂ ≠ 0) :
    HasSumFilter L (fun i ↦ f i / a₂) (a₁ / a₂) ↔ HasSumFilter L f a₁ := by
  simpa only [div_eq_mul_inv] using hasSumFilter_mul_right_iff (inv_ne_zero h)

theorem summableFilter_mul_left_iff (h : a ≠ 0) :
    (SummableFilter L fun i ↦ a * f i) ↔ SummableFilter L f :=
  ⟨fun H ↦ by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, fun H ↦ H.mul_left _⟩

theorem summableFilter_mul_right_iff (h : a ≠ 0) :
    (SummableFilter L fun i ↦ f i * a) ↔ SummableFilter L f :=
  ⟨fun H ↦ by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, fun H ↦ H.mul_right _⟩

theorem summableFilter_div_const_iff (h : a ≠ 0) :
    (SummableFilter L fun i ↦ f i / a) ↔ SummableFilter L f := by
  simpa only [div_eq_mul_inv] using summableFilter_mul_right_iff (inv_ne_zero h)

theorem tsumFilter_mul_left [T2Space α] [L.NeBot] : ∑'[L] x, a * f x = a * ∑'[L] x, f x := by
  classical
  exact if hf : SummableFilter L f then hf.tsumFilter_mul_left a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsumFilter_eq_zero_of_not_summableFilter hf,
              tsumFilter_eq_zero_of_not_summableFilter (mt (summableFilter_mul_left_iff ha).mp hf),
              mul_zero]
alias tsum_mul_left := tsumFilter_mul_left

theorem tsumFilter_mul_right [T2Space α] [L.NeBot] : ∑'[L] x, f x * a = (∑'[L] x, f x) * a := by
  classical
  exact if hf : SummableFilter L f then hf.tsumFilter_mul_right a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsumFilter_eq_zero_of_not_summableFilter hf,
             tsumFilter_eq_zero_of_not_summableFilter (mt (summableFilter_mul_right_iff ha).mp hf),
             zero_mul]

alias tsum_mul_right := tsumFilter_mul_right

theorem tsumFilter_div_const [T2Space α] [L.NeBot] : ∑'[L] x, f x / a = (∑'[L] x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsumFilter_mul_right

theorem HasSumFilter.const_div (h : HasSumFilter L (fun x ↦ 1 / f x) a) (b : α) :
    HasSumFilter L (fun i ↦ b / f i) (b * a) := by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this

theorem SummableFilter.const_div (h : SummableFilter L (fun x ↦ 1 / f x)) (b : α) :
    SummableFilter L fun i ↦ b / f i :=
  (h.hasSumFilter.const_div b).summableFilter

theorem hasSumFilter_const_div_iff (h : a₂ ≠ 0) :
    HasSumFilter L (fun i ↦ a₂ / f i) (a₂ * a₁) ↔ HasSumFilter L (1/ f) a₁ := by
  simpa only [div_eq_mul_inv, one_mul] using hasSumFilter_mul_left_iff h

theorem summableFilter_const_div_iff (h : a ≠ 0) :
    (SummableFilter L fun i ↦ a / f i) ↔ SummableFilter L (1 / f) := by
  simpa only [div_eq_mul_inv, one_mul] using summableFilter_mul_left_iff h

end DivisionSemiring

/-!
### Multiplying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `fun x : ι × κ ↦ f x.1 * g x.2` is summable, since there is no way to
deduce this from the summabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `Analysis.Normed.Module.Basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/


section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [IsTopologicalSemiring α]
  {f : ι → α} {g : κ → α} {s t u : α} {L : Filter (Finset ι)} {L' : Filter (Finset κ)}

theorem HasSumFilter.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i ↦ f i * t) (s * t) := hf.mul_right t
  have this : ∀ i : ι, HasSum (fun c : κ ↦ f i * g c) (f i * t) := fun i ↦ hg.mul_left (f i)
  have key₂ : HasSum (fun i ↦ f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 * g x.2) (s * t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

/-- Product of two infinites sums indexed by arbitrary types.
See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are absolutely summable. -/
protected theorem Summable.tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.hasSum.mul_eq hg.hasSum hfg.hasSum

@[deprecated (since := "2025-04-12")] alias tsum_mul_tsum := Summable.tsum_mul_tsum

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
      Summable fun x : Σ n : A, antidiagonal n ↦ f (x.2 : A × A).1 * g (x.2 : A × A).2 :=
  Finset.sigmaAntidiagonalEquivProd.summable_iff.symm

variable [T3Space α] [IsTopologicalSemiring α]

theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : A × A ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  exact h.sigma' fun n ↦ (hasSum_fintype _).summable

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `Finset.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g` are absolutely
summable. -/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f)
    (hg : Summable g) (hfg : Summable fun x : A × A ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  rw [hf.tsum_mul_tsum hg hfg, ← sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A → α)]
  exact (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg).tsum_sigma'
    (fun n ↦ (hasSum_fintype _).summable)


@[deprecated (since := "2025-04-12")] alias tsum_mul_tsum_eq_tsum_sum_antidiagonal :=
  Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal

end HasAntidiagonal

section Nat

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : ℕ → α}
variable [T3Space α] [IsTopologicalSemiring α]

theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `Finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are absolutely summable.
-/
protected theorem Summable.tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg

@[deprecated (since := "2025-04-12")] alias tsum_mul_tsum_eq_tsum_sum_range :=
  Summable.tsum_mul_tsum_eq_tsum_sum_range

end Nat

end CauchyProduct
