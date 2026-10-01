import Mathlib.Topology.Algebra.Polynomial

open Topology Polynomial Pointwise Filter

-- Prereqs

-- Mathlib.Topology.Order.Basic
/--
Not an instance for performance reasons.
-/
theorem Preorder.topology.orderTopology (α : Type*) [Preorder α] :
  letI := topology α; OrderTopology α := let := Preorder.topology α; ⟨rfl⟩

-- Mathlib.Algebra.Polynomial.Reverse
@[simp]
theorem Polynomial.reflect_natDegree_eq_reverse {R : Type*} [CommSemiring R] (f : R[X]) :
    f.reflect f.natDegree = f.reverse := rfl

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_zero_of_degree_le
    {R : Type*} [CommSemiring R] (f : R[X]) {N : ℕ} (hf : f.degree < N) :
    (f.reflect N).eval 0 = 0 := by
  simp [← coeff_zero_eq_eval_zero, coeff_eq_zero_of_degree_lt hf]

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : R[X]) {N : ℕ} (hf : f.natDegree ≤ N) :
    (f.reflect N).eval (⅟x) * x ^ N = f.eval x := by
  simpa using f.eval₂_reflect_mul_pow (RingHom.id _) x N hf

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) {N : ℕ} (hf : f.natDegree ≤ N) :
    (f.reflect N).eval x⁻¹ * x ^ N = f.eval x := by
  let := invertibleOfNonzero hx
  simpa using f.eval₂_reflect_mul_pow (RingHom.id _) x N hf

-- Mathlib.Algebra.Polynomial.Reverse
@[simp]
theorem Polynomial.eval_reverse_zero
    {R : Type*} [CommSemiring R] (f : R[X]) :
    f.reverse.eval 0 = f.leadingCoeff := by
  simp [← coeff_zero_eq_eval_zero]

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : R[X]) :
    f.reverse.eval (⅟x) * x ^ f.natDegree = f.eval x := by
  simpa using f.eval₂_reverse_mul_pow (RingHom.id _) x

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) :
    f.reverse.eval x⁻¹ * x ^ f.natDegree = f.eval x := by
  let := invertibleOfNonzero hx
  simpa using f.eval_reverse_mul_pow x

-- Mathlib.Order.Filter.Pointwise
theorem Filter.tendsto_iff_tendsto_inv_inv {α β : Type*} [InvolutiveInv α]
    (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m ↔ Tendsto (fun x ↦ f x⁻¹) l⁻¹ m := by
  simp_rw [tendsto_def, mem_inv]
  convert Iff.rfl
  ext
  simp

-- Mathlib.Order.Filter.AtTopBot.Ring
theorem Filter.Tendsto.atTop_pow₀ {α β : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (f : β → α) {l : Filter β} (hf : Tendsto f l atTop) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x ↦ f x ^ n) l atTop := by
    refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx ↦ ?_) hf
    simpa only [pow_one] using pow_le_pow_right₀ hx hn


-- Actual theorems

namespace Polynomial

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_pos
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[>] 0) := by
  have : P ≠ 0 := by grind [leadingCoeff_zero]
  have : Q ≠ 0 := by grind [degree_zero, not_lt_bot]
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦
      x ^ (Q.natDegree - P.natDegree) * P.reverse.eval x / Q.reverse.eval x))]
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · convert ContinuousWithinAt.tendsto _
      · simp [Nat.sub_ne_zero_of_lt (natDegree_lt_natDegree ‹P ≠ 0› hdeg)]
      · fun_prop (disch := simp [‹Q ≠ 0›])
    · refine Filter.Eventually.mono ?_ (fun x ⟨hx₁, hx₂, hx₃⟩ ↦ ?_)
        (p := fun x ↦ 0 < x ∧ 0 < P.reverse.eval x ∧ 0 < Q.reverse.eval x)
      · have hpos : ∀ {f : F[X]}, 0 < f.leadingCoeff →
            ∀ᶠ (x : F) in 𝓝[>] 0, 0 < eval x f.reverse := fun {f} hf ↦ by
          convert ((ContinuousWithinAt.tendsto (f := f.reverse.eval) _).eventually_mem
            (s := Set.Ioo 0 (2 * f.leadingCoeff)) _).mono _
          · fun_prop
          · grind [eval_reverse_zero, Ioo_mem_nhds]
          · grind
        filter_upwards [self_mem_nhdsWithin, hpos hP, hpos hQ] using by grind
      · simpa using by positivity
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  simp [pow_sub₀ x hx (natDegree_le_natDegree hdeg.le),
    ← eval_reverse_mul_pow₀ (x := x⁻¹) (by simpa using hx)]
  field

theorem div_tendsto_atTop_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  rcases eq_or_ne Q 0 with rfl | _
  · simp
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦ P.reverse.eval x  / Q.reverse.eval x))]
  · convert (ContinuousAt.tendsto _).mono_left nhdsWithin_le_nhds using 2
    · simp
    · fun_prop (disch := simp [‹Q ≠ 0›])
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  grind [eval_reverse_mul_pow₀ (x := x⁻¹), pow_ne_zero, natDegree_eq_natDegree]

theorem div_tendsto_atTop_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hlcf : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[>] 0) := by
  wlog hlcf : 0 ≤ P.leadingCoeff
  · simpa using this (P := - P) (Q := - Q)
      (by simpa) (by simpa) (by grind [leadingCoeff_neg])
  apply div_tendsto_atTop_of_degree_lt_of_leadingCoeff_pos <;>
    grind [div_pos_iff, leadingCoeff_eq_zero, degree_zero, not_lt_bot]

theorem div_tendsto_atTop_of_degree_gt [TopologicalSpace F] [OrderTopology F]
    (hdeg : Q.degree < P.degree) (hlcf : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop := by
  convert (div_tendsto_atTop_of_degree_lt hdeg (by grind [div_pos_iff])).inv_tendsto_nhdsGT_zero
  simp

theorem tendsto_atTop_of_leadingCoeff_nonneg
    (hdeg : 0 < P.degree) (hlcf : 0 ≤ P.leadingCoeff) :
    Tendsto P.eval atTop atTop := by
  let := Preorder.topology F
  have := Preorder.topology.orderTopology F
  simpa using div_tendsto_atTop_of_degree_gt (P := P) (Q := 1) (by simpa)
    (by simp; grind [leadingCoeff_eq_zero, not_lt_bot])

end Polynomial
