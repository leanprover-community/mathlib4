import Mathlib.Topology.Algebra.Polynomial

open Topology Polynomial Pointwise Filter

-- Prereqs

-- Mathlib.Topology.Order.Basic
/--
Not an instance for performance reasons.
-/
theorem Preorder.topology.orderTopology (α : Type*) [Preorder α] :
  letI := topology α; OrderTopology α := let := Preorder.topology α; ⟨rfl⟩

-- Mathlib.Algebra.Group.Invertible.Basic
@[reducible] def Invertible.of_ne_zero {G₀ : Type*} [GroupWithZero G₀] {x : G₀} (hx : x ≠ 0) :
  Invertible x := (Units.mk0 _ hx).invertible

-- Mathlib.Algebra.Polynomial.Reverse
@[simp]
theorem Polynomial.eval_reverse_zero
    {R : Type*} [CommSemiring R] (f : Polynomial R) :
    f.reverse.eval 0 = f.leadingCoeff := by
  rw [← coeff_zero_eq_eval_zero, f.coeff_zero_reverse]

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : Polynomial R) :
    f.reverse.eval (⅟x) * x ^ f.natDegree = f.eval x := by
  simpa using f.eval₂_reverse_mul_pow (RingHom.id _) x

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) :
    f.reverse.eval x⁻¹ * x ^ f.natDegree = f.eval x := by
  let := Invertible.of_ne_zero hx
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

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

theorem Polynomial.tendsto_eval_atTop_of_tendsto_eval_reverse_mul
    [TopologicalSpace F] [OrderTopology F]
    {l : Filter F} (h : Tendsto (fun x ↦ P.reverse.eval x * x⁻¹ ^ P.natDegree) (𝓝[>] 0) l):
    Tendsto P.eval atTop l := by
  rwa [tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' <| eventuallyEq_of_mem (s := {0}ᶜ) ?_ fun x hx ↦ ?_]
  · simpa [mem_nhdsWithin] using ⟨Set.univ, by simp⟩
  · grind [P.eval_reverse_mul_pow₀ (x := x⁻¹)]

theorem Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    (hdeg : 0 < P.degree) (hlcf : 0 ≤ P.leadingCoeff) :
    Tendsto P.eval atTop atTop := by
  let := Preorder.topology F
  have := Preorder.topology.orderTopology F
  rw [← Polynomial.natDegree_pos_iff_degree_pos] at hdeg
  exact tendsto_eval_atTop_of_tendsto_eval_reverse_mul <|
    Filter.Tendsto.pos_mul_atTop (C := P.leadingCoeff)
      (by grind [leadingCoeff_eq_zero, not_lt_bot])
      (by simpa using (P.reverse.continuous.tendsto 0).mono_left nhdsWithin_le_nhds)
      (tendsto_inv_nhdsGT_zero.atTop_pow₀ _ hdeg)

theorem Polynomial.div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  rw [← natDegree_lt_natDegree_iff hP] at hdeg
  have : Tendsto (fun x ↦ (P.reverse.eval x * x⁻¹ ^ P.natDegree) / (Q.reverse.eval x * x⁻¹ ^ Q.natDegree)) (𝓝[>] 0) (𝓝 0) := by
    have : ∀ x, P.reverse.eval x * x⁻¹ ^ P.natDegree / (Q.reverse.eval x * x⁻¹ ^ Q.natDegree) =
           (P.reverse.eval x * x ^ (Q.natDegree - P.natDegree)) / Q.reverse.eval x := fun x ↦ by
      rcases eq_or_ne (Q.reverse.eval x) 0 with eq | ne
      · simp [eq]
      rcases eq_or_ne x 0 with rfl | ne
      · simp_all [show Q.natDegree ≠ 0 by grind, show Q.natDegree - P.natDegree ≠ 0 by grind]
      field_simp
      ring_nf
      simp
      have : eval x P.reverse * x ^ (Q.natDegree - P.natDegree) * (x ^ Q.natDegree)⁻¹ =
             eval x P.reverse * x ^ (Q.natDegree - P.natDegree : ℤ) * x ^ (- (Q.natDegree : ℤ)) := by
        simp [← Int.natCast_sub hdeg.le]
      rw [this, mul_assoc, ← zpow_add₀ ne]
      ring_nf
      simp
    simp_rw [this]
    simpa [Pi.div_def] using Filter.Tendsto.div (a := 0) (b := Q.leadingCoeff)
      (by simpa [show Q.natDegree - P.natDegree ≠ 0 by grind] using (Continuous.tendsto (f := fun x => eval x P.reverse * x ^ (Q.natDegree - P.natDegree)) (by fun_prop) 0).mono_left nhdsWithin_le_nhds)
      (by simpa using (Continuous.tendsto (f := fun x => eval x Q.reverse) (by fun_prop) 0).mono_left nhdsWithin_le_nhds)
      (by grind [leadingCoeff_eq_zero])
  rwa [tendsto_iff_tendsto_inv_inv, inv_atTop₀,
      tendsto_congr' <| eventuallyEq_of_mem (s := {0}ᶜ) ?_ fun x hx ↦ ?_]
  · simpa [mem_nhdsWithin] using ⟨Set.univ, by simp⟩
  · simp [← Polynomial.eval_reverse_mul_pow₀ (x := x⁻¹) (by simpa using hx)]
