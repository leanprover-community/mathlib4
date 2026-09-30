import Mathlib.Topology.Algebra.Polynomial

open Topology Polynomial Pointwise Filter

theorem Polynomial.eval_reverse_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : Polynomial R) :
    f.reverse.eval (⅟x) * x ^ f.natDegree = f.eval x := by
  simpa using f.eval₂_reverse_mul_pow (RingHom.id _) x

theorem Polynomial.eval_reverse_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) :
    f.reverse.eval x⁻¹ * x ^ f.natDegree = f.eval x := by
  let : Invertible x := (Units.mk0 _ hx).invertible
  simpa using f.eval_reverse_mul_pow x

theorem Filter.tendsto_iff_tendsto_inv_inv {α β : Type*} [InvolutiveInv α]
    (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m ↔ Tendsto (fun x ↦ f x⁻¹) l⁻¹ m := by
  simp [tendsto_def, mem_inv]
  convert Iff.rfl
  ext
  simp

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

theorem Polynomial.tendsto_eval_atTop_of_tendsto_eval_reverse_mul
    [TopologicalSpace F] [OrderTopology F]
    {l : Filter F} (h : Tendsto (fun x ↦ P.reverse.eval x * x⁻¹ ^ P.natDegree) (𝓝[>] 0) l):
    Tendsto P.eval atTop l := by
  rw [tendsto_iff_tendsto_inv_inv, inv_atTop₀]
  refine (tendsto_congr' (eventuallyEq_of_mem (s := {0}ᶜ) ?_ fun x hx ↦ ?_)).mp h
  · simpa [mem_nhdsWithin] using⟨Set.univ, by simp⟩
  · simpa using P.eval_reverse_mul_pow₀ (x := x⁻¹) (by simp_all)

theorem Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    (hdeg : 0 < P.degree) (hlcf : 0 ≤ P.leadingCoeff) :
    Tendsto (eval · P) atTop atTop := by
  let := Preorder.topology F
  have : OrderTopology F := ⟨rfl⟩
  refine tendsto_eval_atTop_of_tendsto_eval_reverse_mul <|
    Filter.Tendsto.pos_mul_atTop (C := P.leadingCoeff)
      (by grind [leadingCoeff_eq_zero, not_lt_bot]) ?_ ?_
  · simpa [← coeff_zero_eq_eval_zero, P.coeff_zero_reverse] using
      (P.reverse.continuous.tendsto 0).mono_left nhdsWithin_le_nhds
  · rw [tendsto_iff_tendsto_inv_inv]
    simp
    grind [natDegree_pos_iff_degree_pos]
