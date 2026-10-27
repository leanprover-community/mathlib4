/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.GroupTheory.Descent
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.Order.Northcott

/-!
# The naïve height and the approximate parallelogram law

This file defines the *naïve height* on an elliptic curve (over a field `F` with a theory of
heights, i.e., satisfying `[Height.AdmissibleAbsValues F]`).

We then prove the *approximate parallelogram law* for (affine) points on elliptic curves,
```
  |h(P+Q) + h(P-Q) - 2*(h(P) + h(Q))| ≤ C
```
where `h` is the naïve height, `P` and `Q` are affine points on a `WeierstrassCurve` and `C`
is some real constant depending only on the Weierstrass model.
-/

public section

namespace WeierstrassCurve.Affine

open Height

variable {F : Type*} [Field F] [AdmissibleAbsValues F] {W : Affine F}

section NaiveHeight

/-- The naïve logarithmic height of an affine point on `W`. -/
noncomputable def Point.naiveHeight (P : W.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.Point) : P.naiveHeight = logHeight P.xRep :=
  (rfl)

lemma Point.naiveHeight_eq_logHeight₁ {P : W.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. => simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.Point, |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight, Point.sym2x_eq]
  have H₁ := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have H (v : Fin 2 → F) : ![v 0, v 1] = v := by ext i : 1; fin_cases i <;> simp
  have h₀ (P : W.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 := H P.xRep ▸ P.xRep_ne_zero
  specialize hC (h₀ P) (h₀ Q)
  rw [H P.xRep, H Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.IsElliptic]

/-- If `W` is a Weierstrass curve over `F`, then the map `Φ : ℙ² → ℙ²` given by `addSubMap W`
is a morphism.

This implies that `|logHeight (Φ x) - 2 * logHeight x| ≤ C` for a constant `C`,
where `x = ![s, t, u]` and `Φ` acts on the coordinate vector. -/
theorem abs_logHeight_addSubMap_sub_two_mul_logHeight_le :
    ∃ C, ∀ x : Fin 3 → F,
      |logHeight (fun i ↦ (addSubMap W i).eval x) - 2 * logHeight x| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := logHeight_eval_le' <| isHomogeneous_addSubMap W
  obtain ⟨C₂, h⟩ := logHeight_eval_ge' (N := 2)
    fun ij ↦ (isHomogeneous_addSubMapCoeff W ij).C_mul ↑W.Δ'⁻¹
  have hC₂ := fun x ↦ h _ <| addSubMapCoeff_condition W x
  refine ⟨max C₁ (-C₂), fun x ↦ abs_sub_le_iff.mpr ⟨?_, ?_⟩⟩ <;> grind

/-- The **approximate parallelogram law** for the naïve height on an elliptic curve. -/
theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ (P Q : W.Point),
      |(P + Q).naiveHeight + (P - Q).naiveHeight - 2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ := Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  -- speed up `grind` below by reducing to the essentials
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

end NaiveHeight

section Northcott

instance [Northcott (logHeight₁ (K := F))] : Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  have : Filter.TendstoCofinite fun P : W.Point ↦ P.xRep 0 :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr finite_preimage_xRep0
  exact Northcott.comp_of_finite_fibers ..

variable [Northcott (logHeight₁ (K := F))]

variable (W) in
/-- The set of `F`-points on `W` with naïve height bounded by `B` is finite.
This is an important ingredient for the *Mordell-Weil Theorem*. -/
lemma finite_naiveHeight_le (B : ℝ) : {P : W.Point | P.naiveHeight ≤ B}.Finite :=
  Northcott.finite_le B

variable [DecidableEq F] [W.IsElliptic]

/-- The group of `F`-rational torsion points on an elliptic curve is finite when `F` is a field
that has the Northcott property (e.g., a number field). -/
theorem finite_torsion : Finite (AddCommGroup.torsion W.Point) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.finite_torsion_of_descent' hC

end Northcott

end WeierstrassCurve.Affine

@[deprecated (since := "2026-09-05")] alias
  WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le :=
    WeierstrassCurve.Affine.abs_logHeight_addSubMap_sub_two_mul_logHeight_le
end
