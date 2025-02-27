/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a `FiniteMeasure P` on a topological vector space
`V`.

## Probability Character

We first define

`probChar w : C(V, ℂ) := fun (v : V) ↦ e (L v w)`,

where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map. We show:
- `probChar_submonoid`: `{ probChar w | w : W }` is a submonoid of `C(V, ℂ)`. This
  uses `probChar_one_mem` and `probChar_mul_mem`;
- `probChar_starSubalgebra`: `probChar_submonoid` spans is a star subalgebra of
  `C(V, ℂ)`. This uses `probChar_star_mem`;
- `probChar_StarSubalgebra_separatesPoints`: We use `probChar_SeparatesPoints` to
  show that the `probChar_starSubalgebra` separates points as well. Here we assume that `e`
  and `L` are non-trivial;

## Characterictic Function

The characteristic function of a `FiniteMeasure P` on `V` is the mapping

`fun w => ∫ v, e (-L v w) ∂P = ∫ v, probChar w ∂P`

We show:
- `ext_of_charFun_eq`: If the characteristic functions of two finite measures `P` and `P'`
  are equal, then `P = P'`. In other words, characteristic functions separate finite measures.

## Example: Finite Dimensional Case

As an example, we consider the case where `V = W = ℝ ^ d`, `L = ⟪ , ⟫` and `e` is the standard
probability character given by
`e = fun x => Complex.exp (Complex.I * x)`
We show:
- `ext_of_charFun_eq`: A finite measure `P` on `ℝ ^ d` is uniquely
  determined by the integrals of the form `∫ v, exp (Complex.I * ⟨v, w⟩) ∂P` for all `w : ℝ ^ d`.
-/

open MeasureTheory Filter

section probChar

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/-- define probChar, as continuous mapping from V to ℂ -/
noncomputable def probChar (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) : ContinuousMap V ℂ where
  toFun := fun (v : V) ↦ e (L v w)
  continuous_toFun := Continuous.subtype_val
    (he.comp (hL.comp (Continuous.Prod.mk_left w)))

theorem probChar_apply (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v : V) : probChar he hL w v = e (L v w) := rfl

theorem probChar_abs_one (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v : V) : Complex.abs (probChar he hL w v) = 1 :=
  Circle.abs_coe (e (L v w))

theorem probChar_dist_le_two (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) (v v' : V) : dist (probChar he hL w v) (probChar he hL w v') ≤ 2 := by
  rw [dist_eq_norm_sub]
  apply le_trans (norm_sub_le _ _) _
  simp [Complex.norm_eq_abs, probChar_abs_one he hL w _]
  norm_num

theorem probChar_one_mem (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    1 ∈ {probChar he hL w | w : W} := by
  use 0
  ext z
  simp only [probChar, map_zero, neg_zero, AddChar.map_zero_eq_one, OneMemClass.coe_one,
    ContinuousMap.coe_mk, ContinuousMap.one_apply]

theorem probChar_mul_mem (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    ∀ x y : C(V, ℂ), x ∈ {probChar he hL w | w : W} →
    y ∈ {probChar he hL w | w : W} → x * y ∈ {probChar he hL w | w : W} := by
  rintro x y ⟨v, hv⟩ ⟨v', hv'⟩
  use v + v'
  ext z
  simp only [probChar, map_add, ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  rw [AddChar.map_add_eq_mul e, Submonoid.coe_mul]
  rw [← congrFun (congrArg DFunLike.coe hv) z, ← congrFun (congrArg DFunLike.coe hv') z]
  simp [probChar]

theorem probChar_star_mem (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    ∀ x, x ∈ {probChar he hL w | w : W} → star x ∈ {probChar he hL w | w : W} := by
  intro x ⟨w, hw⟩
  use -w
  ext v
  rw [← hw]
  simp only [probChar, map_neg, neg_neg]
  simp [probChar_apply he hL]
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- If `e` and `L` are non-trivial, then `probChar` separates points. -/
theorem probChar_SeparatesPoints (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V} (hv : v ≠ v') :
    ∃ w : W, probChar he hL w v ≠ probChar he hL w v' := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne hv))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [probChar, map_sub, LinearMap.sub_apply, LinearMapClass.map_smul, smul_eq_mul,
    ContinuousMap.coe_mk, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _)]
  rw [div_eq_inv_mul, ← coe_inv_unitSphere]
  rw [← AddChar.map_neg_eq_inv e ((a / ((L v) w - (L v') w) * (L v') w))]
  rw [← Submonoid.coe_mul, ← AddChar.map_add_eq_mul e]
  ring_nf
  rw [← sub_mul, ← mul_sub, mul_assoc, GroupWithZero.mul_inv_cancel (((L v) w - (L v') w)), mul_one]
  · exact fun h => ha (SetLike.coe_eq_coe.mp h)
  · intro h
    apply hw
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, h]

section Submonoid

/-- The set `{(probChar he hL w) | w : W}` forms a submonoid -/
noncomputable
def probChar_submonoid (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    Submonoid C(V, ℂ) where
  carrier := {(probChar he hL w) | w : W}
  mul_mem' := (fun ha hb => probChar_mul_mem he hL _ _ ha hb)
  one_mem' := probChar_one_mem he hL

theorem probChar_submonoid_dist_le_two (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (f : probChar_submonoid he hL) :
    ∀ (v v' : V), dist ((f : C(V, ℂ)) v) ((f : C(V, ℂ)) v') ≤ 2 := by
  rw [← Exists.choose_spec (Set.mem_setOf.1 (Subtype.coe_prop f))]
  exact probChar_dist_le_two he hL _

end Submonoid

namespace StarSubalgebra

/-- The span of `probChar_submonoid` is a `StarSubalgebra` of `C(V, ℂ)` -/
noncomputable
def probChar_starSubalgebra (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    StarSubalgebra ℂ C(V, ℂ) :=
  StarSubalgebra.of_span_submonoid ℂ (probChar_submonoid he hL)
      (probChar_star_mem he hL)

theorem probChar_StarSubalgebra_separatesPoints (he : Continuous e)
    (he' : e ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (hL' : ∀ v ≠ 0, L v ≠ 0) : (probChar_starSubalgebra he hL).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ := probChar_SeparatesPoints he he' hL hL' hvv'
  use (probChar he hL w)
  simp only [StarSubalgebra.coe_toSubalgebra, Set.mem_image, SetLike.mem_coe, DFunLike.coe_fn_eq,
    exists_eq_right, ne_eq]
  exact ⟨Submodule.subset_span ⟨w, rfl⟩, hw⟩

theorem probChar_starSubalgebra_bounded (he : Continuous e)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    ∀ g ∈ (probChar_starSubalgebra he hL), ∃ C, ∀ (v v' : V), dist (g v) (g v') ≤ C := by
  intro g hg
  obtain ⟨n, c, f, hf⟩ := mem_span_set'.1 hg
  by_cases hn : n = 0
  · use 0
    intro x y
    rw [← hf]
    simp only [hn, Fin.isEmpty', Finset.univ_eq_empty, Finset.sum_empty, ContinuousMap.zero_apply,
      dist_self, le_refl]
  have : Nonempty (Fin n) := by
    exact Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero hn)
  let C := Complex.abs (c (Exists.choose (Finite.exists_max (fun i => Complex.abs (c i)))))
  have hC : ∀ i, Complex.abs (c i) ≤ C :=
    Exists.choose_spec (Finite.exists_max (fun i => Complex.abs (c i)))
  use n * (C * 2)
  intro v v'
  rw [dist_eq_norm, Complex.norm_eq_abs, ← hf]
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← Finset.univ.sum_sub_distrib]
  have := AbsoluteValue.sum_le Complex.abs
      Finset.univ fun i ↦ c i * ((f i) : C(V, ℂ)) v - c i * ((f i) : C(V, ℂ)) v'
  apply le_trans this _
  apply le_trans (Finset.sum_le_card_nsmul _ (fun i =>
      Complex.abs ((c i) * ((f i) : C(V, ℂ)) v - (c i) * ((f i) : C(V, ℂ)) v')) (C * 2) _)
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, le_refl]
  · intro i _
    simp only
    rw [← mul_sub]
    rw [AbsoluteValue.map_mul Complex.abs (c i) (((f i) : C(V, ℂ)) v - ((f i) : C(V, ℂ)) v')]
    apply mul_le_mul (hC i) (probChar_submonoid_dist_le_two he hL (f i) _ _)
        (AbsoluteValue.nonneg Complex.abs _) (AbsoluteValue.nonneg Complex.abs (_))

theorem probChar_starSubalgebra_integrable [MeasurableSpace V] [BorelSpace V]
    (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {P : MeasureTheory.FiniteMeasure V} :
    ∀ g ∈ (probChar_starSubalgebra he hL), MeasureTheory.Integrable g P :=
  fun g hg => BoundedContinuousFunction.integrable P
      ⟨g, probChar_starSubalgebra_bounded he hL g hg⟩

end StarSubalgebra

end probChar

section CharFun

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]
    {W : Type*} [TopologicalSpace W] [AddCommGroup W] [Module ℝ W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}

/--
If the characteristic functions of two finite measures `P` and `P'` are equal, then `P = P'`. In
other words, characteristic functions separate finite measures.
-/
theorem FiniteMeasure.ext_of_charFun_eq (he : Continuous e) (he' : e ≠ 0)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (P P' : MeasureTheory.FiniteMeasure V) :
    (∀ w, ∫ v, probChar he hL w v ∂P = ∫ v, probChar he hL w v ∂P') → P = P' := by
  intro h
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (StarSubalgebra.probChar_StarSubalgebra_separatesPoints he he' hL hL')
      (StarSubalgebra.probChar_starSubalgebra_bounded he hL)
  intro g hg
  obtain ⟨n, c, f, hf⟩ := mem_span_set'.1 hg
  rw [← hf]
  have hsum : ∀ (P : MeasureTheory.FiniteMeasure V),
      ∫ v, (Finset.univ.sum fun i ↦ c i • ((f i) : C(V, ℂ))) v ∂P
      = (Finset.univ.sum fun i ↦ ∫ v, c i • ((f i) : C(V, ℂ)) v ∂P) := by
    intro P
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    apply MeasureTheory.integral_finset_sum Finset.univ
    exact fun i _ => MeasureTheory.Integrable.const_mul
        (StarSubalgebra.probChar_starSubalgebra_integrable he hL _
        (Submodule.subset_span (Subtype.coe_prop (f i)))) _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul, MeasureTheory.integral_mul_left, mul_eq_mul_left_iff]
  left
  obtain ⟨w, hw⟩ := Set.mem_setOf.1 (Subtype.coe_prop (f i))
  rw [← hw]; exact h w

/-
The following is an example to show that the previous theorem can be applied in the special case
where `V = W = ℝ ^ d`, `L = ⟪ , ⟫` and `e` is the probability character given by
`e = fun x => Complex.exp (Complex.I * x)`. This is the standard setting in probability theory.
-/
namespace FiniteDimensional

variable {ι : Type*}

/-- dot product of two vectors in ℝ^d as a bilinear map -/
noncomputable
def dotProduct_bilinear (J : Finset ι) : (J → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ := by
  apply LinearMap.mk₂ ℝ (fun v w : J → ℝ => dotProduct v w)
      (fun m1 m2 n => add_dotProduct m1 m2 n)
      (fun c m n ↦ smul_dotProduct c m n)
      (fun m n₁ n₂ ↦ dotProduct_add m n₁ n₂)
      (fun c m n ↦ dotProduct_smul c m n)

theorem continuous_dotProduct (J : Finset ι) :
    Continuous fun p : (J → ℝ) × (J → ℝ) ↦ dotProduct_bilinear (J : Finset ι) p.1 p.2 := by
  apply continuous_finset_sum _ (fun i _ => Continuous.mul
      (Continuous.comp (continuous_apply i) (Continuous.fst continuous_id))
      (Continuous.comp (continuous_apply i) (Continuous.snd continuous_id)))

/-- Exponential map onto the circle, defined as additive character -/
noncomputable
def probFourierChar : AddChar ℝ Circle where
  toFun z := Circle.exp (z)
  map_zero_eq_one' := by simp only; rw [Circle.exp_zero]
  map_add_eq_mul' x y := by simp only; rw [Circle.exp_add]

theorem probFourierChar_apply (z : ℝ) : probFourierChar z = Circle.exp z := rfl

theorem continuous_probFourierChar : Continuous probFourierChar := Circle.exp.continuous

theorem probChar_eq (J : Finset ι) (v w : J → ℝ) : (probFourierChar (dotProduct_bilinear J v w))
    = (probChar continuous_probFourierChar (continuous_dotProduct J) w) v := by
  simp [probFourierChar, probChar]

/-- docBlame -/
theorem ext_of_charFun_eq (J : Finset ι)
    (P P' : MeasureTheory.FiniteMeasure ((i : J) → ℝ)) :
    (∀ w : J → ℝ, ∫ v, ((probFourierChar (dotProduct_bilinear J v w)) : ℂ) ∂P
    = ∫ v, ((probFourierChar (dotProduct_bilinear J v w)) : ℂ) ∂P') → P = P' := by
  have h1 : probFourierChar ≠ 1 := by
    rw [DFunLike.ne_iff]
    use Real.pi
    rw [probFourierChar_apply]
    intro h
    have heq := congrArg Subtype.val h
    rw [Circle.coe_exp Real.pi, Complex.exp_pi_mul_I] at heq
    norm_num at heq
  have h2 : ∀ (v : J → ℝ), v ≠ 0 → dotProduct_bilinear J v ≠ 0 := by
    intro v hv
    rw [DFunLike.ne_iff]
    use v
    rw [LinearMap.zero_apply]
    simpa only [dotProduct_bilinear, LinearMap.mk₂_apply, ne_eq, dotProduct_self_eq_zero]
  intro h
  apply FiniteMeasure.ext_of_charFun_eq FiniteDimensional.continuous_probFourierChar h1 h2
      (continuous_dotProduct J) P P'
  simp [probChar_eq] at *
  exact h

end FiniteDimensional

end CharFun
