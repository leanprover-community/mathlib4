/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a `FiniteMeasure P` on a topological vector space
`V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (-L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

## Main definition

`probChar _ _ w : V →ᵇ ℂ`: The bounded continuous mapping
`fun v ↦ e (L v (Multiplicative.toAdd w))` from `V` to `ℂ`, `e` is a continuous additive
character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

The characteristic function equals `fun w => ∫ v, probChar w ∂P`

## Main statement

If `e`and `L` are non-trivial, we can show `ext_of_charFun_eq`: If the characteristic functions of
two finite measures `P` and `P'` are equal, then `P = P'`. In other words, characteristic functions
separate finite measures.


-/

open Filter BoundedContinuousFunction Complex

namespace MeasureTheory

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

/-- The bounded continuous mapping `fun v ↦ e (L v (Multiplicative.toAdd w))` from `V` to `ℂ`. -/
def probChar (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : Multiplicative W) :
    V →ᵇ ℂ where
  toFun := fun v ↦ e (L v (Multiplicative.toAdd w))
  continuous_toFun :=
    continuous_induced_dom.comp (he.comp (hL.comp (Continuous.prodMk_left w)))
  map_bounded' := by
    refine ⟨2, fun x y ↦ ?_⟩
    calc dist _ _
      ≤ (‖_‖ : ℝ) + ‖_‖ := dist_le_norm_add_norm _ _
    _ ≤ 1 + 1 := add_le_add (by simp) (by simp)
    _ = 2 := by ring

@[simp]
lemma probChar_apply (w : Multiplicative W) (v : V) :
    probChar he hL w v = e (L v (Multiplicative.toAdd w)) := rfl

@[simp]
lemma probChar_one : probChar he hL 1 = 1 := by ext; simp

lemma probChar_mul (x y : Multiplicative W) :
    probChar he hL (x * y) = probChar he hL x * probChar he hL y := by
  ext
  simp [e.map_add_eq_mul]

lemma probChar_inv (w : Multiplicative W) :
    probChar he hL w⁻¹ = star (probChar he hL w) := by ext; simp

theorem probChar_SeparatesPoints (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) {v v' : V} (hv : v ≠ v') :
    ∃ w : W, probChar he hL w v ≠ probChar he hL w v' := by
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.mp (hL' (v - v') (sub_ne_zero_of_ne hv))
  obtain ⟨a, ha⟩ := DFunLike.ne_iff.mp he'
  use (a / (L (v - v') w)) • w
  simp only [map_sub, LinearMap.sub_apply, probChar_apply, ne_eq]
  rw [← div_eq_one_iff_eq (Circle.coe_ne_zero _), div_eq_inv_mul, ← coe_inv_unitSphere,
    ← e.map_neg_eq_inv, ← Submonoid.coe_mul, ← e.map_add_eq_mul, OneMemClass.coe_eq_one]
  calc e (- L v' ((a / (L v w - L v' w)) • w) + L v ((a / (L v w - L v' w)) • w))
  _ = e (- (a / (L v w - L v' w)) • L v' w + (a / (L v w - L v' w)) • L v w) := by
    congr
    · rw [neg_smul, ← LinearMap.map_smul (L v')]
    · rw [← LinearMap.map_smul (L v)]
  _ = e ((a / (L (v - v') w)) • (L (v - v') w)) := by
    simp only [neg_mul, map_sub, LinearMap.sub_apply]
    congr
    module
  _ = e a := by
    congr
    simp only [map_sub, LinearMap.sub_apply, smul_eq_mul]
    rw [div_mul_cancel₀]
    convert hw
    simp
  _ ≠ 1 := ha

/-- Monoid homomorphism mapping `w` to `fun v ↦ e (L v (Multiplicative.toAdd w))`. -/
def probChar_monoidHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    Multiplicative W →* (V →ᵇ ℂ) where
  toFun := probChar he hL
  map_one' := probChar_one
  map_mul' := probChar_mul (he := he) (hL := hL)

@[simp]
lemma probChar_monoidHom_apply (w : Multiplicative W) (v : V) :
    probChar_monoidHom he hL w v = e (L v (Multiplicative.toAdd w)) := by simp [probChar_monoidHom]

/-- Algebra homomorphism mapping `w` to `fun v ↦ e (L v (Multiplicative.toAdd w))`. -/
noncomputable
def probChar_AlgHom (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    AddMonoidAlgebra ℂ W →ₐ[ℂ] (V →ᵇ ℂ) :=
  AddMonoidAlgebra.lift ℂ W (V →ᵇ ℂ) (probChar_monoidHom he hL)

@[simp]
lemma probChar_AlgHom_apply (w : AddMonoidAlgebra ℂ W) (v : V) :
    probChar_AlgHom he hL w v = ∑ a ∈ w.support, w a * (e (L v a) : ℂ) := by
  simp only [probChar_AlgHom, AddMonoidAlgebra.lift_apply]
  rw [Finsupp.sum_of_support_subset w subset_rfl]
  · simp only [coe_sum, BoundedContinuousFunction.coe_smul, probChar_monoidHom_apply, toAdd_ofAdd,
      smul_eq_mul, Finset.sum_apply]
  · simp

lemma probChar_AlgHom_star_mem (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    {x : V →ᵇ ℂ} (hx : x ∈ (probChar_AlgHom he hL).range) :
    star x ∈ (probChar_AlgHom he hL).range := by
  simp only [AlgHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  let z := Finsupp.mapRange star (star_zero _) y
  let f : W ↪ W := ⟨fun x ↦ -x, (fun _ _ ↦ neg_inj.mp)⟩
  refine ⟨z.embDomain f, ?_⟩
  ext1 u
  simp only [probChar_AlgHom_apply, Finsupp.support_embDomain, Finset.sum_map,
    Finsupp.embDomain_apply, star_apply, star_sum, star_mul', Circle.star_addChar]
  rw [Finsupp.support_mapRange_of_injective (star_zero _) y star_injective]
  simp_rw [← map_neg (L u)]
  rfl

/-- The star-subalgebra of exponential polynomials. -/
noncomputable
def probChar_Poly (he : Continuous e) (hL : Continuous fun p : V × W ↦ L p.1 p.2) :
    StarSubalgebra ℂ (V →ᵇ ℂ) where
  toSubalgebra := (probChar_AlgHom he hL).range
  star_mem' := by
    intro x hx
    exact probChar_AlgHom_star_mem he hL hx

lemma mem_probChar_Poly (f : V →ᵇ ℂ) :
    f ∈ probChar_Poly he hL
      ↔ ∃ w : AddMonoidAlgebra ℂ W, f = fun x ↦ ∑ a ∈ w.support, w a * (e (L x a) : ℂ) := by
  change f ∈ (probChar_AlgHom he hL).range ↔ _
  rw [AlgHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    ext
    simp
  · rintro ⟨y, h⟩
    refine ⟨y, ?_⟩
    ext
    simp [h]

lemma probChar_mem_probChar_Poly (w : W) : probChar he hL w ∈ probChar_Poly he hL := by
  rw [mem_probChar_Poly]
  refine ⟨AddMonoidAlgebra.single w 1, ?_⟩
  ext v
  simp only [probChar_apply, AddMonoidAlgebra.single]
  rw [Finset.sum_eq_single w]
  · simp only [Finsupp.single_eq_same, ofReal_one, one_mul, SetLike.coe_eq_coe]
    rfl
  · simp [Finsupp.single_apply_ne_zero]
  · simp

lemma probChar_Poly_separatesPoints (he : Continuous e) (he' : e ≠ 1)
    (hL : Continuous fun p : V × W ↦ L p.1 p.2) (hL' : ∀ v ≠ 0, L v ≠ 0) :
    ((probChar_Poly he hL).map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro v v' hvv'
  obtain ⟨w, hw⟩ := probChar_SeparatesPoints he he' hL hL' hvv'
  use probChar he hL w
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq, SetLike.coe_eq_coe]
  exact ⟨⟨probChar he hL w, probChar_mem_probChar_Poly w, rfl⟩, hw⟩

section ext

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {𝕜 : Type*} [RCLike 𝕜]

/--
If the characteristic functions of two finite measures `P` and `P'` are equal, then `P = P'`. In
other words, characteristic functions separate finite measures.
-/
theorem ext_of_charFun_eq (he : Continuous e) (he' : e ≠ 1)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (P P' : Measure V) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ w, ∫ v, probChar he hL w v ∂P = ∫ v, probChar he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (probChar_Poly_separatesPoints he he' hL hL')
  intro g hg
  simp [StarSubalgebra.mem_map, mem_probChar_Poly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, ∑ a ∈ w.support, w a * ↑(e ((L v) a)) ∂P
      = ∑ a ∈ w.support, ∫ v, w a * ↑(e ((L v) a)) ∂P :=
    integral_finset_sum w.support
      fun a ha => Integrable.const_mul (integrable P (probChar he hL a)) _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_eq_mul, MeasureTheory.integral_mul_left, mul_eq_mul_left_iff]
  left
  exact h i

end ext

end MeasureTheory
