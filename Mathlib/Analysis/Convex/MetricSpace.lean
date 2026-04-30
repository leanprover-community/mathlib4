/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.ConvexSpace.AffineSpace

/-!

# Convex spaces with compatible metric structure

A convex space has a compatible metric structure if `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`.
This is what one would expect from the triangle inequality.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the literature
that has little to do with this definition.

## Main results

- `Convexity.ConvexSpace.IsMetricCompatible`: The (`Prop`-valued) class of convex spaces with
  compatible metric structure.
- `Convexity.continuous_convexComboPair`: Binary convex combination is continuous.
- `Convexity.ConvexSpace.IsMetricCompatible.of_convex`:
  Convex subspaces of normed spaces are convex metric spaces.

## TODO

- Equip `StdSimplex` with a topology and show the analogous continuity result for n-ary
  convex combinations.
- Tidy up the imports with `Mathlib.LinearAlgebra.ConvexSpace.AffineSpace` etc once those files
  are moved to proper places.
-/

public section

namespace Convexity

open ConvexSpace

variable {I X : Type*} [ConvexSpace ℝ X] [MetricSpace X]

variable (X) in
/-- A convex metric space is a real convex space with a compatible metric structure.
Concretely, we ask for `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)`,
which is what one would expect from the triangle inequality.

In particular, convex subsets of normed affine spaces are convex metric spaces.

Note that there is a separate notion of
[convex metric spaces](https://en.wikipedia.org/wiki/Convex_metric_space) in the literature
that has little to do with this definition. -/
class IsConvexDist : Prop where
  /-- Use `dist_iConvexCombo_le` instead. -/
  dist_iConvexCombo_fst_snd_le (f : StdSimplex ℝ (X × X)) :
    dist (f.iConvexCombo Prod.fst) (f.iConvexCombo Prod.snd) ≤ f.iConvexCombo fun (x, y) ↦ dist x y

variable [IsConvexDist X]

/-- `dist(∑ tᵢ xᵢ, ∑ tᵢ yᵢ) ≤ ∑ tᵢ dist(xᵢ, yᵢ)` -/
lemma dist_iConvexCombo_le {ι : Type*} (f : StdSimplex ℝ ι) (x y : ι → X) :
    dist (f.iConvexCombo x) (f.iConvexCombo y) ≤ f.weights.sum fun i r ↦ r * dist (x i) (y i) := by
  simpa [iConvexCombo_map, Function.comp_def]

    using IsConvexDist.dist_iConvexCombo_fst_snd_le (f.map fun i ↦ (x i, y i))
  classical
  let e : ι → ℕ := Function.extend (↑) (f.weights.support.equivFin ·) 0
  have he (x : _) (hx : x ∈ f.weights.support) : e x = ↑(f.weights.support.equivFin ⟨x, hx⟩) :=
      Subtype.val_injective.extend_apply _ _ ⟨x, hx⟩
  let einv : ℕ → ι := Function.extend (↑)
      (f.weights.support.equivFin.symm ·) (fun _ ↦ f.nonempty.some)
  have H (x : _) (hx : x ∈ f.weights.support) : einv (e x) = x := by
    simp [he, hx, einv, Fin.val_injective]
  convert ConvexSpace.IsMetricCompatible.dist_iConvexCombo_le' (f.map e) (x ∘ einv) (y ∘ einv)
    using 0
  simp only [iConvexCombo]
  congr! 3
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · ext1
    simp only [StdSimplex.map, ← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_congr fun x hx ↦ by simp [H, hx]
  · simp only [StdSimplex.map, Function.comp_apply, zero_mul, implies_true, add_mul,
      Finsupp.sum_mapDomain_index]
    exact Finsupp.sum_congr fun x hx ↦ by simp [H, hx]

lemma dist_iConvexCombo_left_le (f : StdSimplex ℝ I) (g : I → X) (x : X) :
    dist (f.iConvexCombo g) x ≤ f.weights.sum fun i r ↦ r * dist (g i) x := by
  simpa using dist_iConvexCombo_le f g (fun _ ↦ x)

lemma dist_iConvexCombo_right_le (x : X) (f : StdSimplex ℝ I) (g : I → X) :
    dist x (f.iConvexCombo g) ≤ f.weights.sum fun i r ↦ r * dist x (g i) := by
  simpa using dist_iConvexCombo_le f (fun _ ↦ x) g

lemma dist_sConvexCombo_left_le (f : StdSimplex ℝ X) (x : X) :
    dist f.sConvexCombo x ≤ f.weights.sum fun i r ↦ r * dist i x := by
  simpa using dist_iConvexCombo_left_le f id x

lemma dist_sConvexCombo_right_le (x : X) (f : StdSimplex ℝ X) :
    dist x f.sConvexCombo ≤ f.weights.sum fun i r ↦ r * dist x i := by
  simpa using dist_iConvexCombo_right_le x f id

@[simp]
lemma dist_convexComboPair_left
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist (convexComboPair s t hs ht h x y) x = t * dist x y := by
  classical
  suffices H : ∀ {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X),
      dist (convexComboPair s t hs ht h x y) x ≤ t * dist x y by
    refine (H ..).antisymm ?_
    conv_lhs => rw [eq_sub_iff_add_eq'.mpr h, sub_mul, one_mul]
    grw [sub_le_iff_le_add, dist_comm x y, ← H ht hs ((add_comm _ _).trans h) y x, dist_comm,
      convexComboPair_symm, ← dist_triangle_left]
  intro s t hs ht h x y
  grw [convexComboPair, dist_sConvexCombo_left_le]
  simp [StdSimplex.duple, Finsupp.sum_add_index, add_mul, dist_comm y x]

@[simp]
lemma dist_convexComboPair_right
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist (convexComboPair s t hs ht h x y) y = s * dist x y := by
  rw [convexComboPair_symm, dist_convexComboPair_left, dist_comm]

@[simp]
lemma dist_left_convexComboPair
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist x (convexComboPair s t hs ht h x y) = t * dist x y := by
  rw [dist_comm, dist_convexComboPair_left]

@[simp]
lemma dist_right_convexComboPair
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y : X) :
    dist y (convexComboPair s t hs ht h x y) = s * dist x y := by
  rw [dist_comm, dist_convexComboPair_right]

/-- `dist(sx + (1-s)y, s'x + (1-s')y) = |s - s'| dist(x, y)`.

See `dist_convexComboPair_convexComboPair_le`
for the version where the weights are fixed and the points change. -/
lemma dist_convexComboPair_convexComboPair
    {s t s' t' : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1)
    (hs' : 0 ≤ s') (ht' : 0 ≤ t') (h' : s' + t' = 1) (x y : X) :
    dist (convexComboPair s t hs ht h x y) (convexComboPair s' t' hs' ht' h' x y) =
      |s - s'| * dist x y := by
  wlog hss' : s' ≤ s generalizing s t s' t'
  · rw [dist_comm, this, abs_sub_comm]; exact le_of_not_ge hss'
  suffices dist (convexComboPair s t hs ht h x y) (convexComboPair s' t' hs' ht' h' x y) ≤
      |s - s'| * dist x y by
    refine this.antisymm ?_
    nth_grw 2 [← abs_dist_sub_le (z := x)]
    have : |t - t'| = |s - s'| := by
      rw [eq_sub_iff_add_eq.mpr h, eq_sub_iff_add_eq.mpr h']; simp [abs_sub_comm t t']
    simp [← sub_mul, this]
  let f : StdSimplex ℝ (Fin 3) :=
  { weights := Finsupp.equivFunOnFinite.symm ![s', s - s', t]
    nonneg i := by fin_cases i <;> simp [*]
    total := by simp [Finsupp.sum_fintype, Fin.sum_univ_succ, ← add_assoc, h] }
  convert dist_iConvexCombo_le f ![x, x, y] ![x, y, y] using 1
  swap; · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, f, hss']
  congr 1
  · delta convexComboPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, ← add_assoc]
  · delta convexComboPair
    congr 1
    ext a
    simp [StdSimplex.duple, StdSimplex.map, Finsupp.mapDomain,
      Finsupp.sum_fintype, Fin.sum_univ_succ, f, show t' = s - s' + t by grind]

/-- `dist(sx + (1-s)y, sx' + (1-s)y') ≤ s dist(x, x') + (1-s) dist(y, y')`.

See `dist_convexComboPair_convexComboPair`
for the version where the points are fixed and the weights change. -/
lemma dist_convexComboPair_convexComboPair_le
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (h : s + t = 1) (x y x' y' : X) :
    dist (convexComboPair s t hs ht h x y) (convexComboPair s t hs ht h x' y') ≤
      s * dist x x' + t * dist y y' := by
  convert dist_iConvexCombo_le (.duple (M := Fin 2) 0 1 hs ht h) ![x, y] ![x', y']
  · simp [convexComboPair_def]
  · simp [convexComboPair_def]
  · simp [Finsupp.sum_fintype, Fin.sum_univ_succ, StdSimplex.duple]

/-- The convex combination `(t, p, q) ↦ t • p + (1 - t) • q` is continuous on `[0, 1] × X × X`
for a convex metric space `X`. -/
lemma continuous_convexComboPair :
    Continuous fun x : Set.Icc (0 : ℝ) 1 × (X × X) ↦ convexComboPair (R := ℝ)
      ↑x.1 (1 - ↑x.1) x.1.prop.left (by simpa using x.1.prop.right) (add_sub_cancel ..)
      x.2.1 x.2.2 := by
  apply continuous_prod_of_continuous_lipschitzWith' (K := 1)
  · intro i x y
    simp only [← coe_nnreal_ennreal_nndist, ENNReal.coe_one, one_mul, ENNReal.coe_le_coe,
      NNReal.toReal_le, coe_nndist]
    grw [dist_convexComboPair_convexComboPair_le, Prod.dist_eq]
    nth_grw 1 [le_max_left (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.left
    nth_grw 2 [le_max_right (dist x.1 y.1) (dist x.2 y.2)]
    swap; · simpa using i.prop.right
    rw [← add_mul, add_sub_cancel, one_mul]
  · intro b
    refine LipschitzWith.continuous (K := nndist b.1 b.2) fun x y ↦ ?_
    rw [mul_comm]
    simp [← coe_nnreal_ennreal_nndist, ← ENNReal.coe_mul, NNReal.toReal_le,
      dist_convexComboPair_convexComboPair, Subtype.dist_eq, dist_eq_norm]

lemma continuous_convexComboPair_of_isBounded
    {T : Type*} [TopologicalSpace T] (f : T → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) (x y : T → X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ))
    (hx' : Bornology.IsBounded (Set.range x)) (hy' : Bornology.IsBounded (Set.range y)) :
    Continuous fun i ↦ convexComboPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) := by
  obtain ⟨D, hD, hD'⟩ := ((Metric.isBounded_iff_eventually.mp (hx'.union hy')).and
    (Filter.eventually_gt_atTop 0)).exists
  replace hD := fun t₁ t₂ ↦ hD (.inl (Set.mem_range_self t₁)) (.inr (Set.mem_range_self t₂))
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : f t ∈ Set.Ioo 0 1
  · exact ((isOpen_Ioo.preimage hf).isOpenEmbedding_subtypeVal.continuousAt_iff
      (x := ⟨t, ht⟩)).mp ((continuous_convexComboPair (X := X)).comp₃ (W := f ⁻¹' Set.Ioo 0 1)
      (e := fun i ↦ ⟨f i, Set.Ioo_subset_Icc_self i.prop⟩) (f := x ∘ (↑)) (k := y ∘ (↑))
      (by fun_prop) (hx.comp_continuous continuous_subtype_val (by simp_all; grind))
      (hy.comp_continuous continuous_subtype_val (by simp_all; grind))).continuousAt
  obtain ht | ht : f t = 0 ∨ f t = 1 := by
    simpa [le_antisymm_iff, hf0, hf1, -not_and, not_and_or] using ht
  · simp only [ContinuousAt, ht, sub_zero, convexComboPair_zero]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hy.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hj hj' ⊢
    grw [dist_triangle _ (convexComboPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x j) (y t)), dist_convexComboPair_convexComboPair_le]
    simp only [dist_self, mul_zero, zero_add, dist_convexComboPair_right]
    grw [sub_le_self _ (hf0 _), hj, hD, (le_abs_self _).trans hj'.le]
    · field_simp; norm_num
    · exact hf0 _
  · simp only [ContinuousAt, ht, sub_self, convexComboPair_one]
    rw [Metric.nhds_basis_ball.tendsto_right_iff]
    intro r hr
    filter_upwards [hx.continuousAt ((hf.isOpen_preimage _ isClosed_singleton.isOpen_compl).mem_nhds
      (x := t) (by simp [*])) (Metric.ball_mem_nhds _ (show 0 < r / 3 by simpa)),
      hf.tendsto' _ _ ht (Metric.ball_mem_nhds _ (show 0 < r / D / 3 by simp [*]))] with j hj hj'
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hj hj' ⊢
    grw [dist_triangle _ (convexComboPair (f j) (1 - f j) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x t) (y j)), dist_convexComboPair_convexComboPair_le]
    simp only [dist_self, mul_zero, add_zero, dist_convexComboPair_left]
    grw [abs_sub_comm, ← le_abs_self] at hj'
    grw [hj, hj', hf1, hD]
    · field_simp; norm_num
    · exact hf0 _

/-- When `X` is a bounded convex metric space, to check continuity of
`t ↦ f(t) • x(t) + (1 - f(t)) • y(t)` it suffices to show that `f` is continuous,
`x` is continuous away from `f(t) = 0`, and `y` is continuous away from `f(t) = 1`. -/
lemma continuous_convexComboPair' [BoundedSpace X]
    {T : Type*} [TopologicalSpace T] (f : T → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) (x y : T → X)
    (hx : ContinuousOn x (f ⁻¹' {0}ᶜ)) (hy : ContinuousOn y (f ⁻¹' {1}ᶜ)) :
    Continuous fun i ↦ convexComboPair (f i) (1 - f i) (hf0 _) (by simpa using hf1 _)
      (add_sub_cancel ..) (x i) (y i) :=
  continuous_convexComboPair_of_isBounded f hf hf0 hf1 x y hx hy (.all _) (.all _)

/-- A convex subset of a vector space is a convex space. -/
-- TODO: this should generalize to arbitrary convex space once `Convex` is redefined.
@[expose, implicit_reducible]
noncomputable def ConvexSpace.ofConvex
    {R E : Type*} [LinearOrder R] [Field R] [IsStrictOrderedRing R]
      [AddCommGroup E] [Module R E] {S : Set E} (H : Convex R S) :
    ConvexSpace R S where
  sConvexCombo f :=
    ⟨sConvexCombo (f.map (↑)), by
    simpa [sConvexCombo_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul] using
      H.sum_mem (fun _ _ ↦ f.nonneg _) f.total fun i _ ↦ i.2⟩
  assoc f := by
    simp [sConvexCombo_eq_sum, StdSimplex.map, Finsupp.sum_mapDomain_index, add_smul,
      StdSimplex.join, Finsupp.sum_sum_index, Finsupp.sum_smul_index, mul_smul, Finsupp.smul_sum]
  sConvexCombo_single x := by simp [sConvexCombo_eq_sum, ← StdSimplex.mk_single, StdSimplex.map]

lemma isAffineMap_coe {R E : Type*} [LinearOrder R] [Field R] [IsStrictOrderedRing R]
      [AddCommGroup E] [Module R E] (S : Set E) (H : Convex R S) :
    letI : ConvexSpace R S := .ofConvex H
    IsAffineMap R ((↑) : S → E) :=
  letI : ConvexSpace R S := .ofConvex H
  ⟨fun _ ↦ rfl⟩

@[simp]
lemma ConvexSpace.ofConvex.coe_sConvexCombo
      {R E : Type*} [LinearOrder R] [Field R] [IsStrictOrderedRing R]
      [AddCommGroup E] [Module R E] (S : Set E) (H : Convex R S) (f : StdSimplex R S) :
    letI : ConvexSpace R S := .ofConvex H
    (↑f.sConvexCombo : E) = (f.map (↑)).sConvexCombo :=
  rfl

@[simp]
lemma ConvexSpace.ofConvex.coe_iConvexCombo
      {R I E : Type*} [LinearOrder R] [Field R] [IsStrictOrderedRing R]
      [AddCommGroup E] [Module R E] (S : Set E) (H : Convex R S) (f : StdSimplex R I) (g : I → S) :
    letI : ConvexSpace R S := .ofConvex H
    (↑(f.iConvexCombo g) : E) = f.iConvexCombo fun x ↦ ↑(g x) :=
  letI : ConvexSpace R S := .ofConvex H
  (isAffineMap_coe S H).map_iConvexCombo f g

instance (priority := low) {V P : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] :
    IsConvexDist P where
  dist_iConvexCombo_le' f σ₁ σ₂ := by
    let p : P := Nonempty.some inferInstance
    simp only [AddTorsor.iConvexCombo_eq_affineCombination, ge_iff_le]
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p,
      Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ f.total p]
    trans ‖f.weights.sum fun a b ↦ b • (σ₁ a -ᵥ σ₂ a)‖
    · simp [dist_eq_norm_vsub, Finsupp.sum, ← Finset.sum_sub_distrib, ← smul_sub]
    grw [Finsupp.sum, Finsupp.sum, norm_sum_le]
    simp [norm_smul, abs_eq_self.mpr (f.nonneg _), dist_eq_norm_vsub]

instance ConvexSpace.IsMetricCompatible.of_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set E} (H : Convex ℝ S) :
    letI : ConvexSpace ℝ S := .ofConvex H
    IsConvexDist S := by
  letI : ConvexSpace ℝ S := .ofConvex H
  refine ⟨fun f σ₁ σ₂ ↦ .trans ?_ (dist_iConvexCombo_le (X := E) f (σ₁ ·) (σ₂ ·))⟩
  simp [Subtype.dist_eq]

end Convexity
