/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul

/-!
# Various ways to combine analytic functions

We show that the following are analytic:

1. Cartesian products of analytic functions
2. Arithmetic on analytic functions: `mul`, `smul`, `inv`, `div`
3. Finite sums and products: `Finset.sum`, `Finset.prod`
-/

noncomputable section

open scoped Classical Topology
open Filter Asymptotics ENNReal NNReal

variable {α : Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

variable {𝕝 : Type*} [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

/-!
### Cartesian products are analytic
-/

/-- The radius of the Cartesian product of two formal series is the minimum of their radii. -/
lemma FormalMultilinearSeries.radius_prod_eq_min
    (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    (p.prod q).radius = min p.radius q.radius := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n ↦ ?_).trans this.isBigO
      rw [norm_mul, norm_norm, norm_mul, norm_norm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    · apply le_max_left
    · apply le_max_right
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [lt_min_iff] at hr
    have := ((p.isLittleO_one_of_lt_radius hr.1).add
      (q.isLittleO_one_of_lt_radius hr.2)).isBigO
    refine (p.prod q).le_radius_of_isBigO ((isBigO_of_le _ fun n ↦ ?_).trans this)
    rw [norm_mul, norm_norm, ← add_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    refine (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ?_
    apply Real.le_norm_self

lemma HasFPowerSeriesWithinOnBall.prod {e : E} {f : E → F} {g : E → G} {r s : ℝ≥0∞} {t : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall f p t e r) (hg : HasFPowerSeriesWithinOnBall g q t e s) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f x, g x)) (p.prod q) t e (min r s) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prod_mk (hg.hasSum h'y ?_)
    · exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    · exact EMetric.mem_ball.mpr (lt_of_lt_of_le hy (min_le_right _ _))

lemma HasFPowerSeriesOnBall.prod {e : E} {f : E → F} {g : E → G} {r s : ℝ≥0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesOnBall f p e r) (hg : HasFPowerSeriesOnBall g q e s) :
    HasFPowerSeriesOnBall (fun x ↦ (f x, g x)) (p.prod q) e (min r s) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg

lemma HasFPowerSeriesWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt f p s e) (hg : HasFPowerSeriesWithinAt g q s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma HasFPowerSeriesAt.prod {e : E} {f : E → F} {g : E → G}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesAt f p e) (hg : HasFPowerSeriesAt g q e) :
    HasFPowerSeriesAt (fun x ↦ (f x, g x)) (p.prod q) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
lemma AnalyticWithinAt.prod {e : E} {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinAt 𝕜 f s e) (hg : AnalyticWithinAt 𝕜 g s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
lemma AnalyticAt.prod {e : E} {f : E → F} {g : E → G}
    (hf : AnalyticAt 𝕜 f e) (hg : AnalyticAt 𝕜 g e) :
    AnalyticAt 𝕜 (fun x ↦ (f x, g x)) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions within a set is analytic. -/
lemma AnalyticWithinOn.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g s) :
    AnalyticWithinOn 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- The Cartesian product of analytic functions is analytic. -/
lemma AnalyticOn.prod {f : E → F} {g : E → G} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- `AnalyticAt.comp` for functions on product spaces -/
theorem AnalyticAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {x : E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x)
    (ga : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun x ↦ h (f x, g x)) x :=
  AnalyticAt.comp ha (fa.prod ga)

/-- `AnalyticWithinAt.comp` for functions on product spaces -/
theorem AnalyticWithinAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E} {x : E}
    (ha : AnalyticWithinAt 𝕜 h s (f x, g x)) (fa : AnalyticWithinAt 𝕜 f t x)
    (ga : AnalyticWithinAt 𝕜 g t x) (hf : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) t x :=
  AnalyticWithinAt.comp ha (fa.prod ga) hf

/-- `AnalyticAt.comp_analyticWithinAt` for functions on product spaces -/
theorem AnalyticAt.comp₂_analyticWithinAt
    {h : F × G → H} {f : E → F} {g : E → G} {x : E} {s : Set E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticWithinAt 𝕜 f s x)
    (ga : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) s x :=
  AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

/-- `AnalyticOn.comp` for functions on product spaces -/
theorem AnalyticOn.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)} {t : Set E}
    (ha : AnalyticOn 𝕜 h s) (fa : AnalyticOn 𝕜 f t) (ga : AnalyticOn 𝕜 g t)
    (m : ∀ x, x ∈ t → (f x, g x) ∈ s) : AnalyticOn 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun _ xt ↦ (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)

/-- `AnalyticWithinOn.comp` for functions on product spaces -/
theorem AnalyticWithinOn.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E}
    (ha : AnalyticWithinOn 𝕜 h s) (fa : AnalyticWithinOn 𝕜 f t)
    (ga : AnalyticWithinOn 𝕜 g t) (m : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticWithinOn 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun x hx ↦ (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m

/-- Analytic functions on products are analytic in the first coordinate -/
theorem AnalyticAt.curry_left {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun x ↦ f (x, p.2)) p.1 :=
  AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left

theorem AnalyticWithinAt.curry_left
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun x ↦ f (x, p.2)) {x | (x, p.2) ∈ s} p.1 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the second coordinate -/
theorem AnalyticAt.curry_right {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun y ↦ f (p.1, y)) p.2 :=
  AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right

theorem AnalyticWithinAt.curry_right
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun y ↦ f (p.1, y)) {y | (p.1, y) ∈ s} p.2 :=
  AnalyticWithinAt.comp₂ fa  analyticWithinAt_const analyticWithinAt_id (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the first coordinate -/
theorem AnalyticOn.curry_left {f : E × F → G} {s : Set (E × F)} {y : F} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left
alias AnalyticOn.along_fst := AnalyticOn.curry_left

theorem AnalyticWithinOn.curry_left
    {f : E × F → G} {s : Set (E × F)} {y : F} (fa : AnalyticWithinOn 𝕜 f s) :
    AnalyticWithinOn 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left

/-- Analytic functions on products are analytic in the second coordinate -/
theorem AnalyticOn.curry_right {f : E × F → G} {x : E} {s : Set (E × F)} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right
alias AnalyticOn.along_snd := AnalyticOn.curry_right

theorem AnalyticWithinOn.curry_right
    {f : E × F → G} {x : E} {s : Set (E × F)} (fa : AnalyticWithinOn 𝕜 f s) :
    AnalyticWithinOn 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right

/-!
### Arithmetic on analytic functions
-/

/-- Scalar multiplication is analytic (jointly in both variables). The statement is a little
pedantic to allow towers of field extensions.

TODO: can we replace `𝕜'` with a "normed module" in such a way that `analyticAt_mul` is a special
case of this? -/
lemma analyticAt_smul [NormedSpace 𝕝 E] [IsScalarTower 𝕜 𝕝 E] (z : 𝕝 × E) :
    AnalyticAt 𝕜 (fun x : 𝕝 × E ↦ x.1 • x.2) z :=
  (ContinuousLinearMap.lsmul 𝕜 𝕝).analyticAt_bilinear z

/-- Multiplication in a normed algebra over `𝕜` is analytic. -/
lemma analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A ↦ x.1 * x.2) z :=
  (ContinuousLinearMap.mul 𝕜 A).analyticAt_bilinear z

/-- Scalar multiplication of one analytic function by another. -/
lemma AnalyticWithinAt.smul [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x • g x) s z :=
  (analyticAt_smul _).comp₂_analyticWithinAt hf hg

/-- Scalar multiplication of one analytic function by another. -/
lemma AnalyticAt.smul [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F] {f : E → 𝕝} {g : E → F} {z : E}
    (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (fun x ↦ f x • g x) z :=
  (analyticAt_smul _).comp₂ hf hg

/-- Scalar multiplication of one analytic function by another. -/
lemma AnalyticWithinOn.smul [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g s) :
    AnalyticWithinOn 𝕜 (fun x ↦ f x • g x) s :=
  fun _ m ↦ (hf _ m).smul (hg _ m)

/-- Scalar multiplication of one analytic function by another. -/
lemma AnalyticOn.smul [NormedSpace 𝕝 F] [IsScalarTower 𝕜 𝕝 F] {f : E → 𝕝} {g : E → F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ f x • g x) s :=
  fun _ m ↦ (hf _ m).smul (hg _ m)

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
lemma AnalyticWithinAt.mul {f g : E → A} {s : Set E} {z : E}
    (hf : AnalyticWithinAt 𝕜 f s z) (hg : AnalyticWithinAt 𝕜 g s z) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x * g x) s z :=
  (analyticAt_mul _).comp₂_analyticWithinAt hf hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
lemma AnalyticAt.mul {f g : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : AnalyticAt 𝕜 g z) :
    AnalyticAt 𝕜 (fun x ↦ f x * g x) z :=
  (analyticAt_mul _).comp₂ hf hg

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
lemma AnalyticWithinOn.mul {f g : E → A} {s : Set E}
    (hf : AnalyticWithinOn 𝕜 f s) (hg : AnalyticWithinOn 𝕜 g s) :
    AnalyticWithinOn 𝕜 (fun x ↦ f x * g x) s :=
  fun _ m ↦ (hf _ m).mul (hg _ m)

/-- Multiplication of analytic functions (valued in a normed `𝕜`-algebra) is analytic. -/
lemma AnalyticOn.mul {f g : E → A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ f x * g x) s :=
  fun _ m ↦ (hf _ m).mul (hg _ m)

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
lemma AnalyticWithinAt.pow {f : E → A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z) (n : ℕ) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x ^ n) s z := by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
lemma AnalyticAt.pow {f : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ f x ^ n) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
lemma AnalyticWithinOn.pow {f : E → A} {s : Set E} (hf : AnalyticWithinOn 𝕜 f s) (n : ℕ) :
    AnalyticWithinOn 𝕜 (fun x ↦ f x ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
lemma AnalyticOn.pow {f : E → A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ f x ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

section Geometric

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [NormOneClass A]

/-- The geometric series `1 + x + x ^ 2 + ...` as a `FormalMultilinearSeries`. -/
def formalMultilinearSeries_geometric : FormalMultilinearSeries 𝕜 A A :=
  fun n ↦ ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

lemma formalMultilinearSeries_geometric_apply_norm (n : ℕ) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ = 1 :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin

end Geometric

lemma formalMultilinearSeries_geometric_radius (𝕜) [NontriviallyNormedField 𝕜]
    (A : Type*) [NormedRing A] [NormOneClass A] [NormedAlgebra 𝕜 A] :
    (formalMultilinearSeries_geometric 𝕜 A).radius = 1 := by
  apply le_antisymm
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
    have := FormalMultilinearSeries.isLittleO_one_of_lt_radius _ hr
    simp_rw [formalMultilinearSeries_geometric_apply_norm, one_mul] at this
    contrapose! this
    simp_rw [IsLittleO, IsBigOWith, not_forall, norm_one, mul_one,
      not_eventually]
    refine ⟨1, one_pos, ?_⟩
    refine ((eventually_ne_atTop 0).mp (Eventually.of_forall ?_)).frequently
    intro n hn
    push_neg
    rwa [norm_pow, one_lt_pow_iff_of_nonneg (norm_nonneg _) hn,
      Real.norm_of_nonneg (NNReal.coe_nonneg _), ← NNReal.coe_one,
      NNReal.coe_lt_coe]
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    rw [← Nat.cast_one, ENNReal.coe_lt_natCast, Nat.cast_one] at hr
    apply FormalMultilinearSeries.le_radius_of_isBigO
    simp_rw [formalMultilinearSeries_geometric_apply_norm, one_mul]
    refine isBigO_of_le atTop (fun n ↦ ?_)
    rw [norm_one, Real.norm_of_nonneg (pow_nonneg (coe_nonneg r) _)]
    exact pow_le_one _ (coe_nonneg r) hr.le

lemma hasFPowerSeriesOnBall_inv_one_sub
    (𝕜 𝕝 : Type*) [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] :
    HasFPowerSeriesOnBall (fun x : 𝕝 ↦ (1 - x)⁻¹) (formalMultilinearSeries_geometric 𝕜 𝕝) 0 1 := by
  constructor
  · exact le_of_eq (formalMultilinearSeries_geometric_radius 𝕜 𝕝).symm
  · exact one_pos
  · intro y hy
    simp_rw [zero_add, formalMultilinearSeries_geometric,
        ContinuousMultilinearMap.mkPiAlgebraFin_apply,
        List.prod_ofFn, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    apply hasSum_geometric_of_norm_lt_one
    simpa only [← ofReal_one, Metric.emetric_ball, Metric.ball,
      dist_eq_norm, sub_zero] using hy

lemma analyticAt_inv_one_sub (𝕝 : Type*) [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝] :
    AnalyticAt 𝕜 (fun x : 𝕝 ↦ (1 - x)⁻¹) 0 :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inv_one_sub 𝕜 𝕝⟩⟩

/-- If `𝕝` is a normed field extension of `𝕜`, then the inverse map `𝕝 → 𝕝` is `𝕜`-analytic
away from 0. -/
lemma analyticAt_inv {z : 𝕝} (hz : z ≠ 0) : AnalyticAt 𝕜 Inv.inv z := by
  let f1 : 𝕝 → 𝕝 := fun a ↦ 1 / z * a
  let f2 : 𝕝 → 𝕝 := fun b ↦ (1 - b)⁻¹
  let f3 : 𝕝 → 𝕝 := fun c ↦ 1 - c / z
  have feq : f1 ∘ f2 ∘ f3 = Inv.inv := by
    ext1 x
    dsimp only [f1, f2, f3, Function.comp_apply]
    field_simp
  have f3val : f3 z = 0 := by simp only [f3, div_self hz, sub_self]
  have f3an : AnalyticAt 𝕜 f3 z := by
    apply analyticAt_const.sub
    simpa only [div_eq_inv_mul] using analyticAt_const.mul analyticAt_id
  exact feq ▸ (analyticAt_const.mul analyticAt_id).comp
    ((f3val.symm ▸ analyticAt_inv_one_sub 𝕝).comp f3an)

/-- `x⁻¹` is analytic away from zero -/
lemma analyticOn_inv : AnalyticOn 𝕜 (fun z ↦ z⁻¹) {z : 𝕝 | z ≠ 0} := by
  intro z m; exact analyticAt_inv m

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
theorem AnalyticWithinAt.inv {f : E → 𝕝} {x : E} {s : Set E}
    (fa : AnalyticWithinAt 𝕜 f s x) (f0 : f x ≠ 0) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f x)⁻¹) s x :=
  (analyticAt_inv f0).comp_analyticWithinAt fa

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
theorem AnalyticAt.inv {f : E → 𝕝} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x ≠ 0) :
    AnalyticAt 𝕜 (fun x ↦ (f x)⁻¹) x :=
  (analyticAt_inv f0).comp fa

/-- `x⁻¹` is analytic away from zero -/
theorem AnalyticWithinOn.inv {f : E → 𝕝} {s : Set E}
    (fa : AnalyticWithinOn 𝕜 f s) (f0 : ∀ x ∈ s, f x ≠ 0) :
    AnalyticWithinOn 𝕜 (fun x ↦ (f x)⁻¹) s :=
  fun x m ↦ (fa x m).inv (f0 x m)

/-- `x⁻¹` is analytic away from zero -/
theorem AnalyticOn.inv {f : E → 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : ∀ x ∈ s, f x ≠ 0) :
    AnalyticOn 𝕜 (fun x ↦ (f x)⁻¹) s :=
  fun x m ↦ (fa x m).inv (f0 x m)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticWithinAt.div {f g : E → 𝕝} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : g x ≠ 0) :
    AnalyticWithinAt 𝕜 (fun x ↦ f x / g x) s x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticAt.div {f g : E → 𝕝} {x : E}
    (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x ≠ 0) :
    AnalyticAt 𝕜 (fun x ↦ f x / g x) x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticWithinOn.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticWithinOn 𝕜 f s) (ga : AnalyticWithinOn 𝕜 g s) (g0 : ∀ x ∈ s, g x ≠ 0) :
    AnalyticWithinOn 𝕜 (fun x ↦ f x / g x) s := fun x m ↦
  (fa x m).div (ga x m) (g0 x m)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticOn.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) (g0 : ∀ x ∈ s, g x ≠ 0) :
    AnalyticOn 𝕜 (fun x ↦ f x / g x) s := fun x m ↦
  (fa x m).div (ga x m) (g0 x m)

/-!
### Finite sums and products of analytic functions
-/

/-- Finite sums of analytic functions are analytic -/
theorem Finset.analyticWithinAt_sum {f : α → E → F} {c : E} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (fun z ↦ ∑ n ∈ N, f n z) s c := by
  induction' N using Finset.induction with a B aB hB
  · simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  · simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m ↦ h b (Or.inr m))

/-- Finite sums of analytic functions are analytic -/
theorem Finset.analyticAt_sum {f : α → E → F} {c : E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (fun z ↦ ∑ n ∈ N, f n z) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

/-- Finite sums of analytic functions are analytic -/
theorem Finset.analyticWithinOn_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinOn 𝕜 (f n) s) :
    AnalyticWithinOn 𝕜 (fun z ↦ ∑ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticWithinAt_sum (fun n m ↦ h n m z zs)

/-- Finite sums of analytic functions are analytic -/
theorem Finset.analyticOn_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (fun z ↦ ∑ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticAt_sum (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticWithinAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s c := by
  induction' N using Finset.induction with a B aB hB
  · simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  · simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m ↦ h b (Or.inr m))

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_prod h

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticWithinOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinOn 𝕜 (f n) s) :
    AnalyticWithinOn 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticWithinAt_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticAt_prod (fun n m ↦ h n m z zs)
