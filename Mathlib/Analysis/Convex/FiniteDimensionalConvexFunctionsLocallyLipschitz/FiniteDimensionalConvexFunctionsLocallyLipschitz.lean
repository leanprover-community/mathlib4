/-
Copyright (c) 2024 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.FiniteDimensionalConvexFunctionsLocallyLipschitz.l1Space
/-!
# Finite-Dimensional Convex Functions and Their Lipschitz Properties

Each convex function on an open convex subset of FiniteDimensional space
is Lipschitz continuous, so that continuous.

During proving , the real difficulty lies in “LocallyUpperBounded”.
Given a convex open set s in a finite dimensional spac , and f is convex on s ,
it wants us to find a convex open subset t of s ,which is
a neighborhood of x and f is upper bounded on t.
We use the interior of the convex hull t formed by the vectors which
the basis multiplied by the appropriate coefficient to make it a subset (int t) of s.

The remaining difficulty is to prove x ∈ int t which
is equivalent to proving that ∃ open set u ⊆ t.
The crucial point is that we use the ball in l₁ space as u.

## Main Results

* `Lipschitz_of_UpperBounded` :Let X be a normed space, x₀ ∈ X, r > 0.
Let f : B(x₀, r) → ℝ be a convex function.
If f(x) ≤ m on B(x₀, r) and ε ∈ (0, r),then f is  Lipschitz on B(x₀, r − ε).

* `LocallyLipschitzOn_of_UpperBounded`: Let X be a normed space, x₀ ∈ X, r > 0.
Let f : B(x₀, r) → ℝ  be a convex function.
If f is upper bounded on a open subset of s , then f is locally Lipschitz on s

* `LocallyUpperBounded` : Finite dimensional convex functions are locally upper bounded
on convex open sets. Let s is open convex set and f : s → ℝ be a convex function,
then there exist a convex open set in s and f is upperbounded on s.

* `FiniDeimensionalConvexFunctionsLocallyLipschitz` :
Each convex function on an open convex subset of FiniteDimensional space is locally Lipschitz

* `FiniDeimensionalConvexFunctionsContinous` : Each convex function on an open convex subset
of FiniteDimensional space is continuous

-/
open Set InnerProductSpace Topology Filter Metric Bornology Real FiniteDimensional

open scoped Pointwise

/-! ### Boundedness of convex function in a normed space -/

section Boundedness


variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    {x₀ : X}{r : ℝ}{f : X → ℝ}

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is upperbounded on B(x₀, r), then bounded on B(x₀, r).
-/
lemma Bounded_of_UpperBounded (hf : ConvexOn ℝ (ball x₀ r) f)
    (f_upperbounded: BddAbove (f '' (ball x₀ r))) : IsBounded (f '' (ball x₀ r)) := by
  dsimp [BddAbove,upperBounds]at f_upperbounded
  rcases f_upperbounded with ⟨m,hm⟩
  simp only [mem_image, mem_ball, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_setOf_eq] at hm
  rw[isBounded_iff_subset_ball 0]
  use |m| + 2 * (|f x₀| + 1)
  intro fx hfx
  simp only [mem_ball, dist_zero_right, Real.norm_eq_abs]
  simp only [mem_image, mem_ball] at hfx
  rcases hfx with ⟨x , hx⟩
  rw[convexOn_iff_forall_pos] at hf
  have x_pos : x ∈ ball x₀ r := hx.1
  let y := ((2 : ℝ) • x₀ - x)
  have y_pos : y ∈ ball x₀ r := by
    simp only [mem_ball, dist_sub_eq_dist_add_left, y ,two_smul,dist_add_left]
    rw[dist_comm]
    apply hx.1
  let a :=  (1 : ℝ) / 2
  have a_pos : 0 < a := by norm_num
  have eq_one : a + a = 1 := by norm_num
  have h := hf.2 x_pos y_pos a_pos a_pos eq_one
  have : x₀ = a • x + a • y := by
    simp only [y]
    rw[smul_sub]
    simp only [add_sub_cancel, a]
    rw[← mul_smul]
    simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      IsUnit.inv_mul_cancel, one_smul]
  rw[← this] at h
  rw[abs_lt,← hx.2]
  simp only [smul_eq_mul, a] at h
  have h' : - f y + 2 * f x₀  ≤  f x := by linarith
  have fy_pos : - |m| ≤ - f y := by
    simp only [neg_le_neg_iff, ge_iff_le]
    apply le_trans (hm y y_pos) (le_abs_self m)
  constructor
  · calc
      _ = -|m| - 2 * (|f x₀| + 1):= neg_add' |m| (2 * (|f x₀| + 1))
      _ <  -f y + 2 * f x₀ := by
        apply add_lt_add_of_le_of_lt fy_pos
        rw[← mul_neg]
        simp only [Nat.ofNat_pos, mul_lt_mul_left,neg_add']
        calc
          _ < -|f x₀| :=by simp only [sub_lt_self_iff, zero_lt_one]
          _ ≤ _ := neg_abs_le (f x₀)
      _ ≤ _ := h'
  · calc
      _ ≤ m := by apply hm x hx.1
      _ ≤ |m| := le_abs_self m
      _ < _ := by
        simp only [lt_add_iff_pos_right, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
        linarith [abs_nonneg (f x₀)]

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is bounded on B(x₀, r) and ε ∈ (0, r), then f is Lipschitz on B(x₀, r − ε).
-/
lemma Lipschitz_of_Bounded [T0Space X](hf : ConvexOn ℝ (ball x₀ r) f)
    (f_bounded: IsBounded (f '' (ball x₀ r)))
    {ε : ℝ}(hε :0 < ε ∧ ε < r): ∃ K , LipschitzOnWith K f (ball x₀ (r - ε)) := by
  rw[isBounded_iff_subset_ball 0] at f_bounded
  rcases f_bounded with ⟨M , hM⟩
  let K := 2 * |M| / ε
  have K_pos : K ≥ 0 := by
    apply div_nonneg
    apply mul_nonneg
    norm_num
    apply abs_nonneg
    apply le_of_lt hε.1
  use ⟨K , K_pos⟩
  dsimp [LipschitzOnWith]
  intro x hx y hy
  --type conversion
  rw[edist_dist,edist_dist]
  rw[ENNReal.coe_nnreal_eq]
  simp only [NNReal.coe_mk, ge_iff_le]
  rw[← ENNReal.ofReal_mul K_pos]
  rw[ENNReal.ofReal_le_ofReal_iff (mul_nonneg K_pos dist_nonneg)]
  --type conversion
  rw[Real.dist_eq,dist_eq_norm]
  rw[convexOn_iff_forall_pos] at hf

  have oneside {uy vx : X}(h : uy ≠ vx)
      (hu : uy ∈ ball x₀ (r - ε))(hv : vx ∈ ball x₀ (r - ε))
      :f uy - f vx ≤ K * ‖uy - vx‖ := by
    have sub : ball x₀ (r - ε) ⊆ ball x₀ r := by
        apply ball_subset_ball
        linarith
    have vx_pos :  vx ∈ ball x₀ r := sub hv
    have uy_pos :  uy ∈ ball x₀ r := sub hu
    let z := uy + (ε / ‖uy - vx‖) • (uy - vx)
    have sub_pos : 0 < ‖uy - vx‖ := by
      apply norm_pos_iff'.mpr
      exact sub_ne_zero_of_ne h
    have z_pos : z ∈ ball x₀ r := by
      simp only [mem_ball,dist_eq_norm,z]
      calc
        _ = ‖(uy - x₀) + (ε / ‖uy - vx‖) • (uy - vx)‖ := by
          congr
          apply add_sub_right_comm uy ((ε / ‖uy - vx‖) • (uy - vx)) x₀
        _ ≤ ‖uy - x₀‖ + ‖(ε / ‖uy - vx‖) • (uy - vx)‖ := by
          exact norm_add_le (uy - x₀) ((ε / ‖uy - vx‖) • (uy - vx))
        _ < (r - ε) + ε := by
          apply add_lt_add_of_lt_of_le
          rw [mem_ball , dist_eq_norm] at hu
          apply hu
          calc
            _ = ‖ε / ‖uy - vx‖‖ * ‖uy - vx‖ := norm_smul (ε / ‖uy - vx‖) (uy - vx)
            _ = |ε| / ‖uy - vx‖ * ‖uy - vx‖ := by simp
            _ = ε / ‖uy - vx‖ * ‖uy - vx‖ := by
              rw[abs_of_pos hε.1]
            _ = ε := by
              apply div_mul_cancel₀
              exact Ne.symm (ne_of_lt sub_pos)
            _ ≤ _ := Preorder.le_refl ε
        _ = r := by linarith
    let a := ε / (ε + ‖uy - vx‖)
    let b := ‖uy - vx‖ / (ε + ‖uy - vx‖)
    have :=(add_pos_of_pos_of_nonneg hε.1 (norm_nonneg (uy - vx)))
    have a_pos : 0 < a := by
      apply div_pos hε.1 this
    have b_pos : 0 < b := by
      apply div_pos
      rw[norm_pos_iff']
      exact sub_ne_zero_of_ne h
      apply this
    have a_add_b_one : a + b = 1 := by
      simp[a,b]
      field_simp
    have z_eq : z = uy + (a / b) • (uy - vx) := by
      have : a / b = ε / ‖uy - vx‖ := by
        simp[a,b]
        apply div_div_div_cancel_right ε
        linarith
      rw[this]
    have h_combin: uy = a • vx + b • z := by
      rw[z_eq]
      simp only [smul_add]
      rw[← mul_smul]
      field_simp
      rw[smul_sub,add_sub,← add_smul,add_comm b a,a_add_b_one]
      simp only [one_smul, add_sub_cancel]
    have h := hf.2 vx_pos z_pos a_pos b_pos a_add_b_one
    have h1 : (ε + ‖uy - vx‖) * f uy ≤ ε * f vx + ‖uy - vx‖ * f z:= by
      rw[← h_combin] at h
      simp[a,b] at h
      rw[← mul_le_mul_left this] at h
      field_simp at h
      exact h
    have h2 : ε * (f uy - f vx) ≤ 2 * M * ‖uy - vx‖ := by
      calc
        _ ≤ (f z - f uy) * ‖uy - vx‖ := by
          rw[add_mul] at h1
          nth_rw 2 [add_comm] at h1
          rw[← sub_le_sub_iff,← mul_sub,← mul_sub] at h1
          nth_rw 2 [mul_comm] at h1
          apply h1
        _ ≤ _ := by
          have fzbounded:= hM ⟨z ,⟨z_pos , rfl⟩⟩
          simp only [mem_ball, dist_zero_right, norm_eq_abs] at fzbounded
          have fuybounded:= hM ⟨uy ,⟨uy_pos , rfl⟩⟩
          simp only [mem_ball, dist_zero_right, norm_eq_abs] at fuybounded
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg (uy - vx))
          calc
            _ ≤ |f z - f uy| :=le_abs_self (f z - f uy)
            _ ≤ |f z| + |f uy|:=abs_sub (f z) (f uy)
            _ ≤ M + M :=by linarith
            _ = 2 * M :=by linarith
    calc
      _ ≤ 2 * M * ‖uy - vx‖ / ε := by rwa[le_div_iff' hε.1]
      _ = (2 * M / ε) * ‖uy - vx‖ := by ring
      _ ≤ _ := by
        simp[K]
        apply mul_le_mul_of_nonneg_right _ (le_of_lt sub_pos)
        rw[div_le_div_right hε.1]
        apply mul_le_mul_of_nonneg_left
        apply le_abs_self
        norm_num
  by_cases h : x = y
  · rw[h]
    simp only [sub_self, abs_zero, norm_zero, mul_zero, le_refl]
  · push_neg at h;
    rw[abs_le]
    constructor
    · rw[neg_le,neg_sub,norm_sub_rev]
      apply oneside h.symm hy hx
    · apply oneside h hx hy

/--
Let X be a normed space, x₀ ∈ X, r > 0.Let f : B(x₀, r) → R be a convex function.
If f is upperbounded on B(x₀, r) and ε ∈ (0, r)
then f is Lipschitz on B(x₀, r − ε).
-/
theorem Lipschitz_of_UpperBounded [T0Space X](hf : ConvexOn ℝ (ball x₀ r) f)
    (f_upperbounded: BddAbove (f '' (ball x₀ r)))
    {ε : ℝ}(hε :0 < ε ∧ ε < r): ∃ K , LipschitzOnWith K f (ball x₀ (r - ε)) := by
  apply Lipschitz_of_Bounded hf _ hε
  apply Bounded_of_UpperBounded hf f_upperbounded

/--
If f is upper bounded on a open subset of s ,
then f is locally Lipschitz on s
-/
theorem LocallyLipschitzOn_of_UpperBounded [T0Space X]{s : Set X}(hs : IsOpen s)
    (f_upperbounded : BddAbove (f '' s)) (f_convex : ConvexOn ℝ s f):
    LocallyLipschitzOn s f := by
  dsimp [LocallyLipschitzOn]
  intro x hx
  rw[exists_comm]
  rw[Metric.isOpen_iff] at hs
  rcases hs x hx with ⟨r , hr⟩
  have : ball x (r / 2) ∈ 𝓝[s] x := by
    apply mem_nhdsWithin_of_mem_nhds
    apply ball_mem_nhds x
    linarith
  use ball x (r - r / 2)
  rw[exists_and_left]
  constructor
  · have eq_r : r - r / 2 = r / 2 := by linarith
    rw[eq_r]
    apply this
  · apply Lipschitz_of_UpperBounded
    apply ConvexOn.subset f_convex hr.2
    exact convex_ball x r
    apply BddAbove.mono _ f_upperbounded
    apply image_mono hr.2
    norm_num
    exact hr.1

end Boundedness

/-! ### Locally Boundedness of convex function in a finite dimensional space -/

section LocallyBoundedness

variable {α : Type*}
    [NormedAddCommGroup α] [InnerProductSpace ℝ α] [FiniteDimensional ℝ α]
    {f : α → ℝ}{s : Set α}
/--
Let X be a finite dimensional space.Let s is open convex set and f : s → R be a convex function.
Then ∃ open convex set t which contain x , and f is upperbounded on t.
-/
lemma LocallyUpperBounded (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)
    (hf : ConvexOn ℝ s f) : ∀ x ∈ s , ∃ t ∈ 𝓝[s] x ,Convex ℝ t ∧ IsOpen t ∧ BddAbove (f '' t) := by
  rw[Metric.isOpen_iff] at hs_isopen
  intro x hx
  rcases hs_isopen x hx with ⟨r₀ , hr₀⟩

  let r := r₀ / 2
  have r_pos : r > 0 := by simp[r];apply hr₀.1
  let n := finrank ℝ α
  let ι := Fin n
  let b := finBasis ℝ α
  have bi_pos : ∀ i : ι , ‖b i‖ ≠ 0 := by
    intro i
    refine norm_ne_zero_iff.mpr ?_
    exact Basis.ne_zero b i
  change Basis ι ℝ α at b
  by_cases hn : n = 0
  · have :  finrank ℝ α = 0 := by
      show n = 0;apply hn;
    rw[FiniteDimensional.finrank_zero_iff] at this
    use s
    simp only [isOpen_discrete, true_and]
    constructor
    exact self_mem_nhdsWithin
    refine ⟨hs_convex, ?h.right.right⟩
    simp[BddAbove]
    use f x
    simp[upperBounds]
    intro a _
    have : a = x := by apply Subsingleton.allEq
    rw[this]
  have n_pos : n > 0 := Nat.zero_lt_of_ne_zero hn

  let fin0 : ι := ⟨0, n_pos⟩

  let u₀ := (⋃ (i : ι), {(r / ‖b i‖) • (b i)})  ∪  (⋃ (i : ι),{- (r / ‖b i‖) • (b i)})
  let u := {x} + u₀
  have u₀_isFinite : u₀.Finite := by
    apply Set.Finite.union
    <;>{
      apply Set.finite_iUnion
      intro i
      apply finite_singleton
      }
  have u_isFinite : u.Finite := by
    apply Set.Finite.add
    exact finite_singleton x
    apply u₀_isFinite
  have u_pos : u ⊆ s := by
    intro y hy
    simp [u,u₀] at hy
    rcases hy with ⟨i , hi⟩ | ⟨i , hi⟩
    · have : y = (r / ‖b i‖) • b i + x:= by
        rw[hi];
        simp only [neg_add_cancel_comm];
      rw[this]
      apply hr₀.2
      simp only [mem_ball, dist_self_add_left,dist_add_self_left]
      rw[norm_smul,norm_div,norm_norm,div_mul_cancel₀]
      simp[r]
      calc
        _ = r₀ / 2:= by rw[abs_of_pos hr₀.1]
        _ < r₀ := by linarith
      apply bi_pos
    · have :  y = - (r / ‖b i‖) • b i + x:= by
        rw[← neg_smul] at hi
        rw[hi]
        simp only [neg_add_cancel_comm]
      rw[this]
      apply hr₀.2
      simp only [mem_ball, dist_self_add_left,dist_add_self_left,neg_smul, norm_neg]
      rw[norm_smul,norm_div,norm_norm,div_mul_cancel₀]
      simp[r]
      calc
        _ = r₀ / 2:= by rw[abs_of_pos hr₀.1]
        _ < r₀ := by linarith
      apply bi_pos

  let U := convexHull ℝ u
  let t := interior U
  use t
  have t_isopen : IsOpen t := isOpen_interior

  let xBall :=  σ.toFun ⁻¹' (ball (σ.toFun x) r)

  have xBall_isopen : IsOpen xBall:= by
    simp[xBall]
    apply Continuous.isOpen_preimage (ContinuousLinearMap.continuous σ)
    exact isOpen_ball
  have x_in_xBall : x ∈ xBall := by
    simp[xBall]
    exact r_pos
  have xBall_in_U : xBall ⊆ U := by
    apply l1Ball_sub_convexHull r_pos hn
  have x_in_t : x ∈ t := by
    apply mem_interior.mpr
    use xBall
  constructor
  · rw[mem_nhdsWithin]
    use t , t_isopen , x_in_t
    simp only [inter_subset_left]
  constructor
  · apply Convex.interior (convex_convexHull ℝ u)
  constructor
  · exact t_isopen
  let u' := Set.Finite.toFinset u_isFinite
  have u_nonempty : Finset.Nonempty u':= by
    use x + (r / ‖b fin0‖) • b fin0
    simp[u',u,u₀]
  use (Finset.sup' u' u_nonempty f)
  intro fx hfx
  rcases hfx with ⟨x₁ , hx₁⟩
  rw[← hx₁.2]
  have hf : ConvexOn ℝ  ((convexHull ℝ) u') f := by
    apply ConvexOn.subset hf _ (convex_convexHull ℝ ↑u')
    rw[Convex.convexHull_subset_iff hs_convex]
    simp[u'];exact u_pos;
  have t_pos : t ⊆ U := by
    simp[t];apply interior_subset
  have hx : x₁ ∈ (convexHull ℝ) u' := by
    simp[u'];apply t_pos hx₁.1
  apply le_sup_of_mem_convexHull hf hx

lemma LocallyLipschitz_of_LocallyUpperBounded (hs : IsOpen s)
    (h : ∀ x ∈ s , ∃ t ∈ 𝓝[s] x , Convex ℝ t ∧ IsOpen t ∧ BddAbove (f '' t))
    (hf : ConvexOn ℝ s f)
    : LocallyLipschitzOn s f := by
  dsimp [LocallyLipschitzOn]
  intro x hx
  rcases h x hx with ⟨t , ht⟩
  have t_isOpen := ht.2.2.1
  have isopen : IsOpen (t ∩ s) := IsOpen.inter t_isOpen hs
  have x_pos : x ∈ (t ∩ s) := by
    apply mem_inter _ hx
    rcases mem_nhdsWithin.1 ht.1 with ⟨u,hu⟩
    exact hu.2.2 (mem_inter hu.2.1 hx)
  rw[Metric.isOpen_iff] at isopen
  rcases isopen x x_pos with ⟨r , hr⟩
  rw[exists_comm]
  have : ball x (r / 2) ∈ 𝓝[s] x := by
    apply mem_nhdsWithin_of_mem_nhds
    apply ball_mem_nhds x
    linarith
  use ball x (r - r / 2)
  rw[exists_and_left]
  constructor
  · have eq_r : r - r / 2 = r / 2 := by linarith
    rw[eq_r];
    exact this
  · apply Lipschitz_of_UpperBounded
    have ball_s: ball x r ⊆ s := Set.Subset.trans hr.2 inter_subset_right
    apply ConvexOn.subset hf ball_s
    apply convex_ball x r
    apply BddAbove.mono _ ht.2.2.2
    have ball_t: ball x r ⊆ t := Set.Subset.trans hr.2 inter_subset_left
    apply image_mono ball_t
    norm_num
    exact hr.1

end LocallyBoundedness

/-! ### Continuity of convex function in a finite dimensional space -/

section Continuity

variable {α : Type*}{β : Type*}
    [NormedAddCommGroup α] [InnerProductSpace ℝ α] [FiniteDimensional ℝ α]
    {f : α → ℝ}{s : Set α}

/-
Each convex function on an open convex subset of FiniteDimensional space
is locally Lipschitz
-/
theorem FiniDeimensionalConvexFunctionsLocallyLipschitz
    (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)(hf : ConvexOn ℝ s f)
    : LocallyLipschitzOn s f :=by
  apply LocallyLipschitz_of_LocallyUpperBounded hs_isopen _ hf
  apply LocallyUpperBounded hs_convex hs_isopen hf

/-
Each convex function on an open convex subset of FiniteDimensional space
is continuous
-/
theorem FiniDeimensionalConvexFunctionsContinous
    (hs_convex : Convex ℝ s)(hs_isopen : IsOpen s)(hf : ConvexOn ℝ s f)
    : ContinuousOn f s := by
  apply LocallyLipschitzOn.continuousOn
  apply FiniDeimensionalConvexFunctionsLocallyLipschitz hs_convex hs_isopen hf

end Continuity
