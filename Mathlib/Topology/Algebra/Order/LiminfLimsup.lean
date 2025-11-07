/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.DenselyOrdered
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

open Filter TopologicalSpace
open scoped Topology

universe u v

variable {ι α β R S : Type*} {X : ι → Type*}

section LiminfLimsupAdd

variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
  [AddLeftMono α]
  {f : Filter ι} [f.NeBot] {u v : ι → α}

lemma le_limsup_add (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₂ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    (limsup u f) + liminf v f ≤ limsup (u + v) f := by
  have h := isCoboundedUnder_le_add h₄ h₂ -- These `have` tactic improve performance.
  have h' := isBoundedUnder_le_add h₃ h₁
  rw [add_comm] at h h'
  refine add_le_of_forall_lt fun a a_u b b_v ↦ (le_limsup_iff h h').2 fun c c_ab ↦ ?_
  refine ((frequently_lt_of_lt_limsup h₂ a_u).and_eventually
    (eventually_lt_of_lt_liminf b_v h₄)).mono fun _ ab_x ↦ ?_
  exact c_ab.trans (add_lt_add ab_x.1 ab_x.2)

lemma limsup_add_le (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault) :
    limsup (u + v) f ≤ (limsup u f) + limsup v f := by
  have h := isCoboundedUnder_le_add h₁ h₃
  have h' := isBoundedUnder_le_add h₂ h₄
  refine le_add_of_forall_lt fun a a_u b b_v ↦ ?_
  rw [limsup_le_iff h h']
  intro c c_ab
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab

lemma le_liminf_add (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    (liminf u f) + liminf v f ≤ liminf (u + v) f := by
  have h := isCoboundedUnder_ge_add h₂ h₄
  have h' := isBoundedUnder_ge_add h₁ h₃
  refine add_le_of_forall_lt fun a a_u b b_v ↦ ?_
  rw [le_liminf_iff h h']
  intro c c_ab
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)

lemma liminf_add_le (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    liminf (u + v) f ≤ (limsup u f) + liminf v f := by
  have h := isCoboundedUnder_ge_add h₂ h₄
  have h' := isBoundedUnder_ge_add h₁ h₃
  refine le_add_of_forall_lt fun a a_u b b_v ↦ (liminf_le_iff h h').2 fun _ c_ab ↦ ?_
  refine ((frequently_lt_of_liminf_lt h₄ b_v).and_eventually
    (eventually_lt_of_limsup_lt a_u h₂)).mono fun _ ab_x ↦ ?_
  exact (add_lt_add ab_x.2 ab_x.1).trans c_ab

end LiminfLimsupAdd

section LiminfLimsupMul

open Filter Real

variable {f : Filter ι} {u v : ι → ℝ}

lemma le_limsup_mul (h₁ : ∃ᶠ x in f, 0 ≤ u x) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    (limsup u f) * liminf v f ≤ limsup (u * v) f := by
  have h := IsCoboundedUnder.of_frequently_ge (a := 0)
    <| (h₁.and_eventually h₃).mono fun x ⟨ux_0, vx_0⟩ ↦ mul_nonneg ux_0 vx_0
  have h' := isBoundedUnder_le_mul_of_nonneg h₁ h₂ h₃ h₄
  have u0 : 0 ≤ limsup u f := le_limsup_of_frequently_le h₁ h₂
  have uv : 0 ≤ limsup (u * v) f :=
    le_limsup_of_frequently_le ((h₁.and_eventually h₃).mono fun _ ⟨hu, hv⟩ ↦ mul_nonneg hu hv) h'
  refine mul_le_of_forall_lt_of_nonneg u0 uv fun a a0 au b b0 bv ↦ ?_
  refine (le_limsup_iff h h').2 fun c c_ab ↦ ?_
  replace h₁ := IsCoboundedUnder.of_frequently_ge h₁ -- Pre-compute it to gain 4 s.
  have h₅ := frequently_lt_of_lt_limsup h₁ au
  have h₆ := eventually_lt_of_lt_liminf bv (isBoundedUnder_of_eventually_ge h₃)
  apply (h₅.and_eventually (h₆.and h₃)).mono
  exact fun x ⟨xa, ⟨xb, _⟩⟩ ↦ c_ab.trans_le <| mul_le_mul xa.le xb.le b0 (a0.trans xa.le)

lemma limsup_mul_le (h₁ : ∃ᶠ x in f, 0 ≤ u x) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    limsup (u * v) f ≤ (limsup u f) * limsup v f := by
  have h := IsCoboundedUnder.of_frequently_ge (a := 0)
    <| (h₁.and_eventually h₃).mono fun x ⟨ux_0, vx_0⟩ ↦ mul_nonneg ux_0 vx_0
  have h' := isBoundedUnder_le_mul_of_nonneg h₁ h₂ h₃ h₄
  refine le_mul_of_forall_lt₀ fun a a_u b b_v ↦ (limsup_le_iff h h').2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v, h₃]
    with x x_a x_b v_0
  apply lt_of_le_of_lt _ c_ab
  rcases lt_or_ge (u x) 0 with u_0 | u_0
  · apply (mul_nonpos_of_nonpos_of_nonneg u_0.le v_0).trans
    exact mul_nonneg ((le_limsup_of_frequently_le h₁ h₂).trans a_u.le) (v_0.trans x_b.le)
  · exact mul_le_mul x_a.le x_b.le v_0 (u_0.trans x_a.le)

lemma le_liminf_mul [f.NeBot] (h₁ : 0 ≤ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    (liminf u f) * liminf v f ≤ liminf (u * v) f := by
  have h := isCoboundedUnder_ge_mul_of_nonneg h₁ h₂ h₃ h₄
  have h' := isBoundedUnder_of_eventually_ge (a := 0)
    <| (h₁.and h₃).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0
  apply mul_le_of_forall_lt_of_nonneg (le_liminf_of_le h₂.isCoboundedUnder_ge h₁)
    (le_liminf_of_le h ((h₁.and h₃).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0))
  intro a a0 au b b0 bv
  refine (le_liminf_iff h h').2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf au (isBoundedUnder_of_eventually_ge h₁),
    eventually_lt_of_lt_liminf bv (isBoundedUnder_of_eventually_ge h₃)] with x xa xb
  exact c_ab.trans_le (mul_le_mul xa.le xb.le b0 (a0.trans xa.le))

lemma liminf_mul_le [f.NeBot] (h₁ : 0 ≤ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    liminf (u * v) f ≤ (limsup u f) * liminf v f := by
  have h := isCoboundedUnder_ge_mul_of_nonneg h₁ h₂ h₃ h₄
  have h' := isBoundedUnder_of_eventually_ge (a := 0)
    <| (h₁.and h₃).mono fun x ⟨u_0, v_0⟩ ↦ mul_nonneg u_0 v_0
  refine le_mul_of_forall_lt₀ fun a a_u b b_v ↦ (liminf_le_iff h h').2 fun c c_ab ↦ ?_
  refine ((frequently_lt_of_liminf_lt h₄ b_v).and_eventually ((eventually_lt_of_limsup_lt a_u).and
    (h₁.and h₃))).mono fun x ⟨x_v, x_u, u_0, v_0⟩ ↦ ?_
  exact (mul_le_mul x_u.le x_v.le v_0 (u_0.trans x_u.le)).trans_lt c_ab

end LiminfLimsupMul
section LiminfLimsupAddSub
variable [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

/-- `liminf (c + xᵢ) = c + liminf xᵢ`. -/
lemma limsup_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ c + f i) F = c + Filter.limsup f F :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_left c).continuousAt bdd_above cobdd).symm

/-- `limsup (xᵢ + c) = (limsup xᵢ) + c`. -/
lemma limsup_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddRightMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_right c).continuousAt bdd_above cobdd).symm

/-- `liminf (c + xᵢ) = c + liminf xᵢ`. -/
lemma liminf_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c + f i) F = c + Filter.liminf f F :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_left c).continuousAt cobdd bdd_below).symm

/-- `liminf (xᵢ + c) = (liminf xᵢ) + c`. -/
lemma liminf_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddRightMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_right c).continuousAt cobdd bdd_below).symm

/-- `limsup (c - xᵢ) = c - liminf xᵢ`. -/
lemma limsup_const_sub (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSub R] [OrderedSub R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c - f i) F = c - Filter.liminf f F := by
  rcases F.eq_or_neBot with rfl | _
  · simp only [liminf, limsInf, limsup, limsSup, map_bot, eventually_bot, Set.setOf_true]
    simp only [IsCoboundedUnder, IsCobounded, map_bot, eventually_bot, true_implies] at cobdd
    rcases cobdd with ⟨x, hx⟩
    refine (csInf_le ?_ (Set.mem_univ _)).antisymm
      (tsub_le_iff_tsub_le.1 (le_csSup ?_ (Set.mem_univ _)))
    · refine ⟨x - x, mem_lowerBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, true_implies]
      exact tsub_le_iff_tsub_le.1 (hx (x - y))
    · refine ⟨x, mem_upperBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, hx y, implies_true]
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c).continuousAt cobdd bdd_below).symm

/-- `limsup (xᵢ - c) = (limsup xᵢ) - c`. -/
lemma limsup_sub_const (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSub R] [OrderedSub R]
    (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ f i - c) F = Filter.limsup f F - c := by
  rcases F.eq_or_neBot with rfl | _
  · have {a : R} : sInf Set.univ ≤ a := by
      apply csInf_le _ (Set.mem_univ a)
      simp only [IsCoboundedUnder, IsCobounded, map_bot, eventually_bot, true_implies] at cobdd
      rcases cobdd with ⟨x, hx⟩
      refine ⟨x, mem_lowerBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, hx y, implies_true]
    simp only [limsup, limsSup, map_bot, eventually_bot, Set.setOf_true]
    exact this.antisymm (tsub_le_iff_right.2 this)
  · apply (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c) _ _).symm
    · exact fun _ _ h ↦ tsub_le_tsub_right h c
    · exact (continuous_sub_right c).continuousAt

/-- `liminf (c - xᵢ) = c - limsup xᵢ`. -/
lemma liminf_const_sub (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] [AddLeftMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.liminf (fun i ↦ c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c).continuousAt bdd_above cobdd).symm

/-- `liminf (xᵢ - c) = (liminf xᵢ) - c`. -/
lemma liminf_sub_const (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt cobdd bdd_below).symm

end LiminfLimsupAddSub -- section
