/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.MeasureTheory.Function.SimpleFunc

#align_import measure_theory.function.simple_func_dense from "leanprover-community/mathlib"@"7317149f12f55affbc900fc873d0d422485122b9"

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `SimpleFunc` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `MeasureTheory.SimpleFunc.approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approxOn` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notations

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/


open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open Classical Topology ENNReal MeasureTheory BigOperators

variable {α β ι E F 𝕜 : Type*}

noncomputable section

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/-- `nearestPtInd e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearestPtInd e N x` returns the least of their indexes. -/
noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearestPtInd e N)
#align measure_theory.simple_func.nearest_pt_ind MeasureTheory.SimpleFunc.nearestPtInd

/-- `nearestPt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearestPt e N x` returns the point with the
least possible index. -/
noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e
#align measure_theory.simple_func.nearest_pt MeasureTheory.SimpleFunc.nearestPt

@[simp]
theorem nearestPtInd_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl
#align measure_theory.simple_func.nearest_pt_ind_zero MeasureTheory.SimpleFunc.nearestPtInd_zero

@[simp]
theorem nearestPt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl
#align measure_theory.simple_func.nearest_pt_zero MeasureTheory.SimpleFunc.nearestPt_zero

theorem nearestPtInd_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x := by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  -- ⊢ (if x ∈ ⋂ (k : ℕ) (_ : k ≤ Nat.add N 0), {x | edist (e (Nat.add N 0 + 1)) x  …
  congr
  -- ⊢ (x ∈ ⋂ (k : ℕ) (_ : k ≤ Nat.add N 0), {x | edist (e (Nat.add N 0 + 1)) x < e …
  simp
  -- 🎉 no goals
#align measure_theory.simple_func.nearest_pt_ind_succ MeasureTheory.SimpleFunc.nearestPtInd_succ

theorem nearestPtInd_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N := by
  induction' N with N ihN; · simp
  -- ⊢ ↑(nearestPtInd e Nat.zero) x ≤ Nat.zero
                             -- 🎉 no goals
  simp only [nearestPtInd_succ]
  -- ⊢ (if ∀ (k : ℕ), k ≤ N → edist (e (N + 1)) x < edist (e k) x then N + 1 else ↑ …
  split_ifs
  -- ⊢ N + 1 ≤ Nat.succ N
  exacts [le_rfl, ihN.trans N.le_succ]
  -- 🎉 no goals
#align measure_theory.simple_func.nearest_pt_ind_le MeasureTheory.SimpleFunc.nearestPtInd_le

theorem edist_nearestPt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
    edist (nearestPt e N x) x ≤ edist (e k) x := by
  induction' N with N ihN generalizing k
  -- ⊢ edist (↑(nearestPt e Nat.zero) x) x ≤ edist (e k) x
  · simp [nonpos_iff_eq_zero.1 hk, le_refl]
    -- 🎉 no goals
  · simp only [nearestPt, nearestPtInd_succ, map_apply]
    -- ⊢ edist (e (if ∀ (k : ℕ), k ≤ N → edist (e (N + 1)) x < edist (e k) x then N + …
    split_ifs with h
    -- ⊢ edist (e (N + 1)) x ≤ edist (e k) x
    · rcases hk.eq_or_lt with (rfl | hk)
      -- ⊢ edist (e (N + 1)) x ≤ edist (e (Nat.succ N)) x
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
      -- 🎉 no goals
    · push_neg at h
      -- ⊢ edist (e (↑(nearestPtInd e N) x)) x ≤ edist (e k) x
      rcases h with ⟨l, hlN, hxl⟩
      -- ⊢ edist (e (↑(nearestPtInd e N) x)) x ≤ edist (e k) x
      rcases hk.eq_or_lt with (rfl | hk)
      -- ⊢ edist (e (↑(nearestPtInd e N) x)) x ≤ edist (e (Nat.succ N)) x
      exacts [(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]
      -- 🎉 no goals
#align measure_theory.simple_func.edist_nearest_pt_le MeasureTheory.SimpleFunc.edist_nearestPt_le

theorem tendsto_nearestPt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) := by
  refine' (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => _
  -- ⊢ ∃ ia, True ∧ ∀ (x_1 : ℕ), x_1 ∈ Set.Ici ia → ↑(nearestPt e x_1) x ∈ ball x ε
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  -- ⊢ ∃ ia, True ∧ ∀ (x_1 : ℕ), x_1 ∈ Set.Ici ia → ↑(nearestPt e x_1) x ∈ ball x ε
  rw [edist_comm] at hN
  -- ⊢ ∃ ia, True ∧ ∀ (x_1 : ℕ), x_1 ∈ Set.Ici ia → ↑(nearestPt e x_1) x ∈ ball x ε
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩
  -- 🎉 no goals
#align measure_theory.simple_func.tendsto_nearest_pt MeasureTheory.SimpleFunc.tendsto_nearestPt

variable [MeasurableSpace β] {f : β → α}

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
noncomputable def approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) : β →ₛ α :=
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : ℕ → α) n) f hf
#align measure_theory.simple_func.approx_on MeasureTheory.SimpleFunc.approxOn

@[simp]
theorem approxOn_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl
#align measure_theory.simple_func.approx_on_zero MeasureTheory.SimpleFunc.approxOn_zero

theorem approxOn_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) (x : β) : approxOn f hf s y₀ h₀ n x ∈ s := by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  -- ⊢ ↑(approxOn f hf s y₀ h₀ n) x ∈ s
  suffices ∀ n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) ∈ s by apply this
  -- ⊢ ∀ (n : ℕ), Nat.casesOn n y₀ (Subtype.val ∘ denseSeq ↑s) ∈ s
  rintro (_ | n)
  -- ⊢ Nat.casesOn Nat.zero y₀ (Subtype.val ∘ denseSeq ↑s) ∈ s
  exacts [h₀, Subtype.mem _]
  -- 🎉 no goals
#align measure_theory.simple_func.approx_on_mem MeasureTheory.SimpleFunc.approxOn_mem

@[simp, nolint simpNF] -- Porting note: LHS doesn't simplify.
theorem approxOn_comp {γ : Type*} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl
#align measure_theory.simple_func.approx_on_comp MeasureTheory.SimpleFunc.approxOn_comp

theorem tendsto_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] {x : β} (hx : f x ∈ closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) := by
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  -- ⊢ Tendsto (fun n => ↑(approxOn f hf s y₀ h₀ n) x) atTop (𝓝 (f x))
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (denseRange_denseSeq s).closure_eq] at hx
  -- ⊢ Tendsto (fun n => ↑(approxOn f hf s y₀ h₀ n) x) atTop (𝓝 (f x))
  simp (config := { iota := false }) only [approxOn, coe_comp]
  -- ⊢ Tendsto (fun n => (↑(nearestPt (fun k => Nat.casesOn k y₀ (Subtype.val ∘ den …
  refine' tendsto_nearestPt (closure_minimal _ isClosed_closure hx)
  -- ⊢ Subtype.val '' closure (Set.range (denseSeq ↑s)) ⊆ closure (Set.range fun k  …
  simp (config := { iota := false }) only [Nat.range_casesOn, closure_union, range_comp]
  -- ⊢ Subtype.val '' closure (Set.range (denseSeq ↑s)) ⊆ closure {y₀} ∪ closure (S …
  exact
    Subset.trans (image_closure_subset_closure_image continuous_subtype_val)
      (subset_union_right _ _)
#align measure_theory.simple_func.tendsto_approx_on MeasureTheory.SimpleFunc.tendsto_approxOn

theorem edist_approxOn_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) {m n : ℕ} (h : m ≤ n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) := by
  dsimp only [approxOn, coe_comp, Function.comp]
  -- ⊢ edist (↑(nearestPt (fun k => Nat.rec y₀ (fun n n_ih => ↑(denseSeq (↑s) n)) k …
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)
  -- 🎉 no goals
#align measure_theory.simple_func.edist_approx_on_mono MeasureTheory.SimpleFunc.edist_approxOn_mono

theorem edist_approxOn_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approxOn_mono hf h₀ x (zero_le n)
#align measure_theory.simple_func.edist_approx_on_le MeasureTheory.SimpleFunc.edist_approxOn_le

theorem edist_approxOn_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := add_le_add_left (edist_approxOn_le hf h₀ x n) _

#align measure_theory.simple_func.edist_approx_on_y0_le MeasureTheory.SimpleFunc.edist_approxOn_y0_le

end SimpleFunc

end MeasureTheory
