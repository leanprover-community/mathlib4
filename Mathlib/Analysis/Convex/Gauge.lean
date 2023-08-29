/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.NormedSpace.Pointwise
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Data.IsROrC.Basic

#align_import analysis.convex.gauge from "leanprover-community/mathlib"@"373b03b5b9d0486534edbe94747f23cb3712f93d"

/-!
# The Minkowski functional

This file defines the Minkowski functional, aka gauge.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a real vector space,
* `gauge`: Aka Minkowski functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gaugeSeminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

Minkowski functional, gauge
-/

set_option autoImplicit true


open NormedField Set
open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E F : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ x ∈ r • s }
#align gauge gauge

variable {s t : Set E} {a : ℝ}

theorem gauge_def : gauge s x = sInf ({ r ∈ Set.Ioi (0 : ℝ) | x ∈ r • s }) :=
  rfl
#align gauge_def gauge_def

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
theorem gauge_def' : gauge s x = sInf {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • x ∈ s} := by
  congrm sInf {r | ?_}
  -- ⊢ 0 < r ∧ x ∈ r • s ↔ r ∈ Ioi 0 ∧ r⁻¹ • x ∈ s
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _
  -- 🎉 no goals
#align gauge_def' gauge_def'

private theorem gauge_set_bddBelow : BddBelow { r : ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun _ hr => hr.1.le⟩

/-- If the given subset is `Absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) :
    { r : ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := absorbs x
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge⟩
#align absorbent.gauge_set_nonempty Absorbent.gauge_set_nonempty

theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun _ =>
  csInf_le_csInf gauge_set_bddBelow hs.gauge_set_nonempty fun _ hr => ⟨hr.1, smul_set_mono h hr.2⟩
#align gauge_mono gauge_mono

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  -- ⊢ ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s
  exact ⟨b, hb, hba, hx⟩
  -- 🎉 no goals
#align exists_lt_of_gauge_lt exists_lt_of_gauge_lt

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • 0 ∈ s} = 0
  by_cases h : (0 : E) ∈ s
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • 0 ∈ s} = 0
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
    -- 🎉 no goals
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]
    -- 🎉 no goals
#align gauge_zero gauge_zero

@[simp]
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext x
  -- ⊢ gauge 0 x = OfNat.ofNat 0 x
  rw [gauge_def']
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ 0} = OfNat.ofNat 0 x
  obtain rfl | hx := eq_or_ne x 0
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • 0 ∈ 0} = OfNat.ofNat 0 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, eq_self_iff_true, sep_true, smul_zero]
    -- 🎉 no goals
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    -- ⊢ sInf {r | r ∈ Ioi 0 ∧ (r = 0 ∨ x = 0)} = 0
    convert Real.sInf_empty
    -- ⊢ {r | r ∈ Ioi 0 ∧ (r = 0 ∨ x = 0)} = ∅
    exact eq_empty_iff_forall_not_mem.2 fun r hr => hr.2.elim (ne_of_gt hr.1) hx
    -- 🎉 no goals
#align gauge_zero' gauge_zero'

@[simp]
theorem gauge_empty : gauge (∅ : Set E) = 0 := by
  ext
  -- ⊢ gauge ∅ x✝ = OfNat.ofNat 0 x✝
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]
  -- 🎉 no goals
#align gauge_empty gauge_empty

theorem gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  -- ⊢ gauge ∅ = 0
  exacts [gauge_empty, gauge_zero']
  -- 🎉 no goals
#align gauge_of_subset_zero gauge_of_subset_zero

/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.sInf_nonneg _ fun _ hx => hx.1.le
#align gauge_nonneg gauge_nonneg

theorem gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x := by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  -- ⊢ gauge s (-x) = gauge s x
  simp_rw [gauge_def', smul_neg, this]
  -- 🎉 no goals
#align gauge_neg gauge_neg

theorem gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x := by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]
  -- 🎉 no goals
#align gauge_neg_set_neg gauge_neg_set_neg

theorem gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) := by
  rw [← gauge_neg_set_neg, neg_neg]
  -- 🎉 no goals
#align gauge_neg_set_eq_gauge_neg gauge_neg_set_eq_gauge_neg

theorem gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a := by
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ gauge s x ≤ 0
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
    -- 🎉 no goals
  · exact csInf_le gauge_set_bddBelow ⟨ha', hx⟩
    -- 🎉 no goals
#align gauge_le_of_mem gauge_le_of_mem

theorem gauge_le_eq (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : Absorbent ℝ s) (ha : 0 ≤ a) :
    { x | gauge s x ≤ a } = ⋂ (r : ℝ) (_ : a < r), r • s := by
  ext x
  -- ⊢ x ∈ {x | gauge s x ≤ a} ↔ x ∈ ⋂ (r : ℝ) (_ : a < r), r • s
  simp_rw [Set.mem_iInter, Set.mem_setOf_eq]
  -- ⊢ gauge s x ≤ a ↔ ∀ (i : ℝ), a < i → x ∈ i • s
  refine' ⟨fun h r hr => _, fun h => le_of_forall_pos_lt_add fun ε hε => _⟩
  -- ⊢ x ∈ r • s
  · have hr' := ha.trans_lt hr
    -- ⊢ x ∈ r • s
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    -- ⊢ r⁻¹ • x ∈ s
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    -- ⊢ r⁻¹ • x ∈ s
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    -- ⊢ (r⁻¹ * δ) • δ⁻¹ • x ∈ s
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    -- ⊢ (r⁻¹ * δ) • δ⁻¹ • x ∈ s
    refine' hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, _⟩
    -- ⊢ r⁻¹ * δ ≤ 1
    rw [inv_mul_le_iff hr', mul_one]
    -- ⊢ δ ≤ r
    exact hδr.le
    -- 🎉 no goals
  · have hε' := (lt_add_iff_pos_right a).2 (half_pos hε)
    -- ⊢ gauge s x < a + ε
    exact
      (gauge_le_of_mem (ha.trans hε'.le) <| h _ hε').trans_lt (add_lt_add_left (half_lt_self hε) _)
#align gauge_le_eq gauge_le_eq

theorem gauge_lt_eq' (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ (r : ℝ) (_ : 0 < r) (_ : r < a), r • s := by
  ext
  -- ⊢ x✝ ∈ {x | gauge s x < a} ↔ x✝ ∈ ⋃ (r : ℝ) (_ : 0 < r) (_ : r < a), r • s
  simp_rw [mem_setOf, mem_iUnion, exists_prop]
  -- ⊢ gauge s x✝ < a ↔ ∃ i, 0 < i ∧ i < a ∧ x✝ ∈ i • s
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩
#align gauge_lt_eq' gauge_lt_eq'

theorem gauge_lt_eq (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ r ∈ Set.Ioo 0 (a : ℝ), r • s := by
  ext
  -- ⊢ x✝ ∈ {x | gauge s x < a} ↔ x✝ ∈ ⋃ (r : ℝ) (_ : r ∈ Ioo 0 a), r • s
  simp_rw [mem_setOf, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  -- ⊢ gauge s x✝ < a ↔ ∃ i, 0 < i ∧ i < a ∧ x✝ ∈ i • s
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩
#align gauge_lt_eq gauge_lt_eq

theorem mem_openSegment_of_gauge_lt_one (absorbs : Absorbent ℝ s) (hgauge : gauge s x < 1) :
    ∃ y ∈ s, x ∈ openSegment ℝ 0 y := by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  -- ⊢ ∃ y_1, y_1 ∈ s ∧ (fun x => r • x) y ∈ openSegment ℝ 0 y_1
  refine ⟨y, hy, 1 - r, r, ?_⟩
  -- ⊢ ∃ x x x, (1 - r) • 0 + r • y = (fun x => r • x) y
  simp [*]
  -- 🎉 no goals

theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x < 1 } ⊆ s := fun _x hx ↦
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx
#align gauge_lt_one_subset_self gauge_lt_one_subset_self

theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one <| by rwa [one_smul]
                                    -- 🎉 no goals
#align gauge_le_one_of_mem gauge_le_one_of_mem

/-- Gauge is subadditive. -/
theorem gauge_add_le (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (x y : E) :
    gauge s (x + y) ≤ gauge s x + gauge s y := by
  refine' le_of_forall_pos_lt_add fun ε hε => _
  -- ⊢ gauge s (x + y) < gauge s x + gauge s y + ε
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
    gauge s (a • x + b • y) ≤ a + b := gauge_le_of_mem (by positivity) <| by
      rw [hs.add_smul ha.le hb.le]
      exact add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
    _ < gauge s (a • x) + gauge s (b • y) + ε := by linarith
#align gauge_add_le gauge_add_le

theorem self_subset_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } := fun _ => gauge_le_one_of_mem
#align self_subset_gauge_le_one self_subset_gauge_le_one

theorem Convex.gauge_le (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) (a : ℝ) :
    Convex ℝ { x | gauge s x ≤ a } := by
  by_cases ha : 0 ≤ a
  -- ⊢ Convex ℝ {x | gauge s x ≤ a}
  · rw [gauge_le_eq hs h₀ absorbs ha]
    -- ⊢ Convex ℝ (⋂ (r : ℝ) (_ : a < r), r • s)
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
    -- 🎉 no goals
  · -- Porting note: `convert` needed help
    convert convex_empty (𝕜 := ℝ) (E := E)
    -- ⊢ {x | gauge s x ≤ a} = ∅
    exact eq_empty_iff_forall_not_mem.2 fun x hx => ha <| (gauge_nonneg _).trans hx
    -- 🎉 no goals
#align convex.gauge_le Convex.gauge_le

theorem Balanced.starConvex (hs : Balanced ℝ s) : StarConvex ℝ 0 s :=
  starConvex_zero_iff.2 fun x hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)
             -- 🎉 no goals
#align balanced.star_convex Balanced.starConvex

theorem le_gauge_of_not_mem (hs₀ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ a • s) :
    a ≤ gauge s x := by
  rw [starConvex_zero_iff] at hs₀
  -- ⊢ a ≤ gauge s x
  obtain ⟨r, hr, h⟩ := hs₂
  -- ⊢ a ≤ gauge s x
  refine' le_csInf ⟨r, hr, singleton_subset_iff.1 <| h _ (Real.norm_of_nonneg hr.le).ge⟩ _
  -- ⊢ ∀ (b : ℝ), b ∈ {r | 0 < r ∧ x ∈ r • s} → a ≤ b
  rintro b ⟨hb, x, hx', rfl⟩
  -- ⊢ a ≤ b
  refine' not_lt.1 fun hba => hx _
  -- ⊢ (fun x => b • x) x ∈ a • s
  have ha := hb.trans hba
  -- ⊢ (fun x => b • x) x ∈ a • s
  refine' ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) _, _⟩
  -- ⊢ a⁻¹ * b ≤ 1
  · rw [← div_eq_inv_mul]
    -- ⊢ b / a ≤ 1
    exact div_le_one_of_le hba.le ha.le
    -- 🎉 no goals
  · dsimp only
    -- ⊢ a • (a⁻¹ * b) • x = b • x
    rw [← mul_smul, mul_inv_cancel_left₀ ha.ne']
    -- 🎉 no goals
#align le_gauge_of_not_mem le_gauge_of_not_mem

theorem one_le_gauge_of_not_mem (hs₁ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ s) :
    1 ≤ gauge s x :=
  le_gauge_of_not_mem hs₁ hs₂ <| by rwa [one_smul]
                                    -- 🎉 no goals
#align one_le_gauge_of_not_mem one_le_gauge_of_not_mem

section LinearOrderedField

variable {α : Type*} [LinearOrderedField α] [MulActionWithZero α ℝ] [OrderedSMul α ℝ]

theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α ℝ (Set E)] {s : Set E} {a : α}
    (ha : 0 ≤ a) (x : E) : gauge s (a • x) = a • gauge s x := by
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ gauge s (0 • x) = 0 • gauge s x
  · rw [zero_smul, gauge_zero, zero_smul]
    -- 🎉 no goals
  rw [gauge_def', gauge_def', ← Real.sInf_smul_of_nonneg ha]
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • a • x ∈ s} = sInf (a • {r | r ∈ Ioi 0 ∧ r⁻¹ • x  …
  congr 1
  -- ⊢ {r | r ∈ Ioi 0 ∧ r⁻¹ • a • x ∈ s} = a • {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ s}
  ext r
  -- ⊢ r ∈ {r | r ∈ Ioi 0 ∧ r⁻¹ • a • x ∈ s} ↔ r ∈ a • {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ s}
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  -- ⊢ r ∈ Ioi 0 ∧ r⁻¹ • a • x ∈ s ↔ ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s) ∧ a • y = r
  constructor
  -- ⊢ r ∈ Ioi 0 ∧ r⁻¹ • a • x ∈ s → ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s) ∧ a • y = r
  · rintro ⟨hr, hx⟩
    -- ⊢ ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s) ∧ a • y = r
    simp_rw [mem_Ioi] at hr ⊢
    -- ⊢ ∃ y, (0 < y ∧ y⁻¹ • x ∈ s) ∧ a • y = r
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    -- ⊢ ∃ y, (0 < y ∧ y⁻¹ • x ∈ s) ∧ a • y = r
    have := smul_pos (inv_pos.2 ha') hr
    -- ⊢ ∃ y, (0 < y ∧ y⁻¹ • x ∈ s) ∧ a • y = r
    refine' ⟨a⁻¹ • r, ⟨this, _⟩, smul_inv_smul₀ ha'.ne' _⟩
    -- ⊢ (a⁻¹ • r)⁻¹ • x ∈ s
    rwa [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv]
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    -- ⊢ a • r ∈ Ioi 0 ∧ (a • r)⁻¹ • a • x ∈ s
    rw [mem_Ioi] at hr ⊢
    -- ⊢ 0 < a • r ∧ (a • r)⁻¹ • a • x ∈ s
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    -- ⊢ 0 < a • r ∧ (a • r)⁻¹ • a • x ∈ s
    have := smul_pos ha' hr
    -- ⊢ 0 < a • r ∧ (a • r)⁻¹ • a • x ∈ s
    refine' ⟨this, _⟩
    -- ⊢ (a • r)⁻¹ • a • x ∈ s
    rw [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc]
    -- ⊢ a • x ∈ a • r • s
    exact smul_mem_smul_set hx
    -- 🎉 no goals
#align gauge_smul_of_nonneg gauge_smul_of_nonneg

theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α ℝ ℝ]
    [IsScalarTower α ℝ ℝ] [IsScalarTower α ℝ E] {s : Set E} {a : α} (ha : 0 ≤ a) :
    gauge (a • s) = a⁻¹ • gauge s := by
  obtain rfl | ha' := ha.eq_or_lt
  -- ⊢ gauge (0 • s) = 0⁻¹ • gauge s
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
    -- 🎉 no goals
  ext x
  -- ⊢ gauge (a • s) x = (a⁻¹ • gauge s) x
  rw [gauge_def', Pi.smul_apply, gauge_def', ← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ a • s} = sInf (a⁻¹ • {r | r ∈ Ioi 0 ∧ r⁻¹ •  …
  congr 1
  -- ⊢ {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ a • s} = a⁻¹ • {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ s}
  ext r
  -- ⊢ r ∈ {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ a • s} ↔ r ∈ a⁻¹ • {r | r ∈ Ioi 0 ∧ r⁻¹ • x ∈ …
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  -- ⊢ (r ∈ Ioi 0 ∧ ∃ y, y ∈ s ∧ a • y = r⁻¹ • x) ↔ ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s)  …
  constructor
  -- ⊢ (r ∈ Ioi 0 ∧ ∃ y, y ∈ s ∧ a • y = r⁻¹ • x) → ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s)  …
  · rintro ⟨hr, y, hy, h⟩
    -- ⊢ ∃ y, (y ∈ Ioi 0 ∧ y⁻¹ • x ∈ s) ∧ a⁻¹ • y = r
    simp_rw [mem_Ioi] at hr ⊢
    -- ⊢ ∃ y, (0 < y ∧ y⁻¹ • x ∈ s) ∧ a⁻¹ • y = r
    refine' ⟨a • r, ⟨smul_pos ha' hr, _⟩, inv_smul_smul₀ ha'.ne' _⟩
    -- ⊢ (a • r)⁻¹ • x ∈ s
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
    -- 🎉 no goals
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    -- ⊢ a⁻¹ • r ∈ Ioi 0 ∧ ∃ y, y ∈ s ∧ a • y = (a⁻¹ • r)⁻¹ • x
    rw [mem_Ioi] at hr ⊢
    -- ⊢ 0 < a⁻¹ • r ∧ ∃ y, y ∈ s ∧ a • y = (a⁻¹ • r)⁻¹ • x
    refine' ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, _⟩
    -- ⊢ a • r⁻¹ • x = (a⁻¹ • r)⁻¹ • x
    rw [smul_inv₀, smul_assoc, inv_inv]
    -- 🎉 no goals
#align gauge_smul_left_of_nonneg gauge_smul_left_of_nonneg

theorem gauge_smul_left [Module α E] [SMulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ]
    [IsScalarTower α ℝ E] {s : Set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
    gauge (a • s) = |a|⁻¹ • gauge s := by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  -- ⊢ gauge (a • s) = gauge (|a| • s)
  obtain h | h := abs_choice a
  -- ⊢ gauge (a • s) = gauge (|a| • s)
  · rw [h]
    -- 🎉 no goals
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    -- ⊢ gauge (a • s) = gauge (a • -s)
    -- Porting note: was congr
    apply congr_arg
    -- ⊢ a • s = a • -s
    apply congr_arg
    -- ⊢ s = -s
    ext y
    -- ⊢ y ∈ s ↔ y ∈ -s
    refine' ⟨symmetric _, fun hy => _⟩
    -- ⊢ y ∈ s
    rw [← neg_neg y]
    -- ⊢ - -y ∈ s
    exact symmetric _ hy
    -- 🎉 no goals
#align gauge_smul_left gauge_smul_left

end LinearOrderedField

section IsROrC

variable [IsROrC 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

theorem gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) :
    gauge s (‖r‖ • x) = gauge s (r • x) := by
  unfold gauge
  -- ⊢ sInf {r_1 | 0 < r_1 ∧ ‖r‖ • x ∈ r_1 • s} = sInf {r_1 | 0 < r_1 ∧ r • x ∈ r_1 …
  congr with θ
  -- ⊢ θ ∈ {r_1 | 0 < r_1 ∧ ‖r‖ • x ∈ r_1 • s} ↔ θ ∈ {r_1 | 0 < r_1 ∧ r • x ∈ r_1 • …
  rw [@IsROrC.real_smul_eq_coe_smul 𝕜]
  -- ⊢ θ ∈ {r_1 | 0 < r_1 ∧ ↑‖r‖ • x ∈ r_1 • s} ↔ θ ∈ {r_1 | 0 < r_1 ∧ r • x ∈ r_1  …
  refine' and_congr_right fun hθ => (hs.smul _).mem_smul_iff _
  -- ⊢ ‖↑‖r‖‖ = ‖r‖
  rw [IsROrC.norm_ofReal, abs_norm]
  -- 🎉 no goals
#align gauge_norm_smul gauge_norm_smul

/-- If `s` is balanced, then the Minkowski functional is ℂ-homogeneous. -/
theorem gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x := by
  rw [← smul_eq_mul, ← gauge_smul_of_nonneg (norm_nonneg r), gauge_norm_smul hs]
  -- 🎉 no goals
#align gauge_smul gauge_smul

end IsROrC

section TopologicalSpace

variable [TopologicalSpace E] [ContinuousSMul ℝ E]

open Filter in
theorem interior_subset_gauge_lt_one (s : Set E) : interior s ⊆ { x | gauge s x < 1 } := by
  intro x hx
  -- ⊢ x ∈ {x | gauge s x < 1}
  have H₁ : Tendsto (fun r : ℝ ↦ r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : ℝ)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one, one_smul] at H₁
  -- ⊢ x ∈ {x | gauge s x < 1}
  have H₂ : ∀ᶠ r in 𝓝[<] (1 : ℝ), x ∈ r • s ∧ 0 < r ∧ r < 1
  -- ⊢ ∀ᶠ (r : ℝ) in 𝓝[Iio 1] 1, x ∈ r • s ∧ 0 < r ∧ r < 1
  · filter_upwards [H₁ (mem_interior_iff_mem_nhds.1 hx), Ioo_mem_nhdsWithin_Iio' one_pos]
    -- ⊢ ∀ (a : ℝ), a ∈ (fun r => r⁻¹ • x) ⁻¹' s → a ∈ Ioo 0 1 → x ∈ a • s ∧ 0 < a ∧  …
    intro r h₁ h₂
    -- ⊢ x ∈ r • s ∧ 0 < r ∧ r < 1
    exact ⟨(mem_smul_set_iff_inv_smul_mem₀ h₂.1.ne' _ _).2 h₁, h₂⟩
    -- 🎉 no goals
  rcases H₂.exists with ⟨r, hxr, hr₀, hr₁⟩
  -- ⊢ x ∈ {x | gauge s x < 1}
  exact (gauge_le_of_mem hr₀.le hxr).trans_lt hr₁
  -- 🎉 no goals
#align interior_subset_gauge_lt_one interior_subset_gauge_lt_one

theorem gauge_lt_one_eq_self_of_open (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) :
    { x | gauge s x < 1 } = s := by
  refine' (gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀).antisymm _
  -- ⊢ s ⊆ {x | gauge s x < 1}
  convert interior_subset_gauge_lt_one s
  -- ⊢ s = interior s
  exact hs₂.interior_eq.symm
  -- 🎉 no goals
#align gauge_lt_one_eq_self_of_open gauge_lt_one_eq_self_of_open

-- porting note: droped unneeded assumptions
theorem gauge_lt_one_of_mem_of_open (hs₂ : IsOpen s) {x : E} (hx : x ∈ s) :
    gauge s x < 1 :=
  interior_subset_gauge_lt_one s <| by rwa [hs₂.interior_eq]
                                       -- 🎉 no goals
#align gauge_lt_one_of_mem_of_open gauge_lt_one_of_mem_of_openₓ

-- porting note: droped unneeded assumptions
theorem gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₂ : IsOpen s) (hx : x ∈ ε • s) :
    gauge s x < ε := by
  have : ε⁻¹ • x ∈ s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  -- ⊢ gauge s x < ε
  have h_gauge_lt := gauge_lt_one_of_mem_of_open hs₂ this
  -- ⊢ gauge s x < ε
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_one]
    at h_gauge_lt
#align gauge_lt_of_mem_smul gauge_lt_of_mem_smulₓ

theorem mem_closure_of_gauge_le_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x ≤ 1) : x ∈ closure s := by
  have : ∀ᶠ r : ℝ in 𝓝[<] 1, r • x ∈ s
  -- ⊢ ∀ᶠ (r : ℝ) in 𝓝[Iio 1] 1, r • x ∈ s
  · filter_upwards [Ico_mem_nhdsWithin_Iio' one_pos] with r ⟨hr₀, hr₁⟩
    -- ⊢ r • x ∈ s
    apply gauge_lt_one_subset_self hc hs₀ ha
    -- ⊢ r • x ∈ {x | gauge s x < 1}
    rw [mem_setOf_eq, gauge_smul_of_nonneg hr₀]
    -- ⊢ r • gauge s x < 1
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
    -- 🎉 no goals
  refine mem_closure_of_tendsto ?_ this
  -- ⊢ Filter.Tendsto (fun x_1 => x_1 • x) (𝓝[Iio 1] 1) (𝓝 x)
  exact Filter.Tendsto.mono_left (Continuous.tendsto' (by continuity) _ _ (one_smul _ _))
    inf_le_left

theorem mem_frontier_of_gauge_eq_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x = 1) : x ∈ frontier s :=
  ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' ↦
    (interior_subset_gauge_lt_one s h').out.ne h⟩

end TopologicalSpace

section TopologicalAddGroup

open Filter

variable [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
theorem continuous_gauge (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) : Continuous (gauge s) := by
  have ha : Absorbent ℝ s := absorbent_nhds_zero hs₀
  -- ⊢ Continuous (gauge s)
  simp only [continuous_iff_continuousAt, ContinuousAt, (nhds_basis_Icc_pos _).tendsto_right_iff]
  -- ⊢ ∀ (x : E) (i : ℝ), 0 < i → ∀ᶠ (x_1 : E) in 𝓝 x, gauge s x_1 ∈ Icc (gauge s x …
  intro x ε hε₀
  -- ⊢ ∀ᶠ (x_1 : E) in 𝓝 x, gauge s x_1 ∈ Icc (gauge s x - ε) (gauge s x + ε)
  rw [← map_add_left_nhds_zero, eventually_map]
  -- ⊢ ∀ᶠ (a : E) in 𝓝 0, gauge s ((fun x x_1 => x + x_1) x a) ∈ Icc (gauge s x - ε …
  have : ε • s ∩ -(ε • s) ∈ 𝓝 0
  -- ⊢ ε • s ∩ -(ε • s) ∈ 𝓝 0
  · exact inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_zero _ ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀))
  filter_upwards [this] with y hy
  -- ⊢ gauge s (x + y) ∈ Icc (gauge s x - ε) (gauge s x + ε)
  constructor
  -- ⊢ gauge s x - ε ≤ gauge s (x + y)
  · rw [sub_le_iff_le_add]
    -- ⊢ gauge s x ≤ gauge s (x + y) + ε
    calc
      gauge s x = gauge s (x + y + (-y)) := by simp
      _ ≤ gauge s (x + y) + gauge s (-y) := gauge_add_le hc ha _ _
      _ ≤ gauge s (x + y) + ε := add_le_add_left (gauge_le_of_mem hε₀.le (mem_neg.1 hy.2)) _
  · calc
      gauge s (x + y) ≤ gauge s x + gauge s y := gauge_add_le hc ha _ _
      _ ≤ gauge s x + ε := add_le_add_left (gauge_le_of_mem hε₀.le hy.1) _

theorem gauge_lt_one_eq_interior (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    { x | gauge s x < 1 } = interior s := by
  refine Subset.antisymm (fun x hx ↦ ?_) (interior_subset_gauge_lt_one s)
  -- ⊢ x ∈ interior s
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  -- ⊢ x ∈ interior s
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy
  -- 🎉 no goals

theorem gauge_lt_one_iff_mem_interior (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x < 1 ↔ x ∈ interior s :=
  Set.ext_iff.1 (gauge_lt_one_eq_interior hc hs₀) _

theorem gauge_le_one_iff_mem_closure (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x ≤ 1 ↔ x ∈ closure s :=
  ⟨mem_closure_of_gauge_le_one hc (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀), fun h ↦
    le_on_closure (fun _ ↦ gauge_le_one_of_mem) (continuous_gauge hc hs₀).continuousOn
      continuousOn_const h⟩

theorem gauge_eq_one_iff_mem_frontier (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    gauge s x = 1 ↔ x ∈ frontier s := by
  rw [eq_iff_le_not_lt, gauge_le_one_iff_mem_closure hc hs₀, gauge_lt_one_iff_mem_interior hc hs₀]
  -- ⊢ x ∈ closure s ∧ ¬x ∈ interior s ↔ x ∈ frontier s
  rfl
  -- 🎉 no goals

theorem gauge_eq_zero [T1Space E] (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    gauge s x = 0 ↔ x = 0 := by
  refine ⟨not_imp_not.1 fun (h : x ≠ 0) ↦ ne_of_gt ?_, fun h ↦ h.symm ▸ gauge_zero⟩
  -- ⊢ 0 < gauge s x
  rcases hb (isOpen_compl_singleton.mem_nhds h.symm) with ⟨c, hc₀, hc⟩
  -- ⊢ 0 < gauge s x
  refine (inv_pos.2 hc₀).trans_le <| le_csInf hs.gauge_set_nonempty ?_
  -- ⊢ ∀ (b : ℝ), b ∈ {r | 0 < r ∧ x ∈ r • s} → c⁻¹ ≤ b
  rintro r ⟨hr₀, x, hx, rfl⟩
  -- ⊢ c⁻¹ ≤ r
  contrapose! hc
  -- ⊢ ∃ a, c ≤ ‖a‖ ∧ ¬s ⊆ a • {r • x}ᶜ
  refine ⟨r⁻¹, ?_, fun h ↦ ?_⟩
  -- ⊢ c ≤ ‖r⁻¹‖
  · rw [norm_inv, Real.norm_of_nonneg hr₀.le, le_inv hc₀ hr₀]
    -- ⊢ r ≤ c⁻¹
    exact hc.le
    -- 🎉 no goals
  · rcases h hx with ⟨y, hy, rfl⟩
    -- ⊢ False
    simp [hr₀.ne'] at hy
    -- 🎉 no goals

theorem gauge_pos [T1Space E] (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    0 < gauge s x ↔ x ≠ 0 := by
  simp only [(gauge_nonneg _).gt_iff_ne, Ne.def, gauge_eq_zero hs hb]
  -- 🎉 no goals

end TopologicalAddGroup

section IsROrC

variable [IsROrC 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-- `gauge s` as a seminorm when `s` is balanced, convex and absorbent. -/
@[simps!]
def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)
#align gauge_seminorm gaugeSeminorm

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s} [TopologicalSpace E]
  [ContinuousSMul ℝ E]

theorem gaugeSeminorm_lt_one_of_open (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_open hs hx
#align gauge_seminorm_lt_one_of_open gaugeSeminorm_lt_one_of_open

theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s := by
  rw [Seminorm.ball_zero_eq]
  -- ⊢ {y | ↑(gaugeSeminorm hs₀ hs₁ hs₂) y < 1} = s
  exact gauge_lt_one_eq_self_of_open hs₁ hs₂.zero_mem hs
  -- 🎉 no goals
#align gauge_seminorm_ball_one gaugeSeminorm_ball_one

end IsROrC

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
protected theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p := by
  ext x
  -- ⊢ gauge (ball p 0 1) x = ↑p x
  obtain hp | hp := { r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1 }.eq_empty_or_nonempty
  -- ⊢ gauge (ball p 0 1) x = ↑p x
  · rw [gauge, hp, Real.sInf_empty]
    -- ⊢ 0 = ↑p x
    by_contra h
    -- ⊢ False
    have hpx : 0 < p x := (map_nonneg _ _).lt_of_ne h
    -- ⊢ False
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    -- ⊢ False
    refine' hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩
    -- ⊢ (2 * ↑p x)⁻¹ • x ∈ ball p 0 1
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂),
      inv_mul_lt_iff hpx₂, mul_one]
    exact lt_mul_of_one_lt_left hpx one_lt_two
    -- 🎉 no goals
  refine' IsGLB.csInf_eq ⟨fun r => _, fun r hr => le_of_forall_pos_le_add fun ε hε => _⟩ hp
  -- ⊢ r ∈ {r | 0 < r ∧ x ∈ r • ball p 0 1} → ↑p x ≤ r
  · rintro ⟨hr, y, hy, rfl⟩
    -- ⊢ ↑p ((fun x => r • x) y) ≤ r
    rw [p.mem_ball_zero] at hy
    -- ⊢ ↑p ((fun x => r • x) y) ≤ r
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
    -- ⊢ r * ↑p y ≤ r
    exact mul_le_of_le_one_right hr.le hy.le
    -- 🎉 no goals
  · have hpε : 0 < p x + ε :=
      -- Porting note: was `by positivity`
      add_pos_of_nonneg_of_pos (map_nonneg _ _) hε
    refine' hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩
    -- ⊢ (↑p x + ε)⁻¹ • x ∈ ball p 0 1
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε),
      inv_mul_lt_iff hpε, mul_one]
    exact lt_add_of_pos_right _ hε
    -- 🎉 no goals
#align seminorm.gauge_ball Seminorm.gauge_ball

theorem Seminorm.gaugeSeminorm_ball (p : Seminorm ℝ E) :
    gaugeSeminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) =
      p :=
  FunLike.coe_injective p.gauge_ball
#align seminorm.gauge_seminorm_ball Seminorm.gaugeSeminorm_ball

end AddCommGroup

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

theorem gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x‖ := by
  rw [← ball_normSeminorm ℝ, Seminorm.gauge_ball, coe_normSeminorm]
  -- 🎉 no goals
#align gauge_unit_ball gauge_unit_ball

theorem gauge_ball (hr : 0 ≤ r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr
  -- ⊢ gauge (ball 0 0) x = ‖x‖ / 0
  · simp
    -- 🎉 no goals
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    -- ⊢ ∀ (x : E), ‖x‖ < 1 → ‖x‖ < 1
    exact fun _ => id
    -- 🎉 no goals

@[deprecated gauge_ball]
theorem gauge_ball' (hr : 0 < r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r :=
  gauge_ball hr.le x
#align gauge_ball gauge_ball'

@[simp]
theorem gauge_closure_zero : gauge (closure (0 : Set E)) = 0 := funext fun x ↦ by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_gt with hx | hx
  -- ⊢ sInf {r | r ∈ Ioi 0 ∧ (r = 0 ∨ ‖x‖ = 0)} = OfNat.ofNat 0 x
  · convert csInf_Ioi (a := (0 : ℝ))
    -- ⊢ {r | r ∈ Ioi 0 ∧ (r = 0 ∨ ‖x‖ = 0)} = Ioi 0
    exact Set.ext fun r ↦ and_iff_left (.inr hx)
    -- 🎉 no goals
  · convert Real.sInf_empty
    -- ⊢ {r | r ∈ Ioi 0 ∧ (r = 0 ∨ ‖x‖ = 0)} = ∅
    exact eq_empty_of_forall_not_mem fun r ⟨hr₀, hr⟩ ↦ hx.ne' <| hr.resolve_left hr₀.out.ne'
    -- 🎉 no goals

@[simp]
theorem gauge_closedBall (hr : 0 ≤ r) (x : E) : gauge (closedBall (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr'
  -- ⊢ gauge (closedBall 0 0) x = ‖x‖ / 0
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
    -- ⊢ OfNat.ofNat 0 x = 0
                                                                         -- 🎉 no goals
  · apply le_antisymm
    -- ⊢ gauge (closedBall 0 r) x ≤ ‖x‖ / r
    · rw [← gauge_ball hr]
      -- ⊢ gauge (closedBall 0 r) x ≤ gauge (ball 0 r) x
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
      -- 🎉 no goals
    · suffices : ∀ᶠ R in 𝓝[>] r, ‖x‖ / R ≤ gauge (closedBall 0 r) x
      -- ⊢ ‖x‖ / r ≤ gauge (closedBall 0 r) x
      · refine le_of_tendsto ?_ this
        -- ⊢ Filter.Tendsto (fun c => ‖x‖ / c) (𝓝[Ioi r] r) (𝓝 (‖x‖ / r))
        exact tendsto_const_nhds.div inf_le_left hr'.ne'
        -- 🎉 no goals
      filter_upwards [self_mem_nhdsWithin] with R hR
      -- ⊢ ‖x‖ / R ≤ gauge (closedBall 0 r) x
      rw [← gauge_ball (hr.trans hR.out.le)]
      -- ⊢ gauge (ball 0 R) x ≤ gauge (closedBall 0 r) x
      refine gauge_mono ?_ (closedBall_subset_ball hR) _
      -- ⊢ Absorbent ℝ (closedBall 0 r)
      exact (absorbent_ball_zero hr').subset ball_subset_closedBall
      -- 🎉 no goals

theorem mul_gauge_le_norm (hs : Metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ‖x‖ := by
  obtain hr | hr := le_or_lt r 0
  -- ⊢ r * gauge s x ≤ ‖x‖
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
    -- 🎉 no goals
  rw [mul_comm, ← le_div_iff hr, ← gauge_ball hr.le]
  -- ⊢ gauge s x ≤ gauge (ball 0 r) x
  exact gauge_mono (absorbent_ball_zero hr) hs x
  -- 🎉 no goals
#align mul_gauge_le_norm mul_gauge_le_norm

theorem Convex.lipschitzWith_gauge {r : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r)
    (hs : Metric.ball (0 : E) r ⊆ s) : LipschitzWith r⁻¹ (gauge s) :=
  have : Absorbent ℝ (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
                                              -- 🎉 no goals
      _ ≤ gauge s y + gauge s (x - y) := gauge_add_le hc (this.subset hs) _ _
      _ ≤ gauge s y + ‖x - y‖ / r :=
        add_le_add_left ((gauge_mono this hs (x - y)).trans_eq (gauge_ball hr.le _)) _
      _ = gauge s y + r⁻¹ * dist x y := by rw [dist_eq_norm, div_eq_inv_mul, NNReal.coe_inv]
                                           -- 🎉 no goals
#align convex.lipschitz_with_gauge Convex.lipschitzWith_gauge

theorem Convex.lipschitz_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    ∃ K, LipschitzWith K (gauge s) :=
  let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : ℝ≥0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩

theorem Convex.uniformContinuous_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    UniformContinuous (gauge s) :=
  let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous
#align convex.uniform_continuous_gauge Convex.uniformContinuous_gauge

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

theorem le_gauge_of_subset_closedBall (hs : Absorbent ℝ s) (hr : 0 ≤ r) (hsr : s ⊆ closedBall 0 r) :
    ‖x‖ / r ≤ gauge s x := by
  rw [← gauge_closedBall hr]
  -- ⊢ gauge (closedBall 0 r) x ≤ gauge s x
  exact gauge_mono hs hsr _
  -- 🎉 no goals

end Normed
