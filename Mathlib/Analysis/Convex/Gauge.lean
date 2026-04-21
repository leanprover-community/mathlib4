/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Seminorm
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.RCLike.Basic

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
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open NormedField Set
open scoped Pointwise Topology NNReal

noncomputable section

variable {𝕜 E : Type*}

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E]

/-- The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : Set E) (x : E) : ℝ :=
  sInf { r : ℝ | 0 < r ∧ x ∈ r • s }

variable {s t : Set E} {x : E} {a : ℝ}

theorem gauge_def : gauge s x = sInf ({ r ∈ Set.Ioi (0 : ℝ) | x ∈ r • s }) :=
  rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
theorem gauge_def' : gauge s x = sInf {r ∈ Set.Ioi (0 : ℝ) | r⁻¹ • x ∈ s} := by
  congrm sInf {r | ?_}
  exact and_congr_right fun hr => mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _

private theorem gauge_set_bddBelow : BddBelow { r : ℝ | 0 < r ∧ x ∈ r • s } :=
  ⟨0, fun _ hr => hr.1.le⟩

/-- If the given subset is `Absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge. -/
theorem Absorbent.gauge_set_nonempty (absorbs : Absorbent ℝ s) :
    { r : ℝ | 0 < r ∧ x ∈ r • s }.Nonempty :=
  let ⟨r, hr₁, hr₂⟩ := (absorbs x).exists_pos
  ⟨r, hr₁, hr₂ r (Real.norm_of_nonneg hr₁.le).ge rfl⟩

theorem gauge_mono (hs : Absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s := fun _ => by
  unfold gauge
  gcongr; exacts [gauge_set_bddBelow, hs.gauge_set_nonempty]

theorem exists_lt_of_gauge_lt (absorbs : Absorbent ℝ s) (h : gauge s x < a) :
    ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s := by
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_csInf_lt absorbs.gauge_set_nonempty h
  exact ⟨b, hb, hba, hx⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp]
theorem gauge_zero : gauge s 0 = 0 := by
  rw [gauge_def']
  by_cases h : (0 : E) ∈ s
  · simp only [smul_zero, sep_true, h, csInf_Ioi]
  · simp only [smul_zero, sep_false, h, Real.sInf_empty]

@[simp]
theorem gauge_zero' : gauge (0 : Set E) = 0 := by
  ext x
  rw [gauge_def']
  obtain rfl | hx := eq_or_ne x 0
  · simp only [csInf_Ioi, mem_zero, Pi.zero_apply, sep_true, smul_zero]
  · simp only [mem_zero, Pi.zero_apply, inv_eq_zero, smul_eq_zero]
    convert Real.sInf_empty
    exact eq_empty_iff_forall_notMem.2 fun r hr => hr.2.elim (ne_of_gt hr.1) hx

@[simp]
theorem gauge_empty : gauge (∅ : Set E) = 0 := by
  ext
  simp only [gauge_def', Real.sInf_empty, mem_empty_iff_false, Pi.zero_apply, sep_false]

theorem gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 := by
  obtain rfl | rfl := subset_singleton_iff_eq.1 h
  exacts [gauge_empty, gauge_zero']

/-- The gauge is always nonnegative. -/
theorem gauge_nonneg (x : E) : 0 ≤ gauge s x :=
  Real.sInf_nonneg fun _ hx => hx.1.le

theorem gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x := by
  have : ∀ x, -x ∈ s ↔ x ∈ s := fun x => ⟨fun h => by simpa using symmetric _ h, symmetric x⟩
  simp_rw [gauge_def', smul_neg, this]

theorem gauge_neg_set_neg (x : E) : gauge (-s) (-x) = gauge s x := by
  simp_rw [gauge_def', smul_neg, neg_mem_neg]

theorem gauge_neg_set_eq_gauge_neg (x : E) : gauge (-s) x = gauge s (-x) := by
  rw [← gauge_neg_set_neg, neg_neg]

theorem gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [mem_singleton_iff.1 (zero_smul_set_subset _ hx), gauge_zero]
  · exact csInf_le gauge_set_bddBelow ⟨ha', hx⟩

theorem gauge_le_eq (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : Absorbent ℝ s) (ha : 0 ≤ a) :
    { x | gauge s x ≤ a } = ⋂ (r : ℝ) (_ : a < r), r • s := by
  ext x
  simp_rw [Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨fun h r hr => ?_, fun h => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · have hr' := ha.trans_lt hr
    rw [mem_smul_set_iff_inv_smul_mem₀ hr'.ne']
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr)
    suffices (r⁻¹ * δ) • δ⁻¹ • x ∈ s by rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this
    rw [mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne'] at hδ
    refine hs₁.smul_mem_of_zero_mem hs₀ hδ ⟨by positivity, ?_⟩
    rw [inv_mul_le_iff₀ hr', mul_one]
    exact hδr.le
  · linarith [gauge_le_of_mem (by linarith) <| h (a + ε / 2) (by linarith)]

theorem gauge_lt_eq' (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ (r : ℝ) (_ : 0 < r) (_ : r < a), r • s := by
  ext
  simp_rw [mem_setOf, mem_iUnion, exists_prop]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

theorem gauge_lt_eq (absorbs : Absorbent ℝ s) (a : ℝ) :
    { x | gauge s x < a } = ⋃ r ∈ Set.Ioo 0 (a : ℝ), r • s := by
  ext
  simp_rw [mem_setOf, mem_iUnion, exists_prop, mem_Ioo, and_assoc]
  exact
    ⟨exists_lt_of_gauge_lt absorbs, fun ⟨r, hr₀, hr₁, hx⟩ =>
      (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩

theorem mem_openSegment_of_gauge_lt_one (absorbs : Absorbent ℝ s) (hgauge : gauge s x < 1) :
    ∃ y ∈ s, x ∈ openSegment ℝ 0 y := by
  rcases exists_lt_of_gauge_lt absorbs hgauge with ⟨r, hr₀, hr₁, y, hy, rfl⟩
  refine ⟨y, hy, 1 - r, r, ?_⟩
  simp [*]

theorem gauge_lt_one_subset_self (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) :
    { x | gauge s x < 1 } ⊆ s := fun _x hx ↦
  let ⟨_y, hys, hx⟩ := mem_openSegment_of_gauge_lt_one absorbs hx
  hs.openSegment_subset h₀ hys hx

theorem gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
  gauge_le_of_mem zero_le_one <| by rwa [one_smul]

/-- Gauge is subadditive. -/
theorem gauge_add_le (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (x y : E) :
    gauge s (x + y) ≤ gauge s x + gauge s y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha, ha', x, hx, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb, hb', y, hy, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
    gauge s (a • x + b • y) ≤ a + b := gauge_le_of_mem (by positivity) <| by
      rw [hs.add_smul ha.le hb.le]
      exact add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)
    _ < gauge s (a • x) + gauge s (b • y) + ε := by linarith

theorem gauge_sum_le {ι : Type*} (hs : Convex ℝ s) (absorbs : Absorbent ℝ s) (t : Finset ι)
    (f : ι → E) : gauge s (∑ i ∈ t, f i) ≤ ∑ i ∈ t, gauge s (f i) :=
  Finset.le_sum_of_subadditive _ gauge_zero.le (gauge_add_le hs absorbs) _ _

theorem self_subset_gauge_le_one : s ⊆ { x | gauge s x ≤ 1 } := fun _ => gauge_le_one_of_mem

theorem Convex.gauge_le (hs : Convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : Absorbent ℝ s) (a : ℝ) :
    Convex ℝ { x | gauge s x ≤ a } := by
  by_cases ha : 0 ≤ a
  · rw [gauge_le_eq hs h₀ absorbs ha]
    exact convex_iInter fun i => convex_iInter fun _ => hs.smul _
  · convert convex_empty (𝕜 := ℝ)
    exact eq_empty_iff_forall_notMem.2 fun x hx => ha <| (gauge_nonneg _).trans hx

theorem Balanced.starConvex (hs : Balanced ℝ s) : StarConvex ℝ 0 s :=
  starConvex_zero_iff.2 fun _ hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)

theorem le_gauge_of_notMem (hs₀ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ a • s) :
    a ≤ gauge s x := by
  rw [starConvex_zero_iff] at hs₀
  obtain ⟨r, hr, h⟩ := hs₂.exists_pos
  refine le_csInf ⟨r, hr, singleton_subset_iff.1 <| h _ (Real.norm_of_nonneg hr.le).ge⟩ ?_
  rintro b ⟨hb, x, hx', rfl⟩
  refine not_lt.1 fun hba => hx ?_
  have ha := hb.trans hba
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (by positivity) ?_, ?_⟩
  · rw [← div_eq_inv_mul]
    exact div_le_one_of_le₀ hba.le ha.le
  · dsimp only
    rw [← mul_smul, mul_inv_cancel_left₀ ha.ne']

theorem one_le_gauge_of_notMem (hs₁ : StarConvex ℝ 0 s) (hs₂ : Absorbs ℝ s {x}) (hx : x ∉ s) :
    1 ≤ gauge s x :=
  le_gauge_of_notMem hs₁ hs₂ <| by rwa [one_smul]

section LinearOrderedField

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [MulActionWithZero α ℝ] [IsStrictOrderedModule α ℝ]

theorem gauge_smul_of_nonneg [MulActionWithZero α E] [IsScalarTower α ℝ (Set E)] {s : Set E} {a : α}
    (ha : 0 ≤ a) (x : E) : gauge s (a • x) = a • gauge s x := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul, gauge_zero, zero_smul]
  rw [gauge_def', gauge_def', ← Real.sInf_smul_of_nonneg ha]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, hx⟩
    simp_rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos (inv_pos.2 ha') hr
    refine ⟨a⁻¹ • r, ⟨this, ?_⟩, smul_inv_smul₀ ha'.ne' _⟩
    rwa [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc,
      mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha'.ne'), inv_inv]
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    rw [← mem_smul_set_iff_inv_smul_mem₀ hr.ne'] at hx
    have := smul_pos ha' hr
    refine ⟨this, ?_⟩
    rw [← mem_smul_set_iff_inv_smul_mem₀ this.ne', smul_assoc]
    exact smul_mem_smul_set hx

theorem gauge_smul_left_of_nonneg [MulActionWithZero α E] [SMulCommClass α ℝ ℝ]
    [IsScalarTower α ℝ ℝ] [IsScalarTower α ℝ E] {s : Set E} {a : α} (ha : 0 ≤ a) :
    gauge (a • s) = a⁻¹ • gauge s := by
  obtain rfl | ha' := ha.eq_or_lt
  · rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_set_subset _)]
  ext x
  rw [gauge_def', Pi.smul_apply, gauge_def', ← Real.sInf_smul_of_nonneg (inv_nonneg.2 ha)]
  congr 1
  ext r
  simp_rw [Set.mem_smul_set, Set.mem_sep_iff]
  constructor
  · rintro ⟨hr, y, hy, h⟩
    simp_rw [mem_Ioi] at hr ⊢
    refine ⟨a • r, ⟨smul_pos ha' hr, ?_⟩, inv_smul_smul₀ ha'.ne' _⟩
    rwa [smul_inv₀, smul_assoc, ← h, inv_smul_smul₀ ha'.ne']
  · rintro ⟨r, ⟨hr, hx⟩, rfl⟩
    rw [mem_Ioi] at hr ⊢
    refine ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, ?_⟩
    rw [smul_inv₀, smul_assoc, inv_inv]

theorem gauge_smul_left [Module α E] [SMulCommClass α ℝ ℝ] [IsScalarTower α ℝ ℝ]
    [IsScalarTower α ℝ E] {s : Set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
    gauge (a • s) = |a|⁻¹ • gauge s := by
  rw [← gauge_smul_left_of_nonneg (abs_nonneg a)]
  obtain h | h := abs_choice a
  · rw [h]
  · rw [h, Set.neg_smul_set, ← Set.smul_set_neg]
    congr
    ext y
    refine ⟨symmetric _, fun hy => ?_⟩
    rw [← neg_neg y]
    exact symmetric _ hy

end LinearOrderedField

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

theorem gauge_norm_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) :
    gauge s (‖r‖ • x) = gauge s (r • x) := by
  unfold gauge
  congr with θ
  rw [@RCLike.real_smul_eq_coe_smul 𝕜]
  refine and_congr_right fun hθ => (hs.smul _).smul_mem_iff ?_
  rw [RCLike.norm_ofReal, abs_norm]

/-- If `s` is balanced, then the Minkowski functional is ℂ-homogeneous. -/
theorem gauge_smul (hs : Balanced 𝕜 s) (r : 𝕜) (x : E) : gauge s (r • x) = ‖r‖ * gauge s x := by
  rw [← smul_eq_mul, ← gauge_smul_of_nonneg (norm_nonneg r), gauge_norm_smul hs]

end RCLike

open Filter

section TopologicalSpace

variable [TopologicalSpace E]

theorem comap_gauge_nhds_zero_le (ha : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    comap (gauge s) (𝓝 0) ≤ 𝓝 0 := fun u hu ↦ by
  rcases (hb hu).exists_pos with ⟨r, hr₀, hr⟩
  filter_upwards [preimage_mem_comap (gt_mem_nhds (inv_pos.2 hr₀))] with x (hx : gauge s x < r⁻¹)
  rcases exists_lt_of_gauge_lt ha hx with ⟨c, hc₀, hcr, y, hy, rfl⟩
  have hrc := (lt_inv_comm₀ hr₀ hc₀).2 hcr
  rcases hr c⁻¹ (hrc.le.trans (le_abs_self _)) hy with ⟨z, hz, rfl⟩
  simpa only [smul_inv_smul₀ hc₀.ne']

variable [T1Space E]

theorem gauge_eq_zero (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    gauge s x = 0 ↔ x = 0 := by
  refine ⟨fun h₀ ↦ by_contra fun (hne : x ≠ 0) ↦ ?_, fun h ↦ h.symm ▸ gauge_zero⟩
  have : {x}ᶜ ∈ comap (gauge s) (𝓝 0) :=
    comap_gauge_nhds_zero_le hs hb (isOpen_compl_singleton.mem_nhds hne.symm)
  rcases ((nhds_basis_zero_abs_lt _).comap _).mem_iff.1 this with ⟨r, hr₀, hr⟩
  exact hr (by simpa [h₀]) rfl

theorem gauge_pos (hs : Absorbent ℝ s) (hb : Bornology.IsVonNBounded ℝ s) :
    0 < gauge s x ↔ x ≠ 0 := by
  simp only [(gauge_nonneg _).lt_iff_ne', Ne, gauge_eq_zero hs hb]

end TopologicalSpace

section ContinuousSMul

variable [TopologicalSpace E] [ContinuousSMul ℝ E]

open Filter in
theorem interior_subset_gauge_lt_one (s : Set E) : interior s ⊆ { x | gauge s x < 1 } := by
  intro x hx
  have H₁ : Tendsto (fun r : ℝ ↦ r⁻¹ • x) (𝓝[<] 1) (𝓝 ((1 : ℝ)⁻¹ • x)) :=
    ((tendsto_id.inv₀ one_ne_zero).smul tendsto_const_nhds).mono_left inf_le_left
  rw [inv_one, one_smul] at H₁
  have H₂ : ∀ᶠ r in 𝓝[<] (1 : ℝ), x ∈ r • s ∧ 0 < r ∧ r < 1 := by
    filter_upwards [H₁ (mem_interior_iff_mem_nhds.1 hx), Ioo_mem_nhdsLT one_pos] with r h₁ h₂
    exact ⟨(mem_smul_set_iff_inv_smul_mem₀ h₂.1.ne' _ _).2 h₁, h₂⟩
  rcases H₂.exists with ⟨r, hxr, hr₀, hr₁⟩
  exact (gauge_le_of_mem hr₀.le hxr).trans_lt hr₁

theorem gauge_lt_one_eq_self_of_isOpen (hs₁ : Convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : IsOpen s) :
    { x | gauge s x < 1 } = s := by
  refine (gauge_lt_one_subset_self hs₁ ‹_› <| absorbent_nhds_zero <| hs₂.mem_nhds hs₀).antisymm ?_
  convert interior_subset_gauge_lt_one s
  exact hs₂.interior_eq.symm

theorem gauge_lt_one_of_mem_of_isOpen (hs₂ : IsOpen s) {x : E} (hx : x ∈ s) :
    gauge s x < 1 :=
  interior_subset_gauge_lt_one s <| by rwa [hs₂.interior_eq]

theorem gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₂ : IsOpen s) (hx : x ∈ ε • s) :
    gauge s x < ε := by
  have : ε⁻¹ • x ∈ s := by rwa [← mem_smul_set_iff_inv_smul_mem₀ hε.ne']
  have h_gauge_lt := gauge_lt_one_of_mem_of_isOpen hs₂ this
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff₀ hε, mul_one]
    at h_gauge_lt

theorem mem_closure_of_gauge_le_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x ≤ 1) : x ∈ closure s := by
  have : ∀ᶠ r : ℝ in 𝓝[<] 1, r • x ∈ s := by
    filter_upwards [Ico_mem_nhdsLT one_pos] with r ⟨hr₀, hr₁⟩
    apply gauge_lt_one_subset_self hc hs₀ ha
    rw [mem_setOf_eq, gauge_smul_of_nonneg hr₀]
    exact mul_lt_one_of_nonneg_of_lt_one_left hr₀ hr₁ h
  refine mem_closure_of_tendsto ?_ this
  exact Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (one_smul _ _))
    inf_le_left

theorem mem_frontier_of_gauge_eq_one (hc : Convex ℝ s) (hs₀ : 0 ∈ s) (ha : Absorbent ℝ s)
    (h : gauge s x = 1) : x ∈ frontier s :=
  ⟨mem_closure_of_gauge_le_one hc hs₀ ha h.le, fun h' ↦
    (interior_subset_gauge_lt_one s h').out.ne h⟩

theorem tendsto_gauge_nhds_zero_nhdsGE (hs : s ∈ 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝[≥] 0) := by
  refine nhdsGE_basis_Icc.tendsto_right_iff.2 fun ε hε ↦ ?_
  rw [← set_smul_mem_nhds_zero_iff hε.ne'] at hs
  filter_upwards [hs] with x hx
  exact ⟨gauge_nonneg _, gauge_le_of_mem hε.le hx⟩

theorem tendsto_gauge_nhds_zero (hs : s ∈ 𝓝 0) : Tendsto (gauge s) (𝓝 0) (𝓝 0) :=
  (tendsto_gauge_nhds_zero_nhdsGE hs).mono_right inf_le_left

/-- If `s` is a neighborhood of the origin, then `gauge s` is continuous at the origin.
See also `continuousAt_gauge`. -/
theorem continuousAt_gauge_zero (hs : s ∈ 𝓝 0) : ContinuousAt (gauge s) 0 := by
  rw [ContinuousAt, gauge_zero]
  exact tendsto_gauge_nhds_zero hs

theorem comap_gauge_nhds_zero (hb : Bornology.IsVonNBounded ℝ s) (h₀ : s ∈ 𝓝 0) :
    comap (gauge s) (𝓝 0) = 𝓝 0 :=
  (comap_gauge_nhds_zero_le (absorbent_nhds_zero h₀) hb).antisymm
    (tendsto_gauge_nhds_zero h₀).le_comap

end ContinuousSMul

section TopologicalVectorSpace

open Filter

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
theorem continuousAt_gauge (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) : ContinuousAt (gauge s) x := by
  have ha : Absorbent ℝ s := absorbent_nhds_zero hs₀
  refine (nhds_basis_Icc_pos _).tendsto_right_iff.2 fun ε hε₀ ↦ ?_
  rw [← map_add_left_nhds_zero, eventually_map]
  have : ε • s ∩ -(ε • s) ∈ 𝓝 0 :=
    inter_mem ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀)
      (neg_mem_nhds_zero _ ((set_smul_mem_nhds_zero_iff hε₀.ne').2 hs₀))
  filter_upwards [this] with y hy
  constructor
  · rw [sub_le_iff_le_add]
    calc
      gauge s x = gauge s (x + y + (-y)) := by simp
      _ ≤ gauge s (x + y) + gauge s (-y) := gauge_add_le hc ha _ _
      _ ≤ gauge s (x + y) + ε := by grw [gauge_le_of_mem hε₀.le (mem_neg.1 hy.2)]
  · calc
      gauge s (x + y) ≤ gauge s x + gauge s y := gauge_add_le hc ha _ _
      _ ≤ gauge s x + ε := by grw [gauge_le_of_mem hε₀.le hy.1]

/-- If `s` is a convex neighborhood of the origin in a topological real vector space, then `gauge s`
is continuous. If the ambient space is a normed space, then `gauge s` is Lipschitz continuous, see
`Convex.lipschitz_gauge`. -/
@[continuity, fun_prop]
theorem continuous_gauge (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) : Continuous (gauge s) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_gauge hc hs₀

theorem gauge_lt_one_eq_interior (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) :
    { x | gauge s x < 1 } = interior s := by
  refine Subset.antisymm (fun x hx ↦ ?_) (interior_subset_gauge_lt_one s)
  rcases mem_openSegment_of_gauge_lt_one (absorbent_nhds_zero hs₀) hx with ⟨y, hys, hxy⟩
  exact hc.openSegment_interior_self_subset_interior (mem_interior_iff_mem_nhds.2 hs₀) hys hxy

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
  rfl

end TopologicalVectorSpace

section RCLike

variable [RCLike 𝕜] [Module 𝕜 E] [IsScalarTower ℝ 𝕜 E]

/-- `gauge s` as a seminorm when `s` is balanced, convex and absorbent. -/
@[simps!]
def gaugeSeminorm (hs₀ : Balanced 𝕜 s) (hs₁ : Convex ℝ s) (hs₂ : Absorbent ℝ s) : Seminorm 𝕜 E :=
  Seminorm.of (gauge s) (gauge_add_le hs₁ hs₂) (gauge_smul hs₀)

variable {hs₀ : Balanced 𝕜 s} {hs₁ : Convex ℝ s} {hs₂ : Absorbent ℝ s} [TopologicalSpace E]
  [ContinuousSMul ℝ E]

theorem gaugeSeminorm_lt_one_of_isOpen (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    gaugeSeminorm hs₀ hs₁ hs₂ x < 1 :=
  gauge_lt_one_of_mem_of_isOpen hs hx

theorem gaugeSeminorm_ball_one (hs : IsOpen s) : (gaugeSeminorm hs₀ hs₁ hs₂).ball 0 1 = s := by
  rw [Seminorm.ball_zero_eq]
  exact gauge_lt_one_eq_self_of_isOpen hs₁ hs₂.zero_mem hs

end RCLike

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp]
protected theorem Seminorm.gauge_ball (p : Seminorm ℝ E) : gauge (p.ball 0 1) = p := by
  ext x
  obtain hp | hp := { r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1 }.eq_empty_or_nonempty
  · rw [gauge, hp, Real.sInf_empty]
    by_contra h
    have hpx : 0 < p x := (apply_nonneg _ _).lt_of_ne h
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, ?_, smul_inv_smul₀ hpx₂.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂),
      inv_mul_lt_iff₀ hpx₂, mul_one]
    exact lt_mul_of_one_lt_left hpx one_lt_two
  refine IsGLB.csInf_eq ⟨fun r => ?_, fun r hr => le_of_forall_pos_le_add fun ε hε => ?_⟩ hp
  · rintro ⟨hr, y, hy, rfl⟩
    rw [p.mem_ball_zero] at hy
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_right hr.le hy.le
  · have hpε : 0 < p x + ε := by positivity
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, ?_, smul_inv_smul₀ hpε.ne' _⟩
    rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε),
      inv_mul_lt_iff₀ hpε, mul_one]
    exact lt_add_of_pos_right _ hε

theorem Seminorm.gaugeSeminorm_ball (p : Seminorm ℝ E) :
    gaugeSeminorm (p.balanced_ball_zero 1) (p.convex_ball 0 1) (p.absorbent_ball_zero zero_lt_one) =
      p :=
  DFunLike.coe_injective p.gauge_ball

end AddCommGroup

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

theorem gauge_unit_ball (x : E) : gauge (ball (0 : E) 1) x = ‖x‖ := by
  rw [← ball_normSeminorm ℝ, Seminorm.gauge_ball, coe_normSeminorm]

theorem gauge_ball (hr : 0 ≤ r) (x : E) : gauge (ball (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · rw [← smul_unitBall_of_pos hr, gauge_smul_left, Pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul]
    simp_rw [mem_ball_zero_iff, norm_neg]
    exact fun _ => id

@[simp]
theorem gauge_closure_zero : gauge (closure (0 : Set E)) = 0 := funext fun x ↦ by
  simp only [← singleton_zero, gauge_def', mem_closure_zero_iff_norm, norm_smul, mul_eq_zero,
    norm_eq_zero, inv_eq_zero]
  rcases (norm_nonneg x).eq_or_lt' with hx | hx
  · convert csInf_Ioi (a := (0 : ℝ))
    exact Set.ext fun r ↦ and_iff_left (.inr hx)
  · convert Real.sInf_empty
    exact eq_empty_of_forall_notMem fun r ⟨hr₀, hr⟩ ↦ hx.ne' <| hr.resolve_left hr₀.out.ne'

@[simp]
theorem gauge_closedBall (hr : 0 ≤ r) (x : E) : gauge (closedBall (0 : E) r) x = ‖x‖ / r := by
  rcases hr.eq_or_lt with rfl | hr'
  · rw [div_zero, closedBall_zero', singleton_zero, gauge_closure_zero]; rfl
  · apply le_antisymm
    · rw [← gauge_ball hr]
      exact gauge_mono (absorbent_ball_zero hr') ball_subset_closedBall x
    · suffices ∀ᶠ R in 𝓝[>] r, ‖x‖ / R ≤ gauge (closedBall 0 r) x by
        refine le_of_tendsto ?_ this
        exact tendsto_const_nhds.div inf_le_left hr'.ne'
      filter_upwards [self_mem_nhdsWithin] with R hR
      rw [← gauge_ball (hr.trans hR.out.le)]
      refine gauge_mono ?_ (closedBall_subset_ball hR) _
      exact (absorbent_ball_zero hr').mono ball_subset_closedBall

theorem mul_gauge_le_norm (hs : Metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ‖x‖ := by
  obtain hr | hr := le_or_gt r 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hr <| gauge_nonneg _).trans (norm_nonneg _)
  rw [mul_comm, ← le_div_iff₀ hr, ← gauge_ball hr.le]
  exact gauge_mono (absorbent_ball_zero hr) hs x

theorem Convex.lipschitzWith_gauge {r : ℝ≥0} (hc : Convex ℝ s) (hr : 0 < r)
    (hs : Metric.ball (0 : E) r ⊆ s) : LipschitzWith r⁻¹ (gauge s) :=
  have : Absorbent ℝ (Metric.ball (0 : E) r) := absorbent_ball_zero hr
  LipschitzWith.of_le_add_mul _ fun x y =>
    calc
      gauge s x = gauge s (y + (x - y)) := by simp
      _ ≤ gauge s y + gauge s (x - y) := gauge_add_le hc (this.mono hs) _ _
      _ ≤ gauge s y + ‖x - y‖ / r := by grw [gauge_mono this hs (x - y), gauge_ball]; positivity
      _ = gauge s y + r⁻¹ * dist x y := by rw [dist_eq_norm, div_eq_inv_mul, NNReal.coe_inv]

theorem Convex.lipschitz_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    ∃ K, LipschitzWith K (gauge s) :=
  let ⟨r, hr₀, hr⟩ := Metric.mem_nhds_iff.1 h₀
  ⟨(⟨r, hr₀.le⟩ : ℝ≥0)⁻¹, hc.lipschitzWith_gauge hr₀ hr⟩

theorem Convex.uniformContinuous_gauge (hc : Convex ℝ s) (h₀ : s ∈ 𝓝 (0 : E)) :
    UniformContinuous (gauge s) :=
  let ⟨_K, hK⟩ := hc.lipschitz_gauge h₀; hK.uniformContinuous

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {r : ℝ} {x : E}
open Metric

theorem le_gauge_of_subset_closedBall (hs : Absorbent ℝ s) (hr : 0 ≤ r) (hsr : s ⊆ closedBall 0 r) :
    ‖x‖ / r ≤ gauge s x := by
  rw [← gauge_closedBall hr]
  exact gauge_mono hs hsr _

end Normed
