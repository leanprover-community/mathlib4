/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Order.Filter.Pointwise
import Mathlib.Order.LiminfLimsup

#align_import analysis.normed.group.basic from "leanprover-community/mathlib"@"41bef4ae1254365bc190aee63b947674d2977f01"

/-!
# Boundedness in normed groups

This file rephrases metric boundedness in terms of norms.

## Tags

normed group
-/

open Filter Metric Bornology
open scoped Pointwise Topology

variable {α ι E F G : Type*}

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive (attr := simp) comap_norm_atTop]
lemma comap_norm_atTop' : comap norm atTop = cobounded E := by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive Filter.HasBasis.cobounded_of_norm]
lemma Filter.HasBasis.cobounded_of_norm' {ι : Sort*} {p : ι → Prop} {s : ι → Set ℝ}
    (h : HasBasis atTop p s) : HasBasis (cobounded E) p fun i ↦ norm ⁻¹' s i :=
  comap_norm_atTop' (E := E) ▸ h.comap _

@[to_additive Filter.hasBasis_cobounded_norm]
lemma Filter.hasBasis_cobounded_norm' : HasBasis (cobounded E) (fun _ ↦ True) ({x | · ≤ ‖x‖}) :=
  atTop_basis.cobounded_of_norm'

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]
lemma tendsto_norm_atTop_iff_cobounded' {f : α → E} {l : Filter α} :
    Tendsto (‖f ·‖) l atTop ↔ Tendsto f l (cobounded E) := by
  rw [← comap_norm_atTop', tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]
lemma tendsto_norm_cobounded_atTop' : Tendsto norm (cobounded E) atTop :=
  tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive eventually_cobounded_le_norm]
lemma eventually_cobounded_le_norm' (a : ℝ) : ∀ᶠ x in cobounded E, a ≤ ‖x‖ :=
  tendsto_norm_cobounded_atTop'.eventually_ge_atTop a

@[to_additive tendsto_norm_cocompact_atTop]
lemma tendsto_norm_cocompact_atTop' [ProperSpace E] : Tendsto norm (cocompact E) atTop :=
  cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'
#align tendsto_norm_cocompact_at_top' tendsto_norm_cocompact_atTop'
#align tendsto_norm_cocompact_at_top tendsto_norm_cocompact_atTop

@[to_additive (attr := simp)]
lemma Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E := by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, (· ∘ ·), norm_inv']

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. -/
@[to_additive "In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity."]
theorem Filter.tendsto_inv_cobounded : Tendsto Inv.inv (cobounded E) (cobounded E) :=
  inv_cobounded.le
#align filter.tendsto_inv_cobounded Filter.tendsto_inv_cobounded
#align filter.tendsto_neg_cobounded Filter.tendsto_neg_cobounded

@[to_additive isBounded_iff_forall_norm_le]
lemma isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)
#align bounded_iff_forall_norm_le' isBounded_iff_forall_norm_le'
#align bounded_iff_forall_norm_le isBounded_iff_forall_norm_le

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'
#align metric.bounded.exists_norm_le' Bornology.IsBounded.exists_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le
#align metric.bounded.exists_norm_le Bornology.IsBounded.exists_norm_le

attribute [to_additive existing exists_norm_le] Bornology.IsBounded.exists_norm_le'

@[to_additive exists_pos_norm_le]
lemma Bornology.IsBounded.exists_pos_norm_le' (hs : IsBounded s) : ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R :=
  let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
  ⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans <| le_max_left _ _⟩
#align metric.bounded.exists_pos_norm_le' Bornology.IsBounded.exists_pos_norm_le'
#align metric.bounded.exists_pos_norm_le Bornology.IsBounded.exists_pos_norm_le

@[to_additive Bornology.IsBounded.exists_pos_norm_lt]
lemma Bornology.IsBounded.exists_pos_norm_lt' (hs : IsBounded s) : ∃ R > 0, ∀ x ∈ s, ‖x‖ < R :=
  let ⟨R, hR₀, hR⟩ := hs.exists_pos_norm_le'
  ⟨R + 1, by positivity, fun x hx ↦ (hR x hx).trans_lt (lt_add_one _)⟩

@[to_additive]
lemma NormedCommGroup.cauchySeq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ‖u m / u n‖ < ε := by
  simp [Metric.cauchySeq_iff, dist_eq_norm_div]
#align normed_comm_group.cauchy_seq_iff NormedCommGroup.cauchySeq_iff
#align normed_add_comm_group.cauchy_seq_iff NormedAddCommGroup.cauchySeq_iff

@[to_additive IsCompact.exists_bound_of_continuousOn]
lemma IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {f : α → E} (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C :=
  (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
    hC _ <| Set.mem_image_of_mem _ hx
#align is_compact.exists_bound_of_continuous_on' IsCompact.exists_bound_of_continuousOn'
#align is_compact.exists_bound_of_continuous_on IsCompact.exists_bound_of_continuousOn

@[to_additive]
lemma HasCompactMulSupport.exists_bound_of_continuous [TopologicalSpace α]
    {f : α → E} (hf : HasCompactMulSupport f) (h'f : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
lemma Filter.Tendsto.op_one_isBoundedUnder_le' {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∃ A, ∀ x y, ‖op x y‖ ≤ A * ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  cases' h_op with A h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedCommGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA <| norm_nonneg' _) <|
      norm_nonneg' _).trans_lt ε₀
  calc
    A * ‖f i‖ * ‖g i‖ ≤ A * δ * C := by gcongr; exact hg
    _ = A * C * δ := mul_right_comm _ _ _
    _ < ε := hδ
#align filter.tendsto.op_one_is_bounded_under_le' Filter.Tendsto.op_one_isBoundedUnder_le'
#align filter.tendsto.op_zero_is_bounded_under_le' Filter.Tendsto.op_zero_isBoundedUnder_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so
that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_isBoundedUnder_le {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (Norm.norm ∘ g)) (op : E → F → G)
    (h_op : ∀ x y, ‖op x y‖ ≤ ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩
#align filter.tendsto.op_one_is_bounded_under_le Filter.Tendsto.op_one_isBoundedUnder_le
#align filter.tendsto.op_zero_is_bounded_under_le Filter.Tendsto.op_zero_isBoundedUnder_le

end SeminormedGroup

section NormedAddGroup
variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

lemma Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCompactSupport f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm
#align continuous.bounded_above_of_compact_support Continuous.bounded_above_of_compact_support

end NormedAddGroup

section NormedAddGroupSource
variable [NormedAddGroup α] {f : α → E}

@[to_additive]
lemma HasCompactMulSupport.exists_pos_le_norm [One E] (hf : HasCompactMulSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : α, R ≤ ‖x‖ → f x = 1 := by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) ?_)⟩
  -- Porting note: `ENNReal.add_lt_add` should be `protected`?
  -- [context: we used `_root_.add_lt_add` in a previous version of this proof]
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one
#align has_compact_mul_support.exists_pos_le_norm HasCompactMulSupport.exists_pos_le_norm
#align has_compact_support.exists_pos_le_norm HasCompactSupport.exists_pos_le_norm

end NormedAddGroupSource
