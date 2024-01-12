/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Lattice

#align_import analysis.normed.order.lattice from "leanprover-community/mathlib"@"5dc275ec639221ca4d5f56938eb966f6ad9bc89f"

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `NormedLatticeAddCommGroup` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/


/-!
### Normed lattice ordered groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/


-- porting note: this now exists as a global notation
-- local notation "|" a "|" => abs a

section SolidNorm

/-- Let `α` be an `AddCommGroup` with a `Lattice` structure. A norm on `α` is *solid* if, for `a`
and `b` in `α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`.
-/
class HasSolidNorm (α : Type*) [NormedAddCommGroup α] [Lattice α] : Prop where
  solid : ∀ ⦃x y : α⦄, |x| ≤ |y| → ‖x‖ ≤ ‖y‖
#align has_solid_norm HasSolidNorm

variable {α : Type*} [NormedAddCommGroup α] [Lattice α] [HasSolidNorm α]

theorem norm_le_norm_of_abs_le_abs {a b : α} (h : |a| ≤ |b|) : ‖a‖ ≤ ‖b‖ :=
  HasSolidNorm.solid h
#align norm_le_norm_of_abs_le_abs norm_le_norm_of_abs_le_abs

/-- If `α` has a solid norm, then the balls centered at the origin of `α` are solid sets. -/
theorem LatticeOrderedAddCommGroup.isSolid_ball (r : ℝ) :
    LatticeOrderedAddCommGroup.IsSolid (Metric.ball (0 : α) r) := fun _ hx _ hxy =>
  mem_ball_zero_iff.mpr ((HasSolidNorm.solid hxy).trans_lt (mem_ball_zero_iff.mp hx))
#align lattice_ordered_add_comm_group.is_solid_ball LatticeOrderedAddCommGroup.isSolid_ball

instance : HasSolidNorm ℝ := ⟨fun _ _ => id⟩

instance : HasSolidNorm ℚ := ⟨fun _ _ _ => by simpa only [norm, ← Rat.cast_abs, Rat.cast_le] ⟩

end SolidNorm

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `‖a‖ ≤ ‖b‖`. Then `α` is
said to be a normed lattice ordered group.
-/
class NormedLatticeAddCommGroup (α : Type*) extends NormedAddCommGroup α, Lattice α, HasSolidNorm α
  where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
#align normed_lattice_add_comm_group NormedLatticeAddCommGroup

instance Real.normedLatticeAddCommGroup : NormedLatticeAddCommGroup ℝ where
  add_le_add_left _ _ h _ := add_le_add le_rfl h

-- see Note [lower instance priority]
/-- A normed lattice ordered group is an ordered additive commutative group
-/
instance (priority := 100) NormedLatticeAddCommGroup.toOrderedAddCommGroup {α : Type*}
    [h : NormedLatticeAddCommGroup α] : OrderedAddCommGroup α :=
  { h with }
#align normed_lattice_add_comm_group_to_ordered_add_comm_group NormedLatticeAddCommGroup.toOrderedAddCommGroup

variable {α : Type*} [NormedLatticeAddCommGroup α]

open LatticeOrderedGroup LatticeOrderedCommGroup HasSolidNorm

theorem dual_solid (a b : α) (h : b ⊓ -b ≤ a ⊓ -a) : ‖a‖ ≤ ‖b‖ := by
  apply solid
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg a]
  rw [← neg_inf]
  rw [abs_eq_sup_neg]
  nth_rw 1 [← neg_neg b]
  rwa [← neg_inf, neg_le_neg_iff, @inf_comm _ _ _ b, @inf_comm _ _ _ a]
#align dual_solid dual_solid

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
instance (priority := 100) OrderDual.normedLatticeAddCommGroup : NormedLatticeAddCommGroup αᵒᵈ :=
  { OrderDual.orderedAddCommGroup, OrderDual.normedAddCommGroup, OrderDual.lattice α with
    solid := dual_solid (α := α) }

theorem norm_abs_eq_norm (a : α) : ‖|a|‖ = ‖a‖ :=
  (solid (abs_abs a).le).antisymm (solid (abs_abs a).symm.le)
#align norm_abs_eq_norm norm_abs_eq_norm

theorem norm_inf_sub_inf_le_add_norm (a b c d : α) : ‖a ⊓ b - c ⊓ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_trans (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊓ b - c ⊓ d| = |a ⊓ b - c ⊓ b + (c ⊓ b - c ⊓ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊓ b - c ⊓ b| + |c ⊓ b - c ⊓ d| := (abs_add_le _ _)
    _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_inf_sub_inf_le_abs _ _ _
      · rw [@inf_comm _ _ c, @inf_comm _ _ c]
        exact abs_inf_sub_inf_le_abs _ _ _
#align norm_inf_sub_inf_le_add_norm norm_inf_sub_inf_le_add_norm

theorem norm_sup_sub_sup_le_add_norm (a b c d : α) : ‖a ⊔ b - c ⊔ d‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [← norm_abs_eq_norm (a - c), ← norm_abs_eq_norm (b - d)]
  refine' le_trans (solid _) (norm_add_le |a - c| |b - d|)
  rw [abs_of_nonneg (|a - c| + |b - d|) (add_nonneg (abs_nonneg (a - c)) (abs_nonneg (b - d)))]
  calc
    |a ⊔ b - c ⊔ d| = |a ⊔ b - c ⊔ b + (c ⊔ b - c ⊔ d)| := by rw [sub_add_sub_cancel]
    _ ≤ |a ⊔ b - c ⊔ b| + |c ⊔ b - c ⊔ d| := (abs_add_le _ _)
    _ ≤ |a - c| + |b - d| := by
      apply add_le_add
      · exact abs_sup_sub_sup_le_abs _ _ _
      · rw [@sup_comm _ _ c, @sup_comm _ _ c]
        exact abs_sup_sub_sup_le_abs _ _ _
#align norm_sup_sub_sup_le_add_norm norm_sup_sub_sup_le_add_norm

theorem norm_inf_le_add (x y : α) : ‖x ⊓ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊓ y - 0 ⊓ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_inf_sub_inf_le_add_norm x y 0 0
  simpa only [inf_idem, sub_zero] using h
#align norm_inf_le_add norm_inf_le_add

theorem norm_sup_le_add (x y : α) : ‖x ⊔ y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x ⊔ y - 0 ⊔ 0‖ ≤ ‖x - 0‖ + ‖y - 0‖ := norm_sup_sub_sup_le_add_norm x y 0 0
  simpa only [sup_idem, sub_zero] using h
#align norm_sup_le_add norm_sup_le_add

-- see Note [lower instance priority]
/-- Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
instance (priority := 100) NormedLatticeAddCommGroup.continuousInf : ContinuousInf α := by
  refine' ⟨continuous_iff_continuousAt.2 fun q => tendsto_iff_norm_sub_tendsto_zero.2 <| _⟩
  have : ∀ p : α × α, ‖p.1 ⊓ p.2 - q.1 ⊓ q.2‖ ≤ ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := fun _ =>
    norm_inf_sub_inf_le_add_norm _ _ _ _
  refine' squeeze_zero (fun e => norm_nonneg _) this _
  convert ((continuous_fst.tendsto q).sub <| tendsto_const_nhds).norm.add
    ((continuous_snd.tendsto q).sub <| tendsto_const_nhds).norm
  simp
#align normed_lattice_add_comm_group_has_continuous_inf NormedLatticeAddCommGroup.continuousInf

-- see Note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.continuousSup {α : Type*}
    [NormedLatticeAddCommGroup α] : ContinuousSup α :=
  OrderDual.continuousSup αᵒᵈ
#align normed_lattice_add_comm_group_has_continuous_sup NormedLatticeAddCommGroup.continuousSup

-- see Note [lower instance priority]
/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
instance (priority := 100) NormedLatticeAddCommGroup.toTopologicalLattice : TopologicalLattice α :=
  TopologicalLattice.mk
#align normed_lattice_add_comm_group_topological_lattice NormedLatticeAddCommGroup.toTopologicalLattice

theorem norm_abs_sub_abs (a b : α) : ‖|a| - |b|‖ ≤ ‖a - b‖ :=
  solid (LatticeOrderedCommGroup.abs_abs_sub_abs_le _ _)
#align norm_abs_sub_abs norm_abs_sub_abs

theorem norm_sup_sub_sup_le_norm (x y z : α) : ‖x ⊔ z - y ⊔ z‖ ≤ ‖x - y‖ :=
  solid (abs_sup_sub_sup_le_abs x y z)
#align norm_sup_sub_sup_le_norm norm_sup_sub_sup_le_norm

theorem norm_inf_sub_inf_le_norm (x y z : α) : ‖x ⊓ z - y ⊓ z‖ ≤ ‖x - y‖ :=
  solid (abs_inf_sub_inf_le_abs x y z)
#align norm_inf_sub_inf_le_norm norm_inf_sub_inf_le_norm

theorem lipschitzWith_sup_right (z : α) : LipschitzWith 1 fun x => x ⊔ z :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_sup_sub_sup_le_norm x y z
#align lipschitz_with_sup_right lipschitzWith_sup_right

theorem lipschitzWith_pos : LipschitzWith 1 (PosPart.pos : α → α) :=
  lipschitzWith_sup_right 0
#align lipschitz_with_pos lipschitzWith_pos

theorem continuous_pos : Continuous (PosPart.pos : α → α) :=
  LipschitzWith.continuous lipschitzWith_pos
#align continuous_pos continuous_pos

theorem continuous_neg' : Continuous (NegPart.neg : α → α) := by
  refine continuous_pos.comp <| @continuous_neg _ _ _ TopologicalAddGroup.toContinuousNeg
  -- porting note: see the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/can't.20infer.20.60ContinuousNeg.60)
#align continuous_neg' continuous_neg'

theorem isClosed_nonneg {E} [NormedLatticeAddCommGroup E] : IsClosed { x : E | 0 ≤ x } := by
  suffices { x : E | 0 ≤ x } = NegPart.neg ⁻¹' {(0 : E)} by
    rw [this]
    exact IsClosed.preimage continuous_neg' isClosed_singleton
  ext1 x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
    @neg_eq_zero_iff E _ _ (OrderedAddCommGroup.to_covariantClass_left_le E)]
  -- porting note: I'm not sure why Lean couldn't synthesize this instance because it works with
  -- `have : CovariantClass E E (· + ·) (· ≤ ·) := inferInstance`
#align is_closed_nonneg isClosed_nonneg

theorem isClosed_le_of_isClosed_nonneg {G} [OrderedAddCommGroup G] [TopologicalSpace G]
    [ContinuousSub G] (h : IsClosed { x : G | 0 ≤ x }) :
    IsClosed { p : G × G | p.fst ≤ p.snd } := by
  have : { p : G × G | p.fst ≤ p.snd } = (fun p : G × G => p.snd - p.fst) ⁻¹' { x : G | 0 ≤ x } :=
    by ext1 p; simp only [sub_nonneg, Set.preimage_setOf_eq]
  rw [this]
  exact IsClosed.preimage (continuous_snd.sub continuous_fst) h
#align is_closed_le_of_is_closed_nonneg isClosed_le_of_isClosed_nonneg

-- See note [lower instance priority]
instance (priority := 100) NormedLatticeAddCommGroup.orderClosedTopology {E}
    [NormedLatticeAddCommGroup E] : OrderClosedTopology E :=
  ⟨isClosed_le_of_isClosed_nonneg isClosed_nonneg⟩
#align normed_lattice_add_comm_group.order_closed_topology NormedLatticeAddCommGroup.orderClosedTopology
