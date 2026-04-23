/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Algebra.Ring.AddAut
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.ApplyFun
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.LeftRight

/-!
# The additive circle

We define the additive circle `AddCircle p` as the quotient `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`.

See also `Circle` and `Real.Angle`.  For the normed group structure on `AddCircle`, see
`AddCircle.NormedAddCommGroup` in a later file.

## Main definitions and results:

* `AddCircle`: the additive circle `𝕜 ⧸ ℤ ∙ p` for some period `p : 𝕜`
* `UnitAddCircle`: the special case `ℝ ⧸ ℤ`
* `AddCircle.equivAddCircle`: the rescaling equivalence `AddCircle p ≃+ AddCircle q`
* `AddCircle.equivIco` and `AddCircle.equivIoc`: the natural equivalences
  `AddCircle p ≃ Ico a (a + p)` and `AddCircle p ≃ Ioc a (a + p)`
* `AddCircle.addOrderOf_div_of_gcd_eq_one`: rational points have finite order
* `AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder`: finite-order points are rational
* `AddCircle.homeoIccQuot`: the natural topological equivalence between `AddCircle p` and
  `Icc a (a + p)` with its endpoints identified.
* `AddCircle.liftIco_continuous` and `AddCircle.liftIoc_continuous`: if `f : ℝ → B` is continuous,
  and `f a = f (a + p)` for some `a`, then there is a continuous function `AddCircle p → B`
  which agrees with `f` on `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `AddCircle (1 : ℚ)`, and so we set things up more generally.

## TODO

* Link with periodicity
* Lie group structure
* Exponential equivalence to `Circle`

-/

@[expose] public section


noncomputable section

open AddCommGroup Set Function AddSubgroup TopologicalSpace

open Topology

variable {𝕜 B : Type*}

section Continuity

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {p : 𝕜} (hp : 0 < p) (a x : 𝕜)

/-- `toIcoDiv` is eventually constant on the right at every point. -/
theorem eventuallyEq_toIcoDiv_nhdsGE : toIcoDiv hp a =ᶠ[𝓝[≥] x] fun _ ↦ toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsGE_of_mem
  rw [← sub_mem_Ico_iff_left, ← toIcoDiv_eq_iff]

/-- `toIcoDiv` is continuous on the right at every point.

In fact, a stronger statement is true:
it's eventually constant on the right, see `eventuallyEq_toIcoDiv_nhdsGE`. -/
theorem continuousWithinAt_toIcoDiv_Ici : ContinuousWithinAt (toIcoDiv hp a) (Ici x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIcoDiv_nhdsGE hp a x) |>.mono_right <| pure_le_nhds _

/-- `toIocDiv` is eventually constant on the left at every point. -/
theorem eventuallyEq_toIocDiv_nhdsLE : toIocDiv hp a =ᶠ[𝓝[≤] x] fun _ ↦ toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsLE_of_mem
  rw [← sub_mem_Ioc_iff_left, ← toIocDiv_eq_iff]

/-- `toIocDiv` is continuous on the left at every point.

In fact, a stronger statement is true:
it's eventually constant on the left, see `eventuallyEq_toIocDiv_nhdsLE`. -/
theorem continuousWithinAt_toIocDiv_Iic : ContinuousWithinAt (toIocDiv hp a) (Iic x) x :=
  Filter.tendsto_pure.mpr (eventuallyEq_toIocDiv_nhdsLE hp a x) |>.mono_right <| pure_le_nhds _

/-- `toIcoMod` is continuous on the right at every point. -/
theorem continuousWithinAt_toIcoMod_Ici : ContinuousWithinAt (toIcoMod hp a) (Ici x) x :=
  continuousWithinAt_id.sub <|
    (continuousWithinAt_toIcoDiv_Ici hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_right_toIcoMod := continuousWithinAt_toIcoMod_Ici

/-- `toIocMod` is continuous on the right at every point. -/
theorem continuousWithinAt_toIocMod_Iic : ContinuousWithinAt (toIocMod hp a) (Iic x) x :=
  continuousWithinAt_id.sub <|
    (continuousWithinAt_toIocDiv_Iic hp a x).smul continuousWithinAt_const

@[deprecated (since := "2026-01-04")]
alias continuous_left_toIocMod := continuousWithinAt_toIocMod_Iic

/-- At every point `x`, for all `y < x` sufficiently close to `x`,
we have `toIcoDiv hp a y = toIocDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
theorem eventuallyEq_toIcoDiv_nhdsLT : toIcoDiv hp a =ᶠ[𝓝[<] x] fun _ ↦ toIocDiv hp a x := by
  simp only [Filter.EventuallyEq, toIcoDiv_eq_iff, sub_mem_Ico_iff_left]
  apply Ico_mem_nhdsLT_of_mem
  rw [← sub_mem_Ioc_iff_left, ← toIocDiv_eq_iff]

/-- At every point `x`, for all `y > x` sufficiently close to `x`,
we have `toIocDiv hp a y = toIcoDiv hp a x`.

Note that we use different functions on the LHS and on the RHS.
-/
theorem eventuallyEq_toIocDiv_nhdsGT : toIocDiv hp a =ᶠ[𝓝[>] x] fun _ ↦ toIcoDiv hp a x := by
  simp only [Filter.EventuallyEq, toIocDiv_eq_iff, sub_mem_Ioc_iff_left]
  apply Ioc_mem_nhdsGT_of_mem
  rw [← sub_mem_Ico_iff_left, ← toIcoDiv_eq_iff]

variable {x}

/-- If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is locally constant near `x`. -/
theorem eventuallyEq_toIcoDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIcoDiv hp a =ᶠ[𝓝 x] fun _ ↦ toIcoDiv hp a x := by
  rw [← nhdsLT_sup_nhdsGE, Filter.EventuallyEq, Filter.eventually_sup]
  refine ⟨?_, eventuallyEq_toIcoDiv_nhdsGE hp a x⟩
  convert (eventuallyEq_toIcoDiv_nhdsLT hp a x).eventually using 3
  rwa [← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/-- If `x` is not congruent to `a` modulo `p`, then `toIcoDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIcoDiv_nhds`. -/
theorem continuousAt_toIcoDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIcoDiv hp a) x :=
  tendsto_nhds_of_eventually_eq <| eventuallyEq_toIcoDiv_nhds hp a hx

/-- `toIcoDiv` is continuous on the set of points that are not congruent to `a` modulo `p`. -/
theorem continuousOn_toIcoDiv : ContinuousOn (toIcoDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx ↦
  (continuousAt_toIcoDiv hp a hx).continuousWithinAt

/-- If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is locally constant near `x`. -/
theorem eventuallyEq_toIocDiv_nhds (hx : ¬x ≡ a [PMOD p]) :
    toIocDiv hp a =ᶠ[𝓝 x] fun _ ↦ toIocDiv hp a x := by
  rw [← nhdsLE_sup_nhdsGT, Filter.EventuallyEq, Filter.eventually_sup]
  refine ⟨eventuallyEq_toIocDiv_nhdsLE hp a x, ?_⟩
  convert (eventuallyEq_toIocDiv_nhdsGT hp a x).eventually using 3
  rwa [eq_comm, ← not_modEq_iff_toIcoDiv_eq_toIocDiv, AddCommGroup.modEq_comm]

/-- If `x` is not congruent to `a` modulo `p`, then `toIocDiv` is continuous at `x`.

In fact, it is locally near `x`, see `eventuallyEq_toIocDiv_nhds`. -/
theorem continuousAt_toIocDiv (hx : ¬x ≡ a [PMOD p]) :
    ContinuousAt (toIocDiv hp a) x :=
  tendsto_nhds_of_eventually_eq <| eventuallyEq_toIocDiv_nhds hp a hx

/-- `toIocDiv` is continuous on the set of points
that aren't congruent to the endpoint modulo the period. -/
theorem continuousOn_toIocDiv :
    ContinuousOn (toIocDiv hp a) {x | ¬x ≡ a [PMOD p]} := fun _x hx ↦
  (continuousAt_toIocDiv hp a hx).continuousWithinAt

theorem toIcoMod_eventuallyEq_toIocMod (hx : ¬x ≡ a [PMOD p]) :
    toIcoMod hp a =ᶠ[𝓝 x] toIocMod hp a := by
  refine IsOpen.mem_nhds ?_ ?_
  · rw [Ico_eq_locus_Ioc_eq_iUnion_Ioo]
    exact isOpen_iUnion fun i => isOpen_Ioo
  · rwa [mem_setOf_eq, ← not_modEq_iff_toIcoMod_eq_toIocMod hp, AddCommGroup.modEq_comm]

theorem continuousAt_toIcoMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIcoMod hp a) x :=
  continuousAt_id.sub <| tendsto_nhds_of_eventually_eq <|
    (eventuallyEq_toIcoDiv_nhds hp a hx).fun_comp (· • p)

theorem continuousAt_toIocMod (hx : ¬x ≡ a [PMOD p]) : ContinuousAt (toIocMod hp a) x :=
  continuousAt_id.sub <| tendsto_nhds_of_eventually_eq <|
    (eventuallyEq_toIocDiv_nhds hp a hx).fun_comp (· • p)

end Continuity

/-- The "additive circle": `𝕜 ⧸ ℤ ∙ p`. See also `Circle` and `Real.Angle`. -/
abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p

namespace AddCircle

section LinearOrderedAddCommGroup

variable [AddCommGroup 𝕜] (p : 𝕜)

theorem coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl

theorem coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl

theorem coe_add (x y : 𝕜) : (↑(x + y) : AddCircle p) = (x : AddCircle p) + (y : AddCircle p) :=
  rfl

theorem coe_sub (x y : 𝕜) : (↑(x - y) : AddCircle p) = (x : AddCircle p) - (y : AddCircle p) :=
  rfl

theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl

@[norm_cast]
theorem coe_zero : ↑(0 : 𝕜) = (0 : AddCircle p) :=
  rfl

theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]

theorem coe_period : (p : AddCircle p) = 0 :=
  (QuotientAddGroup.eq_zero_iff p).2 <| mem_zmultiples p

theorem coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCircle p) = x := by
  rw [coe_add, ← eq_sub_iff_add_eq', sub_self, coe_period]

@[continuity, nolint unusedArguments]
protected theorem continuous_mk' [TopologicalSpace 𝕜] :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng

section Torsion

-- TODO: move this (and the definition `AddCircle`) to GroupTheory.QuotientGroup.Basic
open QuotientAddGroup Cardinal in
theorem card_torsion_le_of_isSMulRegular (n : ℕ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n := by
  have (x : {x : AddCircle p | n • x = 0}) : ∃ (k : Fin n) (y : 𝕜), y = x.1 ∧ n • y = k.1 • p := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := mk_surjective x
    rw [Set.mem_setOf, ← mk_nsmul, eq_zero_iff] at hx
    have ⟨m', hm⟩ := hx
    have : NeZero n := ⟨h0⟩
    rw [← (Int.divModEquiv n).symm_apply_apply m', Int.divModEquiv_symm_apply] at hm
    set m := m'.divModEquiv n
    use m.2, y - m.1 • p
    simp_rw [mk_sub, mk_zsmul, sub_eq_self, coe_period, smul_zero]
    rw [smul_sub, sub_eq_iff_eq_add, ← hm, add_comm]
    simp [add_smul, mul_comm, mul_smul]
  choose f hf using this
  refine (ENat.card_le_card_of_injective (f := f) fun x x' eq ↦ Subtype.ext ?_).trans (by simp)
  have ⟨y, hyx, hy⟩ := hf x
  have ⟨y', hyx', hy'⟩ := hf x'
  rw [eq, ← hy', hn.eq_iff] at hy
  rw [← hyx, hy, hyx']

theorem finite_torsion_of_isSMulRegular (n : ℕ) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
    (card_torsion_le_of_isSMulRegular p n h0 hn).trans_lt <| ENat.coe_lt_top n]

theorem card_torsion_le_of_isSMulRegular_int (n : ℤ) (h0 : n ≠ 0) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.encard ≤ n.natAbs := by
  convert card_torsion_le_of_isSMulRegular p _
    (Int.natAbs_ne_zero.mpr h0) (IsSMulRegular.natAbs_iff.mpr hn) using 1
  simp

theorem finite_torsion_of_isSMulRegular_int (n : ℤ) (hn : IsSMulRegular 𝕜 n) :
    {x : AddCircle p | n • x = 0}.Finite := by
  nontriviality 𝕜
  obtain rfl | h0 := eq_or_ne n 0
  exacts [hn.not_zero.elim, ENat.card_lt_top.mp <|
    (card_torsion_le_of_isSMulRegular_int p n h0 hn).trans_lt <| ENat.coe_lt_top _]

end Torsion

variable [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]

theorem finite_torsion {n : ℕ} (hn : 0 < n) : { u : AddCircle p | n • u = 0 }.Finite :=
  finite_torsion_of_isSMulRegular _ _ <| .of_right_eq_zero_of_smul fun _ ↦ by simp [hn.ne']

theorem finite_setOf_addOrderOf_eq {n : ℕ} (hn : 0 < n) :
    {u : AddCircle p | addOrderOf u = n}.Finite :=
  (finite_torsion p hn).subset fun _ h ↦ ((addOrderOf_eq_iff hn).mp h).1

theorem coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
    (x : AddCircle p) = 0 ↔ ∃ n : ℕ, n • p = x := by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n := by
      contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : ℤ), by simp⟩

variable [hp : Fact (0 < p)] (a : 𝕜) [Archimedean 𝕜]

/-- The equivalence between `AddCircle p` and the half-open interval `[a, a + p)`, whose inverse
is the natural quotient map. -/
def equivIco : AddCircle p ≃ Ico a (a + p) :=
  QuotientAddGroup.equivIcoMod hp.out a

/-- The equivalence between `AddCircle p` and the half-open interval `(a, a + p]`, whose inverse
is the natural quotient map. -/
def equivIoc : AddCircle p ≃ Ioc a (a + p) :=
  QuotientAddGroup.equivIocMod hp.out a

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`[a, a + p)`. -/
def liftIco (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIco p a

/-- Given a function on `𝕜`, return the unique function on `AddCircle p` agreeing with `f` on
`(a, a + p]`. -/
def liftIoc (f : 𝕜 → B) : AddCircle p → B :=
  restrict _ f ∘ AddCircle.equivIoc p a

variable {p a}

theorem equivIco_coe_eq {x : 𝕜} (hx : x ∈ Ico a (a + p)) : (equivIco p a) x = ⟨x, hx⟩ := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, equivIco, QuotientAddGroup.equivIcoMod_symm_apply]

theorem equivIoc_coe_eq {x : 𝕜} (hx : x ∈ Ioc a (a + p)) : (equivIoc p a) x = ⟨x, hx⟩ := by
  rw [Equiv.apply_eq_iff_eq_symm_apply, equivIoc, QuotientAddGroup.equivIocMod_symm_apply]

@[simp]
lemma coe_equivIco {y : AddCircle p} :
    (equivIco p a y : AddCircle p) = y :=
  (equivIco p a).left_inv y

@[simp]
lemma coe_equivIoc {y : AddCircle p} :
    (equivIoc p a y : AddCircle p) = y :=
  (equivIoc p a).left_inv y

lemma equivIco_coe_of_mem {y : 𝕜} (hy : y ∈ Ico a (a + p)) :
    equivIco p a y = y := by
  have : equivIco p a y = ⟨y, hy⟩ := (equivIco p a).right_inv ⟨y, hy⟩
  simp [this]

lemma equivIoc_coe_of_mem {y : 𝕜} (hy : y ∈ Ioc a (a + p)) :
    equivIoc p a y = y := by
  have : equivIoc p a y = ⟨y, hy⟩ := (equivIoc p a).right_inv ⟨y, hy⟩
  simp [this]

theorem coe_eq_coe_iff_of_mem_Ico {x y : 𝕜} (hx : x ∈ Ico a (a + p)) (hy : y ∈ Ico a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIco p a at h
  rw [← (equivIco p a).right_inv ⟨x, hx⟩, ← (equivIco p a).right_inv ⟨y, hy⟩]
  exact h

/-- Ioc version of `coe_eq_coe_iff_of_mem_Ico`. -/
lemma coe_eq_coe_iff_of_mem_Ioc {x y : 𝕜} (hx : x ∈ Ioc a (a + p)) (hy : y ∈ Ioc a (a + p)) :
    (x : AddCircle p) = y ↔ x = y := by
  refine ⟨fun h => ?_, by tauto⟩
  suffices (⟨x, hx⟩ : Ioc a (a + p)) = ⟨y, hy⟩ by exact Subtype.mk.inj this
  apply_fun equivIoc p a at h
  rw [← (equivIoc p a).right_inv ⟨x, hx⟩, ← (equivIoc p a).right_inv ⟨y, hy⟩]
  exact h

theorem liftIco_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico a (a + p)) :
    liftIco p a f ↑x = f x := by
  simp [liftIco, equivIco_coe_eq hx]

theorem liftIoc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) :
    liftIoc p a f ↑x = f x := by
  simp [liftIoc, equivIoc_coe_eq hx]

theorem liftIoc_eq_liftIco_of_ne {f : 𝕜 → B} {x : AddCircle p}
    (x_ne_a : x ≠ a) : liftIoc p a f x = liftIco p a f x := by
  have x_eq_b : x = ↑(equivIco p a x) := coe_equivIco.symm
  rw [x_eq_b, liftIco_coe_apply (equivIco p a x).coe_prop]
  exact liftIoc_coe_apply (by grind)

lemma liftIco_comp_apply {α β : Type*} {f : 𝕜 → α} {g : α → β} {a : 𝕜} {x : AddCircle p} :
    liftIco p a (g ∘ f) x = g (liftIco p a f x) := rfl

lemma liftIoc_comp_apply {α β : Type*} {f : 𝕜 → α} {g : α → β} {a : 𝕜} {x : AddCircle p} :
    liftIoc p a (g ∘ f) x = g (liftIoc p a f x) := rfl

lemma eq_coe_Ico (a : AddCircle p) : ∃ b ∈ Ico 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIcoMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIcoMod hp.out 0).symm_apply_apply a⟩

/-- `Ioc` version of `eq_coe_Ico`. -/
lemma eq_coe_Ioc (a : AddCircle p) : ∃ b ∈ Ioc 0 p, ↑b = a := by
  let b := QuotientAddGroup.equivIocMod hp.out 0 a
  exact ⟨b.1, by simpa only [zero_add] using b.2,
    (QuotientAddGroup.equivIocMod hp.out 0).symm_apply_apply a⟩

lemma coe_eq_zero_iff_of_mem_Ico (ha : a ∈ Ico 0 p) :
    (a : AddCircle p) = 0 ↔ a = 0 := by
  have h0 : 0 ∈ Ico 0 (0 + p) := by simpa [zero_add, left_mem_Ico] using hp.out
  have ha' : a ∈ Ico 0 (0 + p) := by rwa [zero_add]
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico ha' h0, QuotientAddGroup.mk_zero]

variable (p a)

section Continuity

variable [TopologicalSpace 𝕜]

@[continuity]
theorem continuous_equivIco_symm : Continuous (equivIco p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

@[continuity]
theorem continuous_equivIoc_symm : Continuous (equivIoc p a).symm :=
  continuous_quotient_mk'.comp continuous_subtype_val

variable [OrderTopology 𝕜] {x : AddCircle p}

theorem continuousAt_equivIco (hx : x ≠ a) : ContinuousAt (equivIco p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  exact (continuousAt_toIcoMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

theorem continuousAt_equivIoc (hx : x ≠ a) : ContinuousAt (equivIoc p a) x := by
  induction x using QuotientAddGroup.induction_on
  rw [ContinuousAt, Filter.Tendsto, QuotientAddGroup.nhds_eq, Filter.map_map]
  exact (continuousAt_toIocMod hp.out a <| not_modEq_iff_ne_mod_zmultiples.mpr hx).codRestrict _

/-- The quotient map `𝕜 → AddCircle p` as an open partial homeomorphism. -/
@[simps] def openPartialHomeomorphCoe [DiscreteTopology (zmultiples p)] :
    OpenPartialHomeomorph 𝕜 (AddCircle p) where
  toFun := (↑)
  invFun := fun x ↦ equivIco p a x
  source := Ioo a (a + p)
  target := {↑a}ᶜ
  map_source' := by
    intro x hx hx'
    exact hx.1.ne' ((coe_eq_coe_iff_of_mem_Ico (Ioo_subset_Ico_self hx)
      (left_mem_Ico.mpr (lt_add_of_pos_right a hp.out))).mp hx')
  map_target' := by
    intro x hx
    exact (eq_left_or_mem_Ioo_of_mem_Ico (equivIco p a x).2).resolve_left
      (hx ∘ ((equivIco p a).symm_apply_apply x).symm.trans ∘ congrArg _)
  left_inv' :=
    fun x hx ↦ congrArg _ ((equivIco p a).apply_symm_apply ⟨x, Ioo_subset_Ico_self hx⟩)
  right_inv' := fun x _ ↦ (equivIco p a).symm_apply_apply x
  open_source := isOpen_Ioo
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (AddCircle.continuous_mk' p).continuousOn
  continuousOn_invFun := by
    exact continuousOn_of_forall_continuousAt
      (fun _ ↦ continuousAt_subtype_val.comp ∘ continuousAt_equivIco p a)

end Continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
theorem coe_image_Ico_eq : ((↑) : 𝕜 → AddCircle p) '' Ico a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIco p a).symm.range_eq_univ

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → AddCircle p` is
the entire space. -/
@[simp]
theorem coe_image_Ioc_eq : ((↑) : 𝕜 → AddCircle p) '' Ioc a (a + p) = univ := by
  rw [image_eq_range]
  exact (equivIoc p a).symm.range_eq_univ

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → AddCircle p` is the
entire space. -/
@[simp]
theorem coe_image_Icc_eq : ((↑) : 𝕜 → AddCircle p) '' Icc a (a + p) = univ :=
  eq_top_mono (image_mono Ico_subset_Icc_self) <| coe_image_Ico_eq _ _

/-- If functions on AddCircle agree on the image of the interval `[a, a + p)` then they are equal -/
lemma Ico_ext {α : Type*} {f g : AddCircle p → α} (a : 𝕜)
    (h : ∀ x ∈ Ico a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ, ← coe_image_Ico_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

/-- If functions on AddCircle agree on the image of the interval `(a, a + p]` then they are equal -/
lemma Ioc_ext {α : Type*} {f g : AddCircle p → α} (a : 𝕜)
    (h : ∀ x ∈ Ioc a (a + p), f x = g x) : f = g := by
  rw [← Set.eqOn_univ, ← coe_image_Ioc_eq p a]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx

end LinearOrderedAddCommGroup

section LinearOrderedField

variable [Field 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_coe, AddAut.mulRight_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]

@[simp]
theorem equivAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem equivAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl

section
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- The rescaling homeomorphism between additive circles with different periods. -/
def homeomorphAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃ₜ AddCircle q :=
  ⟨equivAddCircle p q hp hq,
    (continuous_quotient_mk'.comp (continuous_mul_const (p⁻¹ * q))).quotient_lift _,
    (continuous_quotient_mk'.comp (continuous_mul_const (q⁻¹ * p))).quotient_lift _⟩

@[simp]
theorem homeomorphAddCircle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    homeomorphAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem homeomorphAddCircle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (homeomorphAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
end

lemma natCast_div_mul_eq_nsmul (r : 𝕜) (m : ℕ) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div, ← nsmul_eq_mul, coe_nsmul]

lemma intCast_div_mul_eq_zsmul (r : 𝕜) (m : ℤ) :
    (↑(↑m / q * r) : AddCircle p) = m • (r / q : AddCircle p) := by
  rw [mul_comm_div, ← zsmul_eq_mul, coe_zsmul]

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [hp : Fact (0 < p)]

section FloorRing

variable [FloorRing 𝕜]

@[simp]
theorem coe_equivIco_mk_apply (x : 𝕜) :
    (equivIco p 0 <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  toIcoMod_eq_fract_mul _ x

instance : DivisibleBy (AddCircle p) ℤ where
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p 0 x : 𝕜)) : AddCircle p)
  div_zero x := by simp
  div_cancel {n} x hn := by
    replace hn : (n : 𝕜) ≠ 0 := by norm_cast
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equivIco p 0 x)) = x
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel₀ hn, one_mul]
    exact (equivIco p 0).symm_apply_apply x

omit [IsStrictOrderedRing 𝕜] in
@[simp] lemma coe_fract (x : 𝕜) : (↑(Int.fract x) : AddCircle (1 : 𝕜)) = x := by
  simp [← Int.self_sub_floor, mem_zmultiples_iff]

end FloorRing

section FiniteOrderPoints

variable {p}

theorem addOrderOf_period_div {n : ℕ} (h : 0 < n) : addOrderOf ((p / n : 𝕜) : AddCircle p) = n := by
  rw [addOrderOf_eq_iff h]
  replace h : 0 < (n : 𝕜) := Nat.cast_pos.2 h
  refine ⟨?_, fun m hn h0 => ?_⟩ <;> simp only [Ne, ← coe_nsmul, nsmul_eq_mul]
  · rw [mul_div_cancel₀ _ h.ne', coe_period]
  rw [coe_eq_zero_of_pos_iff p hp.out (mul_pos (Nat.cast_pos.2 h0) <| div_pos hp.out h)]
  rintro ⟨k, hk⟩
  rw [mul_div, eq_div_iff h.ne', nsmul_eq_mul, mul_right_comm, ← Nat.cast_mul,
    (mul_left_injective₀ hp.out.ne').eq_iff, Nat.cast_inj, mul_comm] at hk
  exact (Nat.le_of_dvd h0 ⟨_, hk.symm⟩).not_gt hn

variable (p) in
theorem gcd_mul_addOrderOf_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
    m.gcd n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  rw [natCast_div_mul_eq_nsmul, IsOfFinAddOrder.addOrderOf_nsmul]
  · rw [addOrderOf_period_div hn, Nat.gcd_comm, Nat.mul_div_cancel']
    exact n.gcd_dvd_left m
  · rwa [← addOrderOf_pos_iff, addOrderOf_period_div hn]

theorem addOrderOf_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : m.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  convert gcd_mul_addOrderOf_div_eq p m hn
  rw [h, one_mul]

theorem addOrderOf_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : m.natAbs.gcd n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  cases m
  · simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.natAbs_natCast] at h ⊢
    exact addOrderOf_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, addOrderOf_neg]
    exact addOrderOf_div_of_gcd_eq_one hn h

theorem addOrderOf_coe_rat {q : ℚ} : addOrderOf (↑(↑q * p) : AddCircle p) = q.den := by
  have : (↑(q.den : ℤ) : 𝕜) ≠ 0 := by
    norm_cast
    exact q.pos.ne.symm
  rw [← q.num_divInt_den, Rat.cast_divInt_of_ne_zero _ this, Int.cast_natCast, Rat.num_divInt_den,
    addOrderOf_div_of_gcd_eq_one' q.pos q.reduced]

protected theorem nsmul_eq_zero_iff {u : AddCircle p} {n : ℕ} (h : 0 < n) :
    n • u = 0 ↔ ∃ m < n, ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u fun k hk ↦ ?_, ?_⟩
  · rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    rintro ⟨m, -, rfl⟩
    constructor; rw [mul_comm, eq_comm]
    exact gcd_mul_addOrderOf_div_eq p m h
  rw [← coe_nsmul, coe_eq_zero_iff] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨a.natMod n, Int.natMod_lt h.ne', ?_⟩
  have h0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 h.ne'
  rw [nsmul_eq_mul, mul_comm, ← div_eq_iff h0, ← a.ediv_mul_add_emod n, add_smul, add_div,
    zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← mul_div, mul_comm _ p,
    mul_div_cancel_right₀ p h0] at ha
  rw [← ha, coe_add, ← Int.cast_natCast, Int.natMod, Int.toNat_of_nonneg, zsmul_eq_mul,
    mul_div_right_comm, eq_comm, add_eq_right, ← zsmul_eq_mul, coe_zsmul, coe_period, smul_zero]
  exact Int.emod_nonneg _ (by exact_mod_cast h.ne')

theorem addOrderOf_eq_pos_iff {u : AddCircle p} {n : ℕ} (h : 0 < n) :
    addOrderOf u = n ↔ ∃ m < n, m.gcd n = 1 ∧ ↑(↑m / ↑n * p) = u := by
  refine ⟨QuotientAddGroup.induction_on u ?_, ?_⟩
  · rintro ⟨m, -, h₁, rfl⟩
    exact addOrderOf_div_of_gcd_eq_one h h₁
  rintro k rfl
  obtain ⟨m, hm, hk⟩ := (AddCircle.nsmul_eq_zero_iff h).mp
    (addOrderOf_nsmul_eq_zero (k : AddCircle p))
  refine ⟨m, hm, mul_right_cancel₀ h.ne' ?_, hk⟩
  convert gcd_mul_addOrderOf_div_eq p m h using 1
  · rw [hk]
  · apply one_mul

theorem exists_gcd_eq_one_of_isOfFinAddOrder {u : AddCircle p} (h : IsOfFinAddOrder u) :
    ∃ m : ℕ, m.gcd (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) / addOrderOf u * p) = u :=
  let ⟨m, hl, hg, he⟩ := (addOrderOf_eq_pos_iff h.addOrderOf_pos).1 rfl
  ⟨m, hg, hl, he⟩

lemma not_isOfFinAddOrder_iff_forall_rat_ne_div {a : 𝕜} :
    ¬ IsOfFinAddOrder (a : AddCircle p) ↔ ∀ q : ℚ, (q : 𝕜) ≠ a / p := by
  simp +contextual [← QuotientAddGroup.mk_zsmul, mul_comm (Int.cast _), mem_zmultiples_iff,
    eq_div_iff (Fact.out : 0 < p).ne', isOfFinAddOrder_iff_zsmul_eq_zero, Rat.forall, div_eq_iff,
    div_mul_eq_mul_div]
  grind

lemma isOfFinAddOrder_iff_exists_rat_eq_div {a : 𝕜} :
    IsOfFinAddOrder (a : AddCircle p) ↔ ∃ q : ℚ, (q : 𝕜) = a / p := by
  simpa using not_isOfFinAddOrder_iff_forall_rat_ne_div.not_right

variable (p)

/-- The natural bijection between points of order `n` and natural numbers less than and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : AddCircle p)` where `m` is coprime to `n` and
satisfies `0 ≤ m < n`. -/
def setAddOrderOfEquiv {n : ℕ} (hn : 0 < n) :
    { u : AddCircle p | addOrderOf u = n } ≃ { m | m < n ∧ m.gcd n = 1 } :=
  Equiv.symm <|
    Equiv.ofBijective (fun m => ⟨↑((m : 𝕜) / n * p), addOrderOf_div_of_gcd_eq_one hn m.prop.2⟩)
      (by
        refine ⟨fun m₁ m₂ h => Subtype.ext ?_, fun u => ?_⟩
        · simp_rw [Subtype.mk_eq_mk, natCast_div_mul_eq_nsmul] at h
          refine nsmul_injOn_Iio_addOrderOf ?_ ?_ h <;> rw [addOrderOf_period_div hn]
          exacts [m₁.2.1, m₂.2.1]
        · obtain ⟨m, hmn, hg, he⟩ := (addOrderOf_eq_pos_iff hn).mp u.2
          exact ⟨⟨m, hmn, hg⟩, Subtype.ext he⟩)

@[simp]
theorem card_addOrderOf_eq_totient {n : ℕ} :
    Nat.card { u : AddCircle p // addOrderOf u = n } = n.totient := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp only [Nat.totient_zero, addOrderOf_eq_zero_iff]
    rcases em (∃ u : AddCircle p, ¬IsOfFinAddOrder u) with (⟨u, hu⟩ | h)
    · have : Infinite { u : AddCircle p // ¬IsOfFinAddOrder u } := by
        rw [← coe_setOf, infinite_coe_iff]
        exact infinite_not_isOfFinAddOrder hu
      exact Nat.card_eq_zero_of_infinite
    · have : IsEmpty { u : AddCircle p // ¬IsOfFinAddOrder u } := by simpa [isEmpty_subtype] using h
      exact Nat.card_of_isEmpty
  · rw [← coe_setOf, Nat.card_congr (setAddOrderOfEquiv p hn),
      n.totient_eq_card_lt_and_coprime]
    simp only [Nat.gcd_comm]

end FiniteOrderPoints

end LinearOrderedField

end AddCircle

section IdentifyIccEnds

/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `AddCircle p`
gives an identification of `AddCircle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace AddCircle

variable [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] (p a : 𝕜)
  [hp : Fact (0 < p)]

local notation "𝕋" => AddCircle p

/-- The relation identifying the endpoints of `Icc a (a + p)`. -/
inductive EndpointIdent : Icc a (a + p) → Icc a (a + p) → Prop
  | mk :
    EndpointIdent ⟨a, left_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩
      ⟨a + p, right_mem_Icc.mpr <| le_add_of_nonneg_right hp.out.le⟩

variable [Archimedean 𝕜]

/-- The equivalence between `AddCircle p` and the quotient of `[a, a + p]` by the relation
identifying the endpoints. -/
def equivIccQuot : 𝕋 ≃ Quot (EndpointIdent p a) where
  toFun x := Quot.mk _ <| inclusion Ico_subset_Icc_self (equivIco _ _ x)
  invFun x :=
    Quot.liftOn x (↑) <| by
      rintro _ _ ⟨_⟩
      exact (coe_add_period p a).symm
  left_inv := (equivIco p a).symm_apply_apply
  right_inv :=
    Quot.ind <| by
      rintro ⟨x, hx⟩
      rcases ne_or_eq x (a + p) with (h | rfl)
      · revert x
        dsimp only
        intro x hx h
        congr
        ext1
        apply congr_arg Subtype.val ((equivIco p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩)
      · rw [← Quot.sound EndpointIdent.mk]
        dsimp only
        congr
        ext1
        apply congr_arg Subtype.val
          ((equivIco p a).right_inv ⟨a, le_refl a, lt_add_of_pos_right a hp.out⟩)

theorem equivIccQuot_comp_mk_eq_toIcoMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIcoMod hp.out a x, Ico_subset_Icc_self <| toIcoMod_mem_Ico _ _ x⟩ :=
  rfl

theorem equivIccQuot_comp_mk_eq_toIocMod :
    equivIccQuot p a ∘ Quotient.mk'' = fun x =>
      Quot.mk _ ⟨toIocMod hp.out a x, Ioc_subset_Icc_self <| toIocMod_mem_Ioc _ _ x⟩ := by
  rw [equivIccQuot_comp_mk_eq_toIcoMod]
  funext x
  by_cases h : a ≡ x [PMOD p]
  · simp_rw [(modEq_iff_toIcoMod_eq_left hp.out).1 h, (modEq_iff_toIocMod_eq_right hp.out).1 h]
    exact Quot.sound EndpointIdent.mk
  · simp_rw [(not_modEq_iff_toIcoMod_eq_toIocMod hp.out).1 h]

/-- The natural map from `[a, a + p] ⊂ 𝕜` with endpoints identified to `𝕜 / ℤ • p`, as a
homeomorphism of topological spaces. -/
def homeoIccQuot [TopologicalSpace 𝕜] [OrderTopology 𝕜] : 𝕋 ≃ₜ Quot (EndpointIdent p a) where
  toEquiv := equivIccQuot p a
  continuous_toFun := by
    simp_rw [isQuotientMap_quotient_mk'.continuous_iff, continuous_iff_continuousAt,
      continuousAt_iff_continuous_left_right]
    intro x; constructor
    on_goal 1 => erw [equivIccQuot_comp_mk_eq_toIocMod]
    on_goal 2 => erw [equivIccQuot_comp_mk_eq_toIcoMod]
    all_goals
      apply continuous_quot_mk.continuousAt.comp_continuousWithinAt
      rw [IsInducing.subtypeVal.continuousWithinAt_iff]
    · apply continuousWithinAt_toIocMod_Iic
    · apply continuousWithinAt_toIcoMod_Ici
  continuous_invFun :=
    continuous_quot_lift _ ((AddCircle.continuous_mk' p).comp continuous_subtype_val)

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `AddCircle p`, by first showing that
various lifts are equivalent. -/


variable {p a}

theorem liftIoc_eq_liftIco {f : 𝕜 → B} (hf : f a = f (a + p)) :
    liftIoc p a f = liftIco p a f := by
  ext q
  obtain ⟨x, hx, rfl⟩ := by simpa only [mem_image] using coe_image_Ico_eq p a ▸ mem_univ q
  rw [liftIco_coe_apply hx]
  obtain (⟨rfl, -⟩ | h) := by rwa [mem_Ico, le_iff_eq_or_lt, or_and_right] at hx
  · rw [← coe_add_period, liftIoc_coe_apply (by simp [hp.out]), hf]
  · exact liftIoc_coe_apply ⟨h.1, h.2.le⟩

theorem liftIco_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) :
    liftIco p a f =
      Quot.lift (restrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a :=
  rfl

theorem liftIoc_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) :
    liftIoc p a f =
      Quot.lift (restrict (Icc a <| a + p) f)
          (by
            rintro _ _ ⟨_⟩
            exact h) ∘
        equivIccQuot p a := by
  rw [← liftIco_eq_lift_Icc h]
  exact liftIoc_eq_liftIco h

theorem liftIco_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico 0 p) : liftIco p 0 f ↑x = f x :=
  liftIco_coe_apply (by rwa [zero_add])

theorem liftIoc_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc 0 p) : liftIoc p 0 f ↑x = f x :=
  liftIoc_coe_apply (by rwa [zero_add])

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

theorem liftIco_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIco p a f) := by
  rw [liftIco_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_restrict.mp hc)

theorem liftIco_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIco p 0 f) :=
  liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

theorem liftIoc_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f a = f (a + p))
    (hc : ContinuousOn f <| Icc a (a + p)) : Continuous (liftIoc p a f) := by
  rw [liftIoc_eq_lift_Icc hf]
  refine Continuous.comp ?_ (homeoIccQuot p a).continuous_toFun
  exact continuous_coinduced_dom.mpr (continuousOn_iff_continuous_restrict.mp hc)

theorem liftIoc_zero_continuous [TopologicalSpace B] {f : 𝕜 → B} (hf : f 0 = f p)
    (hc : ContinuousOn f <| Icc 0 p) : Continuous (liftIoc p 0 f) :=
  liftIoc_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])

end AddCircle

end IdentifyIccEnds
