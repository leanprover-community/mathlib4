/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.Asymptotics.LinearGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Exponential growth

This file defines the exponential growth of a sequence `u : ℕ → ℝ≥0∞`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively.

## Main definitions

- `expGrowthInf`, `expGrowthSup`: respectively, `liminf` and `limsup` of `log (u n) / n`.
- `expGrowthInfTopHom`, `expGrowthSupBotHom`: the functions `expGrowthInf`, `expGrowthSup`
  as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## Tags

asymptotics, exponential
-/

@[expose] public section

namespace ExpGrowth

open ENNReal EReal Filter Function LinearGrowth
open scoped Topology

/-! ### Definition -/

/-- Lower exponential growth of a sequence of extended nonnegative real numbers. -/
noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := liminf (fun n ↦ log (u n) / n) atTop

/-- Upper exponential growth of a sequence of extended nonnegative real numbers. -/
noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := limsup (fun n ↦ log (u n) / n) atTop

lemma expGrowthInf_def {u : ℕ → ℝ≥0∞} :
    expGrowthInf u = linearGrowthInf (log ∘ u) := by
  rfl

lemma expGrowthSup_def {u : ℕ → ℝ≥0∞} :
    expGrowthSup u = linearGrowthSup (log ∘ u) := by
  rfl

/-! ### Basic properties -/

section basic_properties

variable {u v : ℕ → ℝ≥0∞} {a : EReal} {b : ℝ≥0∞}

lemma expGrowthInf_congr (h : u =ᶠ[atTop] v) :
    expGrowthInf u = expGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma expGrowthSup_congr (h : u =ᶠ[atTop] v) :
    expGrowthSup u = expGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma expGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    expGrowthInf u ≤ expGrowthInf v :=
  liminf_le_liminf (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

lemma expGrowthInf_monotone : Monotone expGrowthInf :=
  fun _ _ uv ↦ expGrowthInf_eventually_monotone (Eventually.of_forall uv)

lemma expGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    expGrowthSup u ≤ expGrowthSup v :=
  limsup_le_limsup (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

lemma expGrowthSup_monotone : Monotone expGrowthSup :=
  fun _ _ uv ↦ expGrowthSup_eventually_monotone (Eventually.of_forall uv)

lemma expGrowthInf_le_expGrowthSup : expGrowthInf u ≤ expGrowthSup u := liminf_le_limsup

lemma expGrowthInf_le_expGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    expGrowthInf u ≤ expGrowthSup v :=
  liminf_le_limsup_of_frequently_le <| h.mono fun n u_v ↦ by gcongr

lemma expGrowthInf_le_iff :
    expGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ exp (b * n) := by
  rw [expGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), ← log_exp (n * b), mul_comm _ b]
  exact logOrderIso.le_iff_le

lemma le_expGrowthInf_iff :
    a ≤ expGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, exp (b * n) ≤ u n := by
  rw [expGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

lemma expGrowthSup_le_iff :
    expGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ exp (b * n) := by
  rw [expGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), ← log_exp (n * b), mul_comm _ b]
  exact logOrderIso.le_iff_le

lemma le_expGrowthSup_iff :
    a ≤ expGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, exp (b * n) ≤ u n := by
  rw [expGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

/- Forward direction of `expGrowthInf_le_iff`. -/
lemma frequently_le_exp (h : expGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ exp (a * n) :=
  expGrowthInf_le_iff.1 (le_refl (expGrowthInf u)) a h

/- Forward direction of `le_expGrowthInf_iff`. -/
lemma eventually_exp_le (h : a < expGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n :=
  le_expGrowthInf_iff.1 (le_refl (expGrowthInf u)) a h

/- Forward direction of `expGrowthSup_le_iff`. -/
lemma eventually_le_exp (h : expGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n) :=
  expGrowthSup_le_iff.1 (le_refl (expGrowthSup u)) a h

/- Forward direction of `le_expGrowthSup_iff`. -/
lemma frequently_exp_le (h : a < expGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, exp (a * n) ≤ u n :=
  le_expGrowthSup_iff.1 (le_refl (expGrowthSup u)) a h

lemma _root_.Frequently.expGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) :
    expGrowthInf u ≤ a := by
  apply expGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans ?_
  gcongr

lemma _root_.Eventually.le_expGrowthInf (h : ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthInf u :=
  le_expGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

lemma _root_.Eventually.expGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) :
    expGrowthSup u ≤ a :=
  expGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr

lemma _root_.Frequently.le_expGrowthSup (h : ∃ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthSup u :=
  le_expGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

/-! ### Special cases -/

lemma expGrowthSup_zero : expGrowthSup 0 = ⊥ := by
  rw [← linearGrowthSup_bot, expGrowthSup_def]
  congr 1
  ext _
  rw [comp_apply, Pi.zero_apply, Pi.bot_apply, log_zero]

lemma expGrowthInf_zero : expGrowthInf 0 = ⊥ := by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup

lemma expGrowthInf_top : expGrowthInf ⊤ = ⊤ := by
  rw [← linearGrowthInf_top, expGrowthInf_def]
  rfl

lemma expGrowthSup_top : expGrowthSup ⊤ = ⊤ := by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup

lemma expGrowthInf_const (h : b ≠ 0) (h' : b ≠ ∞) : expGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).liminf_eq

lemma expGrowthSup_const (h : b ≠ 0) (h' : b ≠ ∞) : expGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).limsup_eq

lemma expGrowthInf_pow : expGrowthInf (fun n ↦ b ^ n) = log b := by
  rw [expGrowthInf, ← liminf_const (f := atTop (α := ℕ)) (log b)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]

lemma expGrowthSup_pow : expGrowthSup (fun n ↦ b ^ n) = log b := by
  rw [expGrowthSup, ← limsup_const (f := atTop (α := ℕ)) (log b)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]

lemma expGrowthInf_exp : expGrowthInf (fun n ↦ exp (a * n)) = a :=
  le_antisymm (Frequently.expGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_expGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))

lemma expGrowthSup_exp : expGrowthSup (fun n ↦ exp (a * n)) = a :=
  le_antisymm (Eventually.expGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_expGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))

/-! ### Multiplication and inversion -/

lemma le_expGrowthInf_mul :
    expGrowthInf u + expGrowthInf v ≤ expGrowthInf (u * v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le'` for a version with swapped argument `u` and `v`. -/
lemma expGrowthInf_mul_le (h : expGrowthSup u ≠ ⊥ ∨ expGrowthInf v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthInf v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthSup u + expGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le` for a version with swapped argument `u` and `v`. -/
lemma expGrowthInf_mul_le' (h : expGrowthInf u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthInf u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthInf u + expGrowthSup v := by
  rw [mul_comm, add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

/-- See `le_expGrowthSup_mul'` for a version with swapped argument `u` and `v`. -/
lemma le_expGrowthSup_mul : expGrowthSup u + expGrowthInf v ≤ expGrowthSup (u * v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_expGrowthSup_mul` for a version with swapped argument `u` and `v`. -/
lemma le_expGrowthSup_mul' : expGrowthInf u + expGrowthSup v ≤ expGrowthSup (u * v) := by
  rw [mul_comm, add_comm]
  exact le_expGrowthSup_mul

lemma expGrowthSup_mul_le (h : expGrowthSup u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthSup (u * v) ≤ expGrowthSup u + expGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']

lemma expGrowthInf_inv : expGrowthInf u⁻¹ = - expGrowthSup u := by
  rw [expGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]

lemma expGrowthSup_inv : expGrowthSup u⁻¹ = - expGrowthInf u := by
  rw [expGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]

/-! ### Comparison -/

-- Bound on `expGrowthInf` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
lemma expGrowthInf_le_of_eventually_le (hb : b ≠ ∞) (h : ∀ᶠ n in atTop, u n ≤ b * v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthInf v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top

-- Bound on `expGrowthSup` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
lemma expGrowthSup_le_of_eventually_le (hb : b ≠ ∞) (h : ∀ᶠ n in atTop, u n ≤ b * v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top

lemma expGrowthInf_of_eventually_ge (hb : b ≠ 0) (h : ∀ᶠ n in atTop, b * u n ≤ v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

lemma expGrowthSup_of_eventually_ge (hb : b ≠ 0) (h : ∀ᶠ n in atTop, b * u n ≤ v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

/-! ### Infimum and supremum -/

lemma expGrowthInf_inf : expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v := by
  rw [expGrowthInf, expGrowthInf, expGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.inf_apply, log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower exponential growth as an `InfTopHom`. -/
noncomputable def expGrowthInfTopHom : InfTopHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthInf
  map_inf' _ _ := expGrowthInf_inf
  map_top' := expGrowthInf_top

lemma expGrowthInf_biInf {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, expGrowthInf (u x) := by
  have := map_finset_inf expGrowthInfTopHom hs.toFinset u
  simpa only [expGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

lemma expGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → ℝ≥0∞) :
    expGrowthInf (⨅ i, u i) = ⨅ i, expGrowthInf (u i) := by
  rw [← iInf_univ, expGrowthInf_biInf u Set.finite_univ, iInf_univ]

lemma expGrowthSup_sup : expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [expGrowthSup, expGrowthSup, expGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.sup_apply, log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper exponential growth as a `SupBotHom`. -/
noncomputable def expGrowthSupBotHom : SupBotHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthSup
  map_sup' _ _ := expGrowthSup_sup
  map_bot' := expGrowthSup_zero

lemma expGrowthSup_biSup {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  have := map_finset_sup expGrowthSupBotHom hs.toFinset u
  simpa only [expGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

lemma expGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → ℝ≥0∞) :
    expGrowthSup (⨆ i, u i) = ⨆ i, expGrowthSup (u i) := by
  rw [← iSup_univ, expGrowthSup_biSup u Set.finite_univ, iSup_univ]

/-! ### Addition -/

lemma le_expGrowthInf_add : expGrowthInf u ⊔ expGrowthInf v ≤ expGrowthInf (u + v) :=
  sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)

lemma expGrowthSup_add : expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (b := 2) ofNat_ne_top (Eventually.of_forall fun n ↦ ?_)
    rw [Pi.sup_apply u v n, Pi.add_apply u v n, two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refine expGrowthSup_monotone fun n ↦ ?_
    exact sup_le (self_le_add_right (u n) (v n)) (self_le_add_left (v n) (u n))

-- By lemma `expGrowthSup_add`, `expGrowthSup` is an `AddMonoidHom` from `ℕ → ℝ≥0∞` to
-- `Tropical ERealᵒᵈ`. Lemma `expGrowthSup_sum` is exactly `Finset.trop_inf`. We prove it from
-- scratch to reduce imports.
lemma expGrowthSup_sum {α : Type*} (u : α → ℕ → ℝ≥0∞) (s : Finset α) :
    expGrowthSup (∑ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ha]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → ℝ≥0∞} {v : ℕ → ℕ}

lemma le_expGrowthInf_comp (hu : 1 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n ↦ v n : EReal) * expGrowthInf u ≤ expGrowthInf (u ∘ v) := by
  apply le_linearGrowthInf_comp (hu.mono fun n h ↦ ?_) hv
  rw [Pi.one_apply] at h
  rwa [Pi.zero_apply, zero_le_log_iff]

lemma expGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 1 ≤ u n)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    expGrowthSup (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * expGrowthSup u := by
  apply linearGrowthSup_comp_le (u := log ∘ u) (hu.mono fun n h ↦ ?_) hv₀ hv₁ hv₂
  rwa [comp_apply, zero_le_log_iff]

/-! ### Monotone sequences -/

lemma _root_.Monotone.expGrowthInf_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthInf u := by
  apply (log_monotone.comp h).linearGrowthInf_nonneg
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

lemma _root_.Monotone.expGrowthSup_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthSup u :=
  (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup

lemma expGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthInf (u ∘ v) := by
  apply linearGrowthInf_comp_nonneg (u := log ∘ u) (log_monotone.comp h) _ hv
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'

lemma expGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthSup (u ∘ v) :=
  (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup

lemma _root_.Monotone.expGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) :
    expGrowthInf (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁

lemma _root_.Monotone.le_expGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    (linearGrowthInf fun n ↦ v n : EReal) * expGrowthSup u ≤ expGrowthSup (u ∘ v) :=
  (log_monotone.comp h).le_linearGrowthSup_comp hv

lemma _root_.Monotone.expGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthInf (u ∘ v) = a * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp hv ha ha'

lemma _root_.Monotone.expGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthSup (u ∘ v) = a * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp hv ha ha'

lemma _root_.Monotone.expGrowthInf_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    expGrowthInf (fun n ↦ u (m * n)) = m * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_mul hm

lemma _root_.Monotone.expGrowthSup_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    expGrowthSup (fun n ↦ u (m * n)) = m * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp_mul hm

end composition

end ExpGrowth
