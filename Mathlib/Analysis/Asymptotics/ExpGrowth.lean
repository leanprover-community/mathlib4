/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

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

## TODO
Get bounds on `expGrowthSup (u ∘ v)` with suitable hypotheses on `v : ℕ → ℕ `:
linear growth of `v`, monotonicity.
-/

namespace ExpGrowth

open ENNReal EReal Filter Function

/-! ### Definition -/

/-- Lower exponential growth of a sequence of extended nonnegative real numbers -/
noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := atTop.liminf fun n ↦ log (u n) / n

/-- Upper exponential growth of a sequence of extended nonnegative real numbers -/
noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := atTop.limsup fun n ↦ log (u n) / n

/-! ### Basic properties -/

lemma expGrowthInf_congr {u v : ℕ → ℝ≥0∞} (h : u =ᶠ[atTop] v) :
    expGrowthInf u = expGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma expGrowthSup_congr {u v : ℕ → ℝ≥0∞} (h : u =ᶠ[atTop] v) :
    expGrowthSup u = expGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma expGrowthInf_eventually_monotone {u v : ℕ → ℝ≥0∞} (h : u ≤ᶠ[atTop] v) :
    expGrowthInf u ≤ expGrowthInf v :=
  liminf_le_liminf (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

lemma expGrowthInf_monotone :
    Monotone expGrowthInf :=
  fun _ _ uv ↦ expGrowthInf_eventually_monotone (Eventually.of_forall uv)

lemma expGrowthSup_eventually_monotone {u v : ℕ → ℝ≥0∞} (h : u ≤ᶠ[atTop] v) :
    expGrowthSup u ≤ expGrowthSup v :=
  limsup_le_limsup (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))

lemma expGrowthSup_monotone :
    Monotone expGrowthSup :=
  fun _ _ uv ↦ expGrowthSup_eventually_monotone (Eventually.of_forall uv)

lemma expGrowthInf_le_expGrowthSup {u : ℕ → ℝ≥0∞} :
    expGrowthInf u ≤ expGrowthSup u :=
  liminf_le_limsup

lemma expGrowthInf_le_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    expGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n < exp (b * n) := by
  rw [expGrowthInf, Filter.liminf_le_iff]
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [EReal.div_lt_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma le_expGrowthInf_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    a ≤ expGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, exp (b * n) < u n := by
  rw [expGrowthInf, Filter.le_liminf_iff]
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [EReal.lt_div_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma expGrowthSup_le_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    expGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n < exp (b * n) := by
  rw [expGrowthSup, Filter.limsup_le_iff]
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [EReal.div_lt_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma le_expGrowthSup_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    a ≤ expGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, exp (b * n) < u n := by
  rw [expGrowthSup, Filter.le_limsup_iff]
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [EReal.lt_div_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

/-! ### Special cases -/

lemma expGrowthSup_zero : expGrowthSup 0 = ⊥ := by
  rw [← limsup_const (f := atTop (α := ℕ)) ⊥]
  apply limsup_congr
  simp only [Pi.zero_apply, log_zero, eventually_atTop]
  exact ⟨1, fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma expGrowthInf_zero : expGrowthInf 0 = ⊥ := by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup

lemma expGrowthInf_top : expGrowthInf ⊤ = ⊤ := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) ⊤]
  apply liminf_congr
  simp only [log_top, eventually_atTop]
  exact ⟨1, fun n n_pos ↦ top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma expGrowthSup_top : expGrowthSup ⊤ = ⊤ := by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup

lemma expGrowthInf_const {a : ℝ≥0∞} (h : a ≠ 0) (h' : a ≠ ∞) : expGrowthInf (fun _ ↦ a) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).liminf_eq

lemma expGrowthSup_const {a : ℝ≥0∞} (h : a ≠ 0) (h' : a ≠ ∞) : expGrowthSup (fun _ ↦ a) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).limsup_eq

lemma expGrowthInf_pow {a : ℝ≥0∞} : expGrowthInf (fun n ↦ a ^ n) = log a := by
  rw [expGrowthInf, ← liminf_const (f := atTop (α := ℕ)) (log a)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]

lemma expGrowthSup_pow {a : ℝ≥0∞} : expGrowthSup (fun n ↦ a ^ n) = log a := by
  rw [expGrowthSup, ← limsup_const (f := atTop (α := ℕ)) (log a)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]

/-! ### Multiplication and inversion -/

lemma le_expGrowthInf_mul {u v : ℕ → ℝ≥0∞} :
    expGrowthInf u + expGrowthInf v ≤ expGrowthInf (u * v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le'` for a version with swapped argument `u` and `v`. -/
lemma expGrowthInf_mul_le {u v : ℕ → ℝ≥0∞} (h : expGrowthSup u ≠ ⊥ ∨ expGrowthInf v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthInf v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthSup u + expGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le` for a version with swapped argument `u` and `v`. -/
lemma expGrowthInf_mul_le' {u v : ℕ → ℝ≥0∞} (h : expGrowthInf u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthInf u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthInf u + expGrowthSup v := by
  rw [mul_comm, add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

/-- See `le_expGrowthSup_mul'` for a version with swapped argument `u` and `v`. -/
lemma le_expGrowthSup_mul {u v : ℕ → ℝ≥0∞} :
    expGrowthSup u + expGrowthInf v ≤ expGrowthSup (u * v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_expGrowthSup_mul` for a version with swapped argument `u` and `v`. -/
lemma le_expGrowthSup_mul' {u v : ℕ → ℝ≥0∞} :
    expGrowthInf u + expGrowthSup v ≤ expGrowthSup (u * v) := by
  rw [mul_comm, add_comm]
  exact le_expGrowthSup_mul

lemma expGrowthSup_mul_le {u v : ℕ → ℝ≥0∞} (h : expGrowthSup u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthSup (u * v) ≤ expGrowthSup u + expGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']

lemma expGrowthInf_inv {u : ℕ → ℝ≥0∞} :
    expGrowthInf u⁻¹ = - expGrowthSup u := by
  rw [expGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]

lemma expGrowthSup_inv {u : ℕ → ℝ≥0∞} :
    expGrowthSup u⁻¹ = - expGrowthInf u := by
  rw [expGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]

/-! ### Comparison -/

-- Bound on `expGrowthInf` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
lemma expGrowthInf_le_of_eventually_le {u v : ℕ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ᶠ n in atTop, u n ≤ C * v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos C with rfl | C_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const C_pos.ne' hC]
    · exact zero_add (expGrowthInf v)
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

-- Bound on `expGrowthSup` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
lemma expGrowthSup_le_of_eventually_le {u v : ℕ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ᶠ n in atTop, u n ≤ C * v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos C with rfl | C_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const C_pos.ne' hC]
    · exact zero_add (expGrowthSup v)
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

lemma expGrowthInf_of_eventually_ge {u v : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0)
    (h : ∀ᶠ n in atTop, c * u n ≤ v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top c with rfl | c_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hc c_top.ne, zero_add]

lemma expGrowthSup_of_eventually_ge {u v : ℕ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ 0)
    (h : ∀ᶠ n in atTop, c * u n ≤ v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top c with rfl | c_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hc c_top.ne, zero_add]

/-! ### Infimum and supremum -/

lemma expGrowthInf_inf {u v : ℕ → ℝ≥0∞} :
    expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v := by
  rw [expGrowthInf, expGrowthInf, expGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.inf_apply, log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower exponential growth as an `InfTopHom` -/
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

lemma expGrowthSup_sup {u v : ℕ → ℝ≥0∞} :
    expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [expGrowthSup, expGrowthSup, expGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.sup_apply, log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper exponential growth as a `SupBotHom` -/
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

lemma le_expGrowthInf_add {u v : ℕ → ℝ≥0∞} :
    expGrowthInf u ⊔ expGrowthInf v ≤ expGrowthInf (u + v) :=
  sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)

lemma expGrowthSup_add {u v : ℕ → ℝ≥0∞} :
    expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (C := 2) ofNat_ne_top (Eventually.of_forall fun n ↦ ?_)
    rw [Pi.sup_apply u v n, Pi.add_apply u v n, two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refine expGrowthSup_monotone fun n ↦ ?_
    rw [Pi.sup_apply u v n, Pi.add_apply u v n]
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
  | @insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ha]

end ExpGrowth
