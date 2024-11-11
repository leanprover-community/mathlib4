/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exponential growth
-/

namespace ExpGrowth

open ENNReal EReal Filter Function

/-! ### General lemmas -/

lemma right_distrib_mul_by_nonneg {a b c : EReal} (h : 0 ≤ c) (h' : c ≠ ⊤) :
    (a + b) * c = a * c + b * c := by
  let d := c.toReal
  have : d = c := coe_toReal h' (bot_lt_zero.trans_le h).ne.symm
  rw [← this] at h h' ⊢
  rcases eq_or_lt_of_le h with d_zero | d_pos
  · rw [← d_zero, mul_zero, mul_zero, mul_zero, add_zero]
  apply EReal.induction₂_symm (P := fun a b ↦ (a + b) * d = a * d + b * d)
  · intro x y x_y
    rw [add_comm y x, add_comm (y * d) (x * d)]
    exact x_y
  · rw [top_add_top, top_mul_of_pos d_pos, top_add_top]
  · intro _ _
    rw [top_add_coe, top_mul_of_pos d_pos, ← EReal.coe_mul, top_add_coe]
  · rw [zero_mul, add_zero, add_zero]
  · intro _ _
    rw [top_add_coe, top_mul_of_pos d_pos, ← EReal.coe_mul, top_add_coe]
  · rw [add_bot, bot_mul_of_pos d_pos, add_bot]
  · intro _ _
    rw [add_bot, bot_mul_of_pos d_pos, add_bot]
  · intro x y
    norm_cast
    exact right_distrib x y d
  · rw [add_bot, bot_mul_of_pos d_pos, add_bot]
  · intro _ _
    rw [add_bot, bot_mul_of_pos d_pos, add_bot]
  · rw [add_bot, bot_mul_of_pos d_pos, add_bot]

lemma left_distrib_mul_by_nonneg {a b c : EReal} (h : 0 ≤ c) (h' : c ≠ ⊤) :
    c * (a + b) = c * a + c * b := by
  rw [mul_comm c, mul_comm c, mul_comm c]
  exact right_distrib_mul_by_nonneg h h'

lemma EReal.div_eq_iff {a b c : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    c / b = a ↔ c = a * b := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [EReal.mul_div b a b, mul_comm a b]
  exact ⟨fun h₀ ↦ (strictMono_div_right_of_pos h h').injective h₀, fun h₀ ↦ h₀ ▸ rfl⟩

lemma EReal.lt_div_iff {a b c : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    a < c / b ↔ a * b < c := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [EReal.mul_div b a b, mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

lemma EReal.div_lt_iff {a b c : EReal} (h : 0 < b) (h' : b ≠ ⊤) :
    c / b < a ↔ c < a * b := by
  nth_rw 1 [← @mul_div_cancel a b (ne_bot_of_gt h) h' (ne_of_gt h)]
  rw [EReal.mul_div b a b, mul_comm a b]
  exact (strictMono_div_right_of_pos h h').lt_iff_lt

lemma bot_lt_inv (x : EReal) : ⊥ < x⁻¹ := by
  induction x with
  | h_bot => exact inv_bot ▸ bot_lt_zero
  | h_top => exact EReal.inv_top ▸ bot_lt_zero
  | h_real x => exact (coe_inv x).symm ▸ bot_lt_coe (x⁻¹)

lemma inv_lt_top (x : EReal) : x⁻¹ < ⊤ := by
  induction x with
  | h_bot => exact inv_bot ▸ zero_lt_top
  | h_top => exact EReal.inv_top ▸ zero_lt_top
  | h_real x => exact (coe_inv x).symm ▸ coe_lt_top (x⁻¹)

lemma div_right_distrib_by_nonneg {a b c : EReal} (h : 0 ≤ c) :
    (a + b) / c = a / c + b / c := by
  apply right_distrib_mul_by_nonneg (inv_nonneg_of_nonneg h) (inv_lt_top c).ne

/-! ### ExpGrowth -/

noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := atTop.liminf fun n ↦ log (u n) / n

noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := atTop.limsup fun n ↦ log (u n) / n

/-! ### Order properties -/

lemma expGrowthInf_congr {u v : ℕ → ℝ≥0∞} (h : u =ᶠ[atTop] v) :
    expGrowthInf u = expGrowthInf v :=
  liminf_congr (h.mono fun _ u_v ↦ u_v ▸ rfl)

lemma expGrowthSup_congr {u v : ℕ → ℝ≥0∞} (h : u =ᶠ[atTop] v) :
    expGrowthSup u = expGrowthSup v :=
  limsup_congr (h.mono fun _ u_v ↦ u_v ▸ rfl)

lemma expGrowthInf_eventually_monotone {u v : ℕ → ℝ≥0∞} (h : u ≤ᶠ[atTop] v) :
    expGrowthInf u ≤ expGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v ↦ monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    (log_monotone u_v))

lemma expGrowthInf_monotone :
    Monotone expGrowthInf :=
  fun _ _ u_v ↦ expGrowthInf_eventually_monotone (Eventually.of_forall u_v)

lemma expGrowthSup_eventually_monotone {u v : ℕ → ℝ≥0∞} (h : u ≤ᶠ[atTop] v) :
    expGrowthSup u ≤ expGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v ↦ monotone_div_right_of_nonneg (Nat.cast_nonneg' n)
    (log_monotone u_v))

lemma expGrowthSup_monotone :
    Monotone expGrowthSup :=
  fun _ _ u_v ↦ expGrowthSup_eventually_monotone (Eventually.of_forall u_v)

lemma expGrowthInf_le_expGrowthSup {u : ℕ → ℝ≥0∞} :
    expGrowthInf u ≤ expGrowthSup u :=
  liminf_le_limsup

lemma expGrowthInf_le_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    expGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n < exp (b * n) := by
  rw [expGrowthInf, Filter.liminf_le_iff]
  refine forall₂_congr fun b a_b ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_lt_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma le_expGrowthInf_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    a ≤ expGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, exp (b * n) < u n := by
  rw [expGrowthInf, Filter.le_liminf_iff]
  refine forall₂_congr fun b a_b ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.lt_div_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma expGrowthSup_le_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    expGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n < exp (b * n) := by
  rw [expGrowthSup, Filter.limsup_le_iff]
  refine forall₂_congr fun b a_b ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_lt_iff (by norm_cast) (natCast_ne_top n)]
  nth_rw 1 [← EReal.log_exp (b * n)]
  exact logOrderIso.lt_iff_lt

lemma le_expGrowthSup_iff {u : ℕ → ℝ≥0∞} {a : EReal} :
    a ≤ expGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, exp (b * n) < u n := by
  rw [expGrowthSup, Filter.le_limsup_iff]
  refine forall₂_congr fun b a_b ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
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
  rw [EReal.div_eq_iff (by norm_cast) (natCast_ne_top n), log_pow, mul_comm]

lemma expGrowthSup_pow {a : ℝ≥0∞} : expGrowthSup (fun n ↦ a ^ n) = log a := by
  rw [expGrowthSup, ← limsup_const (f := atTop (α := ℕ)) (log a)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (by norm_cast) (natCast_ne_top n), log_pow, mul_comm]

/-! ### Multiplication and inversion -/

-- TODO : Finitary version
lemma le_expGrowthInf_mul {u v : ℕ → ℝ≥0∞} :
    (expGrowthInf u) + expGrowthInf v ≤ expGrowthInf (u * v) := by
  refine add_liminf_le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← div_right_distrib_by_nonneg (Nat.cast_nonneg' n), log_mul_add]

/-- See `expGrowthInf_mul_le'` for a version with swapped argument `u` and `v`.-/
lemma expGrowthInf_mul_le {u v : ℕ → ℝ≥0∞} (h : expGrowthSup u ≠ ⊥ ∨ expGrowthInf v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthInf v ≠ ⊥) :
    expGrowthInf (u * v) ≤ (expGrowthSup u) + expGrowthInf v := by
  refine (liminf_add_le_limsup_add_liminf h h').trans_eq'
    (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← div_right_distrib_by_nonneg (Nat.cast_nonneg' n), log_mul_add]

/-- See `expGrowthInf_mul_le` for a version with swapped argument `u` and `v`.-/
lemma expGrowthInf_mul_le' {u v : ℕ → ℝ≥0∞} (h : expGrowthInf u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthInf u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthInf (u * v) ≤ (expGrowthInf u) + expGrowthSup v := by
  rw [mul_comm, add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

/-- See `le_expGrowthSup_mul'` for a version with swapped argument `u` and `v`.-/
lemma le_expGrowthSup_mul {u v : ℕ → ℝ≥0∞} :
    (expGrowthSup u) + expGrowthInf v ≤ expGrowthSup (u * v) := by
  refine limsup_add_liminf_le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← div_right_distrib_by_nonneg (Nat.cast_nonneg' n), log_mul_add]

/-- See `le_expGrowthSup_mul` for a version with swapped argument `u` and `v`.-/
lemma le_expGrowthSup_mul' {u v : ℕ → ℝ≥0∞} :
    (expGrowthInf u) + expGrowthSup v ≤ expGrowthSup (u * v) := by
  rw [mul_comm, add_comm]
  exact le_expGrowthSup_mul

-- TODO : Finitary version
lemma expGrowthSup_mul_le {u v : ℕ → ℝ≥0∞} (h : expGrowthSup u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthSup (u * v) ≤ (expGrowthSup u) + expGrowthSup v := by
  refine (limsup_add_le_add_limsup h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← div_right_distrib_by_nonneg (Nat.cast_nonneg' n), log_mul_add]

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

lemma expGrowthInf_le_of_bigO {u v : ℕ → ℝ≥0∞} (h : ∃ C ≠ ∞, ∀ᶠ n in atTop, u n ≤ C * v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  obtain ⟨C, C_top, u_v⟩ := h
  apply (expGrowthInf_eventually_monotone u_v).trans
  rcases eq_zero_or_pos C with rfl | C_pos
  · simp only [zero_mul]
    exact expGrowthInf_zero ▸ bot_le
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const C_pos.ne' C_top]
    · exact zero_add (expGrowthInf v)
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

lemma expGrowthSup_le_of_bigO {u v : ℕ → ℝ≥0∞} (h : ∃ C ≠ ∞, ∀ᶠ n in atTop, u n ≤ C * v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  obtain ⟨C, C_top, u_v⟩ := h
  apply (expGrowthSup_eventually_monotone u_v).trans
  rcases eq_zero_or_pos C with rfl | C_pos
  · simp only [zero_mul]
    exact expGrowthSup_zero ▸ bot_le
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const C_pos.ne' C_top]
    · exact zero_add (expGrowthSup v)
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

lemma expGrowthInf_of_bigO {u v : ℕ → ℝ≥0∞} (h : ∃ c ≠ 0, ∀ᶠ n in atTop, c * u n ≤ v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  obtain ⟨c, c_pos, u_v⟩ := h
  apply (expGrowthInf_eventually_monotone u_v).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top c with rfl | c_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const c_pos c_top.ne, zero_add]

lemma expGrowthSup_of_bigO {u v : ℕ → ℝ≥0∞} (h : ∃ c ≠ 0, ∀ᶠ n in atTop, c * u n ≤ v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  obtain ⟨c, c_pos, u_v⟩ := h
  apply (expGrowthSup_eventually_monotone u_v).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top c with rfl | c_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const c_pos c_top.ne, zero_add]

/-! ### Infimum and supremum -/

lemma expGrowthInf_inf {u v : ℕ → ℝ≥0∞} :
    expGrowthInf (u ⊓ v) = (expGrowthInf u) ⊓ expGrowthInf v := by
  rw [expGrowthInf, expGrowthInf, expGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [← Monotone.map_min (monotone_div_right_of_nonneg (Nat.cast_nonneg' n)),
    ← Monotone.map_min log_monotone, Pi.inf_apply]

noncomputable def expGrowthInf_infTopHom : InfTopHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthInf
  map_inf' := fun u v ↦ @expGrowthInf_inf u v
  map_top' := expGrowthInf_top

lemma expGrowthInf_biInf {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, expGrowthInf (u x) := by
  have := map_finset_inf expGrowthInf_infTopHom hs.toFinset u
  simp only [expGrowthInf_infTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply] at this
  exact this

lemma expGrowthInf_iInf {ι : Type*} (u : ι → ℕ → ℝ≥0∞) (h : Finite ι) :
    expGrowthInf (⨅ i, u i) = ⨅ i, expGrowthInf (u i) := by
  rw [← iInf_univ, expGrowthInf_biInf u Set.finite_univ, iInf_univ]

lemma expGrowthSup_sup {u v : ℕ → ℝ≥0∞} :
    expGrowthSup (u ⊔ v) = (expGrowthSup u) ⊔ expGrowthSup v := by
  rw [expGrowthSup, expGrowthSup, expGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [← Monotone.map_max (monotone_div_right_of_nonneg (Nat.cast_nonneg' n)),
    ← Monotone.map_max log_monotone, Pi.sup_apply]

noncomputable def expGrowthSup_supBotHom : SupBotHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthSup
  map_sup' := fun u v ↦ @expGrowthSup_sup u v
  map_bot' := expGrowthSup_zero

lemma expGrowthSup_biSup {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  have := map_finset_sup expGrowthSup_supBotHom hs.toFinset u
  simp only [expGrowthSup_supBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply] at this
  exact this

lemma expGrowthSup_iSup {ι : Type*} (u : ι → ℕ → ℝ≥0∞) (h : Finite ι) :
    expGrowthSup (⨆ i, u i) = ⨆ i, expGrowthSup (u i) := by
  rw [← iSup_univ, expGrowthSup_biSup u Set.finite_univ, iSup_univ]

/-! ### Addition -/

lemma expGrowthSup_add {u v : ℕ → ℝ≥0∞} :
    expGrowthSup (u + v) = (expGrowthSup u) ⊔ expGrowthSup v := by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_bigO ⟨2, by norm_num, Eventually.of_forall fun n ↦ ?_⟩
    rw [Pi.sup_apply u v n, Pi.add_apply u v n, two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refine expGrowthSup_monotone fun n ↦ ?_
    rw [Pi.sup_apply u v n, Pi.add_apply u v n]
    exact sup_le (self_le_add_right (u n) (v n)) (self_le_add_left (v n) (u n))

-- By lemma `expGrowthSup_add`, `expGrowthSup` is an `AddMonoidHom` from `ℕ → ℝ≥0∞` to
-- `Tropical ERealᵒᵈ`. Lemma `expGrowthSup_sum` is exactly `Finset.trop_inf`. We prove it from
-- scratch to avoid importing `Mathlib.Algebra.Tropical.BigOperators`.
lemma expGrowthSup_sum {α : Type*} (u : α → ℕ → ℝ≥0∞) (s : Finset α) :
    expGrowthSup (∑ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | @insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ha]

end ExpGrowth
