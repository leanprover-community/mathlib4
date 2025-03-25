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
-/

namespace ExpGrowth

open ENNReal EReal Filter Function Set

/-! ### Definition -/

/-- Lower exponential growth of a sequence of extended nonnegative real numbers. -/
noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := liminf (fun n ↦ log (u n) / n) atTop

/-- Upper exponential growth of a sequence of extended nonnegative real numbers. -/
noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := limsup (fun n ↦ log (u n) / n) atTop

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
    expGrowthInf u ≤ expGrowthSup v := by
  refine (liminf_le_limsup_of_frequently_le) (h.mono fun n u_v ↦ ?_)
  exact div_le_div_right_of_nonneg n.cast_nonneg' (log_monotone u_v)

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
  exact exp_monotone (mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg')

lemma _root_.Eventually.le_expGrowthInf (h : ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthInf u := by
  apply le_expGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' ?_
  exact exp_monotone (mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg')

lemma _root_.Eventually.expGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) :
    expGrowthSup u ≤ a:= by
  apply expGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans ?_
  exact exp_monotone (mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg')

lemma _root_.Frequently.le_expGrowthSup (h : ∃ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthSup u := by
  apply le_expGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' ?_
  exact exp_monotone (mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg')

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
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

-- Bound on `expGrowthSup` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
lemma expGrowthSup_le_of_eventually_le (hb : b ≠ ∞) (h : ∀ᶠ n in atTop, u n ≤ b * v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact Or.inl EReal.zero_ne_bot
    · exact Or.inl EReal.zero_ne_top

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
  rw [← iInf_univ, expGrowthInf_biInf u finite_univ, iInf_univ]

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
  rw [← iSup_univ, expGrowthSup_biSup u finite_univ, iSup_univ]

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

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → ℝ≥0∞} {v : ℕ → ℕ}

lemma Real.eventually_atTop_exists_int_between {a b : ℝ} (h : a < b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℤ, a * x ≤ n ∧ n ≤ b * x := by
  refine (eventually_ge_atTop (b-a)⁻¹).mono fun x ab_x ↦ ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h), mul_comm, sub_mul, le_sub_iff_add_le'] at ab_x
  obtain ⟨n, n_bx, hn⟩ := (b * x).exists_floor
  refine ⟨n, ?_, n_bx⟩
  specialize hn (n + 1)
  simp only [Int.cast_add, Int.cast_one, add_le_iff_nonpos_right, Int.reduceLE, imp_false,
    not_le] at hn
  exact le_of_add_le_add_right (ab_x.trans hn.le)

lemma Real.eventually_atTop_exists_nat_between {a b : ℝ} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, a * x ≤ n ∧ n ≤ b * x := by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans ?_, ?_⟩ <;>  rw [← Int.cast_natCast]
  · exact Int.cast_le.2 (Int.self_le_toNat m)
  · apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
    norm_cast
    exact Int.toNat_eq_max m

lemma EReal.eventually_atTop_exists_nat_between {a b : EReal} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, a * n ≤ m ∧ m ≤ b * n :=
  match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n ↦ ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · exact mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)
    · exact mul_nonneg hb n.cast_nonneg'
  | (a : ℝ) =>
    match b with
    | ⊤ => by
      refine (eventually_gt_atTop 0).mono fun n n_0 ↦ ?_
      obtain ⟨m, hm⟩ := exists_nat_ge_mul h.ne n
      exact ⟨m, hm, le_of_le_of_eq le_top (top_mul_of_pos (Nat.cast_pos'.2 n_0)).symm⟩
    | ⊥ => (not_lt_bot h).rec
    | (b : ℝ) => by
      obtain ⟨x, hx⟩ := eventually_atTop.1 <| Real.eventually_atTop_exists_nat_between
        (EReal.coe_lt_coe_iff.1 h) (EReal.coe_nonneg.1 hb)
      obtain ⟨n, x_n⟩ := exists_nat_ge x
      refine eventually_atTop.2 ⟨n, fun k n_k ↦ ?_⟩
      simp only [← coe_coe_eq_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact hx k (x_n.trans (Nat.cast_le.2 n_k))

lemma linGrowthInf_nonneg (v : ℕ → ℕ) : 0 ≤ liminf (fun n ↦ (v n : EReal) / n) atTop :=
  (le_liminf_of_le) (Eventually.of_forall fun n ↦ div_nonneg (v n).cast_nonneg' n.cast_nonneg')

lemma tendsto_atTop_of_linGrowthInf_pos (h : liminf (fun n ↦ (v n : EReal) / n) atTop ≠ 0) :
    Tendsto v atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M ↦ eventually_atTop.1 ?_
  obtain ⟨a, a_0, a_v⟩ := exists_between (h.symm.lt_of_le (linGrowthInf_nonneg v))
  have h₁ : ∀ᶠ n : ℕ in atTop, M ≤ a * n := by
    obtain ⟨n, hn⟩ := EReal.exists_nat_ge_mul a.inv_lt_top.ne M
    rw [← EReal.div_eq_inv_mul, EReal.div_le_iff_le_mul a_0 (ne_top_of_lt a_v)] at hn
    refine eventually_atTop.2 ⟨n, fun k k_n ↦ ?_⟩
    exact hn.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 k_n) a_0.le)
  have h₂ : ∀ᶠ n : ℕ in atTop, a * n ≤ v n := by
    refine (eventually_lt_of_lt_liminf a_v).mp (eventually_atTop.2 ⟨1, fun n n_1 a_vn ↦ ?_⟩)
    rw [lt_div_iff (Nat.cast_pos'.2 n_1) (natCast_ne_top n)] at a_vn
    exact a_vn.le
  filter_upwards [h₁, h₂] with n M_a a_vn
  exact Nat.cast_le.1 (M_a.trans a_vn)

lemma le_expGrowthInf_comp (hu : 1 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (liminf (fun n ↦ (v n : EReal) / n) atTop) * expGrowthInf u ≤ expGrowthInf (u ∘ v) := by
  have uv_exp_0 : 0 ≤ expGrowthInf (u ∘ v) := by
    rw [← expGrowthInf_const one_ne_zero one_ne_top]
    exact expGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linGrowthInf_nonneg v) uv_exp_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ ↦ Eventually.le_expGrowthInf ?_
  have b_exp_uv := eventually_map.1 ((eventually_exp_le b_u).filter_mono hv)
  filter_upwards [b_exp_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact b_uvn.trans' (exp_monotone (mul_le_mul_of_nonneg_left a_vn b_0.le))

lemma expGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 1 ≤ u n)
    (hv₀ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ 0)
    (hv₁ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    expGrowthSup (u ∘ v) ≤ (limsup (fun n ↦ (v n : EReal) / n) atTop) * expGrowthSup u := by
  have v_0 := hv₀.symm.lt_of_le <| (linGrowthInf_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ Eventually.expGrowthSup_le ?_
  have b_0 : 0 ≤ b := by
    rw [← expGrowthInf_const one_ne_zero one_ne_top]
    exact (expGrowthInf_le_expGrowthSup_of_frequently_le hu).trans u_b.le
  have uv_b_exp : ∀ᶠ n in atTop, u (v n) ≤ exp (b * (v n : EReal)) :=
    eventually_map.1 ((eventually_le_exp u_b).filter_mono hv₂)
  filter_upwards [uv_b_exp, eventually_lt_of_limsup_lt v_a, eventually_gt_atTop 0]
    with n uvn_b vn_a n_0
  replace vn_a := ((div_lt_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact uvn_b.trans <| exp_monotone (mul_le_mul_of_nonneg_left vn_a b_0)

/-! ### Monotone sequences -/

lemma _root_.Monotone.expGrowthInf_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthInf u := by
  simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : ∀ᶠ n in atTop, u m ≤ u n := eventually_atTop.2 ⟨m, fun _ hb ↦ h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (expGrowthInf_top.symm.trans_le (expGrowthInf_eventually_monotone m_n))
  · rw [← expGrowthInf_const hm hm']
    exact expGrowthInf_eventually_monotone m_n

lemma _root_.Monotone.expGrowthSup_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthSup u :=
  (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup

lemma expGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthInf (u ∘ v) := by
  simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : ∀ᶠ n in atTop, u m ≤ (u ∘ v) n := by
    apply (eventually_map (P := fun n : ℕ ↦ u m ≤ u n)).2
    exact (eventually_atTop.2 ⟨m, fun n m_n ↦ h m_n⟩).filter_mono hv
  apply (expGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'
  · rw [hum', ← Pi.top_def, expGrowthInf_top]; exact le_top
  · rw [expGrowthInf_const hum hum']

lemma expGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthSup (u ∘ v) :=
  (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup

lemma _root_.Monotone.expGrowthInf_comp_le (h : Monotone u)
    (hv₀ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ 0)
    (hv₁ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ ⊤) :
    expGrowthInf (u ∘ v) ≤ (limsup (fun n ↦ (v n : EReal) / n) atTop) * expGrowthInf u := by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = 0
  · rw [u_0, Pi.zero_comp, expGrowthInf_zero]; exact bot_le
  have v_0 := hv₀.symm.lt_of_le <| (linGrowthInf_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ ?_
  have a_0 := v_0.trans v_a
  have b_0 := (h.expGrowthInf_nonneg u_0).trans_lt u_b
  rcases eq_or_ne a ⊤ with rfl | a_top
  · rw [top_mul_of_pos b_0]; exact le_top
  apply Frequently.expGrowthInf_le
  obtain ⟨a', v_a', a_a'⟩ := exists_between v_a
  -- We get an epsilon of room: if `m` is large enough, then `v n ≤ a' * n < a * n`.
  -- Using `u_b`, we can find arbitrarily large values `n` such that `u n ≤ exp (b * n)`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a⁻¹ * n ≤ k ≤ a'⁻¹ * n`, or, in other words, `a' * k ≤ n ≤ a * k`.
  -- Then `v k ≤ a' * k ≤ n`, so `u (v k) ≤ u n ≤ exp (b * n) ≤ exp (b * a * k)`.
  have a_0' := v_0.trans v_a'
  have a_a_inv' : a⁻¹ < a'⁻¹ := EReal.inv_strictAntiOn (mem_Ioi.2 a_0') (mem_Ioi.2 a_0) a_a'
  replace v_a' : ∀ᶠ n : ℕ in atTop, v n ≤ a' * n := by
    filter_upwards [eventually_lt_of_limsup_lt v_a', eventually_gt_atTop 0] with n vn_a' n_0
    rw [mul_comm]
    exact (div_le_iff_le_mul (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a'.le
  suffices h : (∀ᶠ n : ℕ in atTop, v n ≤ a' * n) → ∃ᶠ n : ℕ in atTop, (u ∘ v) n ≤ exp (a * b * n)
    from h v_a'
  rw [← frequently_imp_distrib]
  replace u_b := ((frequently_le_exp u_b).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (EReal.inv_nonneg_of_nonneg a_0'.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := EReal.exists_nat_ge_mul a_top M
  obtain ⟨n, n_M', ⟨un_bn, _⟩, k, an_k, k_an'⟩ := frequently_atTop.1 u_b M'
  refine ⟨k, ?_, fun vk_ak' ↦ ?_⟩
  · rw [mul_comm a, ← le_div_iff_mul_le a_0 a_top, EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k.trans' _
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 n_M') (inv_nonneg_of_nonneg a_0.le)
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0' (ne_top_of_lt a_a'), mul_comm] at k_an'
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0 a_top] at an_k
    have vk_n := Nat.cast_le.1 (vk_ak'.trans k_an')
    exact (h vk_n).trans <| un_bn.trans (exp_monotone (mul_le_mul_of_nonneg_left an_k b_0.le))

lemma _root_.Monotone.le_expGrowthSup_comp (h : Monotone u)
    (hv : liminf (fun n ↦ (v n : EReal) / n) atTop ≠ 0) :
    (liminf (fun n ↦ (v n : EReal) / n) atTop) * expGrowthSup u ≤ expGrowthSup (u ∘ v) := by
  have v_0 := hv.symm.lt_of_le (linGrowthInf_nonneg v)
  -- WLOG, `u` is non-zero, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = 0
  · rw [u_0, expGrowthSup_zero, mul_bot_of_pos v_0]; exact bot_le
  apply mul_le_of_forall_lt_of_nonneg v_0.le
    (expGrowthSup_comp_nonneg h u_0 (tendsto_atTop_of_linGrowthInf_pos hv))
  refine fun a ⟨a_0, a_v⟩ b ⟨b_0, b_u⟩ ↦ Frequently.le_expGrowthSup ?_
  obtain ⟨a', a_a', a_v'⟩ := exists_between a_v
  -- We get an epsilon of room: if `m` is large enough, then `a * n < a' * n ≤ v n`.
  -- Using `b_u`, we can find arbitrarily large values `n` such that `exp (b * n) ≤ u n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a'⁻¹ * n ≤ k ≤ a⁻¹ * n`, or, in other words, `a * k ≤ n ≤ a' * k`.
  -- Then `v k ≥ a' * k ≥ n`, so `u (v k) ≥ u n ≥ exp (b * n) ≥ exp (b * a * k)`.
  have a_top' := ne_top_of_lt a_v'
  have a_0' := a_0.trans a_a'
  have a_a_inv' : a'⁻¹ < a⁻¹ := inv_strictAntiOn (mem_Ioi.2 a_0) (mem_Ioi.2 a_0') a_a'
  replace a_v' : ∀ᶠ n : ℕ in atTop, a' * n ≤ v n := by
    filter_upwards [eventually_lt_of_lt_liminf a_v', eventually_gt_atTop 0] with n a_vn' n_0
    exact (le_div_iff_mul_le (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn'.le
  suffices h : (∀ᶠ n : ℕ in atTop, a' * n ≤ v n) → ∃ᶠ n : ℕ in atTop, exp (a * b * n) ≤ (u ∘ v) n
    from h a_v'
  rw [← frequently_imp_distrib]
  replace b_u := ((frequently_exp_le b_u).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := EReal.exists_nat_ge_mul a_top' M
  obtain ⟨n, n_M', ⟨bn_un, _⟩, k, an_k', k_an⟩ := frequently_atTop.1 b_u M'
  refine ⟨k, ?_, fun ak_vk' ↦ ?_⟩
  · rw [mul_comm a', ← le_div_iff_mul_le a_0' a_top', EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k'.trans' _
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 n_M') (inv_nonneg_of_nonneg a_0'.le)
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0' a_top'] at an_k'
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0 (ne_top_of_lt a_a'), mul_comm] at k_an
    have n_vk := Nat.cast_le.1 (an_k'.trans ak_vk')
    exact (exp_monotone (mul_le_mul_of_nonneg_left k_an b_0.le)).trans <| bn_un.trans (h n_vk)

lemma _root_.Monotone.expGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (nhds a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthInf (u ∘ v) = a * expGrowthInf u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linGrowthInf_nonneg v)
  have v_top := tendsto_atTop_of_linGrowthInf_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_expGrowthInf_comp` and `expGrowthInf_comp_le`.
  by_cases u_0 : u = 0
  · rw [u_0, Pi.zero_comp, expGrowthInf_zero, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases h1 : ∃ᶠ n : ℕ in atTop, u n ≤ 1
  · replace h' (n : ℕ) : u n ≤ 1 := by
      obtain ⟨m, n_m, um_1⟩ := (frequently_atTop.1 h1) n
      exact (h n_m).trans um_1
    have u_0' : expGrowthInf u = 0 := by
      apply le_antisymm _ (h.expGrowthInf_nonneg u_0)
      exact (expGrowthInf_monotone h').trans_eq (expGrowthInf_const one_ne_zero one_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (expGrowthInf_comp_nonneg h u_0 v_top)
    refine (expGrowthInf_monotone fun n ↦ ?_).trans_eq (expGrowthInf_const one_ne_zero one_ne_top)
    rw [comp_apply]; exact h' (v n)
  · replace h' := (not_frequently.1 h1).mono fun _ hn ↦ le_of_not_le hn
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact h.expGrowthInf_comp_le ha ha'
    · rw [← hv.liminf_eq]
      exact le_expGrowthInf_comp h' v_top

lemma _root_.Monotone.expGrowthSup_comp {a : EReal} (hu : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (nhds a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthSup (u ∘ v) = a * expGrowthSup u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linGrowthInf_nonneg v)
  have v_top := tendsto_atTop_of_linGrowthInf_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_expGrowthSup_comp` and `expGrowthSup_comp_le`.
  by_cases u_0 : u = 0
  · rw [u_0, Pi.zero_comp, expGrowthSup_zero, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases u_1 : ∀ᶠ n : ℕ in atTop, u n ≤ 1
  · have u_0' : expGrowthSup u = 0 := by
      apply le_antisymm _ (hu.expGrowthSup_nonneg u_0)
      apply (expGrowthSup_eventually_monotone u_1).trans_eq
      exact (expGrowthSup_const one_ne_zero one_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (expGrowthSup_comp_nonneg hu u_0 v_top)
    apply (expGrowthSup_eventually_monotone (v_top.eventually u_1)).trans_eq
    exact expGrowthSup_const one_ne_zero one_ne_top
  · replace h' := (not_eventually.1 u_1).mono fun x hx ↦ (lt_of_not_le hx).le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact expGrowthSup_comp_le h' ha ha' v_top
    · rw [← hv.liminf_eq]
      exact hu.le_expGrowthSup_comp hv₁.ne.symm

lemma _root_.Monotone.expGrowthInf_comp_mul {m : ℕ} (hu : Monotone u) (hm : m ≠ 0) :
    expGrowthInf (fun n ↦ u (m * n)) = m * expGrowthInf u := by
  have h : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (nhds m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact hu.expGrowthInf_comp h (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

lemma _root_.Monotone.expGrowthSup_comp_mul {m : ℕ} (hu : Monotone u) (hm : m ≠ 0) :
    expGrowthSup (fun n ↦ u (m * n)) = m * expGrowthSup u := by
  have h : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (nhds m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact hu.expGrowthSup_comp h (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

end composition

end ExpGrowth
