/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Linear growth

This file defines the linear growth of a sequence `u : ℕ → R`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively. Most properties are developed for
`R = EReal`.

## Main definitions

- `linearGrowthInf`, `linearGrowthSup`: respectively, `liminf` and `limsup` of `(u n) / n`.
- `linearGrowthInfTopHom`, `linearGrowthSupBotHom`: the functions `linearGrowthInf`,
  `linearGrowthSup` as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## TODO

Generalize statements from `EReal` to `ENNReal` (or others). This may need additional typeclasses.

Lemma about coercion from `ENNReal` to `EReal`. This needs additional lemmas about
`ENNReal.toEReal`.
-/

@[expose] public section

namespace LinearGrowth

open EReal Filter Function
open scoped Topology

/-! ### Definition -/

section definition

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]

/-- Lower linear growth of a sequence. -/
noncomputable def linearGrowthInf (u : ℕ → R) : R := liminf (fun n ↦ u n / n) atTop

/-- Upper linear growth of a sequence. -/
noncomputable def linearGrowthSup (u : ℕ → R) : R := limsup (fun n ↦ u n / n) atTop

end definition

/-! ### Basic properties -/

section basic_properties

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R] {u v : ℕ → R}

lemma linearGrowthInf_congr (h : u =ᶠ[atTop] v) :
    linearGrowthInf u = linearGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linearGrowthSup_congr (h : u =ᶠ[atTop] v) :
    linearGrowthSup u = linearGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linearGrowthInf_le_linearGrowthSup
    (h : IsBoundedUnder (· ≤ ·) atTop fun n ↦ u n / n := by isBoundedDefault)
    (h' : IsBoundedUnder (· ≥ ·) atTop fun n ↦ u n / n := by isBoundedDefault) :
    linearGrowthInf u ≤ linearGrowthSup u :=
  liminf_le_limsup h h'

end basic_properties

section basic_properties

variable {u v : ℕ → EReal} {a b : EReal}

lemma linearGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthInf u ≤ linearGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v ↦ EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linearGrowthInf_monotone (h : u ≤ v) : linearGrowthInf u ≤ linearGrowthInf v :=
  linearGrowthInf_eventually_monotone (Eventually.of_forall h)

lemma linearGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthSup u ≤ linearGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v ↦ monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linearGrowthSup_monotone (h : u ≤ v) : linearGrowthSup u ≤ linearGrowthSup v :=
  linearGrowthSup_eventually_monotone (Eventually.of_forall h)

lemma linearGrowthInf_le_linearGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    linearGrowthInf u ≤ linearGrowthSup v :=
  (liminf_le_limsup_of_frequently_le) <| h.mono fun n u_v ↦ by gcongr

lemma linearGrowthInf_le_iff :
    linearGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linearGrowthInf_iff :
    a ≤ linearGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

lemma linearGrowthSup_le_iff :
    linearGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linearGrowthSup_iff :
    a ≤ linearGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

/- Forward direction of `linearGrowthInf_le_iff`. -/
lemma frequently_le_mul (h : linearGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

/- Forward direction of `le_linearGrowthInf_iff`. -/
lemma eventually_mul_le (h : a < linearGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

/- Forward direction of `linearGrowthSup_le_iff`. -/
lemma eventually_le_mul (h : linearGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

/- Forward direction of `le_linearGrowthSup_iff`. -/
lemma frequently_mul_le (h : a < linearGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h

lemma _root_.Frequently.linearGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthInf u ≤ a :=
  linearGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr

lemma _root_.Eventually.le_linearGrowthInf (h : ∀ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthInf u :=
  le_linearGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

lemma _root_.Eventually.linearGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthSup u ≤ a :=
  linearGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr

lemma _root_.Frequently.le_linearGrowthSup (h : ∃ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthSup u :=
  le_linearGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

/-! ### Special cases -/

lemma linearGrowthSup_bot : linearGrowthSup (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  nth_rw 2 [← limsup_const (f := atTop (α := ℕ)) ⊥]
  refine limsup_congr <| (eventually_gt_atTop 0).mono fun n n_pos ↦ ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)

lemma linearGrowthInf_bot : linearGrowthInf (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup

lemma linearGrowthInf_top : linearGrowthInf ⊤ = (⊤ : EReal) := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos ↦ top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma linearGrowthSup_top : linearGrowthSup (⊤ : ℕ → EReal) = (⊤ : EReal) := by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup

lemma linearGrowthInf_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

lemma linearGrowthSup_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

lemma linearGrowthInf_zero : linearGrowthInf 0 = (0 : EReal) :=
  linearGrowthInf_const zero_ne_bot zero_ne_top

lemma linearGrowthSup_zero : linearGrowthSup 0 = (0 : EReal) :=
  linearGrowthSup_const zero_ne_bot zero_ne_top

lemma linearGrowthInf_const_mul_self : linearGrowthInf (fun n ↦ a * n) = a :=
  le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))

lemma linearGrowthSup_const_mul_self : linearGrowthSup (fun n ↦ a * n) = a :=
  le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))

lemma linearGrowthInf_natCast_nonneg (v : ℕ → ℕ) :
    0 ≤ linearGrowthInf fun n ↦ (v n : EReal) :=
  (le_liminf_of_le) (Eventually.of_forall fun n ↦ div_nonneg (v n).cast_nonneg' n.cast_nonneg')

lemma tendsto_atTop_of_linearGrowthInf_pos (h : 0 < linearGrowthInf u) :
    Tendsto u atTop (𝓝 ⊤) := by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M ↦ eventually_atTop.2 ?_
  lift a to ℝ using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨n, hn⟩ := exists_nat_ge (M / a)
  refine ⟨n + 1, fun k k_n ↦ ?_⟩
  rw [← coe_coe_eq_natCast, ← coe_mul, EReal.coe_lt_coe_iff, mul_comm]
  exact (div_lt_iff₀ a_0).1 (hn.trans_lt (Nat.cast_lt.2 k_n))

/-! ### Addition and negation -/

lemma le_linearGrowthInf_add :
    linearGrowthInf u + linearGrowthInf v ≤ linearGrowthInf (u + v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linearGrowthInf_add_le'` for a version with swapped argument `u` and `v`. -/
lemma linearGrowthInf_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthInf v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthInf v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthSup u + linearGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linearGrowthInf_add_le` for a version with swapped argument `u` and `v`. -/
lemma linearGrowthInf_add_le' (h : linearGrowthInf u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthInf u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthInf u + linearGrowthSup v := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

/-- See `le_linearGrowthSup_add'` for a version with swapped argument `u` and `v`. -/
lemma le_linearGrowthSup_add : linearGrowthSup u + linearGrowthInf v ≤ linearGrowthSup (u + v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_linearGrowthSup_add` for a version with swapped argument `u` and `v`. -/
lemma le_linearGrowthSup_add' :
    linearGrowthInf u + linearGrowthSup v ≤ linearGrowthSup (u + v) := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add

lemma linearGrowthSup_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthSup (u + v) ≤ linearGrowthSup u + linearGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

lemma linearGrowthInf_neg : linearGrowthInf (-u) = - linearGrowthSup u := by
  rw [linearGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

lemma linearGrowthSup_inv : linearGrowthSup (-u) = - linearGrowthInf u := by
  rw [linearGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

/-! ### Affine bounds -/

lemma linearGrowthInf_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthInf u ≤ linearGrowthInf v := by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

lemma linearGrowthSup_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthSup u ≤ linearGrowthSup v := by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

/-! ### Infimum and supremum -/

lemma linearGrowthInf_inf :
    linearGrowthInf (u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v) := by
  rw [linearGrowthInf, linearGrowthInf, linearGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower linear growth as an `InfTopHom`. -/
noncomputable def linearGrowthInfTopHom : InfTopHom (ℕ → EReal) EReal where
  toFun := linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top

lemma linearGrowthInf_biInf {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, linearGrowthInf (u x) := by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

lemma linearGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthInf (⨅ i, u i) = ⨅ i, linearGrowthInf (u i) := by
  rw [← iInf_univ, linearGrowthInf_biInf u Set.finite_univ, iInf_univ]

lemma linearGrowthSup_sup :
    linearGrowthSup (u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v) := by
  rw [linearGrowthSup, linearGrowthSup, linearGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper linear growth as a `SupBotHom`. -/
noncomputable def linearGrowthSupBotHom : SupBotHom (ℕ → EReal) EReal where
  toFun := linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot

lemma linearGrowthSup_biSup {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, linearGrowthSup (u x) := by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

lemma linearGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthSup (⨆ i, u i) = ⨆ i, linearGrowthSup (u i) := by
  rw [← iSup_univ, linearGrowthSup_biSup u Set.finite_univ, iSup_univ]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → EReal} {v : ℕ → ℕ}

lemma Real.eventually_atTop_exists_int_between {a b : ℝ} (h : a < b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℤ, a * x ≤ n ∧ n ≤ b * x := by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x ↦ ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h), mul_comm, sub_mul, le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩

lemma Real.eventually_atTop_exists_nat_between {a b : ℝ} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, a * x ≤ n ∧ n ≤ b * x := by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  norm_cast
  exact Int.toNat_eq_max m

lemma EReal.eventually_atTop_exists_nat_between {a b : EReal} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, a * n ≤ m ∧ m ≤ b * n :=
  match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n ↦ ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
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

lemma tendsto_atTop_of_linearGrowthInf_natCast_pos (h : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    Tendsto v atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  have := tendsto_atTop_of_linearGrowthInf_pos (h.lt_of_le' (linearGrowthInf_natCast_nonneg v))
  exact (tendsto_nhds_top_iff_real.1 this M).mono fun n ↦ by exact_mod_cast le_of_lt

lemma le_linearGrowthInf_comp (hu : 0 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n ↦ v n : EReal) * linearGrowthInf u ≤ linearGrowthInf (u ∘ v) := by
  have uv_0 : 0 ≤ linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ ↦ Eventually.le_linearGrowthInf ?_
  have b_uv := eventually_map.1 ((eventually_mul_le b_u).filter_mono hv)
  filter_upwards [b_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact b_uvn.trans' <| by gcongr

lemma linearGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 0 ≤ u n)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    linearGrowthSup (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * linearGrowthSup u := by
  have v_0 := hv₀.symm.lt_of_le <| (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) ?_
  refine fun a v_a b u_b ↦ Eventually.linearGrowthSup_le ?_
  have b_0 : 0 ≤ b := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact (linearGrowthInf_le_linearGrowthSup_of_frequently_le hu).trans u_b.le
  have uv_b : ∀ᶠ n in atTop, u (v n) ≤ b * v n :=
    eventually_map.1 ((eventually_le_mul u_b).filter_mono hv₂)
  filter_upwards [uv_b, eventually_lt_of_limsup_lt v_a, eventually_gt_atTop 0]
    with n uvn_b vn_a n_0
  replace vn_a := ((div_lt_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact uvn_b.trans <| by gcongr

/-! ### Monotone sequences -/

lemma _root_.Monotone.linearGrowthInf_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linearGrowthInf u := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : ∀ᶠ n in atTop, u m ≤ u n := eventually_atTop.2 ⟨m, fun _ hb ↦ h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linearGrowthInf_top.symm.trans_le (linearGrowthInf_eventually_monotone m_n))
  · rw [← linearGrowthInf_const hm hm']
    exact linearGrowthInf_eventually_monotone m_n

lemma _root_.Monotone.linearGrowthSup_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linearGrowthSup u :=
  (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)

lemma linearGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linearGrowthInf (u ∘ v) := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : ∀ᶠ n in atTop, u m ≤ (u ∘ v) n :=
    (eventually_atTop.2 ⟨m, fun n m_n ↦ h m_n⟩).filter_mono hv
  apply (linearGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'
  · rw [hum', ← Pi.top_def, linearGrowthInf_top]; exact le_top
  · rw [linearGrowthInf_const hum hum']

lemma linearGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linearGrowthSup (u ∘ v) :=
  (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup

lemma _root_.Monotone.linearGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) :
    linearGrowthInf (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * linearGrowthInf u := by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot]; exact bot_le
  have v_0 := hv₀.symm.lt_of_le <| (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ ?_
  have a_0 := v_0.trans v_a
  have b_0 := (h.linearGrowthInf_nonneg u_0).trans_lt u_b
  rcases eq_or_ne a ⊤ with rfl | a_top
  · rw [top_mul_of_pos b_0]; exact le_top
  apply Frequently.linearGrowthInf_le
  obtain ⟨a', v_a', a_a'⟩ := exists_between v_a
  -- We get an epsilon of room: if `m` is large enough, then `v n ≤ a' * n < a * n`.
  -- Using `u_b`, we can find arbitrarily large values `n` such that `u n ≤ b * n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a⁻¹ * n ≤ k ≤ a'⁻¹ * n`, or, in other words, `a' * k ≤ n ≤ a * k`.
  -- Then `v k ≤ a' * k ≤ n`, so `u (v k) ≤ u n ≤ b * n ≤ b * a * k`.
  have a_0' := v_0.trans v_a'
  have a_a_inv' : a⁻¹ < a'⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0') (Set.mem_Ioi.2 a_0) a_a'
  replace v_a' : ∀ᶠ n : ℕ in atTop, v n ≤ a' * n := by
    filter_upwards [eventually_lt_of_limsup_lt v_a', eventually_gt_atTop 0] with n vn_a' n_0
    rw [mul_comm]
    exact (div_le_iff_le_mul (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a'.le
  suffices h : (∀ᶠ n : ℕ in atTop, v n ≤ a' * n) → ∃ᶠ n : ℕ in atTop, (u ∘ v) n ≤ a * b * n
    from h v_a'
  rw [← frequently_imp_distrib]
  replace u_b := ((frequently_le_mul u_b).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0'.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top M
  obtain ⟨n, n_M', ⟨un_bn, _⟩, k, an_k, k_an'⟩ := frequently_atTop.1 u_b M'
  refine ⟨k, ?_, fun vk_ak' ↦ ?_⟩
  · rw [mul_comm a, ← le_div_iff_mul_le a_0 a_top, EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0' (ne_top_of_lt a_a'), mul_comm] at k_an'
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0 a_top] at an_k
    have vk_n := Nat.cast_le.1 (vk_ak'.trans k_an')
    exact (h vk_n).trans <| un_bn.trans <| by gcongr

lemma _root_.Monotone.le_linearGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    (linearGrowthInf fun n ↦ v n : EReal) * linearGrowthSup u ≤ linearGrowthSup (u ∘ v) := by
  have v_0 := hv.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linearGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply EReal.mul_le_of_forall_lt_of_nonneg v_0.le
    (linearGrowthSup_comp_nonneg h u_0 (tendsto_atTop_of_linearGrowthInf_natCast_pos hv))
  intro a ⟨a_0, a_v⟩ b ⟨b_0, b_u⟩
  apply Frequently.le_linearGrowthSup
  obtain ⟨a', a_a', a_v'⟩ := exists_between a_v
  -- We get an epsilon of room: if `m` is large enough, then `a * n < a' * n ≤ v n`.
  -- Using `b_u`, we can find arbitrarily large values `n` such that `b * n ≤ u n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a'⁻¹ * n ≤ k ≤ a⁻¹ * n`, or, in other words, `a * k ≤ n ≤ a' * k`.
  -- Then `v k ≥ a' * k ≥ n`, so `u (v k) ≥ u n ≥ b * n ≥ b * a * k`.
  have a_top' := ne_top_of_lt a_v'
  have a_0' := a_0.trans a_a'
  have a_a_inv' : a'⁻¹ < a⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0) (Set.mem_Ioi.2 a_0') a_a'
  replace a_v' : ∀ᶠ n : ℕ in atTop, a' * n ≤ v n := by
    filter_upwards [eventually_lt_of_lt_liminf a_v', eventually_gt_atTop 0] with n a_vn' n_0
    exact (le_div_iff_mul_le (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn'.le
  suffices h : (∀ᶠ n : ℕ in atTop, a' * n ≤ v n) → ∃ᶠ n : ℕ in atTop, a * b * n ≤ (u ∘ v) n
    from h a_v'
  rw [← frequently_imp_distrib]
  replace b_u := ((frequently_mul_le b_u).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top' M
  obtain ⟨n, n_M', ⟨bn_un, _⟩, k, an_k', k_an⟩ := frequently_atTop.1 b_u M'
  refine ⟨k, ?_, fun ak_vk' ↦ ?_⟩
  · rw [mul_comm a', ← le_div_iff_mul_le a_0' a_top', EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k'.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0' a_top'] at an_k'
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0 (ne_top_of_lt a_a'), mul_comm] at k_an
    have n_vk := Nat.cast_le.1 (an_k'.trans ak_vk')
    exact le_trans (by gcongr) <| bn_un.trans (h n_vk)

lemma _root_.Monotone.linearGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linearGrowthInf (u ∘ v) = a * linearGrowthInf u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthInf_comp` and `linearGrowthInf_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! h' : ∃ᶠ n : ℕ in atTop, u n ≤ 0
  · replace h' (n : ℕ) : u n ≤ 0 := by
      obtain ⟨m, n_m, um_1⟩ := (frequently_atTop.1 h') n
      exact (h n_m).trans um_1
    have u_0' : linearGrowthInf u = 0 := by
      apply le_antisymm _ (h.linearGrowthInf_nonneg u_0)
      exact (linearGrowthInf_monotone h').trans_eq (linearGrowthInf_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linearGrowthInf_comp_nonneg h u_0 v_top)
    apply (linearGrowthInf_monotone fun n ↦ h' (v n)).trans_eq
    exact linearGrowthInf_const zero_ne_bot zero_ne_top
  · replace h' := h'.mono fun _ hn ↦ hn.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact h.linearGrowthInf_comp_le ha ha'
    · rw [← hv.liminf_eq]
      exact le_linearGrowthInf_comp h' v_top

lemma _root_.Monotone.linearGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linearGrowthSup (u ∘ v) = a * linearGrowthSup u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthSup_comp` and `linearGrowthSup_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthSup_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! u_1 : ∀ᶠ n : ℕ in atTop, u n ≤ 0
  · have u_0' : linearGrowthSup u = 0 := by
      apply le_antisymm _ (h.linearGrowthSup_nonneg u_0)
      apply (linearGrowthSup_eventually_monotone u_1).trans_eq
      exact (linearGrowthSup_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linearGrowthSup_comp_nonneg h u_0 v_top)
    apply (linearGrowthSup_eventually_monotone (v_top.eventually u_1)).trans_eq
    exact linearGrowthSup_const zero_ne_bot zero_ne_top
  · replace u_1 := u_1.mono fun x hx ↦ hx.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact linearGrowthSup_comp_le u_1 ha ha' v_top
    · rw [← hv.liminf_eq]
      exact h.le_linearGrowthSup_comp hv₁.ne.symm

lemma _root_.Monotone.linearGrowthInf_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    linearGrowthInf (fun n ↦ u (m * n)) = m * linearGrowthInf u := by
  have : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthInf_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

lemma _root_.Monotone.linearGrowthSup_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    linearGrowthSup (fun n ↦ u (m * n)) = m * linearGrowthSup u := by
  have : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthSup_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

end composition

end LinearGrowth
