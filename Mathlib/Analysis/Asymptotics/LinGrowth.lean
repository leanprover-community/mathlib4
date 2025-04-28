/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exponential growth

This file defines the linear growth of a sequence `u : ℕ → EReal`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively.

## Main definitions

- `linGrowthInf`, `linGrowthSup`: respectively, `liminf` and `limsup` of `(u n) / n`.
- `linGrowthInfTopHom`, `linGrowthSupBotHom`: the functions `linGrowthInf`, `linGrowthSup`
as homomorphisms preserving finitary `Inf`/`Sup` respectively.
-/

namespace LinGrowth

open EReal Filter Function
open scoped Topology

/-! ### Definition -/

/-- Lower linear growth of a sequence of extended real numbers. -/
noncomputable def linGrowthInf (u : ℕ → EReal) : EReal := liminf (fun n ↦ u n / n) atTop

/-- Upper linear growth of a sequence of extended real numbers. -/
noncomputable def linGrowthSup (u : ℕ → EReal) : EReal := limsup (fun n ↦ u n / n) atTop

/-! ### Basic properties -/

section basic_properties

variable {u v : ℕ → EReal} {a b : EReal}

lemma linGrowthInf_congr (h : u =ᶠ[atTop] v) :
    linGrowthInf u = linGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linGrowthSup_congr (h : u =ᶠ[atTop] v) :
    linGrowthSup u = linGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linGrowthInf u ≤ linGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v ↦ monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linGrowthInf_monotone : Monotone linGrowthInf :=
  fun _ _ uv ↦ linGrowthInf_eventually_monotone (Eventually.of_forall uv)

lemma linGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linGrowthSup u ≤ linGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v ↦ monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linGrowthSup_monotone : Monotone linGrowthSup :=
  fun _ _ uv ↦ linGrowthSup_eventually_monotone (Eventually.of_forall uv)

lemma linGrowthInf_le_linGrowthSup : linGrowthInf u ≤ linGrowthSup u := liminf_le_limsup

lemma linGrowthInf_le_linGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    linGrowthInf u ≤ linGrowthSup v := by
  refine (liminf_le_limsup_of_frequently_le) (h.mono fun n u_v ↦ ?_)
  exact div_le_div_right_of_nonneg n.cast_nonneg' u_v

lemma linGrowthInf_le_iff :
    linGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linGrowthInf_iff :
    a ≤ linGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

lemma linGrowthSup_le_iff :
    linGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linGrowthSup_iff :
    a ≤ linGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

/- Forward direction of `linGrowthInf_le_iff`. -/
lemma frequently_le_mul (h : linGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linGrowthInf_le_iff.1 (le_refl (linGrowthInf u)) a h

/- Forward direction of `le_linGrowthInf_iff`. -/
lemma eventually_mul_le (h : a < linGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linGrowthInf_iff.1 (le_refl (linGrowthInf u)) a h

/- Forward direction of `linGrowthSup_le_iff`. -/
lemma eventually_le_mul (h : linGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linGrowthSup_le_iff.1 (le_refl (linGrowthSup u)) a h

/- Forward direction of `le_linGrowthSup_iff`. -/
lemma frequently_mul_le (h : a < linGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linGrowthSup_iff.1 (le_refl (linGrowthSup u)) a h

lemma _root_.Frequently.linGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linGrowthInf u ≤ a := by
  apply linGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans ?_
  exact mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg'

lemma _root_.Eventually.le_linGrowthInf (h : ∀ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linGrowthInf u := by
  apply le_linGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' ?_
  exact mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg'

lemma _root_.Eventually.linGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linGrowthSup u ≤ a:= by
  apply linGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans ?_
  exact mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg'

lemma _root_.Frequently.le_linGrowthSup (h : ∃ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linGrowthSup u := by
  apply le_linGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' ?_
  exact mul_le_mul_of_nonneg_right c_u.le n.cast_nonneg'

/-! ### Special cases -/

lemma linGrowthSup_zero : linGrowthSup 0 = 0 := by
  nth_rw 2 [← limsup_const (f := atTop (α := ℕ)) 0]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.zero_apply, zero_div]

lemma linGrowthInf_zero : linGrowthInf 0 = 0 := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) 0]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.zero_apply, zero_div]

lemma linGrowthInf_top : linGrowthInf ⊤ = ⊤ := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos ↦ top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma linGrowthSup_top : linGrowthSup ⊤ = ⊤ := by
  apply top_le_iff.1
  rw [← linGrowthInf_top]
  exact linGrowthInf_le_linGrowthSup

lemma linGrowthSup_bot : linGrowthSup ⊥ = ⊥ := by
  nth_rw 2 [← limsup_const (f := atTop (α := ℕ)) ⊥]
  refine limsup_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos ↦ bot_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma linGrowthInf_bot : linGrowthInf ⊥ = ⊥ := by
  apply le_bot_iff.1
  rw [← linGrowthSup_bot]
  exact linGrowthInf_le_linGrowthSup

lemma linGrowthInf_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

lemma linGrowthSup_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

lemma linGrowthInf_mul : linGrowthInf (fun n ↦ a * n) = a :=
  le_antisymm (Frequently.linGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_linGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))

lemma linGrowthSup_mul : linGrowthSup (fun n ↦ a * n) = a :=
  le_antisymm (Eventually.linGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_linGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))

lemma linGrowthInf_nonneg (v : ℕ → ℕ) : 0 ≤ liminf (fun n ↦ (v n : EReal) / n) atTop :=
  (le_liminf_of_le) (Eventually.of_forall fun n ↦ div_nonneg (v n).cast_nonneg' n.cast_nonneg')

/-! ### Multiplication and inversion -/

lemma le_linGrowthInf_add :
    linGrowthInf u + linGrowthInf v ≤ linGrowthInf (u + v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linGrowthInf_add_le'` for a version with swapped argument `u` and `v`. -/
lemma linGrowthInf_add_le (h : linGrowthSup u ≠ ⊥ ∨ linGrowthInf v ≠ ⊤)
    (h' : linGrowthSup u ≠ ⊤ ∨ linGrowthInf v ≠ ⊥) :
    linGrowthInf (u + v) ≤ linGrowthSup u + linGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linGrowthInf_add_le` for a version with swapped argument `u` and `v`. -/
lemma linGrowthInf_add_le' (h : linGrowthInf u ≠ ⊥ ∨ linGrowthSup v ≠ ⊤)
    (h' : linGrowthInf u ≠ ⊤ ∨ linGrowthSup v ≠ ⊥) :
    linGrowthInf (u + v) ≤ linGrowthInf u + linGrowthSup v := by
  rw [add_comm u v, add_comm (linGrowthInf u) (linGrowthSup v)]
  exact linGrowthInf_add_le h'.symm h.symm

/-- See `le_linGrowthSup_add'` for a version with swapped argument `u` and `v`. -/
lemma le_linGrowthSup_add : linGrowthSup u + linGrowthInf v ≤ linGrowthSup (u + v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_linGrowthSup_mul` for a version with swapped argument `u` and `v`. -/
lemma le_linGrowthSup_add' : linGrowthInf u + linGrowthSup v ≤ linGrowthSup (u + v) := by
  rw [add_comm u v, add_comm (linGrowthInf u) (linGrowthSup v)]
  exact le_linGrowthSup_add

lemma linGrowthSup_add_le (h : linGrowthSup u ≠ ⊥ ∨ linGrowthSup v ≠ ⊤)
    (h' : linGrowthSup u ≠ ⊤ ∨ linGrowthSup v ≠ ⊥) :
    linGrowthSup (u + v) ≤ linGrowthSup u + linGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

lemma linGrowthInf_neg : linGrowthInf (- u) = - linGrowthSup u := by
  rw [linGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

lemma linGrowthSup_inv : linGrowthSup (- u) = - linGrowthInf u := by
  rw [linGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

/-! ### Infimum and supremum -/

lemma linGrowthInf_inf : linGrowthInf (u ⊓ v) = min (linGrowthInf u) (linGrowthInf v) := by
  rw [linGrowthInf, linGrowthInf, linGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.inf_apply]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower exponential growth as an `InfTopHom`. -/
noncomputable def linGrowthInfTopHom : InfTopHom (ℕ → EReal) EReal where
  toFun := linGrowthInf
  map_inf' _ _ := linGrowthInf_inf
  map_top' := linGrowthInf_top

lemma linGrowthInf_biInf {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, linGrowthInf (u x) := by
  have := map_finset_inf linGrowthInfTopHom hs.toFinset u
  simpa only [linGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

lemma linGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linGrowthInf (⨅ i, u i) = ⨅ i, linGrowthInf (u i) := by
  rw [← iInf_univ, linGrowthInf_biInf u Set.finite_univ, iInf_univ]

lemma linGrowthSup_sup : linGrowthSup (u ⊔ v) = max (linGrowthSup u) (linGrowthSup v) := by
  rw [linGrowthSup, linGrowthSup, linGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.sup_apply]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper exponential growth as a `SupBotHom`. -/
noncomputable def linGrowthSupBotHom : SupBotHom (ℕ → EReal) EReal where
  toFun := linGrowthSup
  map_sup' _ _ := linGrowthSup_sup
  map_bot' := linGrowthSup_bot

lemma linGrowthSup_biSup {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, linGrowthSup (u x) := by
  have := map_finset_sup linGrowthSupBotHom hs.toFinset u
  simpa only [linGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

lemma linGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linGrowthSup (⨆ i, u i) = ⨆ i, linGrowthSup (u i) := by
  rw [← iSup_univ, linGrowthSup_biSup u Set.finite_univ, iSup_univ]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → EReal} {v : ℕ → ℕ}

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

lemma tendsto_atTop_of_linGrowthInf_pos (h : liminf (fun n ↦ (v n : EReal) / n) atTop ≠ 0) :
    Tendsto v atTop atTop := by
  refine tendsto_atTop_atTop.2 fun M ↦ eventually_atTop.1 ?_
  obtain ⟨a, a_0, a_v⟩ := exists_between (h.symm.lt_of_le (linGrowthInf_nonneg v))
  have h₁ : ∀ᶠ n : ℕ in atTop, M ≤ a * n := by
    obtain ⟨n, hn⟩ := exists_nat_ge_mul a.inv_lt_top.ne M
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0 (ne_top_of_lt a_v)] at hn
    refine eventually_atTop.2 ⟨n, fun k k_n ↦ ?_⟩
    exact hn.trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 k_n) a_0.le)
  have h₂ : ∀ᶠ n : ℕ in atTop, a * n ≤ v n := by
    refine (eventually_lt_of_lt_liminf a_v).mp (eventually_atTop.2 ⟨1, fun n n_1 a_vn ↦ ?_⟩)
    rw [lt_div_iff (Nat.cast_pos'.2 n_1) (natCast_ne_top n)] at a_vn
    exact a_vn.le
  filter_upwards [h₁, h₂] with n M_a a_vn
  exact Nat.cast_le.1 (M_a.trans a_vn)

lemma le_linGrowthInf_comp (hu : 0 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (liminf (fun n ↦ (v n : EReal) / n) atTop) * linGrowthInf u ≤ linGrowthInf (u ∘ v) := by
  have uv_0 : 0 ≤ linGrowthInf (u ∘ v) := by
    rw [← linGrowthInf_const zero_ne_bot zero_ne_top]
    exact linGrowthInf_eventually_monotone (hv.eventually hu)
  apply mul_le_of_forall_lt_of_nonneg (linGrowthInf_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ ↦ Eventually.le_linGrowthInf ?_
  have b_uv := eventually_map.1 ((eventually_mul_le b_u).filter_mono hv)
  filter_upwards [b_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact b_uvn.trans' (mul_le_mul_of_nonneg_left a_vn b_0.le)

lemma linGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 0 ≤ u n)
    (hv₀ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ 0)
    (hv₁ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    linGrowthSup (u ∘ v) ≤ (limsup (fun n ↦ (v n : EReal) / n) atTop) * linGrowthSup u := by
  have v_0 := hv₀.symm.lt_of_le <| (linGrowthInf_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ Eventually.linGrowthSup_le ?_
  have b_0 : 0 ≤ b := by
    rw [← linGrowthInf_const zero_ne_bot zero_ne_top]
    exact (linGrowthInf_le_linGrowthSup_of_frequently_le hu).trans u_b.le
  have uv_b : ∀ᶠ n in atTop, u (v n) ≤ b * v n :=
    eventually_map.1 ((eventually_le_mul u_b).filter_mono hv₂)
  filter_upwards [uv_b, eventually_lt_of_limsup_lt v_a, eventually_gt_atTop 0]
    with n uvn_b vn_a n_0
  replace vn_a := ((div_lt_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact uvn_b.trans (mul_le_mul_of_nonneg_left vn_a b_0)

/-! ### Monotone sequences -/

lemma _root_.Monotone.linGrowthInf_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linGrowthInf u := by
  simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : ∀ᶠ n in atTop, u m ≤ u n := eventually_atTop.2 ⟨m, fun _ hb ↦ h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linGrowthInf_top.symm.trans_le (linGrowthInf_eventually_monotone m_n))
  · rw [← linGrowthInf_const hm hm']
    exact linGrowthInf_eventually_monotone m_n

lemma _root_.Monotone.linGrowthSup_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linGrowthSup u :=
  (h.linGrowthInf_nonneg h').trans linGrowthInf_le_linGrowthSup

lemma linGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linGrowthInf (u ∘ v) := by
  simp only [ne_eq, funext_iff, Pi.zero_apply, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : ∀ᶠ n in atTop, u m ≤ (u ∘ v) n := by
    apply (eventually_map (P := fun n : ℕ ↦ u m ≤ u n)).2
    exact (eventually_atTop.2 ⟨m, fun n m_n ↦ h m_n⟩).filter_mono hv
  apply (linGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'
  · rw [hum', ← Pi.top_def, linGrowthInf_top]; exact le_top
  · rw [linGrowthInf_const hum hum']

lemma linGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linGrowthSup (u ∘ v) :=
  (linGrowthInf_comp_nonneg h h' hv).trans linGrowthInf_le_linGrowthSup

lemma _root_.Monotone.linGrowthInf_comp_le (h : Monotone u)
    (hv₀ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ 0)
    (hv₁ : limsup (fun n ↦ (v n : EReal) / n) atTop ≠ ⊤) :
    linGrowthInf (u ∘ v) ≤ (limsup (fun n ↦ (v n : EReal) / n) atTop) * linGrowthInf u := by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linGrowthInf_bot]; exact bot_le
  have v_0 := hv₀.symm.lt_of_le <| (linGrowthInf_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ ?_
  have a_0 := v_0.trans v_a
  have b_0 := (h.linGrowthInf_nonneg u_0).trans_lt u_b
  rcases eq_or_ne a ⊤ with rfl | a_top
  · rw [top_mul_of_pos b_0]; exact le_top
  apply Frequently.linGrowthInf_le
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
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 n_M') (inv_nonneg_of_nonneg a_0.le)
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0' (ne_top_of_lt a_a'), mul_comm] at k_an'
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0 a_top] at an_k
    have vk_n := Nat.cast_le.1 (vk_ak'.trans k_an')
    exact (h vk_n).trans <| un_bn.trans (mul_le_mul_of_nonneg_left an_k b_0.le)

lemma _root_.Monotone.le_linGrowthSup_comp (h : Monotone u)
    (hv : liminf (fun n ↦ (v n : EReal) / n) atTop ≠ 0) :
    (liminf (fun n ↦ (v n : EReal) / n) atTop) * linGrowthSup u ≤ linGrowthSup (u ∘ v) := by
  have v_0 := hv.symm.lt_of_le (linGrowthInf_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply mul_le_of_forall_lt_of_nonneg v_0.le
    (linGrowthSup_comp_nonneg h u_0 (tendsto_atTop_of_linGrowthInf_pos hv))
  refine fun a ⟨a_0, a_v⟩ b ⟨b_0, b_u⟩ ↦ Frequently.le_linGrowthSup ?_
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
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.2 n_M') (inv_nonneg_of_nonneg a_0'.le)
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0' a_top'] at an_k'
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0 (ne_top_of_lt a_a'), mul_comm] at k_an
    have n_vk := Nat.cast_le.1 (an_k'.trans ak_vk')
    exact (mul_le_mul_of_nonneg_left k_an b_0.le).trans <| bn_un.trans (h n_vk)

lemma _root_.Monotone.linGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linGrowthInf (u ∘ v) = a * linGrowthInf u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linGrowthInf_nonneg v)
  have v_top := tendsto_atTop_of_linGrowthInf_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linGrowthInf_comp` and `linGrowthInf_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linGrowthInf_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases h1 : ∃ᶠ n : ℕ in atTop, u n ≤ 0
  · replace h' (n : ℕ) : u n ≤ 0 := by
      obtain ⟨m, n_m, um_1⟩ := (frequently_atTop.1 h1) n
      exact (h n_m).trans um_1
    have u_0' : linGrowthInf u = 0 := by
      apply le_antisymm _ (h.linGrowthInf_nonneg u_0)
      exact (linGrowthInf_monotone h').trans_eq (linGrowthInf_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linGrowthInf_comp_nonneg h u_0 v_top)
    refine (linGrowthInf_monotone fun n ↦ ?_).trans_eq (linGrowthInf_const zero_ne_bot zero_ne_top)
    rw [comp_apply]; exact h' (v n)
  · replace h' := (not_frequently.1 h1).mono fun _ hn ↦ le_of_not_le hn
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact h.linGrowthInf_comp_le ha ha'
    · rw [← hv.liminf_eq]
      exact le_linGrowthInf_comp h' v_top

lemma _root_.Monotone.linGrowthSup_comp {a : EReal} (hu : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linGrowthSup (u ∘ v) = a * linGrowthSup u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linGrowthInf_nonneg v)
  have v_top := tendsto_atTop_of_linGrowthInf_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linGrowthSup_comp` and `linGrowthSup_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linGrowthSup_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases u_1 : ∀ᶠ n : ℕ in atTop, u n ≤ 0
  · have u_0' : linGrowthSup u = 0 := by
      apply le_antisymm _ (hu.linGrowthSup_nonneg u_0)
      apply (linGrowthSup_eventually_monotone u_1).trans_eq
      exact (linGrowthSup_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linGrowthSup_comp_nonneg hu u_0 v_top)
    apply (linGrowthSup_eventually_monotone (v_top.eventually u_1)).trans_eq
    exact linGrowthSup_const zero_ne_bot zero_ne_top
  · replace h' := (not_eventually.1 u_1).mono fun x hx ↦ (lt_of_not_le hx).le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact linGrowthSup_comp_le h' ha ha' v_top
    · rw [← hv.liminf_eq]
      exact hu.le_linGrowthSup_comp hv₁.ne.symm

lemma _root_.Monotone.linGrowthInf_comp_mul {m : ℕ} (hu : Monotone u) (hm : m ≠ 0) :
    linGrowthInf (fun n ↦ u (m * n)) = m * linGrowthInf u := by
  have h : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact hu.linGrowthInf_comp h (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

lemma _root_.Monotone.linGrowthSup_comp_mul {m : ℕ} (hu : Monotone u) (hm : m ≠ 0) :
    linGrowthSup (fun n ↦ u (m * n)) = m * linGrowthSup u := by
  have h : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact hu.linGrowthSup_comp h (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

end composition

end LinGrowth
