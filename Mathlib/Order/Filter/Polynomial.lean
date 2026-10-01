/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma, Artie Khovanov
-/
module
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.Group.Order

/-!
# Limits related to polynomial and rational functions

We prove various limits for polynomial and rational functions, depending on
the degrees and leading coefficients of the considered polynomials.
-/

public section

-- TODO : Filter.Tendsto.of_tendsto_comp -> Filter.Tendsto.of_tendsto_comap

-- Prereqs

-- Mathlib.Topology.Order.Basic
/--
Not an instance for performance reasons.
-/
theorem Preorder.topology.orderTopology (α : Type*) [Preorder α] :
  letI := topology α; OrderTopology α := let := Preorder.topology α; ⟨rfl⟩

-- Mathlib.Algebra.Polynomial.Reverse
@[simp]
theorem Polynomial.reflect_natDegree_eq_reverse {R : Type*} [CommSemiring R] (f : R[X]) :
    f.reflect f.natDegree = f.reverse := rfl

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_zero_of_degree_le
    {R : Type*} [CommSemiring R] (f : R[X]) {N : ℕ} (hf : f.degree < N) :
    (f.reflect N).eval 0 = 0 := by
  simp [← coeff_zero_eq_eval_zero, coeff_eq_zero_of_degree_lt hf]

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : R[X]) {N : ℕ} (hf : f.natDegree ≤ N) :
    (f.reflect N).eval (⅟x) * x ^ N = f.eval x := by
  simpa using f.eval₂_reflect_mul_pow (RingHom.id _) x N hf

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reflect_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) {N : ℕ} (hf : f.natDegree ≤ N) :
    (f.reflect N).eval x⁻¹ * x ^ N = f.eval x := by
  let := invertibleOfNonzero hx
  simpa using f.eval₂_reflect_mul_pow (RingHom.id _) x N hf

-- Mathlib.Algebra.Polynomial.Reverse
@[simp]
theorem Polynomial.eval_reverse_zero
    {R : Type*} [CommSemiring R] (f : R[X]) :
    f.reverse.eval 0 = f.leadingCoeff := by
  simp [← coeff_zero_eq_eval_zero]

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow
    {R : Type*} [CommSemiring R] (x : R) [Invertible x] (f : R[X]) :
    f.reverse.eval (⅟x) * x ^ f.natDegree = f.eval x := by
  simpa using f.eval₂_reverse_mul_pow (RingHom.id _) x

-- Mathlib.Algebra.Polynomial.Reverse
theorem Polynomial.eval_reverse_mul_pow₀
    {F : Type*} [Field F] {x : F} (hx : x ≠ 0) (f : F[X]) :
    f.reverse.eval x⁻¹ * x ^ f.natDegree = f.eval x := by
  let := invertibleOfNonzero hx
  simpa using f.eval_reverse_mul_pow x

-- Mathlib.Order.Filter.Pointwise
theorem Filter.tendsto_iff_tendsto_inv_inv {α β : Type*} [InvolutiveInv α]
    (f : α → β) (l : Filter α) (m : Filter β) :
    Tendsto f l m ↔ Tendsto (fun x ↦ f x⁻¹) l⁻¹ m := by
  simp_rw [tendsto_def, mem_inv]
  convert Iff.rfl
  ext
  simp

-- Mathlib.Order.Filter.AtTopBot.Ring
theorem Filter.Tendsto.atTop_pow₀ {α β : Type*} [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (f : β → α) {l : Filter β} (hf : Tendsto f l atTop) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x ↦ f x ^ n) l atTop := by
    refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx ↦ ?_) hf
    simpa only [pow_one] using pow_le_pow_right₀ hx hn


-- Actual theorems

namespace Polynomial

open Filter

open scoped Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

section PolynomialDivAtTop

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_pos
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[>] 0) := by
  have : P ≠ 0 := by grind [leadingCoeff_zero]
  have : Q ≠ 0 := by grind [degree_zero, not_lt_bot]
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦
      x ^ (Q.natDegree - P.natDegree) * P.reverse.eval x / Q.reverse.eval x))]
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · convert ContinuousWithinAt.tendsto _
      · simp [Nat.sub_ne_zero_of_lt (natDegree_lt_natDegree ‹P ≠ 0› hdeg)]
      · fun_prop (disch := simp [‹Q ≠ 0›])
    · refine Filter.Eventually.mono ?_ (fun x ⟨hx₁, hx₂, hx₃⟩ ↦ ?_)
        (p := fun x ↦ 0 < x ∧ 0 < P.reverse.eval x ∧ 0 < Q.reverse.eval x)
      · have hpos : ∀ {f : F[X]}, 0 < f.leadingCoeff →
            ∀ᶠ (x : F) in 𝓝[>] 0, 0 < eval x f.reverse := fun {f} hf ↦ by
          convert ((ContinuousWithinAt.tendsto (f := f.reverse.eval) _).eventually_mem
            (s := Set.Ioo 0 (2 * f.leadingCoeff)) _).mono _
          · fun_prop
          · grind [eval_reverse_zero, Ioo_mem_nhds]
          · grind
        filter_upwards [self_mem_nhdsWithin, hpos hP, hpos hQ] using by grind
      · simpa using by positivity
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  simp [pow_sub₀ x hx (natDegree_le_natDegree hdeg.le),
    ← eval_reverse_mul_pow₀ (x := x⁻¹) (by simpa using hx)]
  field

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[>] 0) := by
  wlog hnng : 0 ≤ P.leadingCoeff
  · simpa using this (P := - P) (Q := - Q)
      (by simpa) (by simpa) (by grind [leadingCoeff_neg])
  apply div_tendsto_atTop_of_degree_lt_of_leadingCoeff_pos <;>
    grind [div_pos_iff, leadingCoeff_eq_zero, degree_zero, not_lt_bot]

theorem div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_neg
    [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) (hpos : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝[<] 0) := by
  convert tendsto_neg_nhdsGT.comp <| div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos
      (P := -P) (Q := Q) (by simpa) (by simp; grind) <;>
    simp; ring

theorem div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) := by
  rcases lt_trichotomy (P.leadingCoeff / Q.leadingCoeff) 0 with neg | eq | pos
  · exact (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_neg hdeg neg).mono_right
      nhdsWithin_le_nhds
  · rw [div_eq_zero_iff] at eq
    cases eq <;> simp_all
  · exact (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos hdeg pos).mono_right
      nhdsWithin_le_nhds

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  rcases eq_or_ne Q 0 with rfl | _
  · simp
  rw [Filter.tendsto_iff_tendsto_inv_inv, inv_atTop₀,
    tendsto_congr' (f₂ := (fun x ↦ P.reverse.eval x  / Q.reverse.eval x))]
  · convert (ContinuousAt.tendsto _).mono_left nhdsWithin_le_nhds using 2
    · simp
    · fun_prop (disch := simp [‹Q ≠ 0›])
  filter_upwards [show {0}ᶜ ∈ _ from ⟨Set.univ, by simp⟩] with x hx
  grind [eval_reverse_mul_pow₀ (x := x⁻¹), pow_ne_zero, natDegree_eq_natDegree]

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ P.eval x / Q.eval x) atTop atTop := by
  let := Preorder.topology F
  have := Preorder.topology.orderTopology F
  convert (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_pos hdeg
    (by grind [div_pos_iff])).inv_tendsto_nhdsGT_zero
  simp

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atTop :=
  have hpos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne' hnng (by grind [leadingCoeff_eq_zero, not_lt_bot])
  div_tendsto_atTop_of_degree_gt' hdeg hpos

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot := by
  let := Preorder.topology F
  have := Preorder.topology.orderTopology F
  convert (div_tendsto_atTop_of_degree_lt_of_leadingCoeff_div_neg hdeg
    (by grind [div_neg_iff])).inv_tendsto_nhdsLT_zero
  simp

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot :=
  have hneg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne' hnps (by grind [leadingCoeff_eq_zero, not_lt_bot])
  div_tendsto_atBot_of_degree_gt' hdeg hneg

-- TODO : bounded iff version

theorem div_tendsto_atTop_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atTop_zero_of_degree_lt⟩
  contrapose! h
  rcases h.lt_or_eq' with lt | eq
  · grind [div_tendsto_atTop_of_degree_gt, div_tendsto_atBot_of_degree_gt, disjoint_nhds_atTop,
      disjoint_nhds_atBot, Tendsto.not_tendsto]
  · exact (div_tendsto_atTop_leadingCoeff_div_of_degree_eq eq).not_tendsto <| by
      grind [disjoint_nhds_nhds, div_eq_zero_iff, leadingCoeff_eq_zero, degree_zero,
        le_bot_iff, degree_eq_bot]

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (div_tendsto_atTop_of_degree_gt hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (div_tendsto_atBot_of_degree_gt hdeg hQ h.le)

end PolynomialDivAtTop

section PolynomialDivAtBot

theorem div_tendsto_atBot_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun ht ↦ ?_, fun hdeg ↦ ?_⟩
  · rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X,
        ← div_tendsto_atTop_zero_iff_degree_lt (by simpa)]
    convert ht.comp tendsto_neg_atTop_atBot
    simp
  · rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
    convert (div_tendsto_atTop_zero_of_degree_lt hdeg).comp tendsto_neg_atBot_atTop
    simp

alias ⟨_, div_tendsto_atBot_zero_of_degree_lt⟩ := div_tendsto_atBot_zero_iff_degree_lt

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  sorry
  -- degrees same so sign switch when going to -∞ same

theorem abs_div_tendsto_atBot_atTop_of_degree_gt [TopologicalSpace F] [OrderTopology F]
    (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert (abs_div_tendsto_atTop_atTop_of_degree_gt hdeg (by simpa)).comp tendsto_neg_atBot_atTop
  simp

end PolynomialDivAtBot

section PolynomialAtTop

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hlcf : 0 ≤ P.leadingCoeff) :
    Tendsto P.eval atTop atTop := by
  let := Preorder.topology F
  have := Preorder.topology.orderTopology F
  simpa using div_tendsto_atTop_of_degree_gt' (P := P) (Q := 1) (by simpa)
    (by simp; grind [leadingCoeff_eq_zero, not_lt_bot])

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P) atTop atBot := by
  simpa using tendsto_atTop_of_leadingCoeff_nonneg (P := -P)
    (by simpa using hdeg) (by simpa using hnps)

theorem tendsto_atTop_or_tendsto_atBot (hdeg : 0 < P.degree) :
    Tendsto P.eval atTop atTop ∨ Tendsto P.eval atTop atBot := by
  rcases lt_or_ge 0 P.leadingCoeff with pos | neg
  · exact Or.inl <| tendsto_atTop_of_leadingCoeff_nonneg hdeg pos.le
  · exact Or.inr <| tendsto_atBot_of_leadingCoeff_nonpos hdeg neg

theorem tendsto_pure_iff {c : F} :
    Tendsto P.eval atTop (pure c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  have mp' : Tendsto P.eval atTop (pure c) → P.degree ≤ 0 := fun h ↦ by
    contrapose! h
    rcases tendsto_atTop_or_tendsto_atBot h with top | bot
    · exact top.not_tendsto (disjoint_pure_atTop _).symm
    · exact bot.not_tendsto (disjoint_pure_atBot _).symm
  have mpr' : P.degree ≤ 0 → Tendsto P.eval atTop (pure P.leadingCoeff) := fun h ↦ by
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simp
  grind [Filter.Tendsto.not_tendsto, disjoint_pure_pure]

theorem tendsto_nhds_iff [TopologicalSpace F] [OrderTopology F] {c : F} :
    Tendsto P.eval atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (tendsto_pure_iff.mpr h).mono_right (by simp)⟩
  · have : P.degree ≤ 0 := by
      contrapose! h
      rcases tendsto_atTop_or_tendsto_atBot h with top | bot
      · exact top.not_tendsto (disjoint_nhds_atTop _).symm
      · exact bot.not_tendsto (disjoint_nhds_atBot _).symm
    refine ⟨?_, this⟩
    rw! [Polynomial.eq_C_of_degree_le_zero this] at h ⊢
    simp_all

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto P.eval atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h ↦ ?_, fun h ↦ tendsto_atTop_of_leadingCoeff_nonneg h.1 h.2⟩
  have hdeg : 0 < P.degree := by
    contrapose! h
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simpa using tendsto_const_pure.not_tendsto (disjoint_pure_atTop _)
  refine ⟨hdeg, ?_⟩
  revert h
  refine degree_pos_induction_on P hdeg
    (fun ha h ↦ ?_) (fun hdeg ih h ↦ ?_) (fun {_ a} hdeg ih h ↦ ?_)
  · simpa using ((tendsto_const_mul_atTop_iff_pos tendsto_id).mp (by simpa using h)).le
  · simpa using ih <| by
      contrapose! h
      simpa using tendsto_atTop_or_tendsto_atBot hdeg |>.resolve_left h |>.atBot_mul_atTop₀
        tendsto_id |>.not_tendsto disjoint_atBot_atTop
  · rw [leadingCoeff_add_of_degree_lt' (degree_C_le.trans_lt hdeg)]
    exact ih (by simpa using tendsto_atTop_add_const_right _ (-a) h)

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto P.eval atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (abs <| eval · P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop (|eval · P|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop h)

theorem abs_tendsto_atTop_iff : Tendsto (fun x ↦ abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atTop_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop⟩

end PolynomialAtTop

section PolynomialAtBot

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot h)

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atBot_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot⟩

end PolynomialAtBot

end Polynomial


namespace Polynomial

open Filter

open scoped Topology

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {P Q : F[X]}

section PolynomialAtTop

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) :
    0 ≤ P.leadingCoeff → Tendsto P.eval atTop atTop := by
  refine degree_pos_induction_on P hdeg
    (fun _ _ ↦ ?_) (fun _ ih hnnng ↦ ?_) (fun _ _ _ ↦ ?_)
  · simpa using tendsto_id.const_mul_atTop (by simp at *; grind)
  · simpa using (ih (by simpa using hnnng)).atTop_mul_atTop₀ tendsto_id
  · simpa using tendsto_atTop_add_const_right _ _
      (by grind [leadingCoeff_add_of_degree_lt', degree_C_le])

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P) atTop atBot := by
  simpa using tendsto_atTop_of_leadingCoeff_nonneg (P := -P)
    (by simpa using hdeg) (by simpa using hnps)

theorem tendsto_atTop_or_tendsto_atBot (hdeg : 0 < P.degree) :
    Tendsto P.eval atTop atTop ∨ Tendsto P.eval atTop atBot := by
  rcases lt_or_ge 0 P.leadingCoeff with pos | neg
  · exact Or.inl <| tendsto_atTop_of_leadingCoeff_nonneg hdeg pos.le
  · exact Or.inr <| tendsto_atBot_of_leadingCoeff_nonpos hdeg neg

theorem tendsto_pure_iff {c : F} :
    Tendsto P.eval atTop (pure c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  have mp' : Tendsto P.eval atTop (pure c) → P.degree ≤ 0 := fun h ↦ by
    contrapose! h
    rcases tendsto_atTop_or_tendsto_atBot h with top | bot
    · exact top.not_tendsto (disjoint_pure_atTop _).symm
    · exact bot.not_tendsto (disjoint_pure_atBot _).symm
  have mpr' : P.degree ≤ 0 → Tendsto P.eval atTop (pure P.leadingCoeff) := fun h ↦ by
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simp
  grind [Filter.Tendsto.not_tendsto, disjoint_pure_pure]

theorem tendsto_nhds_iff [TopologicalSpace F] [OrderTopology F] {c : F} :
    Tendsto P.eval atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (tendsto_pure_iff.mpr h).mono_right (by simp)⟩
  · have : P.degree ≤ 0 := by
      contrapose! h
      rcases tendsto_atTop_or_tendsto_atBot h with top | bot
      · exact top.not_tendsto (disjoint_nhds_atTop _).symm
      · exact bot.not_tendsto (disjoint_nhds_atBot _).symm
    refine ⟨?_, this⟩
    rw! [Polynomial.eq_C_of_degree_le_zero this] at h ⊢
    simp_all

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto P.eval atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h ↦ ?_, fun h ↦ tendsto_atTop_of_leadingCoeff_nonneg h.1 h.2⟩
  have hdeg : 0 < P.degree := by
    contrapose! h
    rw! [Polynomial.eq_C_of_degree_le_zero h]
    simpa using tendsto_const_pure.not_tendsto (disjoint_pure_atTop _)
  refine ⟨hdeg, ?_⟩
  revert h
  refine degree_pos_induction_on P hdeg
    (fun ha h ↦ ?_) (fun hdeg ih h ↦ ?_) (fun {_ a} hdeg ih h ↦ ?_)
  · simpa using ((tendsto_const_mul_atTop_iff_pos tendsto_id).mp (by simpa using h)).le
  · simpa using ih <| by
      contrapose! h
      simpa using tendsto_atTop_or_tendsto_atBot hdeg |>.resolve_left h |>.atBot_mul_atTop₀
        tendsto_id |>.not_tendsto disjoint_atBot_atTop
  · rw [leadingCoeff_add_of_degree_lt' (degree_C_le.trans_lt hdeg)]
    exact ih (by simpa using tendsto_atTop_add_const_right _ (-a) h)

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto P.eval atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (abs <| eval · P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop (|eval · P|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop h)

theorem abs_tendsto_atTop_iff : Tendsto (fun x ↦ abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atTop_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop⟩

end PolynomialAtTop

section PolynomialAtBot

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr(abs $(_root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot h)

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt isBoundedUnder_abs_atBot_iff.mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot⟩

end PolynomialAtBot

section PolynomialDivAtTop

theorem div_tendsto_atTop_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) := by
  by_cases hP : P = 0
  · simp [hP]
  sorry

theorem div_tendsto_atTop_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atTop_zero_of_degree_lt⟩
  by_cases hPQ : P.leadingCoeff / Q.leadingCoeff = 0
  · simp only [div_eq_mul_inv, inv_eq_zero, mul_eq_zero] at hPQ
    rcases hPQ with hP0 | hQ0
    · rw [leadingCoeff_eq_zero.1 hP0, degree_zero]
      exact bot_lt_iff_ne_bot.2 fun hQ' ↦ hQ (degree_eq_bot.1 hQ')
    · exact absurd (leadingCoeff_eq_zero.1 hQ0) hQ
  · sorry

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop (𝓝 <| P.leadingCoeff / Q.leadingCoeff) := by
  sorry

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atTop := by
  have hQ : Q ≠ 0 := fun h ↦ by simp [h] at hpos
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  sorry

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atTop :=
  have ratio_pos : 0 < P.leadingCoeff / Q.leadingCoeff :=
    lt_of_le_of_ne hnng
      (div_ne_zero (fun h ↦ ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h ↦
          hQ <| leadingCoeff_eq_zero.mp h).symm
  div_tendsto_atTop_of_degree_gt' hdeg ratio_pos

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot := by
  have hQ : Q ≠ 0 := fun h ↦ by
    simp only [h, div_zero, leadingCoeff_zero] at hneg
    exact hneg.false
  rw [← natDegree_lt_natDegree_iff hQ] at hdeg
  sorry

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0)
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atTop atBot :=
  have ratio_neg : P.leadingCoeff / Q.leadingCoeff < 0 :=
    lt_of_le_of_ne hnps
      (div_ne_zero (fun h ↦ ne_zero_of_degree_gt hdeg <| leadingCoeff_eq_zero.mp h) fun h ↦
        hQ <| leadingCoeff_eq_zero.mp h)
  div_tendsto_atBot_of_degree_gt' hdeg ratio_neg

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atTop atTop := by
  by_cases! h : 0 ≤ P.leadingCoeff / Q.leadingCoeff
  · exact tendsto_abs_atTop_atTop.comp (div_tendsto_atTop_of_degree_gt hdeg hQ h)
  · exact tendsto_abs_atBot_atTop.comp (div_tendsto_atBot_of_degree_gt hdeg hQ h.le)

end PolynomialDivAtTop

section PolynomialDivAtBot

theorem div_tendsto_atBot_zero_of_degree_lt [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree < Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  convert! (div_tendsto_atTop_zero_of_degree_lt hdeg).comp tendsto_neg_atBot_atTop using 2
  simp

theorem div_tendsto_atBot_zero_iff_degree_lt [TopologicalSpace F] [OrderTopology F] (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  sorry

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq [TopologicalSpace F] [OrderTopology F]
    (hdeg : P.degree = Q.degree) :
    Tendsto (fun x ↦ eval x P / eval x Q) atBot (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  sorry

theorem abs_div_tendsto_atBot_atTop_of_degree_gt [TopologicalSpace F] [OrderTopology F]
    (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x ↦ |eval x P / eval x Q|) atBot atTop := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at hdeg
  replace hQ : Q.comp (-X) ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    simp [hQ]
  convert! (abs_div_tendsto_atTop_atTop_of_degree_gt hdeg hQ).comp tendsto_neg_atBot_atTop
    using 2
  simp

end PolynomialDivAtBot

end Polynomial
