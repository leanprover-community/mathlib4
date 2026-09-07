/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.Polynomial.Sturm.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Algebraic certificates for Sturm chains

A signed remainder chain ending in a nonzero constant certifies a real root count.
The certificate consists of polynomial identities and positive scalar factors;
its correctness is independent of how the chain was found.
-/

public section
noncomputable section
open Polynomial Filter Topology
namespace Sturm

private theorem coprime_step_rev {a b c' : Polynomial ℝ} {c₀ k : ℝ} {Q : Polynomial ℝ}
    (hk : k ≠ 0)
    (hrel : Polynomial.C c₀ * a = Q * b - Polynomial.C k * c')
    (h : IsCoprime b c') : IsCoprime a b := by
  obtain ⟨u, v, huv⟩ := h
  have hCk : Polynomial.C k⁻¹ * Polynomial.C k = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hk, Polynomial.C_1]
  have hc' : c' = Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a) := by
    have hkc' : Polynomial.C k * c' = Q * b - Polynomial.C c₀ * a := by rw [hrel]; ring
    calc c' = Polynomial.C k⁻¹ * (Polynomial.C k * c') := by rw [← mul_assoc, hCk, one_mul]
      _ = Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a) := by rw [hkc']
  refine ⟨-(v * Polynomial.C k⁻¹ * Polynomial.C c₀), u + v * Polynomial.C k⁻¹ * Q, ?_⟩
  calc -(v * Polynomial.C k⁻¹ * Polynomial.C c₀) * a
        + (u + v * Polynomial.C k⁻¹ * Q) * b
      = u * b + v * (Polynomial.C k⁻¹ * (Q * b - Polynomial.C c₀ * a)) := by ring
    _ = u * b + v * c' := by rw [← hc']
    _ = 1 := huv

private theorem eventually_flank_of_deriv_pos {f : Polynomial ℝ} {r : ℝ}
    (h0 : f.eval r = 0) (hd : 0 < f.derivative.eval r) :
    (∀ᶠ x in nhdsWithin r (Set.Iio r), f.eval x < 0) ∧
      (∀ᶠ x in nhdsWithin r (Set.Ioi r), 0 < f.eval x) := by
  have hder : HasDerivAt (fun y => f.eval y) (f.derivative.eval r) r :=
    f.hasDerivAt r
  have hslope : Filter.Tendsto (slope (fun y => f.eval y) r) (nhdsWithin r {r}ᶜ)
      (nhds (f.derivative.eval r)) := hasDerivAt_iff_tendsto_slope.mp hder
  have hpos : ∀ᶠ x in nhdsWithin r {r}ᶜ, slope (fun y => f.eval y) r x ∈ Set.Ioi 0 :=
    hslope (Ioi_mem_nhds hd)
  constructor
  · have hmono : nhdsWithin r (Set.Iio r) ≤ nhdsWithin r {r}ᶜ :=
      nhdsWithin_mono r (fun x hx => ne_of_lt hx)
    filter_upwards [hpos.filter_mono hmono, self_mem_nhdsWithin] with x hx hxr
    have hx' : 0 < (f.eval x - f.eval r) / (x - r) := by
      have := Set.mem_Ioi.mp hx
      rwa [slope_def_field] at this
    rw [h0, sub_zero] at hx'
    have hxr' : x - r < 0 := sub_neg.mpr (Set.mem_Iio.mp hxr)
    have h2 : f.eval x = f.eval x / (x - r) * (x - r) :=
      (div_mul_cancel₀ _ (ne_of_lt hxr')).symm
    rw [h2]
    exact mul_neg_of_pos_of_neg hx' hxr'
  · have hmono : nhdsWithin r (Set.Ioi r) ≤ nhdsWithin r {r}ᶜ :=
      nhdsWithin_mono r (fun x hx => (ne_of_lt (Set.mem_Ioi.mp hx)).symm)
    filter_upwards [hpos.filter_mono hmono, self_mem_nhdsWithin] with x hx hxr
    have hx' : 0 < (f.eval x - f.eval r) / (x - r) := by
      have := Set.mem_Ioi.mp hx
      rwa [slope_def_field] at this
    rw [h0, sub_zero] at hx'
    have hxr' : 0 < x - r := sub_pos.mpr (Set.mem_Ioi.mp hxr)
    have h2 : f.eval x = f.eval x / (x - r) * (x - r) :=
      (div_mul_cancel₀ _ (ne_of_gt hxr')).symm
    rw [h2]
    exact mul_pos hx' hxr'

/-- **The head-pair flank.** If `s₀` vanishes at `r`, `s₁` does not, and
`s₀' = C γ · s₁` with `γ > 0` (the executable seeds: the primitive parts of
`p` and `p'`), then `s₀ · s₁` is negative just left of `r` and positive just
right: its derivative at `r` is `γ · s₁(r)² > 0`. -/
private theorem flank_of_key {s₀ s₁ : Polynomial ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hkey : Polynomial.derivative s₀ = Polynomial.C γ * s₁)
    {r : ℝ} (h0 : s₀.eval r = 0) (h1 : s₁.eval r ≠ 0) :
    (∀ᶠ x in nhdsWithin r (Set.Iio r), (s₀ * s₁).eval x < 0) ∧
      (∀ᶠ x in nhdsWithin r (Set.Ioi r), 0 < (s₀ * s₁).eval x) := by
  apply eventually_flank_of_deriv_pos
  · rw [Polynomial.eval_mul, h0, zero_mul]
  · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, h0, zero_mul, add_zero, hkey, Polynomial.eval_mul,
      Polynomial.eval_C, mul_assoc]
    exact mul_pos hγ (mul_self_pos.mpr h1)

/-! # Assembly: the executable chain is a Sturm chain -/

/-- Coprime polynomials never vanish together. -/
private theorem eval_ne_zero_of_isCoprime {a b : Polynomial ℝ} (h : IsCoprime a b)
    {x : ℝ} (ha : a.eval x = 0) : b.eval x ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h
  intro hb
  have h2 := congrArg (Polynomial.eval x) huv
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, ha, hb,
    mul_zero, mul_zero, add_zero, Polynomial.eval_one] at h2
  exact zero_ne_one h2


/-- The algebraic conditions on a signed remainder chain, before checking its seeds. -/
structure RemainderChain (chain : List ℝ[X]) : Prop where
  nonzero : ∀ p ∈ chain, p ≠ 0
  coprime : ∀ i a b, chain[i]? = some a → chain[i + 1]? = some b → IsCoprime a b
  alternates : ∀ i x a b c, chain[i]? = some a → chain[i + 1]? = some b →
    chain[i + 2]? = some c → b.eval x = 0 →
    a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  last : ∀ p, chain.getLast? = some p → ∀ x, p.eval x ≠ 0

/-- Terminate a certificate at a nonzero constant. -/
theorem RemainderChain.pair {p : ℝ[X]} {c : ℝ} (hp : p ≠ 0) (hc : c ≠ 0) :
    RemainderChain [p, C c] where
  nonzero := by simp_all
  coprime := by
    intro i a b ha hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hb
      subst b
      refine ⟨0, C c⁻¹, ?_⟩
      simp [← C_mul, hc]
    | succ i => cases i <;> simp at hb
  alternates := by
    intro i x a b d ha hb hd
    cases i <;> simp at hd
  last := by simp_all

/-- Prepend a positive multiple of a signed remainder identity. -/
theorem RemainderChain.cons {p q r : ℝ[X]} {tail : List ℝ[X]} {a b : ℝ}
    {d : ℝ[X]} (h : RemainderChain (q :: r :: tail)) (hp : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hid : C a * p = d * q - C b * r) :
    RemainderChain (p :: q :: r :: tail) where
  nonzero := by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hp h.nonzero
  coprime := by
    intro i u v hu hv
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hv
      subst u; subst v
      exact coprime_step_rev (ne_of_gt hb) hid (h.coprime 0 q r rfl rfl)
    | succ i => exact h.coprime i u v hu hv
  alternates := by
    intro i x u v w hu hv hw hv0
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hv hw
      subst u; subst v; subst w
      have hr := eval_ne_zero_of_isCoprime (h.coprime 0 q r rfl rfl) hv0
      have he := congrArg (Polynomial.eval x) hid
      simp only [eval_mul, eval_C, eval_sub, hv0, mul_zero, zero_sub] at he
      have hpr : p.eval x * r.eval x < 0 := by
        have hs : 0 < r.eval x * r.eval x := mul_self_pos.mpr hr
        by_contra hg
        have hh := mul_nonneg ha.le (le_of_not_gt hg)
        nlinarith [congrArg (fun z : ℝ => z * r.eval x) he, mul_pos hb hs]
      exact ⟨fun hz => by simp [hz] at hpr, hr, hpr⟩
    | succ i => exact h.alternates i x u v w hu hv hw hv0
  last := by simpa using h.last

/-- A remainder chain whose second term is a positive multiple of the derivative
satisfies the hypotheses of Sturm's theorem and certifies separability. -/
theorem RemainderChain.sturm {p q : ℝ[X]} {tail : List ℝ[X]} {a : ℝ}
    (h : RemainderChain (p :: q :: tail)) (ha : 0 < a)
    (hd : derivative p = C a * q) : IsSturmChain p (p :: q :: tail) ∧ p.Separable := by
  have hc := h.coprime 0 p q rfl rfl
  refine ⟨⟨by simp, rfl, ?_, h.nonzero, ?_, h.alternates, h.last⟩, ?_⟩
  · intro x hx
    have hq := eval_ne_zero_of_isCoprime hc hx
    exact ⟨q, rfl, hq, flank_of_key ha hd hx hq⟩
  · intro i x u v hu hv hx
    exact eval_ne_zero_of_isCoprime (h.coprime i u v hu hv) hx
  · rw [separable_def, hd]
    exact (isCoprime_mul_unit_left_right
      ((isUnit_C).mpr (isUnit_iff_ne_zero.mpr (ne_of_gt ha))) p q).mpr hc

/-- Convert the variation count of a checked chain to the number of distinct real roots. -/
theorem RemainderChain.card_rootSet {f : ℚ[X]} {p q : ℝ[X]} {tail : List ℝ[X]}
    {a : ℝ} {n : ℕ} (h : RemainderChain (p :: q :: tail)) (ha : 0 < a)
    (hd : derivative p = C a * q) (hf : f.map (algebraMap ℚ ℝ) = p)
    (hn : (sturmVarNegInf (p :: q :: tail) : ℤ) - sturmVarPosInf (p :: q :: tail) = n) :
    Fintype.card (f.rootSet ℝ) = n := by
  classical
  obtain ⟨hs, hsep⟩ := h.sturm ha hd
  have hc := sturm_line (h.nonzero p (by simp)) hsep.squarefree hs
  have he : p.roots.card = n := by omega
  have hh : f.rootSet ℝ = (p.roots.toFinset : Set ℝ) := by
    simp [rootSet_def, aroots_def, hf]
  calc Fintype.card (f.rootSet ℝ) = Fintype.card (p.roots.toFinset : Set ℝ) :=
         Fintype.card_congr (Equiv.cast (congrArg (fun s : Set ℝ => ↥s) hh))
       _ = n := by simpa [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)] using he

end Sturm
