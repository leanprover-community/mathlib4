/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Polynomial.Sturm.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Tactic.Ring

/-!
# Algebraic certificates for Sturm chains

A signed remainder chain ending in a nonzero constant certifies a real root count.
The certificate consists of polynomial identities and positive scalar factors;
its correctness is independent of how the chain was found.

## Main results

* `Sturm.RemainderChain.pair` and `Sturm.RemainderChain.cons` build certificates.
* `Sturm.RemainderChain.isSturmChain` verifies the derivative relation.
* `Sturm.RemainderChain.separable` proves that the first entry is separable.
* `Sturm.RemainderChain.card_rootSet` counts the distinct real roots.
-/

public section

noncomputable section

open Polynomial Filter Topology

namespace Sturm

private theorem coprime_of_remainder {p q r : ℝ[X]} {a b : ℝ} {d : ℝ[X]}
    (hb : b ≠ 0) (hid : C a * p = d * q - C b * r) (h : IsCoprime q r) :
    IsCoprime p q := by
  apply IsCoprime.of_mul_left_right (x := C a)
  rw [hid, IsCoprime.mul_sub_right_left_iff,
    isCoprime_mul_unit_left_left (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hb))]
  exact h.symm

private theorem sign_near_root {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r = 0) (hd : 0 < p.derivative.eval r) :
    (∀ᶠ x in 𝓝[<] r, p.eval x < 0) ∧ (∀ᶠ x in 𝓝[>] r, 0 < p.eval x) := by
  obtain ⟨hl, hu⟩ := hasDerivAt_iff_tendsto_slope_left_right.mp (p.hasDerivAt r)
  constructor
  · filter_upwards [hl.eventually_const_lt hd, self_mem_nhdsWithin] with x hx hxr
    simp only [slope_def_field, hr, sub_zero] at hx
    rcases div_pos_iff.mp hx with ⟨_, h⟩ | ⟨h, _⟩
    · exact False.elim ((sub_neg.mpr hxr).not_gt h)
    · exact h
  · filter_upwards [hu.eventually_const_lt hd, self_mem_nhdsWithin] with x hx hxr
    simp only [slope_def_field, hr, sub_zero] at hx
    rcases div_pos_iff.mp hx with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · exact False.elim ((sub_pos.mpr hxr).not_gt h)

/-- The product of the first two entries changes from negative to positive
at a root of the first entry. -/
private theorem mul_sign_near_root {s₀ s₁ : Polynomial ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hkey : Polynomial.derivative s₀ = Polynomial.C γ * s₁)
    {r : ℝ} (h0 : s₀.eval r = 0) (h1 : s₁.eval r ≠ 0) :
    (∀ᶠ x in nhdsWithin r (Set.Iio r), (s₀ * s₁).eval x < 0) ∧
      (∀ᶠ x in nhdsWithin r (Set.Ioi r), 0 < (s₀ * s₁).eval x) := by
  apply sign_near_root
  · rw [Polynomial.eval_mul, h0, zero_mul]
  · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, h0, zero_mul, add_zero, hkey, Polynomial.eval_mul,
      Polynomial.eval_C, mul_assoc]
    exact mul_pos hγ (mul_self_pos.mpr h1)

/-- Coprime polynomials never vanish together. -/
private theorem eval_ne_zero_of_isCoprime {a b : Polynomial ℝ} (h : IsCoprime a b)
    {x : ℝ} (ha : a.eval x = 0) : b.eval x ≠ 0 := by
  have hc := h.map (evalRingHom x)
  simpa [ha, isCoprime_zero_left, isUnit_iff_ne_zero] using hc

/-- The algebraic conditions on a signed remainder chain, before checking its seeds. -/
structure RemainderChain (chain : List ℝ[X]) : Prop where
  /-- Every entry is a nonzero polynomial. -/
  nonzero_mem : ∀ p ∈ chain, p ≠ 0
  /-- Consecutive entries are coprime. -/
  coprime : ∀ i a b, chain[i]? = some a → chain[i + 1]? = some b → IsCoprime a b
  /-- Neighbors of a vanishing interior entry have opposite signs. -/
  interior_alternates : ∀ i x a b c, chain[i]? = some a → chain[i + 1]? = some b →
    chain[i + 2]? = some c → b.eval x = 0 →
    a.eval x ≠ 0 ∧ c.eval x ≠ 0 ∧ a.eval x * c.eval x < 0
  /-- The last entry has no real roots. -/
  last_no_root : ∀ p, chain.getLast? = some p → ∀ x, p.eval x ≠ 0

/-- Terminate a certificate at a nonzero constant. -/
theorem RemainderChain.pair {p : ℝ[X]} {c : ℝ} (hp : p ≠ 0) (hc : c ≠ 0) :
    RemainderChain [p, C c] where
  nonzero_mem := by simp_all
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
  interior_alternates := by
    intro i x a b d ha hb hd
    cases i <;> simp at hd
  last_no_root := by simp_all

/-- Prepend a positive multiple of a signed remainder identity. -/
theorem RemainderChain.cons {p q r : ℝ[X]} {tail : List ℝ[X]} {a b : ℝ}
    {d : ℝ[X]} (h : RemainderChain (q :: r :: tail)) (hp : p ≠ 0)
    (ha : 0 < a) (hb : 0 < b) (hid : C a * p = d * q - C b * r) :
    RemainderChain (p :: q :: r :: tail) where
  nonzero_mem := by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hp h.nonzero_mem
  coprime := by
    intro i u v hu hv
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hu
      simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hv
      subst u; subst v
      exact coprime_of_remainder (ne_of_gt hb) hid (h.coprime 0 q r rfl rfl)
    | succ i => exact h.coprime i u v hu hv
  interior_alternates := by
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
        apply (mul_lt_mul_iff_right₀ ha).mp
        calc a * (p.eval x * r.eval x) = -(b * (r.eval x * r.eval x)) := by
               rw [← mul_assoc, he]
               ring
             _ < a * 0 := by simpa using neg_neg_of_pos (mul_pos hb hs)
      exact ⟨fun hz => by simp [hz] at hpr, hr, hpr⟩
    | succ i => exact h.interior_alternates i x u v w hu hv hw hv0
  last_no_root := by simpa using h.last_no_root

/-- A remainder chain starting with a positive multiple of the derivative is a Sturm chain. -/
theorem RemainderChain.isSturmChain {p q : ℝ[X]} {tail : List ℝ[X]} {a : ℝ}
    (h : RemainderChain (p :: q :: tail)) (ha : 0 < a)
    (hd : derivative p = C a * q) : IsSturmChain p (p :: q :: tail) where
  head := rfl
  root_flank := by
    intro x hx
    have hq := eval_ne_zero_of_isCoprime (h.coprime 0 p q rfl rfl) hx
    exact ⟨q, rfl, hq, mul_sign_near_root ha hd hx hq⟩
  nonzero_mem := h.nonzero_mem
  interior_alternates := h.interior_alternates
  last_no_root := h.last_no_root

/-- A remainder chain whose second entry is a nonzero multiple of the derivative
certifies separability. -/
theorem RemainderChain.separable {p q : ℝ[X]} {tail : List ℝ[X]} {a : ℝ}
    (h : RemainderChain (p :: q :: tail)) (ha : a ≠ 0)
    (hd : derivative p = C a * q) : p.Separable := by
  rw [separable_def, hd, isCoprime_mul_unit_left_right
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha))]
  exact h.coprime 0 p q rfl rfl

/-- Convert the variation count of a checked chain to the number of distinct real roots. -/
theorem RemainderChain.card_rootSet {R : Type*} [CommRing R] [Algebra R ℝ]
    {f : R[X]} {p q : ℝ[X]} {tail : List ℝ[X]}
    {a : ℝ} {n : ℕ} (h : RemainderChain (p :: q :: tail)) (ha : 0 < a)
    (hd : derivative p = C a * q) (hf : f.map (algebraMap R ℝ) = p)
    (hn : sturmVarPosInf (p :: q :: tail) + n = sturmVarNegInf (p :: q :: tail)) :
    Fintype.card (f.rootSet ℝ) = n := by
  classical
  have hs := h.separable (ne_of_gt ha) hd
  have hc := (h.isSturmChain ha hd).sturm (Polynomial.nodup_roots hs)
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, aroots_def, hf]
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs)]
  omega

end Sturm
