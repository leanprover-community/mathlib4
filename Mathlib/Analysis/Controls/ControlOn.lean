/-
Copyright (c) 2026 Nikolas Tapia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolas Tapia
-/
module
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Control functions on a set

This file defines `ControlOn α s`, a variant of `Control` (see `Roughlib.Analysis.Control`) where
superadditivity and continuity are only required on a subset `s : Set α`. This is useful when
working with intervals or other restricted domains.

## Main definitions

- `ControlOn`: the structure bundling a superadditive continuous function vanishing on the diagonal,
  restricted to a set `s`.
- `ControlOn.map_convex_mono`: composing a `ControlOn` with a convex, monotone, continuous
  function preserving zero yields a new `ControlOn`.
- `ControlOn.rpow`: the `θ`-th power of a `ControlOn` is a `ControlOn` for `1 ≤ θ`.
- `ControlOn.mul`: the pointwise product of two `ControlOn`s is a `ControlOn`.
- `ControlOn.mul_rpow`: the Hölder combination `(ω^(p/(p+q)) · ω'^(q/(p+q)))^(p+q)` of two
  `ControlOn`s is a `ControlOn` for `1 ≤ p + q`.
- `ControlOn.sub_of_monotone`: the oscillation `(f t - f s)₊` of a monotone function on `s`
  is a `ControlOn`.

## Main statements

- `ControlOn.monotone_right`, `ControlOn.antitone_left`: monotonicity properties
  (see [friz-victoir2010], Lemma 1.7).

## References

* [P. Friz and N. Victoir, *Multidimensional Stochastic Processes as Rough Paths*][friz-victoir2010]
  (Section 1.2)

## Tags

control function, modulus of continuity, rough paths, superadditive, restricted domain
-/

@[expose] public section

open scoped NNReal

structure ControlOn (α) [PartialOrder α] [TopologicalSpace α] (s : Set α) where
  /-- The underlying two-variable function. -/
  toFun : α → α → ℝ≥0
  /-- Superadditivity on `s`: `ω a b + ω b c ≤ ω a c` for `a, b, c ∈ s` with `a ≤ b ≤ c`. -/
  superadd ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s) ⦃c⦄ (_ : c ∈ s) :
    a ≤ b → b ≤ c → toFun a b + toFun b c ≤ toFun a c
  /-- The diagonal vanishes: `ω a a = 0`. -/
  zero_diag ⦃a⦄ : toFun a a = 0
  /-- Continuity of `ω` on `{(s, t) ∈ s × s | s ≤ t}`. -/
  continuous : ContinuousOn (fun p : α × α => toFun p.1 p.2) {p ∈ s ×ˢ s | p.1 ≤ p.2}

namespace ControlOn

variable {α} [PartialOrder α] [TopologicalSpace α] {a b c : α} {s : Set α}

instance instCoeFun : CoeFun (ControlOn α s) (fun _ => α → α → ℝ≥0) := ⟨toFun⟩

instance : SMul ℝ≥0 (ControlOn α s) where
  smul r ω := by
    refine ⟨fun s t => r * ω s t, ?_, ?_, ?_⟩
    · intro _ ha _ hb _ hc hsu hut
      simpa [← mul_add] using mul_le_mul_of_nonneg_left (ω.superadd ha hb hc hsu hut) (zero_le r)
    · simp [ω.zero_diag]
    · exact ω.continuous.const_mul r

instance : Add (ControlOn α s) where
  add ω ω' := by
    refine ⟨fun s t => ω s t + ω' s t, ?_, ?_, ?_⟩
    · intro _ ha _ hb _ hc hsu hut
      simpa [add_comm, ← add_assoc] using
        add_le_add (ω.superadd ha hb hc hsu hut) (ω'.superadd ha hb hc hsu hut)
    · simp [ω.zero_diag, ω'.zero_diag]
    · exact ω.continuous.add ω'.continuous

variable {ω ω' : ControlOn α s}

/-- A control is monotone in the right variable. See [friz-victoir2010], Lemma 1.7. -/
theorem monotone_right (ha : a ∈ s) : MonotoneOn (fun x => ω a x) {x ∈ s | a ≤ x} := by
  intro b ⟨hb, hbl⟩ c ⟨hc, hcl⟩ hbc
  exact (le_add_of_nonneg_right (zero_le (ω b c))).trans <|
    ω.superadd ha hb hc hbl hbc

/-- Monotonicity in the right variable for explicit membership and inequalities `a ≤ b ≤ c`. -/
lemma mono_right_of_le_le (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≤ b) (hbc : b ≤ c) : ω a b ≤ ω a c :=
  monotone_right ha (Set.mem_setOf.mpr ⟨hb, hab⟩) (Set.mem_setOf.mpr ⟨hc, hab.trans hbc⟩) hbc

/-- A control is antitone in the left variable. See [friz-victoir2010], Lemma 1.7. -/
theorem antitone_left (hc : c ∈ s) : AntitoneOn (fun x => ω x c) {x ∈ s | x ≤ c} := by
  intro a ⟨ha, hal⟩ b ⟨hb, hbl⟩ hab
  exact (le_add_of_nonneg_left (zero_le _)).trans <|
    ω.superadd ha hb hc hab hbl

/-- Antitononicity in the left variable for explicit membership and inequalities `a ≤ b ≤ c`. -/
lemma anti_left_of_le_le (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≤ b) (hbc : b ≤ c) : ω b c ≤ ω a c :=
  antitone_left hc (Set.mem_setOf.mpr ⟨ha, hab.trans hbc⟩) (Set.mem_setOf.mpr ⟨hb, hbc⟩) hab

/-- The right-variable function `ω a ·` is continuous on `{x ∈ s | a ≤ x}`. -/
theorem continuous_right (ha : a ∈ s) : ContinuousOn (fun x => ω a x) {x ∈ s | a ≤ x} :=
  ω.continuous.comp (continuousOn_const.prodMk continuousOn_id)
    fun _ ⟨hx, hax⟩ => ⟨Set.mk_mem_prod ha hx, hax⟩

/-- The left-variable function `ω · b` is continuous on `{x ∈ s | x ≤ b}`. -/
theorem continuous_left (hb : b ∈ s) : ContinuousOn (fun a => ω a b) {x ∈ s | x ≤ b} :=
  ω.continuous.comp (continuousOn_id.prodMk continuousOn_const)
    fun _ ⟨hx, hxb⟩ => ⟨Set.mk_mem_prod hx hb, hxb⟩

/-- Composing a control with a convex, monotone, continuous function that preserves zero yields a
new control. See [friz-victoir2010], Exercise 1.9. -/
def map_convex_mono {φ : ℝ≥0 → ℝ≥0} (hz : φ 0 = 0) (hφ : ConvexOn ℝ≥0 Set.univ φ)
    (hφ_mono : Monotone φ) (hφ_cont : Continuous φ) : ControlOn α s where
  toFun a b := φ (ω a b)
  superadd _ ha _ hb _ hc hab hbc :=(superadd_of_convexOn_zero (u := ⊤) hz hφ (Set.mem_univ _)
    (Set.mem_univ _) (by positivity) (by positivity)).trans
      (hφ_mono <| ω.superadd ha hb hc hab hbc)
  zero_diag := by simp [ω.zero_diag, hz]
  continuous := hφ_cont.comp_continuousOn ω.continuous

theorem nnreal_of_real {f : ℝ≥0 → ℝ≥0}
    (hf : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => (f x.toNNReal : ℝ)) : ConvexOn ℝ≥0 ⊤ f where
  left := convex_univ
  right := by
    intro x hx y hy a b ha hb hab
    simpa [← NNReal.coe_mul, ← NNReal.coe_add] using
      hf.2 x.coe_nonneg y.coe_nonneg a.coe_nonneg b.coe_nonneg (by exact_mod_cast hab)

/-- The `θ`-th power of a control is a control for `1 ≤ θ`.
See [friz-victoir2010], Exercise 1.9. -/
noncomputable def rpow {θ : ℝ} (hθ : 1 ≤ θ) : ControlOn α s :=
  map_convex_mono (ω := ω) (φ := (· ^ θ))
    (NNReal.zero_rpow (by positivity))
    (nnreal_of_real <|
      (convexOn_rpow hθ).congr fun x hx => by simp [NNReal.coe_rpow, Real.coe_toNNReal x hx])
    (NNReal.monotone_rpow_of_nonneg (by positivity))
    (NNReal.continuous_rpow_const (by positivity))

/-- The pointwise product of two `ControlOn`s is a `ControlOn`. -/
def mul : ControlOn α s where
  toFun a b := ω a b * ω' a b
  superadd _ ha _ hb _ hc hab hbc := by
    suffices ineq : ∀ a₁ a₂ b₁ b₂ : ℝ≥0, a₁ * a₂ + b₁ * b₂ ≤ (a₁ + b₁) * (a₂ + b₂) by
      exact (ineq (ω _ _) (ω' _ _) (ω _ _) (ω' _ _)).trans <|
        mul_le_mul (ω.superadd ha hb hc hab hbc) (ω'.superadd ha hb hc hab hbc) (by positivity)
        (by positivity)
    intro a₁ a₂ b₁ b₂
    ring_nf
    simpa [← add_assoc] using
      le_add_of_nonneg_right (add_nonneg
        (mul_nonneg (zero_le a₁) (zero_le b₂))
        (mul_nonneg (zero_le a₂) (zero_le b₁))
      )
  zero_diag := by simp [mul_eq_zero_of_left, ω.zero_diag]
  continuous := ContinuousOn.mul ω.continuous ω'.continuous

/-- The Hölder combination `ω^p · ω'^q` (with `p + q = 1`) of two `ControlOn`s is a `ControlOn`.
The superadditivity follows from the two-term Hölder inequality. -/
noncomputable def mul_rpow_base {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ControlOn α s where
  toFun a b := (ω a b) ^ p * (ω' a b) ^ q
  superadd a ha b hb c hc hab hbc := by
    rcases eq_or_lt_of_le hp, eq_or_lt_of_le hq with ⟨rfl | hp, rfl | hq⟩
    · simp_all
    · simp_all only [NNReal.rpow_zero, one_mul, NNReal.rpow_one, zero_add]
      exact ω'.superadd ha hb hc hab hbc
    · simp_all only [NNReal.rpow_zero, mul_one, NNReal.rpow_one, add_zero]
      exact ω.superadd ha hb hc hab hbc
    · suffices h2 : ∀ a b c d : ℝ≥0, ∀ ⦃u : ℝ⦄, 0 < u → ∀ ⦃v : ℝ⦄, 0 < v → u + v = 1 →
          a ^ u * b ^ v + c ^ u * d ^ v ≤ (a + c) ^ u * (b + d) ^ v by
        exact (h2 (ω a b) (ω' a b) (ω b c) (ω' b c) hp hq hpq).trans <| mul_le_mul
          (NNReal.monotone_rpow_of_nonneg hp.le <| ω.superadd ha hb hc hab hbc)
          (NNReal.monotone_rpow_of_nonneg hq.le <| ω'.superadd ha hb hc hab hbc)
          (by positivity) (by positivity)
      intro a b c d u hu v hv huv
      simpa [Fin.sum_succ, ← NNReal.rpow_mul, mul_inv_cancel₀ hu.ne', mul_inv_cancel₀ hv.ne']
        using NNReal.inner_le_Lp_mul_Lq ⊤ ![a ^ u, c ^ u] ![b ^ v, d ^ v]
          (Real.HolderConjugate.inv_inv hu hv huv)
  zero_diag := by
    rcases eq_or_lt_of_le hp, eq_or_lt_of_le hq with ⟨rfl | hp, rfl | hq⟩
      <;> try { simp [ω.zero_diag, ω'.zero_diag]; simp_all}
    simp [hp.ne.symm, ω.zero_diag]
  continuous := ContinuousOn.mul
    (Continuous.comp_continuousOn (NNReal.continuous_rpow_const hp) ω.continuous)
    (Continuous.comp_continuousOn (NNReal.continuous_rpow_const hq) ω'.continuous)

/-- The Hölder combination `(ω^(p/(p+q)) · ω'^(q/(p+q)))^(p+q)` of two `ControlOn`s is a
`ControlOn` for `1 ≤ p + q`. -/
noncomputable def mul_rpow {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 1 ≤ p + q) : ControlOn α s :=
  (mul_rpow_base (ω := ω) (ω' := ω') (p := p / (p + q)) (q := q / (p + q))
    (by positivity) (by positivity) (by field_simp)).rpow (θ := p + q) hpq

/-- For a function `f : α → ℝ` that is monotone and continuous on `s`, the oscillation
`(f t - f s)₊` is a `ControlOn`. -/
def sub_of_monotone {f : α → ℝ} (hf : MonotoneOn f s) (hc : ContinuousOn f s) : ControlOn α s where
  toFun a b := (f b - f a).toNNReal
  superadd _ ha _ hb _ hc hab hbc := by
    rw [← Real.toNNReal_add (sub_nonneg.mpr (hf _ _ hab)) (sub_nonneg.mpr (hf _ _ hbc))]
    · simp
    all_goals simp [ha, hb, hc]
  zero_diag := by simp
  continuous := by
    refine continuous_real_toNNReal.comp_continuousOn (.sub ?_ ?_)
    · exact hc.comp (by fun_prop) fun x ⟨hx, _⟩ => (Set.mem_prod.mp hx).2
    · exact hc.comp (by fun_prop) fun x ⟨hx, _⟩ => (Set.mem_prod.mp hx).1

end ControlOn
