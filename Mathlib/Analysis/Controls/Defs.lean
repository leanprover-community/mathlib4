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
# Control functions

A **control function** (or modulus of continuity) on a partially ordered topological space `α`
is a function `ω : α → α → ℝ≥0` that vanishes on the diagonal and is superadditive:
`ω s u + ω u t ≤ ω s t` for `s ≤ u ≤ t`, with continuity on the upper triangle
`{(s, t) | s ≤ t}`. Control functions arise naturally in the theory of rough paths as a way to
measure the regularity of paths and their iterated integrals.

## Main definitions

- `Control`: the structure bundling a superadditive continuous function vanishing on the diagonal.
- `Control.map_convex_mono`: composing a control with a convex, monotone, continuous function
  preserving zero yields a new control.
- `Control.rpow`: the `θ`-th power of a control is a control for `1 ≤ θ`.
- `Control.mul`: the pointwise product of two controls is a control.
- `Control.mul_rpow`: the Hölder combination `(ω^(p/(p+q)) · ω'^(q/(p+q)))^(p+q)` of two
  controls is a control for `1 ≤ p + q`.
- `Control.sub_of_monotone`: the oscillation `(f t - f s)₊` of a monotone function is a control.

## Main statements

- `Control.monotone_right`, `Control.antitone_left`: monotonicity properties
  (see [friz-victoir2010], Lemma 1.7).
- `Control.exists_middle`: for any interval `[a, c]` there exists a midpoint `b` such that
  `ω a b ⊔ ω b c ≤ ω a c / 2` (intermediate value argument).
- `cex_max`: the pointwise maximum of two controls need not be a control.

## References

* [P. Friz and N. Victoir, *Multidimensional Stochastic Processes as Rough Paths*][friz-victoir2010]
  (Section 1.2)

## Tags

control function, modulus of continuity, rough paths, superadditive
-/

@[expose] public section

open scoped NNReal

structure Control (α) [PartialOrder α] [TopologicalSpace α] where
  /-- The underlying two-variable function. -/
  toFun : α → α → ℝ≥0
  /-- Superadditivity: `ω a b + ω b c ≤ ω a c` for `a ≤ b ≤ c`. -/
  superadd {a b c} : a ≤ b → b ≤ c → toFun a b + toFun b c ≤ toFun a c
  /-- The diagonal vanishes: `ω a a = 0`. -/
  zero_diag {a} : toFun a a = 0
  /-- Continuity of `ω` on the upper triangle `{(s, t) | s ≤ t}`. -/
  continuous : ContinuousOn (fun p : α × α => toFun p.1 p.2) {p | p.1 ≤ p.2}

namespace Control

variable {α} [PartialOrder α] [TopologicalSpace α]

instance instCoeFun : CoeFun (Control α) (fun _ => α → α → ℝ≥0) := ⟨toFun⟩

instance : SMul ℝ≥0 (Control α) where
  smul r ω := by
    refine ⟨fun s t => r * ω s t, ?_, ?_, ?_⟩
    · intro _ _ _ hab hbc
      simpa [← mul_add] using mul_le_mul_of_nonneg_left (ω.superadd hab hbc) (zero_le r)
    · simp [ω.zero_diag]
    · exact ω.continuous.const_mul r

instance : Add (Control α) where
  add ω ω' := by
    refine ⟨fun s t => ω s t + ω' s t, ?_, ?_, ?_⟩
    · intro _ _ _ hab hbc
      simpa [add_comm, ← add_assoc] using
        add_le_add (ω.superadd hab hbc) (ω'.superadd hab hbc)
    · simp [ω.zero_diag, ω'.zero_diag]
    · exact ω.continuous.add ω'.continuous

variable {a b c : α} {ω ω' : Control α}

/-- A control is monotone in the second variable. -/
theorem monotone_right : MonotoneOn (fun x => ω a x) {x | a ≤ x} := by
  intro b hb c hc hbc
  exact (le_add_of_nonneg_right <| zero_le (ω b c)).trans <| ω.superadd hb hbc

/-- Monotonicity in the second variable for explicit inequalities `a ≤ b ≤ c`. -/
lemma mono_right_of_le_le (hab : a ≤ b) (hbc : b ≤ c) : ω a b ≤ ω a c :=
  monotone_right hab (hab.trans hbc) hbc

/-- A control is antitone in the first variable. -/
theorem antitone_left : AntitoneOn (fun x => ω x c) {x | x ≤ c} := by
  intro a ha b hb hab
  exact (le_add_of_nonneg_left (zero_le _)).trans <| ω.superadd hab hb

/-- Antitononicity in the first variable for explicit inequalities `a ≤ b ≤ c`. -/
lemma anti_left_of_le_le (hab : a ≤ b) (hbc : b ≤ c) : ω b c ≤ ω a c :=
  antitone_left (hab.trans hbc) hbc hab

/-- The right-variable function `ω a ·` is continuous on `{x | a ≤ x}`. -/
theorem continuous_right : ContinuousOn (fun x => ω a x) {x | a ≤ x} :=
  ω.continuous.comp (continuousOn_const.prodMk continuousOn_id) fun _ hx => hx

/-- The left-variable function `ω · b` is continuous on `{x | x ≤ b}`. -/
theorem continuous_left : ContinuousOn (fun a => ω a b) {x | x ≤ b} :=
  ω.continuous.comp (continuousOn_id.prodMk continuousOn_const) fun _ hx => hx

/-- Composing a control with a convex, monotone, continuous function that preserves zero yields a
new control. -/
def map_convex_mono {φ : ℝ≥0 → ℝ≥0} (hz : φ 0 = 0) (hφ : ConvexOn ℝ≥0 ⊤ φ)
    (hφ_mono : Monotone φ) (hφ_cont : Continuous φ) : Control α where
  toFun a b := φ (ω a b)
  superadd {a b c} hab hbc := (superadd_of_convexOn_zero (u := ⊤) hz hφ (Set.mem_univ _)
    (Set.mem_univ _) (by positivity) (by positivity)).trans (hφ_mono <| ω.superadd hab hbc)
  zero_diag := by simp [ω.zero_diag, hz]
  continuous := hφ_cont.comp_continuousOn ω.continuous

/-- Transfer `ConvexOn ℝ` on `[0, ∞)` to `ConvexOn ℝ≥0` on `Set.univ` via coercion. -/
theorem nnreal_of_real {f : ℝ≥0 → ℝ≥0}
    (hf : ConvexOn ℝ (Set.Ici 0) fun x : ℝ => (f x.toNNReal : ℝ)) : ConvexOn ℝ≥0 ⊤ f where
  left := convex_univ
  right := by
    intro x hx y hy a b ha hb hab
    simpa [← NNReal.coe_mul, ← NNReal.coe_add] using
      hf.2 x.coe_nonneg y.coe_nonneg a.coe_nonneg b.coe_nonneg (by exact_mod_cast hab)

/-- The `θ`-th power of a control is a control for `1 ≤ θ`. -/
noncomputable def rpow {θ : ℝ} (hθ : 1 ≤ θ) : Control α :=
  map_convex_mono (ω := ω) (φ := (· ^ θ))
    (NNReal.zero_rpow (by positivity))
    (nnreal_of_real <|
      (convexOn_rpow hθ).congr fun x hx => by simp [NNReal.coe_rpow, Real.coe_toNNReal x hx])
    (NNReal.monotone_rpow_of_nonneg (by positivity))
    (NNReal.continuous_rpow_const (by positivity))


/-- The pointwise product of two controls is a control. -/
def mul : Control α where
  toFun a b := ω a b * ω' a b
  superadd hab hbc := by
    suffices ineq : ∀ a₁ a₂ b₁ b₂ : ℝ≥0, a₁ * a₂ + b₁ * b₂ ≤ (a₁ + b₁) * (a₂ + b₂) by
      exact (ineq (ω _ _) (ω' _ _) (ω _ _) (ω' _ _)).trans <|
        mul_le_mul (ω.superadd hab hbc) (ω'.superadd hab hbc) (by positivity)
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

/-- The Hölder combination `ω^p · ω'^q` (with `p + q = 1`) of two controls is a control.
The superadditivity follows from the two-term Hölder inequality. -/
noncomputable def mul_rpow_base {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    Control α where
  toFun a b := (ω a b) ^ p * (ω' a b) ^ q
  superadd {a b c} hab hbc := by
    rcases eq_or_lt_of_le hp, eq_or_lt_of_le hq with ⟨rfl | hp, rfl | hq⟩
    · simp_all
    · simp_all only [NNReal.rpow_zero, one_mul, NNReal.rpow_one, zero_add]
      exact ω'.superadd hab hbc
    · simp_all only [NNReal.rpow_zero, mul_one, NNReal.rpow_one, add_zero]
      exact ω.superadd hab hbc
    · suffices h2 : ∀ a b c d : ℝ≥0, ∀ ⦃u : ℝ⦄, 0 < u → ∀ ⦃v : ℝ⦄, 0 < v → u + v = 1 →
          a ^ u * b ^ v + c ^ u * d ^ v ≤ (a + c) ^ u * (b + d) ^ v by
        exact (h2 (ω a b) (ω' a b) (ω b c) (ω' b c) hp hq hpq).trans <| mul_le_mul
          (NNReal.monotone_rpow_of_nonneg hp.le <| ω.superadd hab hbc)
          (NNReal.monotone_rpow_of_nonneg hq.le <| ω'.superadd hab hbc)
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

/-- The Hölder combination `(ω^(p/(p+q)) · ω'^(q/(p+q)))^(p+q)` of two controls is a control
for `1 ≤ p + q`. -/
noncomputable def mul_rpow {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 1 ≤ p + q) : Control α :=
  (mul_rpow_base (ω := ω) (ω' := ω') (p := p / (p + q)) (q := q / (p + q))
    (by positivity) (by positivity) (by field_simp)).rpow (θ := p + q) hpq

/-- For a monotone continuous function `f : α → ℝ`, the oscillation `(f t - f s)₊` is a
control. -/
def sub_of_monotone {f : α → ℝ} (hf : Monotone f) (hc : Continuous f) : Control α where
  toFun a b := (f b - f a).toNNReal
  superadd hab hbc := by
    rw [← Real.toNNReal_add (sub_nonneg.mpr (hf hab)) (sub_nonneg.mpr (hf hbc))]
    · simp
  zero_diag := by simp
  continuous := (continuous_real_toNNReal.comp <|
    .sub (hc.comp continuous_snd) (hc.comp continuous_fst)).continuousOn

end Control

/-- The identity control on `ℝ≥0`: `sub_id s t = t - s`. -/
def sub_id : Control ℝ≥0 := Control.sub_of_monotone monotone_id NNReal.continuous_coe

/-- The pointwise maximum of two controls need not be a control: the sup of `t - s` and
`(t² - s²)₊` on `[0, 1]` is a counterexample. -/
theorem cex_max : ∃ ω ω' : Control ℝ≥0, ¬ ∃ ω₀ : Control ℝ≥0,
    ω₀.toFun = fun a b => (ω a b) ⊔ (ω' a b) := by
  refine ⟨sub_id, Control.sub_of_monotone (NNReal.monotone_rpow_of_nonneg (z := 2) (by positivity))
    (NNReal.continuous_coe.comp (NNReal.continuous_rpow_const (by positivity))), ?_⟩
  intro ⟨ω₀, hω₀⟩
  have h := ω₀.superadd (a := 0) (b := 1/2) (c := 1) (by positivity) (by simp)
  simp only [hω₀, sub_id, Control.sub_of_monotone] at h
  exact absurd (NNReal.coe_le_coe.mpr h)
    (by push_cast [NNReal.coe_max, Real.coe_toNNReal]; norm_num)

theorem Control.exists_middle {α} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {a c : α} (hac : a < c) {ω : Control α} :
    ∃ b ∈ Set.Icc a c, ω a b ⊔ ω b c ≤ ω a c / 2 := by
  suffices h : ∃ b ∈ Set.Icc a c, ω a b = ω b c by
    obtain ⟨b, h_mem, hω⟩ := h
    exists b
    simp only [sup_le_iff, h_mem, hω, true_and, and_self]
    apply (le_div_iff₀ (c := (2 : ℝ≥0)) (by positivity)).mpr
    simpa [mul_two] using hω ▸ ω.superadd h_mem.left h_mem.right
  exact IsPreconnected.intermediate_value₂ isPreconnected_Icc
    (Set.left_mem_Icc.mpr <| hac.le)
    (Set.right_mem_Icc.mpr <| hac.le)
    (ω.continuous_right.mono Set.Icc_subset_Ici_self)
    (ω.continuous_left.mono Set.Icc_subset_Iic_self)
    (by simp [ω.zero_diag])
    (by simp [ω.zero_diag])
