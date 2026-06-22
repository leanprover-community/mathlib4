/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Tactic.Ring

/-!
# Euler continued fraction

This file formalizes a transformation on generalized continued fractions over a field `K`.
It defines a map sending a generalized continued fraction to an equivalent Euler continued
fraction obtained by an explicit transformation of its coefficient stream.

## Main definitions

* `GenContFract.euler` : constructs a generalized continued fraction from a head term `h`
  and a coefficient stream `ρ`.
* `GenContFract.toEuler` : transforms a generalized continued fraction to a Euler continued
  fraction.

## Main results

* `euler_convs` : explicit formula for convergents of an Euler-transformed continued fraction.
* `convs_toEuler_eq_convs` : equivalence of convergents between a generalized continued fraction
  and its corresponding Euler continued fraction.

## References

* https://en.wikipedia.org/wiki/Euler%27s_continued_fraction_formula
* [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

-/

public section

namespace GenContFract

variable {K : Type*} [Field K]

variable {n : ℕ} {h : K} {ρ : Stream'.Seq K} {g : GenContFract K}

/-- An *Euler continued fraction* is a generalized continued fraction of the form
$$
  h + \cfrac{\rho_0}
            {1 - \cfrac{\rho_1}
                       {1 + \rho_1 - \cfrac{\rho_2}
                                           {1 + \rho_2 - \cfrac{\rho_3}
                                                               {1 + \rho_3 - \dots}}}}
$$
`euler h ρ` constructs an Euler continued fraction whose coefficients are obtained
from the stream `ρ` with head term `h`.
-/
def euler (h : K) (ρ : Stream'.Seq K) : GenContFract K :=
  ⟨h, ρ.enum.map fun (n, ρ) => n.casesOn ⟨ρ, 1⟩ fun _ => ⟨-ρ, 1 + ρ⟩⟩

/-- `toEuler g` is the Euler continued fraction equivalent to `g`, where `ρ₀` = `a₀ / b₀` and
`ρₙ` = `- aₙ * Bₙ₋₁ / Bₙ₊₁` for `n > 0`.
-/
def toEuler (g : GenContFract K) : GenContFract K :=
  euler g.h <| g.s.enum.map fun (n, ⟨a, b⟩) =>
    n.casesOn (a / b) fun n' => - a * g.dens n' / g.dens (n' + 2)

section Translation

open Stream'.Seq

theorem exists_toEuler : ∃ ρ, g.toEuler = euler g.h ρ := ⟨_, rfl⟩

theorem terminatedAt_euler_iff_terminatedAt : (euler h ρ).TerminatedAt n ↔ ρ.TerminatedAt n := by
  simp [euler, TerminatedAt, Stream'.Seq.TerminatedAt]

theorem exists_euler_s_of_not_terminatedAt_zero
    (not_terminatedAt_zero : ¬ρ.TerminatedAt 0) :
    ∃ a, (euler h ρ).s.get? 0 = some ⟨a, 1⟩ := by
  simpa [euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_zero

theorem exists_euler_s_of_not_terminatedAt_succ
    (not_terminatedAt_n_succ : ¬ρ.TerminatedAt (n + 1)) :
    ∃ a, (euler h ρ).s.get? (n + 1) = some ⟨-a, 1 + a⟩ := by
  simpa [euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_n_succ

theorem terminatedAt_toEuler_iff_terminatedAt : g.toEuler.TerminatedAt n ↔ g.TerminatedAt n := by
  rw [toEuler, terminatedAt_euler_iff_terminatedAt, TerminatedAt]
  simp [Stream'.Seq.TerminatedAt]

theorem toEuler_s_zero : (toEuler g).s.get? 0 = (g.s.get? 0).map fun ⟨a, b⟩ => ⟨a / b, 1⟩ := by
  simp only [toEuler, euler, map_get?, get?_enum]
  rcases g.s.get? 0 with _ | ⟨a, b⟩ <;> simp

theorem toEuler_s_succ :
    (toEuler g).s.get? (n + 1) =
      (g.s.get? (n + 1)).map
        fun ⟨a, _⟩ => ⟨a * g.dens n / g.dens (n + 2), 1 - a * g.dens n / g.dens (n + 2)⟩ := by
  simp only [toEuler, euler, map_get?, get?_enum]
  rcases g.s.get? (n + 1) with _ | a
  · simp
  · simpa [neg_div] using SubNegMonoid.sub_eq_add_neg .. |>.symm

end Translation

theorem euler_h : (euler h ρ).h = h := by rfl

private theorem dens_euler_one : (euler h ρ).dens 1 = 1 :=
  Decidable.em ((euler h ρ).TerminatedAt 0) |>.elim
    (fun terminatedAt_zero =>
      (dens_stable_of_terminated (Nat.zero_le 1) <| terminatedAt_zero) ▸ zeroth_den_eq_one)
    (fun not_terminatedAt_zero =>
      first_den_eq <| exists_euler_s_of_not_terminatedAt_zero
        (terminatedAt_euler_iff_terminatedAt (K := K) |>.eq ▸ not_terminatedAt_zero) |>.choose_spec)

/-- The denominators of an Euler continued fraction are all 1. -/
theorem dens_euler : (euler h ρ).dens n = 1 := by
  set g := euler h ρ
  induction n using Nat.strong_induction_on with | h n ih =>
  match n with
  | 0 => exact zeroth_den_eq_one
  | n + 1 =>
    rcases Decidable.em <| g.TerminatedAt n with terminatedAt_n | not_terminatedAt_n
    · specialize ih n n.lt_add_one
      rwa [dens_stable_of_terminated n.le_succ terminatedAt_n]
    · rw [terminatedAt_euler_iff_terminatedAt] at not_terminatedAt_n
      match n with
      | 0 => exact dens_euler_one
      | n + 1 =>
        obtain ⟨a, s_n_succ_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
          exists_euler_s_of_not_terminatedAt_succ not_terminatedAt_n
        simp [dens_recurrence s_n_succ_eq, ih]

private theorem nums_euler_one : (euler h ρ).nums 1 = h + (ρ.get? 0).getD 0 := by
  set g := euler h ρ
  rcases Decidable.em <| ρ.TerminatedAt 0 with terminatedAt_zero | not_terminatedAt_zero
  · rw [g.nums_stable_of_terminated zero_le_one <|
      terminatedAt_euler_iff_terminatedAt.mpr terminatedAt_zero]
    simp [show ρ.get? 0 = none from terminatedAt_zero, g, euler_h]
  · obtain ⟨a, g_zeroth_eq⟩ : ∃ a, (euler h ρ).s.get? 0 = some ⟨a, 1⟩ :=
      exists_euler_s_of_not_terminatedAt_zero not_terminatedAt_zero
    rw [first_num_eq g_zeroth_eq]
    simp [euler] at g_zeroth_eq
    grind [euler_h]

private theorem nums_euler_aux : (euler h ρ).nums (n + 1) - (euler h ρ).nums n =
    ∏ j ∈ Finset.range (n + 1), (ρ.get? j).getD 0 := by
  set g := euler h ρ
  induction n with
  | zero => simp [g, nums_euler_one, euler_h]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    rcases Decidable.em <| ρ.TerminatedAt n.succ with terminatedAt_n_succ | not_terminatedAt_n_succ
    · rw [nums_stable_of_terminated n.succ.le_succ <| terminatedAt_euler_iff_terminatedAt.mpr
        terminatedAt_n_succ, terminatedAt_n_succ]
      grind
    · obtain ⟨a, g_n_succ_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
        exists_euler_s_of_not_terminatedAt_succ not_terminatedAt_n_succ
      rw [nums_recurrence g_n_succ_eq rfl rfl]
      simp [g, euler] at g_n_succ_eq
      grind

/-- The numerators of an Euler continued fraction are given by the formula
$$
  A_n = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$
-/
theorem nums_euler :
    (euler h ρ).nums n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  simp only [← nums_euler_aux (h := h)]
  rw [Finset.sum_range_sub, zeroth_num_eq_h, euler_h, add_sub_cancel]

/-- **Euler's continued fraction formula**: the convergents of an Euler continued fraction
are given by the formula
$$
  \dfrac{A_n}{B_n} = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$
for example:
- `A₀ / B₀ = h`
- `A₁ / B₁ = h + ρ₀`
- `A₂ / B₂ = h + ρ₀ + ρ₀ * ρ₁`
- `Aₙ / Bₙ = h + ρ₀ + ρ₀ * ρ₁ + ρ₀ * ρ₁ * ρ₂ + ... + ρ₀ * ρ₁ * ρ₂ * ... * ρₙ₋₁`
-/
theorem convs_euler :
    (euler h ρ).convs n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  rw [convs, dens_euler, nums_euler, div_one]

/-- The transformation `toEuler` is idempotent. -/
theorem toEuler_toEuler :
  g.toEuler.toEuler = g.toEuler := by
  set h : K := g.h
  set ρ : Stream'.Seq K := g.s.enum.map fun (n, ⟨a, b⟩) =>
    n.casesOn (a / b) fun n' => - a * g.dens n' / g.dens (n' + 2)
  change (euler h ρ).toEuler = euler h ρ
  ext n : 2
  · rfl
  · match n with
    | 0 =>
      rw [toEuler_s_zero, euler]
      rcases hρ₀ : ρ.get? 0 with _ | a <;> simp [hρ₀]
    | n' + 1 =>
      rcases Decidable.em <| ρ.TerminatedAt (n' + 1) with hρₙ | hρₙ
      · rw [← terminatedAt_euler_iff_terminatedAt (h := h)] at hρₙ
        rw [hρₙ]
        rw [← terminatedAt_toEuler_iff_terminatedAt] at hρₙ
        rw [hρₙ]
      · rw [toEuler_s_succ]
        obtain ⟨a, g_n_succ_eq⟩ : ∃ a, (euler h ρ).s.get? (n' + 1) = some ⟨-a, 1 + a⟩ :=
          exists_euler_s_of_not_terminatedAt_succ hρₙ
        grind [dens_euler]

theorem convs_toEuler_eq_convs_of_forall_le_dens_ne_zero (hB : ∀ m ≤ n, g.dens m ≠ 0) :
    ∀ m ≤ n, g.toEuler.convs m = g.convs m := by
  intro m hm
  conv_lhs =>
    rw [convs]
    conv => rhs; rw [toEuler, dens_euler]
    rw [div_one]
  induction m using Nat.strong_induction_on with | h m ih =>
  match m with
  | 0 => simp [toEuler, euler_h]
  | m + 1 =>
    replace ih := fun m hm => ih m hm <| by omega
    rw [← sub_left_inj (a := g.convs m), ← ih m m.lt_add_one]
    rcases Decidable.em <| TerminatedAt g m with terminatedAt_m | not_terminatedAt_m
    · rw [nums_stable_of_terminated m.le_succ <| terminatedAt_toEuler_iff_terminatedAt.mpr
        terminatedAt_m, sub_self, ih m m.lt_add_one,
        g.convs_stable_of_terminated m.lt_add_one.le terminatedAt_m, sub_self]
    · obtain ⟨⟨a, b⟩, g_mth_eq⟩ : ∃ gp, g.s.get? m = some gp :=
        Option.ne_none_iff_exists'.mp not_terminatedAt_m
      match m with
      | 0 =>
        have g_toEuler_zeroth_eq : g.toEuler.s.get? 0 = some ⟨a / b, 1⟩ := by
          simp [toEuler_s_zero, g_mth_eq]
        simp only [zero_add, zeroth_num_eq_h, sub_left_inj]
        simp only [convs, first_num_eq g_mth_eq, first_den_eq g_mth_eq,
          first_num_eq g_toEuler_zeroth_eq, one_mul]
        rw [add_div, mul_div_cancel_left₀ _ fun nh => hB 1 hm
          (first_den_eq g_mth_eq ▸ nh), toEuler, euler_h]
      | m + 1 =>
        have g_toEuler_mth_eq : g.toEuler.s.get? (m + 1) =
            some ⟨a * g.dens m / g.dens (m + 2), 1 - a * g.dens m / g.dens (m + 2)⟩ := by
          simp only [toEuler_s_succ, g_mth_eq, Option.map_some]
        grind [nums_recurrence g_mth_eq rfl rfl, dens_recurrence g_mth_eq rfl rfl,
          nums_recurrence g_toEuler_mth_eq rfl rfl, convs, hB m, hB (m + 1), hB (m + 2)]

/-- The transformation `toEuler` preserves the convergents. -/
theorem convs_toEuler_eq_convs (hB : ∀ m, g.dens m ≠ 0) :
    g.toEuler.convs = g.convs :=
  funext fun m =>
    convs_toEuler_eq_convs_of_forall_le_dens_ne_zero (fun m _ => hB m) m m.le_succ

end GenContFract
