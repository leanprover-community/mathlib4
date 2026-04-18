/-
Copyright (c) 2026 emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: emlis
-/
module

public import Mathlib.Algebra.ContinuedFractions.Determinant

/-!
# Euler's continued fraction

This file formalizes an transformation on generalized continued fractions over a field `K`.
It defines a map sending a generalized continued fraction to an equivalent Euler's continued
fraction obtained by an explicit transformation of its coefficient stream.

## Main definitions

* `GenContFract.Euler` : constructs a generalized continued fraction from a head term `h`
  and a coefficient stream `ρ`.
* `GenContFract.toEuler` : transforms a generalized continued fraction to a Euler's continued
  fraction.

## Main results

* `euler_convs` : explicit formula for convergents of an Euler-transformed continued fraction.
* `convs_eq_toEuler_convs` : equivalence of convergents between a generalized continued fraction
  and its corresponding Euler's continued fraction.

## References

* https://en.wikipedia.org/wiki/Euler%27s_continued_fraction_formula
* [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

-/

public section

namespace GenContFract

variable {K : Type*} [Field K]
variable {n : ℕ} {h : K} {ρ : Stream'.Seq K} {g : GenContFract K}

/-- A *Euler's continued fraction* is a generalized continued fraction of the form
$$
  h + \cfrac{\rho_0}
            {1 - \cfrac{\rho_1}
                       {1 + \rho_1 - \cfrac{\rho_2}
                                           {1 + \rho_2 - \cfrac{\rho_3}
                                                               {1 + \rho_3 - \dots}}}}
$$
`Euler h ρ` constructs a Euler's continued fraction whose coefficients are obtained
from the stream `ρ` with head term `h`.
-/
def Euler (h : K) (ρ : Stream'.Seq K) : GenContFract K :=
  ⟨h, ρ.enum.map fun (n, ρ) => n.casesOn ⟨ρ, 1⟩ fun _ => ⟨-ρ, 1 + ρ⟩⟩

private def toEulerAux (g : GenContFract K) : Stream'.Seq K :=
  g.s.enum.map fun (n, c) =>
    n.casesOn (c.a / c.b) (fun n => - c.a * g.dens n / g.dens (n + 2))

/--
`toEuler g` is the Euler's continued fraction equivalent to `g`, where `ρ₀` = `a₀ / b₀` and
`ρₙ` = `- aₙ * Bₙ₋₁ / Bₙ₊₁` for `n > 0`.
-/
def toEuler (g : GenContFract K) : GenContFract K :=
  Euler g.h (toEulerAux g)

theorem euler_terminatedAt_iff_terminatedAt : (Euler h ρ).TerminatedAt n ↔ ρ.TerminatedAt n := by
  cases n <;> simp [TerminatedAt, Euler, Stream'.Seq.TerminatedAt]

theorem exists_euler_s_of_not_terminatedAt_zero
    (not_terminatedAt_zero : ¬ρ.TerminatedAt 0) :
    ∃ a, (Euler h ρ).s.get? 0 = some ⟨a, 1⟩ := by
  simpa [Euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_zero

theorem exists_euler_s_of_not_terminatedAt_succ
    (not_terminatedAt_n_add_one : ¬ρ.TerminatedAt (n + 1)) :
    ∃ a, (Euler h ρ).s.get? (n + 1) = some ⟨-a, 1 + a⟩ := by
  simpa [Euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_n_add_one

/-- the denominators of an Euler's continued fraction are all 1. -/
theorem euler_dens : (Euler h ρ).dens n = 1 := by
  set g := Euler h ρ
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => exact zeroth_den_eq_one
    | n + 1 =>
      rcases Decidable.em <| g.TerminatedAt n with terminatedAt_n | not_terminatedAt_n
      · specialize ih n <| lt_add_one n
        rwa [dens_stable_of_terminated n.le_succ <| terminatedAt_n]
      · rw [euler_terminatedAt_iff_terminatedAt] at not_terminatedAt_n
        match n with
        | 0 =>
          exact first_den_eq <|
            exists_euler_s_of_not_terminatedAt_zero not_terminatedAt_n |>.choose_spec
        | n + 1 =>
          obtain ⟨a, ρ_n_add_one_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
            exists_euler_s_of_not_terminatedAt_succ not_terminatedAt_n
          simp [dens_recurrence ρ_n_add_one_eq rfl rfl, ih]

private theorem euler_nums_aux : (Euler h ρ).nums (n + 1) - (Euler h ρ).nums n =
    ∏ j ∈ Finset.range (n + 1), (ρ.get? j).getD 0 := by
  set g := Euler h ρ
  induction n with
  | zero =>
    rcases Decidable.em <| ρ.TerminatedAt 0 with terminatedAt_zero | not_terminatedAt_zero
    · rw [g.nums_stable_of_terminated (Nat.zero_le _) <|
        euler_terminatedAt_iff_terminatedAt.mpr terminatedAt_zero]
      simp [← terminatedAt_zero.symm]
    · obtain ⟨a, g_zeroth_eq⟩ : ∃ a, g.s.get? 0 = some ⟨a, 1⟩ :=
        exists_euler_s_of_not_terminatedAt_zero not_terminatedAt_zero
      rw [first_num_eq g_zeroth_eq]
      simp [g, Euler] at g_zeroth_eq
      simp [g_zeroth_eq]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    rcases Decidable.em <| ρ.TerminatedAt n.succ with terminatedAt_n_succ | not_terminatedAt_n_succ
    · rw [nums_stable_of_terminated n.succ.le_succ <| euler_terminatedAt_iff_terminatedAt.mpr
        terminatedAt_n_succ, terminatedAt_n_succ]
      simp [g]
    · obtain ⟨a, g_n_add_one_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
        exists_euler_s_of_not_terminatedAt_succ not_terminatedAt_n_succ
      rw [nums_recurrence g_n_add_one_eq rfl rfl]
      simp [g, Euler] at g_n_add_one_eq
      simp [g_n_add_one_eq]
      ring

theorem euler_nums_zero : (Euler h ρ).nums 0 = h := by rfl

/-- the numerators of an Euler's continued fraction are given by the formula
$$
  A_n = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$
for example:
- `A₀ = h`
- `A₁ = h + ρ₀`
- `A₂ = h + ρ₀ + ρ₀ * ρ₁`
- `A₃ = h + ρ₀ + ρ₀ * ρ₁ + ρ₀ * ρ₁ * ρ₂`
-/
theorem euler_nums :
    (Euler h ρ).nums n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  simp only [← euler_nums_aux (h := h)]
  rw [Finset.sum_range_sub, euler_nums_zero, add_sub_cancel]

/-- **Euler's continued fraction formula**: the convergents of an Euler's continued fraction
are given by the formula
$$
  \dfrac{A_n}{B_n} = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$
for example:
- `A₀ / B₀ = h`
- `A₁ / B₁ = h + ρ₀`
- `A₂ / B₂ = h + ρ₀ + ρ₀ * ρ₁`
- `A₃ / B₃ = h + ρ₀ + ρ₀ * ρ₁ + ρ₀ * ρ₁ * ρ₂`
-/
theorem euler_convs {h : K} {ρ : Stream'.Seq K} :
    (Euler h ρ).convs n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  rw [convs, euler_dens, euler_nums, div_one]

/-- the transformation `toEuler` is idempotent. -/
theorem toEuler_toEuler :
  g.toEuler.toEuler = g.toEuler := by
  set h := g.h
  set ρ := toEulerAux g
  change (Euler h ρ).toEuler = Euler h ρ
  ext n : 2
  · rfl
  · match n with
    | 0 =>
      simp only [toEuler, Euler, toEulerAux]
      simp only [neg_mul, Stream'.Seq.map_get?, Stream'.Seq.get?_enum, Option.map_map]
      congr 1; ext a; simp
    | n + 1 =>
      set g := Euler h ρ
      simp only [toEuler, Euler, toEulerAux]
      simp only [neg_mul, Stream'.Seq.map_get?, Stream'.Seq.get?_enum, Option.map_map]
      conv => enter [1, 1, ρ]; simp [g]
      rcases Decidable.em <| g.TerminatedAt <| n + 1 with terminatedAt_n | not_terminatedAt_n
      · rw [terminatedAt_n, Option.map_none]
      · obtain ⟨a, g_nth_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
          exists_euler_s_of_not_terminatedAt_succ <| by
            rwa [euler_terminatedAt_iff_terminatedAt] at not_terminatedAt_n
        simp [g_nth_eq, euler_dens]

private theorem convs_eq_toEuler_convs_aux (hB: ∀ m ≤ n + 1, g.dens m ≠ 0) :
    ∀ m ≤ n, g.convs (m + 1) - g.convs m =
      -(∏ i ∈ Finset.range (m + 1), (- (g.partNums.get? i).getD 0)) /
        (g.dens m * g.dens (m + 1)) := by
  intro m hm
  calc
    _ = g.nums (m + 1) / g.dens (m + 1) - g.nums m / g.dens m := rfl
    _ = (g.nums (m + 1) * g.dens m - g.dens (m + 1) * g.nums m) / (g.dens (m + 1) * g.dens m) :=
      div_sub_div _ _ (hB _ <| Nat.add_le_add_iff_right.mpr hm) (hB _ <| Nat.le_add_right_of_le hm)
    _ = (g.dens m * g.nums (m + 1) - g.nums m * g.dens (m + 1)) / (g.dens m * g.dens (m + 1)) :=
      congr(($(mul_comm _ _) - $(mul_comm _ _)) / $(mul_comm _ _))
    _ = -(g.nums m * g.dens (m + 1) - g.dens m * g.nums (m + 1)) / (g.dens m * g.dens (m + 1)) :=
      congr($(neg_sub _ _ |>.symm) / _)
    _ = _ := congr(-$(determinant) / _)

theorem convs_eq_toEuler_convs_of_forall_le_dens_nonzero (hB : ∀ m ≤ n, g.dens m ≠ 0) :
    ∀ m ≤ n, g.convs m = g.toEuler.convs m := by
  intro m hm
  match n with
  | 0 =>
    rw [Nat.le_zero] at hm
    subst m
    simp only [zeroth_conv_eq_h]
    rfl
  | n + 1 =>
    rw [toEuler, euler_convs, ← sub_eq_iff_eq_add']
    calc
      _ = g.convs m - g.convs 0 := congr(_ - $(zeroth_conv_eq_h.symm))
      _ = ∑ i ∈ Finset.range m, (g.convs (i + 1) - g.convs i) := Finset.sum_range_sub _ _ |>.symm
      _ = _ := Finset.sum_congr rfl <| by
        rintro i hi
        rw [Finset.mem_range] at hi
        rw [convs_eq_toEuler_convs_aux hB i (by omega)]
        simp only [partNums, Stream'.Seq.map_get?]
        induction i with
        | zero =>
          simp only [zero_add, Finset.range_one, Finset.prod_singleton]
          simp only [toEulerAux]
          simp only [neg_neg, zeroth_den_eq_one, one_mul, neg_mul, Stream'.Seq.map_get?,
            Stream'.Seq.get?_enum, Option.map_map]
          rcases Decidable.em (TerminatedAt g 0) with terminatedAt_0 | not_terminatedAt_0
          · rw [terminatedAt_0]
            simp
          · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp not_terminatedAt_0
            simp [hc, first_den_eq]
        | succ i ih =>
          iterate 2 rw [Finset.prod_range_succ (n := i + 1)]
          rw [← ih (by omega)]; clear ih
          simp only [← mul_neg, neg_neg, neg_div, neg_mul]
          simp only [toEulerAux]
          simp only [Stream'.Seq.map, Stream'.Seq.enum, Stream'.Seq.zip, Stream'.Seq.zipWith,
            Stream'.Seq.nats_get?, Option.map₂_coe_left, Stream'.Seq.get?_mk, Stream'.map,
            Stream'.get, Option.map_map]
          rw [← mul_div_right_comm, mul_div_assoc, mul_div_assoc]
          congr 1; rcases g.s.get? (i + 1) with _ | c
          · simp
          · simp only [Option.map_some, Option.getD_some, neg_mul, neg_div, Function.comp_apply,
            neg_neg]
            rw [div_div, mul_comm (g.dens i), ← mul_assoc, mul_comm]
            rw [mul_div_mul_right _ _ (hB _ (by omega))]

/-- the transformation `toEuler` preserves the convergents -/
theorem convs_eq_toEuler_convs (hB : ∀ m, g.dens m ≠ 0) :
    g.convs = g.toEuler.convs :=
  funext fun m =>
    convs_eq_toEuler_convs_of_forall_le_dens_nonzero (fun m _ => hB m) m <| Nat.le_succ m

end GenContFract
