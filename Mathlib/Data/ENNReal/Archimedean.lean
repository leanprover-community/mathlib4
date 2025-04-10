/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Archimedean
import Mathlib.Order.Interval.Set.WithBotTop

/-!
# Extended non-negative reals

We define `ENNReal = ℝ≥0∞ := WithTop ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `MeasureTheory.Measure`,
and of the extended distance `edist` in an `EMetricSpace`.

In this file we set up many of the instances on `ℝ≥0∞`, and provide relationships between `ℝ≥0∞` and
`ℝ≥0`, and between `ℝ≥0∞` and `ℝ`. In particular, we provide a coercion from `ℝ≥0` to `ℝ≥0∞` as well
as functions `ENNReal.toNNReal`, `ENNReal.ofReal` and `ENNReal.toReal`, all of which take the value
zero wherever they cannot be the identity. Also included is the relationship between `ℝ≥0∞` and `ℕ`.
The interaction of these functions, especially `ENNReal.ofReal` and `ENNReal.toReal`, with the
algebraic and lattice structure can be found in `Data.ENNReal.Real`.

This file proves many of the order properties of `ℝ≥0∞`, with the exception of the ways those relate
to the algebraic structure, which are included in `Data.ENNReal.Operations`.
This file also defines inversion and division: this includes `Inv` and `Div` instances on `ℝ≥0∞`
making it into a `DivInvOneMonoid`.
As a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation with integer
exponent: this and other properties is shown in `Data.ENNReal.Inv`.


## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `WithTop ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and
    `a * ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.
  - `a / b` is defined as `a * b⁻¹`.

  This inversion and division include `Inv` and `Div` instances on `ℝ≥0∞`,
  making it into a `DivInvOneMonoid`. Further properties of these are shown in `Data.ENNReal.Inv`.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `Coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ENNReal.toNNReal` sends `↑p` to `p` and `∞` to `0`;

  - `ENNReal.toReal := coe ∘ ENNReal.toNNReal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ENNReal.ofReal := coe ∘ Real.toNNReal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ENNReal.neTopEquivNNReal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `CanLift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `Data.Real.NNReal`;
* `∞`: a localized notation in `ENNReal` for `⊤ : ℝ≥0∞`.

-/

assert_not_exists Finset

open Function Set NNReal ENNReal

variable {α : Type*}

namespace ENNReal

noncomputable instance : CompleteLinearOrder ℝ≥0∞ :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℝ≥0))

instance : DenselyOrdered ℝ≥0∞ := inferInstanceAs (DenselyOrdered (WithTop ℝ≥0))

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}


section Order

theorem lt_iff_exists_rat_btwn :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : ℝ≥0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩,
      fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

theorem lt_iff_exists_real_btwn :
    a < b ↔ ∃ r : ℝ, 0 ≤ r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : ℝ≥0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

protected theorem exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
  lift r to ℝ≥0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_natCast.2 hn⟩

@[simp]
theorem iUnion_Iio_coe_nat : ⋃ n : ℕ, Iio (n : ℝ≥0∞) = {∞}ᶜ := by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩

@[simp]
theorem iUnion_Iic_coe_nat : ⋃ n : ℕ, Iic (n : ℝ≥0∞) = {∞}ᶜ :=
  Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx) <|
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

@[simp]
theorem iUnion_Ioc_coe_nat : ⋃ n : ℕ, Ioc a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]

@[simp]
theorem iUnion_Ioo_coe_nat : ⋃ n : ℕ, Ioo a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]

@[simp]
theorem iUnion_Icc_coe_nat : ⋃ n : ℕ, Icc a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, diff_eq]

@[simp]
theorem iUnion_Ico_coe_nat : ⋃ n : ℕ, Ico a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, diff_eq]

@[simp]
theorem iInter_Ici_coe_nat : ⋂ n : ℕ, Ici (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

@[simp]
theorem iInter_Ioi_coe_nat : ⋂ n : ℕ, Ioi (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

end Order

section CompleteLattice
variable {ι : Sort*} {f : ι → ℝ≥0}

theorem coe_sSup {s : Set ℝ≥0} : BddAbove s → (↑(sSup s) : ℝ≥0∞) = ⨆ a ∈ s, ↑a :=
  WithTop.coe_sSup

theorem coe_sInf {s : Set ℝ≥0} (hs : s.Nonempty) : (↑(sInf s) : ℝ≥0∞) = ⨅ a ∈ s, ↑a :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

theorem coe_iSup {ι : Sort*} {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
    (↑(iSup f) : ℝ≥0∞) = ⨆ a, ↑(f a) :=
  WithTop.coe_iSup _ hf

@[norm_cast]
theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0) : (↑(iInf f) : ℝ≥0∞) = ⨅ a, ↑(f a) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

lemma iSup_coe_eq_top : ⨆ i, (f i : ℝ≥0∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
lemma iSup_coe_lt_top : ⨆ i, (f i : ℝ≥0∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
lemma iInf_coe_eq_top : ⨅ i, (f i : ℝ≥0∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
lemma iInf_coe_lt_top : ⨅ i, (f i : ℝ≥0∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

end CompleteLattice

end ENNReal
