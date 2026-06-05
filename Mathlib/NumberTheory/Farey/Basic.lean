/-
Copyright (c) 2026 Saar Shai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saar Shai
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Farey sequences and the Stern–Brocot mediant

This file develops **Farey sequences** `F n` — the reduced rationals in `[0,1]` with denominator at
most `n` — together with the **mediant / unimodular-neighbour** structure underlying them and the
**Stern–Brocot tree**. For fractions `a/b`, `c/d` the *mediant* is `(a+c)/(b+d)`, and the pair is a
*unimodular neighbour* when `b * c - a * d = 1`. The Farey sequence as an object, its length, and
its neighbour theorem are not currently in Mathlib.

## Main definitions

* `Farey.Unimodular a b c d` : the unimodular-neighbour relation `b * c - a * d = 1`.
* `Farey.farey n` : the Farey sequence `F n`, as a `Finset ℚ`.

## Main results

* `Farey.Unimodular.isCoprime_mediant` : the mediant of a unimodular pair is in lowest terms.
* `Farey.Unimodular.den_ge_of_strictBetween` : between unimodular neighbours every intermediate
  fraction has denominator `≥ b + d`; with the mediant achieving `b + d`, the mediant is the unique
  simplest fraction strictly between.
* `Farey.isFareyChain_insert_mediant` : mediant insertion preserves unimodular adjacency — the
  Stern–Brocot inductive step.
* `Farey.Unimodular.rat_sub` : the Farey gap formula, `c/d - a/b = 1/(b*d)`.
* `Farey.card_farey` : **the length of the Farey sequence**, `|F n| = 1 + ∑_{k=1}^n φ(k)`.
* `Farey.mem_farey` : membership in `F n` is exactly `0 ≤ q`, `q ≤ 1`, and `q.den ≤ n`.
* `Farey.neighbour_unimodular` : **the Farey neighbour theorem** — consecutive Farey fractions are
  unimodular neighbours (Hardy–Wright, Theorem 28).
* `Farey.unimodular_of_consecutive` : the neighbour theorem on the `farey n` object itself —
  consecutive elements of `F n` (none of `F n` strictly between) are unimodular neighbours.

## References

* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 5th ed., Oxford
  University Press, 1979. The neighbour identity `k * h' - h * k' = 1` for successive terms is
  Theorem 28 (Chapter III, §3.1); the mediant is Theorem 29. The exact count `|F n| = Φ(n) + 1`
  appears in §18.5 (p. 268), preceding the asymptotic Theorem 331 (`|F n| ∼ 3n²/π²`); see also
  Theorem 330 (`Φ(n) ∼ 3n²/π²`) and OEIS A005728.
* R. L. Graham, D. E. Knuth and O. Patashnik, *Concrete Mathematics*, 2nd ed., 1994, §4.5
  (the Stern–Brocot tree and the mediant).
-/

@[expose] public section

open Finset

namespace Farey

variable {a b c d : ℤ}

/-- The determinant `b*c - a*d` of the ordered pair of fractions `a/b`, `c/d`. It equals `+1`
for unimodular (Farey/Stern–Brocot) neighbours and is positive exactly when `a/b < c/d`
(for positive denominators). -/
def det (a b c d : ℤ) : ℤ := b * c - a * d

/-- Two fractions `a/b`, `c/d` are **unimodular neighbours** when `b*c - a*d = 1`. This is the
defining adjacency relation of the Farey sequence and the Stern–Brocot tree. -/
def Unimodular (a b c d : ℤ) : Prop := det a b c d = 1

@[simp] lemma det_def (a b c d : ℤ) : det a b c d = b * c - a * d := rfl

/-- Inserting the mediant `(a+c)/(b+d)` to the right of `a/b` leaves the determinant unchanged. -/
lemma det_mediant_left (a b c d : ℤ) : det a b (a + c) (b + d) = det a b c d := by
  simp only [det_def]; ring

/-- Inserting the mediant `(a+c)/(b+d)` to the left of `c/d` leaves the determinant unchanged. -/
lemma det_mediant_right (a b c d : ℤ) : det (a + c) (b + d) c d = det a b c d := by
  simp only [det_def]; ring

/-- The mediant of a unimodular pair is a unimodular neighbour of the left parent. -/
lemma Unimodular.mediant_left (h : Unimodular a b c d) : Unimodular a b (a + c) (b + d) := by
  unfold Unimodular at h ⊢; rw [det_mediant_left]; exact h

/-- The mediant of a unimodular pair is a unimodular neighbour of the right parent. -/
lemma Unimodular.mediant_right (h : Unimodular a b c d) : Unimodular (a + c) (b + d) c d := by
  unfold Unimodular at h ⊢; rw [det_mediant_right]; exact h

/-- **The mediant of a unimodular pair is in lowest terms.** This is why every fraction produced
by Stern–Brocot mediant insertion is automatically reduced. The witness comes from
`c*(b+d) - d*(a+c) = b*c - a*d = 1`. -/
lemma Unimodular.isCoprime_mediant (h : Unimodular a b c d) : IsCoprime (a + c) (b + d) :=
  ⟨-d, c, by unfold Unimodular det at h; linear_combination h⟩

/-- For positive denominators, `a/b < c/d` (cross-multiplied) implies `a/b` is strictly below its
mediant with `c/d`, in cross-multiplied form: `a*(b+d) < (a+c)*b`. -/
lemma mediant_strictAnti_left (h : a * d < c * b) : a * (b + d) < (a + c) * b := by
  nlinarith [h]

/-- For positive denominators, `a/b < c/d` (cross-multiplied) implies the mediant is strictly
below `c/d`, in cross-multiplied form: `(a+c)*d < c*(b+d)`. -/
lemma mediant_strictMono_right (h : a * d < c * b) : (a + c) * d < c * (b + d) := by
  nlinarith [h]

/-- A unimodular pair is strictly ordered in cross-multiplied form: `a*d < c*b` (which is
`a/b < c/d` once the denominators are positive). This needs only `det = 1`, not positivity. -/
lemma Unimodular.ad_lt_cb (h : Unimodular a b c d) : a * d < c * b := by
  unfold Unimodular det at h; linarith [h]

/-! ## Farey / Stern–Brocot chains

A **Farey chain** is a list of fractions (as `(numerator, denominator)` pairs) whose consecutive
entries are unimodular neighbours. Because unimodularity forces strict order
(`Unimodular.ad_lt_cb`), a Farey chain is automatically strictly increasing. The Farey sequence
`F_n` is a Farey chain, and the Stern–Brocot construction extends Farey chains by *mediant
insertion*; the key invariant is that mediant insertion preserves the chain (proved below).
-/

/-- A fraction as a `(numerator, denominator)` pair. -/
abbrev Frac := ℤ × ℤ

/-- The mediant `(a+c, b+d)` of fractions `p = (a,b)` and `q = (c,d)`. -/
def medFrac (p q : Frac) : Frac := (p.1 + q.1, p.2 + q.2)

/-- The unimodular-neighbour relation on fractions: `Adj (a,b) (c,d) ↔ b*c - a*d = 1`. -/
def Adj (p q : Frac) : Prop := Unimodular p.1 p.2 q.1 q.2

/-- Mediant insertion makes the mediant a unimodular neighbour of the left parent. -/
lemma Adj.medFrac_left {p q : Frac} (h : Adj p q) : Adj p (medFrac p q) :=
  Unimodular.mediant_left h

/-- Mediant insertion makes the mediant a unimodular neighbour of the right parent. -/
lemma Adj.medFrac_right {p q : Frac} (h : Adj p q) : Adj (medFrac p q) q :=
  Unimodular.mediant_right h

/-- Farey-chain neighbours are strictly increasing (cross-multiplied): `a*d < c*b`. So a Farey
chain is sorted. -/
lemma Adj.lt {p q : Frac} (h : Adj p q) : p.1 * q.2 < q.1 * p.2 :=
  Unimodular.ad_lt_cb h

/-- A **Farey chain**: a list of fractions whose consecutive entries are unimodular neighbours. -/
def IsFareyChain (l : List Frac) : Prop := l.IsChain Adj

/-- The base Farey chain `[0/1, 1/1]`. -/
lemma isFareyChain_base : IsFareyChain [((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))] := by
  unfold IsFareyChain
  rw [List.isChain_pair]
  simp only [Adj, Unimodular, det]; norm_num

/-- **Mediant insertion preserves the Farey-chain property.** Given a Farey chain beginning
`p :: q :: l`, inserting the mediant of the first two entries yields the Farey chain
`p :: medFrac p q :: q :: l`. This is the inductive step of the Stern–Brocot construction of the
Farey sequence, and the source of the Farey neighbour theorem (consecutive Farey fractions are
unimodular). -/
lemma isFareyChain_insert_mediant {p q : Frac} {l : List Frac}
    (h : IsFareyChain (p :: q :: l)) :
    IsFareyChain (p :: medFrac p q :: q :: l) := by
  unfold IsFareyChain at h ⊢
  rw [List.isChain_cons_cons] at h
  obtain ⟨hpq, hrest⟩ := h
  rw [List.isChain_cons_cons, List.isChain_cons_cons]
  exact ⟨hpq.medFrac_left, hpq.medFrac_right, hrest⟩

/-! ## The denominator bound: Farey neighbours are spread out

The key quantitative fact behind the Farey neighbour theorem and the Stern–Brocot tree: between
two unimodular neighbours `a/b < c/d`, every intermediate fraction `p/q` has denominator
`q ≥ b + d`. Since the mediant achieves `q = b + d` and is reduced (`Unimodular.isCoprime_mediant`),
**the mediant is the unique simplest fraction strictly between two unimodular neighbours.**
-/

/-- **Between unimodular neighbours, every intermediate fraction has denominator `≥ b + d`.**
If `b*c - a*d = 1` (with `b, d > 0`) and `a/b < p/q < c/d` (cross-multiplied), then `b + d ≤ q`.
The one-line identity `q = d*(b*p - a*q) + b*(c*q - d*p)` (valid because `b*c - a*d = 1`) makes both
summands `≥ d` and `≥ b` respectively. -/
lemma Unimodular.den_ge_of_strictBetween {p q : ℤ} (h : Unimodular a b c d)
    (hb : 0 < b) (hd : 0 < d) (h1 : a * q < p * b) (h2 : p * d < c * q) : b + d ≤ q := by
  unfold Unimodular det at h
  have e1 : (1 : ℤ) ≤ p * b - a * q := by omega
  have e2 : (1 : ℤ) ≤ c * q - p * d := by omega
  have key : d * (p * b - a * q) + b * (c * q - p * d) = q := by
    have hexp : d * (p * b - a * q) + b * (c * q - p * d) = q * (b * c - a * d) := by ring
    rw [hexp, h, mul_one]
  nlinarith [mul_nonneg hd.le (by omega : (0 : ℤ) ≤ p * b - a * q - 1),
             mul_nonneg hb.le (by omega : (0 : ℤ) ≤ c * q - p * d - 1), key]

/-- **Adjacency criterion (sufficient direction).** If `a/b, c/d` are unimodular neighbours with
`n < b + d`, then *no* fraction `p/q` with `0 < q ≤ n` lies strictly between them — i.e. they are
adjacent in the Farey sequence `F_n`. (Immediate from `den_ge_of_strictBetween`.) -/
lemma Unimodular.not_strictBetween_of_den_le {p q n : ℤ} (h : Unimodular a b c d)
    (hb : 0 < b) (hd : 0 < d) (hqn : q ≤ n) (hn : n < b + d)
    (h1 : a * q < p * b) (h2 : p * d < c * q) : False := by
  have := h.den_ge_of_strictBetween hb hd h1 h2
  omega

/-! ## The Farey gap formula (in ℚ)

Two unimodular neighbours, viewed as rationals, differ by exactly `1/(b*d)`. This is the classical
fact that consecutive Farey fractions `a/b < c/d` satisfy `c/d - a/b = 1/(b*d)`.
-/

/-- **Farey gap formula.** Unimodular neighbours `a/b < c/d` (with `b, d > 0`) differ by exactly
`1/(b*d)` in `ℚ`. -/
lemma Unimodular.rat_sub (h : Unimodular a b c d) (hb : 0 < b) (hd : 0 < d) :
    (c : ℚ) / d - (a : ℚ) / b = 1 / ((b : ℚ) * d) := by
  have hb0 : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb.ne'
  have hd0 : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have h' : (b : ℚ) * c - a * d = 1 := by unfold Unimodular det at h; exact_mod_cast h
  rw [div_sub_div _ _ hd0 hb0, div_eq_div_iff (mul_ne_zero hd0 hb0) (mul_ne_zero hb0 hd0)]
  linear_combination (b : ℚ) * d * h'



/-- The `q`-th **Farey level**: the reduced fractions `a/q` in `[0,1)` with denominator exactly
`q`, namely `a/q` for `0 ≤ a < q` with `gcd(q, a) = 1`. Its cardinality is `Nat.totient q`. -/
def fareyLevel (q : ℕ) : Finset ℚ :=
  ((range q).filter fun a => q.Coprime a).image fun a : ℕ => (a : ℚ) / q

/-- The **Farey sequence** `F n`: the reduced rationals in `[0,1]` with denominator at most `n`.
Built as the endpoint `1` together with the levels `fareyLevel q` for `1 ≤ q ≤ n` (which cover
`[0,1)`). For `n = 0` this degenerates to `{1}`; the intended object is for `n ≥ 1`. -/
def farey (n : ℕ) : Finset ℚ :=
  insert 1 ((Icc 1 n).biUnion fareyLevel)

/-- Each Farey level has cardinality `Nat.totient q`. -/
lemma card_fareyLevel (q : ℕ) (hq : 0 < q) : (fareyLevel q).card = q.totient := by
  have hinj : Set.InjOn (fun a : ℕ => (a : ℚ) / q)
      ↑((range q).filter fun a => q.Coprime a) := by
    intro a _ b _ hab
    dsimp only at hab
    have hq' : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    rw [div_eq_div_iff hq' hq'] at hab
    exact_mod_cast mul_right_cancel₀ hq' hab
  unfold fareyLevel
  rw [card_image_of_injOn hinj]
  exact (Nat.totient_eq_card_coprime q).symm

/-- The denominator of an element of the `q`-th Farey level is exactly `q`. -/
lemma den_of_mem_fareyLevel {q : ℕ} {x : ℚ} (hx : x ∈ fareyLevel q) : x.den = q := by
  unfold fareyLevel at hx
  rw [mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [mem_filter, mem_range] at ha
  obtain ⟨haq, hcop⟩ := ha
  have hq : 0 < q := by omega
  have hb0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hcop' : Nat.Coprime ((a : ℤ).natAbs) ((q : ℤ).natAbs) := by
    simpa [Int.natAbs_natCast] using hcop.symm
  have h := Rat.den_div_eq_of_coprime hb0 hcop'
  have hbridge : ((a : ℚ) / (q : ℚ)) = (((a : ℤ) : ℚ) / ((q : ℤ) : ℚ)) := by push_cast; ring
  rw [hbridge]
  exact_mod_cast h

/-- Elements of any Farey level are `< 1`. -/
lemma mem_fareyLevel_lt_one {q : ℕ} {x : ℚ} (hx : x ∈ fareyLevel q) : x < 1 := by
  unfold fareyLevel at hx
  rw [mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [mem_filter, mem_range] at ha
  obtain ⟨haq, _⟩ := ha
  have hq : 0 < q := by omega
  rw [div_lt_one (by exact_mod_cast hq)]
  exact_mod_cast haq

/-- Elements of any Farey level are `≥ 0`. -/
lemma mem_fareyLevel_nonneg {q : ℕ} {x : ℚ} (hx : x ∈ fareyLevel q) : 0 ≤ x := by
  unfold fareyLevel at hx
  rw [mem_image] at hx
  obtain ⟨a, _, rfl⟩ := hx
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **The length of the Farey sequence.** `|F n| = 1 + ∑_{k=1}^n φ(k)`, where `φ` is Euler's
totient. The exact count `|F n| = Φ(n) + 1` is the remark in Hardy–Wright, §18.5 (p. 268),
preceding the asymptotic Theorem 331; see also OEIS A005728. -/
theorem card_farey (n : ℕ) : (farey n).card = 1 + ∑ q ∈ Icc 1 n, q.totient := by
  have h1 : (1 : ℚ) ∉ (Icc 1 n).biUnion fareyLevel := by
    rw [mem_biUnion]
    rintro ⟨q, _, hx⟩
    exact absurd (mem_fareyLevel_lt_one hx) (lt_irrefl 1)
  have hdisj : ((Icc 1 n : Finset ℕ) : Set ℕ).PairwiseDisjoint fareyLevel := by
    intro q _ q' _ hqq'
    change Disjoint (fareyLevel q) (fareyLevel q')
    rw [Finset.disjoint_left]
    intro x hxq hxq'
    exact hqq' ((den_of_mem_fareyLevel hxq).symm.trans (den_of_mem_fareyLevel hxq'))
  have hsum : ((Icc 1 n).biUnion fareyLevel).card = ∑ q ∈ Icc 1 n, q.totient := by
    rw [card_biUnion hdisj]
    exact Finset.sum_congr rfl fun q hq => card_fareyLevel q (mem_Icc.mp hq).1
  unfold farey
  rw [card_insert_of_notMem h1, hsum]
  omega

-- Sanity checks: `|F₁| = 2`, `|F₂| = 3`, `|F₃| = 5`.
example : (farey 1).card = 2 := by rw [card_farey]; decide
example : (farey 2).card = 3 := by rw [card_farey]; decide
example : (farey 3).card = 5 := by rw [card_farey]; decide

/-- **Membership in the Farey sequence.** For `n ≥ 1`, the elements of `F n` are exactly the
rationals in `[0,1]` with denominator at most `n`. -/
theorem mem_farey {n : ℕ} (hn : 1 ≤ n) {x : ℚ} :
    x ∈ farey n ↔ 0 ≤ x ∧ x ≤ 1 ∧ x.den ≤ n := by
  unfold farey
  rw [mem_insert, mem_biUnion]
  constructor
  · rintro (rfl | ⟨q, hq, hx⟩)
    · exact ⟨zero_le_one, le_refl 1, by simpa using hn⟩
    · rw [mem_Icc] at hq
      exact ⟨mem_fareyLevel_nonneg hx, (mem_fareyLevel_lt_one hx).le,
        by rw [den_of_mem_fareyLevel hx]; exact hq.2⟩
  · rintro ⟨hx0, hx1, hxden⟩
    rcases eq_or_lt_of_le hx1 with heq | hxlt
    · exact Or.inl heq
    · refine Or.inr ⟨x.den, mem_Icc.mpr ⟨Rat.den_pos x, hxden⟩, ?_⟩
      have h0 : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
      simp only [fareyLevel, mem_image, mem_filter, mem_range]
      refine ⟨x.num.toNat, ⟨?_, ?_⟩, ?_⟩
      · have h2 : x.num < (x.den : ℤ) := Rat.num_lt_denom_iff.mpr hxlt
        have h3 : (x.num.toNat : ℤ) = x.num := Int.toNat_of_nonneg h0
        omega
      · have hnt : x.num.natAbs = x.num.toNat := by
          have ha := Int.natAbs_of_nonneg h0
          have hb := Int.toNat_of_nonneg h0
          omega
        have hred : Nat.Coprime x.num.natAbs x.den := x.reduced
        rw [hnt] at hred
        exact hred.symm
      · have hcast : ((x.num.toNat : ℚ)) = (x.num : ℚ) := by
          exact_mod_cast Int.toNat_of_nonneg h0
        rw [hcast]
        exact Rat.num_div_den x



/-- **Farey neighbour theorem (Hardy–Wright, Thm 28).** Consecutive Farey fractions are unimodular
neighbours. Here `hadj` is the consecutiveness hypothesis: no `x/y` with `0 < y ≤ n` lies strictly
between `a/b` and `c/d` (in cross-multiplied form). -/
theorem neighbour_unimodular {a b c d n : ℤ}
    (hb : 0 < b) (hbn : b ≤ n) (hdn : d ≤ n)
    (hab : IsCoprime a b) (hcd : IsCoprime c d)
    (hlt : a * d < c * b)
    (hadj : ∀ x y : ℤ, 0 < y → y ≤ n → a * y < x * b → ¬ (x * d < c * y)) :
    b * c - a * d = 1 := by
  have hmpos : 1 ≤ b * c - a * d := by
    have h2 : a * d < b * c := by linarith [hlt, mul_comm c b]
    omega
  -- Bézout solution of `b*x - a*y = 1` with denominator `y ∈ (n - b, n]`.
  obtain ⟨x, y, hbez, hylo, hyhi⟩ :
      ∃ x y : ℤ, b * x - a * y = 1 ∧ n - b < y ∧ y ≤ n := by
    obtain ⟨u, v, huv⟩ := hab
    have hQb : ((n + u) / b) * b = (n + u) - (n + u) % b := by
      have h := Int.mul_ediv_add_emod (n + u) b
      linarith [h, mul_comm b ((n + u) / b)]
    have hmod1 : 0 ≤ (n + u) % b := Int.emod_nonneg _ hb.ne'
    have hmod2 : (n + u) % b < b := Int.emod_lt_of_pos _ hb
    refine ⟨v + ((n + u) / b) * a, -u + ((n + u) / b) * b, by linear_combination huv, ?_, ?_⟩
    · rw [hQb]; linarith [hmod2]
    · rw [hQb]; linarith [hmod1]
  have hy0 : 0 < y := by omega
  have hax : a * y < x * b := by nlinarith [hbez]
  have hcle : c * y ≤ x * d := not_lt.mp (hadj x y hy0 hyhi hax)
  -- determinant identity: `(b*c-a*d)·(y,x) = (d,c) - (d*x-c*y)·(b,a)`
  have eqd : (b * c - a * d) * y = d - (d * x - c * y) * b := by linear_combination d * hbez
  have eqc : (b * c - a * d) * x = c - (d * x - c * y) * a := by linear_combination c * hbez
  have hm'0 : 0 ≤ d * x - c * y := by nlinarith [hcle]
  rcases eq_or_lt_of_le hm'0 with hm'eq | hm'pos
  · -- `d*x - c*y = 0`: then `(b*c-a*d) ∣ c` and `∣ d`, so it divides `gcd(c,d) = 1`.
    rw [← hm'eq, zero_mul, sub_zero] at eqd eqc
    have hunit : IsUnit (b * c - a * d) := hcd.isUnit_of_dvd' ⟨x, eqc.symm⟩ ⟨y, eqd.symm⟩
    rcases Int.isUnit_iff.mp hunit with h1 | h1
    · exact h1
    · omega
  · -- `d*x - c*y ≥ 1`: then `d = (b*c-a*d)*y + (d*x-c*y)*b ≥ y + b > n`, contradicting `d ≤ n`.
    exfalso
    have hp1 : (0 : ℤ) ≤ b * c - a * d - 1 := by linarith [hmpos]
    have hp2 : (0 : ℤ) ≤ d * x - c * y - 1 := by omega
    nlinarith [eqd, mul_nonneg hp1 hy0.le, mul_nonneg hp2 hb.le, hylo, hdn]


/-- **The Farey neighbour theorem on `F n`.** If `r < s` are *consecutive* in the Farey sequence
`F n` — i.e. no element of `F n` lies strictly between them — then they are unimodular neighbours:
`r.den * s.num - r.num * s.den = 1`. This is `neighbour_unimodular` realised on the Farey set
`farey n`; the adjacency hypothesis (no fraction of denominator `≤ n` strictly between) is supplied
by the fact that any such fraction would itself lie in `F n`. -/
theorem unimodular_of_consecutive {n : ℕ} (hn : 1 ≤ n) {r s : ℚ}
    (hr : r ∈ farey n) (hs : s ∈ farey n) (hrs : r < s)
    (hbetween : ∀ t ∈ farey n, ¬ (r < t ∧ t < s)) :
    Unimodular r.num (r.den : ℤ) s.num (s.den : ℤ) := by
  obtain ⟨hr0, hr1, hrden⟩ := (mem_farey hn).mp hr
  obtain ⟨hs0, hs1, hsden⟩ := (mem_farey hn).mp hs
  have hrdenℚ : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have hsdenℚ : (0 : ℚ) < (s.den : ℚ) := by exact_mod_cast s.den_pos
  change (r.den : ℤ) * s.num - r.num * (s.den : ℤ) = 1
  apply neighbour_unimodular (n := (n : ℤ))
  · exact_mod_cast r.den_pos
  · exact_mod_cast hrden
  · exact_mod_cast hsden
  · rw [Int.isCoprime_iff_gcd_eq_one]
    simp only [Int.gcd, Int.natAbs_natCast]
    exact r.reduced
  · rw [Int.isCoprime_iff_gcd_eq_one]
    simp only [Int.gcd, Int.natAbs_natCast]
    exact s.reduced
  · have h := hrs
    rw [← Rat.num_div_den r, ← Rat.num_div_den s] at h
    exact_mod_cast (div_lt_div_iff₀ hrdenℚ hsdenℚ).mp h
  · intro x y hy0 hyn hrx hxs
    have hypos : (0 : ℚ) < (y : ℚ) := by exact_mod_cast hy0
    have hrz : r < (x : ℚ) / (y : ℚ) := by
      rw [← Rat.num_div_den r, div_lt_div_iff₀ hrdenℚ hypos]
      exact_mod_cast hrx
    have hzs : (x : ℚ) / (y : ℚ) < s := by
      rw [← Rat.num_div_den s, div_lt_div_iff₀ hypos hsdenℚ]
      exact_mod_cast hxs
    have hzden : ((x : ℚ) / (y : ℚ)).den ≤ n := by
      have hdvd : (((x : ℚ) / (y : ℚ)).den : ℤ) ∣ y := by
        rw [Rat.intCast_div_eq_divInt]
        exact Rat.den_dvd x y
      have hle := Int.le_of_dvd hy0 hdvd
      omega
    exact hbetween ((x : ℚ) / (y : ℚ))
      ((mem_farey hn).mpr ⟨le_of_lt (lt_of_le_of_lt hr0 hrz),
        le_of_lt (lt_of_lt_of_le hzs hs1), hzden⟩) ⟨hrz, hzs⟩

end Farey
