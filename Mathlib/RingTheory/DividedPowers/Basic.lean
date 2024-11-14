/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Choose.Multinomial

/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power* structure on `I` is the datum of operations `a n ↦ dpow a n`
satisfying relations that model the intuitive formula `dpow n a = a ^ n / n.factorial` and
collected by the structure `DividedPowers`. The list of axioms is embedded in the structure:
To avoid coercions, we rather consider `DividedPowers.dpow : ℕ → A → A`, extended by 0.

* `DividedPowers.dpow_null` asserts that `dpow n x = 0` for `x ∉ I`

* `DividedPowers.dpow_mem` : `dpow n x ∈ I` for `n ≠ 0`
For `x y : A` and `m n : ℕ` such that `x ∈ I` and `y ∈ I`, one has
* `DividedPowers.dpow_zero` : `dpow 0 x = 1`
* `DividedPowers.dpow_one` : `dpow 1 x = 1`
* `DividedPowers.dpow_add` : `dpow n (x + y) =
(antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y`,
this is the binomial theorem without binomial coefficients.
* `DividedPowers.dpow_mul`: `dpow n (a * x) = a ^ n * dpow n x`
* `DividedPowers.mul_dpow` : `dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x`
* `DividedPowers.dpow_comp` : `dpow m (dpow n x) = uniformBell m n * dpow (m * n) x`

* `DividedPowers.dividedPowersBot` : the trivial divided powers structure on the zero ideal

* `DividedPowers.prod_dpow`: a product of divided powers is a multinomial coefficients
times a divided power

* `DividedPowers.dpow_sum`: the multinomial theorem for divided powers,
without multinomial coefficients.

* `DividedPowers.ofRingEquiv`: transfer divided powers along `RingEquiv`

* `DividedPowers.equiv`: the equivalence `DividedPowers I ≃ DividedPowers J`,
for `e : R ≃+* S`, and `I : Ideal R`,  `J : Ideal S` such that `I.map e = J`

* `DividedPowers.exp`: the power series `Σ (dpow n a) X ^n`

* `DividedPowers.exp_add`: its multiplicativity

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## Discussion

* In practice, one often has a single such structure to handle on a given ideal,
but several ideals of the same ring might be considered.
Without any explicit mention of the ideal, it is not clear whether such structures
should be provided as instances.

* We do not provide any notation such as `a ^[n]` for `dpow a n`.

-/


section DividedPowersDefinition
/- ## Definition of divided powers -/

open Finset Nat

/-- The divided power structure on an ideal I of a commutative ring A -/
structure DividedPowers {A : Type*} [CommSemiring A] (I : Ideal A) where
  /-- The divided power function underlying a divided power structure -/
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y
  dpow_mul : ∀ (n) {a : A} {x} (_ : x ∈ I),
    dpow n (a * x) = a ^ n * dpow n x
  mul_dpow : ∀ (m n) {x} (_ : x ∈ I),
    dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : ∀ (m) {n x} (_ : n ≠ 0) (_ : x ∈ I),
    dpow m (dpow n x) = uniformBell m n * dpow (m * n) x

/-- The canonical `DividedPowers` structure on the zero ideal -/
def dividedPowersBot (A : Type*) [CommSemiring A] [DecidableEq A] :
    DividedPowers (⊥ : Ideal A) where
  dpow n a := ite (a = 0 ∧ n = 0) 1 0
  dpow_null {n a} ha := by
    simp only [Ideal.mem_bot] at ha
    dsimp
    rw [if_neg]
    exact not_and_of_not_left (n = 0) ha
  dpow_zero {a} ha := by
    rw [Ideal.mem_bot.mp ha]
    simp only [and_self, ite_true]
  dpow_one {a} ha := by
    simp [Ideal.mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [Ideal.mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add n a b ha hb := by
    rw [Ideal.mem_bot.mp ha, Ideal.mem_bot.mp hb, add_zero]
    simp only [true_and, ge_iff_le, tsub_eq_zero_iff_le, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · symm
      apply sum_eq_zero
      intro i hi
      simp only [mem_antidiagonal] at hi
      split_ifs with h2 h1
      · rw [h1, h2, add_zero] at hi
        exfalso
        exact h hi.symm
      · rfl
      · rfl
  dpow_mul n {a x} hx := by
    rw [Ideal.mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  mul_dpow m n {x} hx := by
    rw [Ideal.mem_bot.mp hx]
    simp only [true_and, mul_ite, mul_one, mul_zero, add_eq_zero]
    by_cases hn : n = 0
    · simp only [hn, ite_true, and_true, add_zero, choose_self, cast_one]
    · rw [if_neg hn, if_neg]
      exact not_and_of_not_right (m = 0) hn
  dpow_comp m {n a} hn ha := by
    rw [Ideal.mem_bot.mp ha]
    simp only [true_and, ite_eq_right_iff, _root_.mul_eq_zero, mul_ite, mul_one, mul_zero]
    by_cases hm: m = 0
    · simp only [hm, and_true, true_or, ite_true, uniformBell_zero_left, cast_one]
      rw [if_pos]
      exact fun h => False.elim (hn h)
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]

instance {A : Type*} [CommSemiring A] [DecidableEq A] :
    Inhabited (DividedPowers (⊥ : Ideal A)) := ⟨dividedPowersBot A⟩

/-- The coercion from the divided powers structures to functions -/
instance {A : Type*} [CommSemiring A] (I : Ideal A) :
    CoeFun (DividedPowers I) fun _ => ℕ → A → A := ⟨fun hI => hI.dpow⟩

@[ext]
theorem DividedPowers.ext {A : Type*} [CommSemiring A]
    {I : Ideal A} (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (_ : x ∈ I), hI.dpow n x = hI'.dpow n x) :
    hI = hI' := by
  obtain ⟨hI, h₀, _⟩ := hI
  obtain ⟨hI', h₀', _⟩ := hI'
  simp only [mk.injEq]
  ext n x
  by_cases hx : x ∈ I
  · exact h_eq n hx
  · rw [h₀ hx, h₀' hx]

theorem DividedPowers.coe_injective {A : Type*} [CommSemiring A] (I : Ideal A) :
    Function.Injective (fun (h : DividedPowers I) ↦ (h : ℕ → A → A)) := fun hI hI' h ↦ by
  ext n x
  exact congr_fun (congr_fun h n) x

end DividedPowersDefinition

namespace DividedPowers

open Finset Nat

section BasicLemmas

/- ## Basic lemmas for divided powers -/

variable {A : Type*} [CommSemiring A] {I : Ideal A}

/-- Variant of `DividedPowers.dpow_add` with a sum on `range (n + 1)` -/
theorem dpow_add' (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    hI.dpow n (x + y) = (range (n + 1)).sum fun k => hI.dpow k x * hI.dpow (n - k) y := by
  rw [hI.dpow_add n hx hy, sum_antidiagonal_eq_sum_range_succ_mk]

/-- The exponential series of an element in the context of divided powers,
`Σ (dpow n a) X ^ n` -/
def exp (hI : DividedPowers I) (a : A) :=
  PowerSeries.mk fun n => hI.dpow n a

theorem exp_add_aux (dp : ℕ → A → A) {a b : A} -- (ha : a ∈ I) (hb : b ∈ I) :
    (dp_add : ∀ n, dp n (a + b) = (antidiagonal n).sum fun k ↦ dp k.1 a * dp k.2 b) :
    PowerSeries.mk (fun n ↦ dp n (a + b)) =
      (PowerSeries.mk fun n ↦ dp n a) * (PowerSeries.mk fun n ↦ dp n b) := by
  ext n
  simp only [exp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, dp_add n,
    sum_antidiagonal_eq_sum_range_succ_mk]

theorem exp_add (hI : DividedPowers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    hI.exp (a + b) = hI.exp a * hI.exp b := by
  ext n
  simp only [exp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, hI.dpow_add n ha hb]

variable (hI : DividedPowers I)

/- ## Rewriting lemmas -/

theorem dpow_smul (n : ℕ) (a : A) {x : A} (hx : x ∈ I) :
    hI.dpow n (a • x) = a ^ n • hI.dpow n x := by
  simp only [smul_eq_mul, hI.dpow_mul, hx]

theorem dpow_mul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
    hI.dpow n (a * x) = hI.dpow n a * x ^ n := by
  rw [mul_comm, hI.dpow_mul n ha, mul_comm]

theorem dpow_smul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
    hI.dpow n (a • x) = hI.dpow n a • x ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right n ha, smul_eq_mul]

theorem factorial_mul_dpow_eq_pow (n : ℕ) (x : A) (hx : x ∈ I) :
    (n.factorial : A) * hI.dpow n x = x ^ n := by
  induction n with
  | zero => rw [factorial_zero, cast_one, one_mul, pow_zero, hI.dpow_zero hx]
  | succ n ih =>
    rw [factorial_succ, mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← choose_symm_add, cast_mul, mul_assoc,
      ← hI.mul_dpow n 1 hx, ← mul_assoc, ih, hI.dpow_one hx, pow_succ, mul_comm]

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_mul n I.zero_mem,
    zero_pow hn, zero_mul, zero_mul]

/-- If an element of a divided power ideal is killed by multiplication
by some nonzero integer `n`, then its `n`th power is zero.

Proposition 1.2.7 of [Berthelot-1974], part (i). -/
theorem nilpotent_of_mem_dpIdeal {n : ℕ} (hn : n ≠ 0) (hnI : ∀ {y} (_ : y ∈ I), n • y = 0)
    (hI : DividedPowers I) {x} (hx : x ∈ I) :
    x ^ n = 0 := by
  have h_fac : (n.factorial : A) * hI.dpow n x =
    n • ((n - 1).factorial : A) * hI.dpow n x := by
    rw [nsmul_eq_mul, ← cast_mul, mul_factorial_pred (Nat.pos_of_ne_zero hn)]
  rw [← factorial_mul_dpow_eq_pow hI _ _ hx, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))

/-- If J is another ideal of A with divided powers,
then the divided powers of I and J coincide on I • J

[Berthelot-1974], 1.6.1 (ii) -/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} {a : A} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [Algebra.id.smul_eq_mul, hJ.dpow_mul n hb, mul_comm a b, hI.dpow_mul n ha, ←
      hJ.factorial_mul_dpow_eq_pow n b hb, ← hI.factorial_mul_dpow_eq_pow n a ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy),
      hJ.dpow_add n (Ideal.mul_le_left hx) (Ideal.mul_le_left hy)]
    apply sum_congr rfl
    intro k _
    rw [hx', hy']

/-- A product of divided powers is a multinomial coefficient times the divided power

[Roby-1965], formula (III') -/
theorem prod_dpow {ι : Type*} {s : Finset ι} (n : ι → ℕ) {a : A} (ha : a ∈ I) :
    (s.prod fun i => hI.dpow (n i) a) = multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, multinomial_empty, cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert hi hrec =>
    rw [prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n _) a),
      mul_assoc, mul_dpow _ _ _ ha, ← sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [multinomial_insert hi, mul_comm, cast_mul, sum_insert hi]

-- TODO : can probably be simplified using `DividedPowers.exp`

/-- Lemma towards `dpow_sum` when we only have partial information on a divided power ideal

See also `dpow_sum_aux'` for a more general result-/
theorem dpow_sum_aux (dpow : ℕ → A → A)
    (dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1)
    (dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
      dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dpow n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => dpow (Multiset.count i k) (x i) := by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with -- a s ha ih
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, cast_one]
    · rw [dpow_eval_zero hn, eq_comm, ← cast_zero]
      apply congr_arg
      rw [card_eq_zero, sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi => hx i (mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add n (hx a (mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ => m.filterNe a)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        simp only [succ_eq_add_one, mem_sym_iff, mem_insert, Sym.mem_fill_iff]
        simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
        intro b
        apply Or.imp (fun h ↦ h.2) (fun h ↦ hm b h))
      (fun m _ => m.fill_filterNe a)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← Sym.fill_filterNe a m, Sym.coe_fill]
      simp only [Multiset.count_add, add_right_eq_self, Multiset.count_eq_zero,
        Sym.mem_coe, Sym.mem_replicate, not_and]
      exact fun _ => ne_of_mem_of_not_mem hi ha
    · intro m hm
      convert sym_filterNe_mem a hm
      rw [erase_insert ha]
    -- explicit arguments above rather than m.fill_filter_ne a
    -- adjust once multinomial has been incorporated to mathlib

/-- A generic “multinomial” theorem for divided powers — but without multinomial coefficients
  — using only `dpow_zero`, `dpow_add` and `dpow_eval_zero`

  It is more difficult to apply than `dpow_sum_aux` because of necessary coercions. -/
theorem dpow_sum_aux' {M D : Type*} [AddCommMonoid M] [CommSemiring D] (dp : ℕ → M → D)
    (dpow_zero : ∀ x, dp 0 x = 1)
    (dpow_add : ∀ n x y, dp n (x + y) =
      (antidiagonal n).sum fun (k, l) => dp k x * dp l y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dp n 0 = 0)
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → M} (n : ℕ) :
    dp n (s.sum x) =
      (s.sym n).sum fun k => s.prod fun i => dp (Multiset.count i k) (x i) := by
  simp only [sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction_on generalizing n with
  | empty =>
    rw [sum_empty]
    by_cases hn : n = 0
    · rw [hn]
      haveI : Unique (Sym ι 0) := Sym.uniqueZero
      rw [dpow_zero, sum_unique_nonempty, prod_empty]
      simp only [zero_eq, sym_zero, singleton_nonempty]
    · rw [dpow_eval_zero hn, eq_comm]
      convert sum_empty
      rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    simp_rw [sum_insert ha, dpow_add n, sum_range, ih, mul_sum, sum_sigma', eq_comm]
    apply sum_bij'
      (fun m _ => Sym.filterNe a m)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
          rw [mem_sym_iff]
          intro i hi
          rw [Sym.mem_fill_iff] at hi
          cases hi with
          | inl hi =>
            rw [hi.2]
            apply mem_insert_self
          | inr hi =>
            simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
            exact mem_insert_of_mem (hm i hi))
        (fun m _ => Sym.fill_filterNe a _)
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [prod_insert ha]
      apply congr_arg₂ _ rfl
      apply prod_congr rfl
      intro i hi
      apply congr_arg₂ _ _ rfl
      conv_lhs => rw [← Sym.fill_filterNe a m, Sym.coe_fill]
      simp only [Multiset.count_add, add_right_eq_self, Multiset.count_eq_zero,
        Sym.mem_coe, Sym.mem_replicate, not_and]
      exact fun _ => ne_of_mem_of_not_mem hi ha
    · intro m hm
      convert sym_filterNe_mem a hm
      rw [erase_insert ha]
    -- explicit arguments above rather than m.fill_filter_ne a
    -- adjust once multinomial has been incorporated to mathlib

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_sum {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → A}
    (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    hI.dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => hI.dpow (Multiset.count i k) (x i) := by
  refine dpow_sum_aux hI.dpow ?_ ?_ ?_ hx n
  · intro x
    exact hI.dpow_zero
  · intro n x y hx hy
    rw [hI.dpow_add n hx hy,
      sum_antidiagonal_eq_sum_range_succ (fun k l ↦ hI.dpow k x * hI.dpow l y)]
  · intro n hn
    exact hI.dpow_eval_zero hn

end BasicLemmas

section Equiv
/- ## Relation of divided powers with ring equivalences -/

variable {A B : Type*} [CommRing A] {I : Ideal A} [CommRing B] {J : Ideal B}
  {e : A ≃+* B} (h : I.map e = J)

/-- Transfer divided powers under an equivalence -/
def ofRingEquiv (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null {n} {x} hx := by
    rw [AddEquivClass.map_eq_zero_iff, hI.dpow_null]
    rwa [Ideal.symm_apply_mem_of_equiv_iff, h]
  dpow_zero {x} hx := by
    rw [MulEquivClass.map_eq_one_iff, hI.dpow_zero]
    rwa [Ideal.symm_apply_mem_of_equiv_iff, h]
  dpow_one {x} hx := by
    simp only
    rw [dpow_one, RingEquiv.apply_symm_apply]
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_mem {n} {x} hn hx := by
    simp only
    rw [← h, I.apply_mem_of_equiv_iff]
    apply hI.dpow_mem hn
    rwa [I.symm_apply_mem_of_equiv_iff, h]
  dpow_add n {x y} hx hy:= by
    simp only [map_add]
    rw [hI.dpow_add n (Ideal.symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))
        (Ideal.symm_apply_mem_of_equiv_iff.mpr (h ▸ hy))]
    simp only [map_sum, map_mul]
  dpow_mul n {a x} hx := by
    simp only [map_mul]
    rw [hI.dpow_mul n (Ideal.symm_apply_mem_of_equiv_iff.mpr (h ▸ hx))]
    rw [map_mul, map_pow]
    simp only [RingEquiv.apply_symm_apply]
  mul_dpow m n {x} hx := by
    simp only
    rw [← map_mul, hI.mul_dpow, map_mul]
    · simp only [map_natCast]
    · rwa [Ideal.symm_apply_mem_of_equiv_iff, h]
  dpow_comp m {n x} hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp _ hn]
    · simp only [map_mul, map_natCast]
    · rwa [Ideal.symm_apply_mem_of_equiv_iff, h]

@[simp]
theorem ofRingEquiv_dpow (hI : DividedPowers I) (n : ℕ) (b : B) :
    (ofRingEquiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

theorem ofRingEquiv_dpow_apply (hI : DividedPowers I) (n : ℕ) (a : A) :
    (ofRingEquiv h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp

/-- Transfer divided powers under an equivalence (Equiv version) -/
def equiv : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv h
  invFun := ofRingEquiv (show Ideal.map e.symm J = I by rw [← h]; exact I.map_of_equiv e)
  left_inv := fun hI ↦ by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ ↦ by ext n b; simp [ofRingEquiv]

theorem equiv_apply (hI : DividedPowers I) (n : ℕ) (b : B) :
    (equiv h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

/-- Variant of `DividedPowers.equiv_apply` -/
theorem equiv_apply' (hI : DividedPowers I) (n : ℕ) (a : A) :
    (equiv h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_dpow_apply h hI n a

end Equiv

end DividedPowers

