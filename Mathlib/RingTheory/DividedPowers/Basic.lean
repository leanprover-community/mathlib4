/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández
-/

-- import .DividedPowers.ForMathlib.AlgebraLemmas

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Mchoose

/-! # Divided powers

Let `A` be a commutative (semi)ring and `I` be an ideal of `A`.
A *divided power* structure on `I` is the datum of operations `dpow : ℕ → I → A`
satisfying relations that model the intuitive formula `dpow n a = a ^ n / n.factorial` and
collected by the structure `DividedPowers`.

To avoid coercions, we rather consider `dpow : ℕ → A → A`, extended by 0.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

## Discussion

* In practice, one often has a single such structure to handle on a given ideal,
but several ideals on the same ring might be considered.
Without any explicit mention of the ideal, it is not clear whether such structures
should be provided as instances.

* We do not provide any notation such as `a ^[n]` for `dpow a n`.

-/


section DividedPowersDefinition

open Finset Nat

/-- The divided power structure on an ideal I of a commutative ring A -/
@[ext]
structure DividedPowers {A : Type*} [CommSemiring A] (I : Ideal A) where
  dpow : ℕ → A → A
  dpow_null : ∀ {n x} (_ : x ∉ I), dpow n x = 0
  dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1
  dpow_one : ∀ {x} (_ : x ∈ I), dpow 1 x = x
  dpow_mem : ∀ {n x} (_ : n ≠ 0) (_ : x ∈ I), dpow n x ∈ I
  dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
    dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y
  dpow_smul : ∀ (n) {a : A} {x} (_ : x ∈ I),
    dpow n (a * x) = a ^ n * dpow n x
  dpow_mul : ∀ (m n) {x} (_ : x ∈ I),
    dpow m x * dpow n x = choose (m + n) m * dpow (m + n) x
  dpow_comp : ∀ (m) {n x} (_ : n ≠ 0) (_ : x ∈ I),
    dpow m (dpow n x) = mchoose m n * dpow (m * n) x

-- MI: Shouldn't this be renames?
def dividedPowersBot (A : Type _) [CommSemiring A] [DecidableEq A] : DividedPowers (⊥ : Ideal A)
    where
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
    simp only [and_false, ite_false]
    rw [Ideal.mem_bot.mp ha]
  dpow_mem {n a} hn _ := by
    simp only [Ideal.mem_bot, ite_eq_right_iff, and_imp]
    exact fun _ a => False.elim (hn a)
  dpow_add n a b ha hb := by
    rw [Ideal.mem_bot.mp ha, Ideal.mem_bot.mp hb, add_zero]
    simp only [true_and, ge_iff_le, tsub_eq_zero_iff_le, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · simp [h]
    · apply symm
      apply Finset.sum_eq_zero
      intro i hi
      simp only [mem_antidiagonal] at hi
      split_ifs with h2 h1
      · rw [h1, h2, add_zero] at hi
        exfalso
        exact h hi.symm
      · rfl
      · rfl
  dpow_smul n {a x} hx := by
    rw [Ideal.mem_bot.mp hx]
    simp only [mul_zero, true_and, mul_ite, mul_one]
    by_cases hn : n = 0
    · rw [if_pos hn, hn, if_pos rfl, _root_.pow_zero]
    · simp only [if_neg hn]
  dpow_mul m n {x} hx := by
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
    · simp only [hm, and_true, true_or, ite_true, mchoose_zero, cast_one]
      rw [if_pos]
      exact fun h => False.elim (hn h)
    · simp only [hm, and_false, ite_false, false_or, if_neg hn]
#align divided_powers_bot dividedPowersBot

instance {A : Type _} [CommSemiring A] [DecidableEq A] :
  Inhabited (DividedPowers (⊥ : Ideal A)) := ⟨dividedPowersBot A⟩

instance {A : Type _} [CommSemiring A] (I : Ideal A) :
  CoeFun (DividedPowers I) fun _ => ℕ → A → A := ⟨fun hI => hI.dpow⟩

theorem coe_to_fun_apply {A : Type _} [CommSemiring A]
  (I : Ideal A) (hI : DividedPowers I) (n : ℕ) (a : A) : hI n a = hI.dpow n a := rfl
#align coe_to_fun_apply coe_to_fun_apply

structure dpRing (A : Type _) extends CommSemiring A where
  dpIdeal : Ideal A
  dividedPowers : DividedPowers dpIdeal
#align pd_ring dpRing

instance {A : Type _} [CommSemiring A] [DecidableEq A] : Inhabited (dpRing A)
  where default :=
  { toCommSemiring := inferInstance
    dpIdeal := ⊥
    dividedPowers := dividedPowersBot A }

end DividedPowersDefinition

namespace DividedPowers

section BasicLemmas

variable {A : Type _} [CommSemiring A] {I : Ideal A}

def dpow_add' (hI : DividedPowers I) (n : ℕ) {x y : A} (hx : x ∈ I) (hy : y ∈ I):
    hI.dpow n (x + y) = (Finset.range (n + 1)).sum fun k => hI.dpow k x * hI.dpow (n - k) y := by
  rw [hI.dpow_add n hx hy, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

def dpowExp (hI : DividedPowers I) (a : A) :=
  PowerSeries.mk fun n => hI.dpow n a
#align divided_powers.dpow_exp DividedPowers.dpowExp

theorem add_dpowExp (hI : DividedPowers I) {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    hI.dpowExp (a + b) = hI.dpowExp a * hI.dpowExp b := by
  ext n
  simp only [dpowExp, PowerSeries.coeff_mk, PowerSeries.coeff_mul, hI.dpow_add n ha hb,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
#align divided_powers.add_dpow_exp DividedPowers.add_dpowExp

theorem eq_of_eq_on_ideal (hI : DividedPowers I) (hI' : DividedPowers I)
    (h_eq : ∀ (n : ℕ) {x : A} (_ : x ∈ I), hI.dpow n x = hI'.dpow n x) : hI = hI' := by
  ext n x
  by_cases hx : x ∈ I
  · exact h_eq n hx
  · rw [hI.dpow_null hx, hI'.dpow_null hx]
#align divided_powers.eq_of_eq_on_ideal DividedPowers.eq_of_eq_on_ideal

/- noncomputable
def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) :
  ℕ → A → A := λ n,
  function.extend
    (λ (a : I), a.val)
    (λ a, power_series.coeff A n (ε a))
    (λ (a :A) , (0 : A))

-- Golfed version of definition
noncomputable def dpow_of_dpow_exp (I : ideal A) (ε : I → power_series A) : ℕ → A → A :=
λ n, function.extend (λ (a : I), (a : A)) (λ (a : I), power_series.coeff A n (ε a)) 0

def divided_powers_of_dpow_exp (I : ideal A) (ε : I → power_series A)
  (hε_add : ∀ (a b : I), ε(a + b) = ε(a) * ε(b))
  (hε_zero : ε(0) = 1) -/
variable (hI : DividedPowers I)

-- Rewriting lemmas
theorem dpow_smul' (n : ℕ) (a : A) {x : A} (hx : x ∈ I) :
  hI.dpow n (a • x) = a ^ n • hI.dpow n x := by
  simp only [smul_eq_mul, hI.dpow_smul, hx]
#align divided_powers.dpow_smul' DividedPowers.dpow_smul'

theorem dpow_mul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
  hI.dpow n (a * x) = hI.dpow n a * x ^ n := by
  rw [mul_comm, hI.dpow_smul n ha, mul_comm]
#align divided_powers.dpow_mul_right DividedPowers.dpow_mul_right

theorem dpow_smul_right (n : ℕ) {a : A} (ha : a ∈ I) (x : A) :
  hI.dpow n (a • x) = hI.dpow n a • x ^ n := by
  rw [smul_eq_mul, hI.dpow_mul_right n ha, smul_eq_mul]
#align divided_powers.dpow_smul_right DividedPowers.dpow_smul_right

theorem factorial_mul_dpow_eq_pow (n : ℕ) (x : A) (hx : x ∈ I) :
    (n.factorial : A) * hI.dpow n x = x ^ n := by
  induction n with
  | zero => rw [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero, hI.dpow_zero hx]
  | add_one n ih =>
    rw [Nat.factorial_succ, mul_comm (n + 1)]
    nth_rewrite 1 [← (n + 1).choose_one_right]
    rw [← Nat.choose_symm_add, Nat.cast_mul, mul_assoc,
      ← hI.dpow_mul n 1 hx, ← mul_assoc, ih, hI.dpow_one hx, pow_succ', mul_comm]
#align divided_powers.factorial_mul_dpow_eq_pow DividedPowers.factorial_mul_dpow_eq_pow

theorem dpow_eval_zero {n : ℕ} (hn : n ≠ 0) : hI.dpow n 0 = 0 := by
  rw [← MulZeroClass.mul_zero (0 : A), hI.dpow_smul n I.zero_mem,
    zero_pow hn, zero_mul, zero_mul]
#align divided_powers.dpow_eval_zero DividedPowers.dpow_eval_zero

/-- Proposition 1.2.7 of [B74], part (i). -/
theorem nilpotent_of_mem_dpIdeal (hI : DividedPowers I) {n : ℕ} (hn : n ≠ 0)
    (hnI : ∀ {y : A} (_ : y ∈ I), n • y = 0) {x : A} (hx : x ∈ I) : x ^ n = 0 :=
  by
  have h_fac : (n.factorial : A) * hI.dpow n x =
    n • ((n - 1).factorial : A) * hI.dpow n x := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_factorial_pred (Nat.pos_of_ne_zero hn)]
  rw [← factorial_mul_dpow_eq_pow hI _ _ hx, h_fac, smul_mul_assoc]
  exact hnI (I.mul_mem_left ((n - 1).factorial : A) (hI.dpow_mem hn hx))
#align divided_powers.nilpotent_of_pd_ideal_mem DividedPowers.nilpotent_of_mem_dpIdeal
-- DividedPowers.nilpotent_of_pd_ideal_mem

/-- If J is another ideal of A with divided powers,
then the divided powers of I and J coincide on I • J
(Berthelot, 1.6.1 (ii))-/
theorem coincide_on_smul {J : Ideal A} (hJ : DividedPowers J) {n : ℕ} {a : A} (ha : a ∈ I • J) :
    hI.dpow n a = hJ.dpow n a := by
  induction ha using Submodule.smul_induction_on' generalizing n with
  | smul a ha b hb =>
    rw [Algebra.id.smul_eq_mul, hJ.dpow_smul n hb, mul_comm a b, hI.dpow_smul n ha, ←
      hJ.factorial_mul_dpow_eq_pow n b hb, ← hI.factorial_mul_dpow_eq_pow n a ha]
    ring
  | add x hx y hy hx' hy' =>
    rw [hI.dpow_add n (Ideal.mul_le_right hx) (Ideal.mul_le_right hy),
      hJ.dpow_add n (Ideal.mul_le_left hx) (Ideal.mul_le_left hy)]
    apply Finset.sum_congr rfl
    intro k _
    rw [hx', hy']
#align divided_powers.coincide_on_smul DividedPowers.coincide_on_smul

open Finset

-- Rob65, formula (III')
/-- A product of divided powers is a multinomial coefficient times the divided power-/
theorem mul_dpow {ι : Type _} {s : Finset ι} (n : ι → ℕ) {a : A} (ha : a ∈ I) :
    (s.prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [prod_empty, Nat.multinomial_empty, Nat.cast_one, sum_empty, one_mul]
    rw [hI.dpow_zero ha]
  | insert hi hrec =>
    rw [Finset.prod_insert hi, hrec, ← mul_assoc, mul_comm (hI.dpow (n _) a),
      mul_assoc, dpow_mul _ _ _ ha, ← Finset.sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [Nat.multinomial_insert hi, mul_comm, Nat.cast_mul, Finset.sum_insert hi]
#align divided_powers.mul_dpow DividedPowers.mul_dpow

example {α : Type*}  {n : ℕ} [DecidableEq α] (a : α) (m : Sym α n) (i : α) (hi : i ≠ a) :
    Multiset.count i (Sym.filterNe a m).snd = Multiset.count i m := by
  conv_rhs => rw [← Sym.fill_filterNe a m]
  dsimp [Sym.fill]
  simp only [Multiset.count_add, self_eq_add_right, Multiset.count_eq_zero, Sym.mem_coe,
    Sym.mem_replicate, ne_eq, not_and]
  exact fun _ => hi

-- A slightly more general result is below but it is awkward to apply it
-- TODO : can probably be simplified using exponential series
-- Also : can it be used to deduce dpow_comp from the rest?
theorem dpow_sum_aux (dpow : ℕ → A → A)
    (dpow_zero : ∀ {x} (_ : x ∈ I), dpow 0 x = 1)
    (dpow_add : ∀ (n) {x y} (_ : x ∈ I) (_ : y ∈ I),
      dpow n (x + y) = (antidiagonal n).sum fun k => dpow k.1 x * dpow k.2 y)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dpow n 0 = 0)
    {ι : Type _} [DecidableEq ι] {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) (n : ℕ) :
    dpow n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => dpow (Multiset.count i k) (x i) := by
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction generalizing n with -- a s ha ih
  | empty =>
    simp only [sum_empty, prod_empty, sum_const, nsmul_eq_mul, mul_one]
    by_cases hn : n = 0
    · rw [hn]
      rw [dpow_zero I.zero_mem]
      simp only [sym_zero, card_singleton, Nat.cast_one]
    · rw [dpow_eval_zero hn]
      apply symm
      rw [← Nat.cast_zero]
      apply congr_arg
      rw [card_eq_zero]
      rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    have hx' : ∀ i, i ∈ s → x i ∈ I := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    simp_rw [sum_insert ha,
      dpow_add n (hx a (Finset.mem_insert_self a s)) (I.sum_mem fun i => hx' i),
      sum_range, ih hx', mul_sum, sum_sigma']
    apply symm
    apply sum_bij'
      (fun m _ => Sym.filterNe a m)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => Finset.mem_sigma.2 ⟨mem_univ _, _⟩)
      (fun m hm => by
        rw [mem_sym_iff]
        intro i hi
        rw [Sym.mem_fill_iff] at hi
        cases hi with
        | inl hi =>
          rw [hi.2]
          exact mem_insert_self a s
        | inr hi =>
          simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
          exact mem_insert_of_mem (hm i hi))
      (fun m _ => Sym.fill_filterNe a _ )
    · intro m hm
      simp only [mem_sigma, mem_univ, mem_sym_iff, true_and] at hm
      exact Sym.filter_ne_fill a m fun a_1 => ha (hm a a_1)
    · intro m hm
      simp only [mem_sym_iff, mem_insert] at hm
      rw [Finset.prod_insert ha]
      apply congr_arg₂ _ rfl
      apply Finset.prod_congr rfl
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
    #align divided_powers.dpow_sum_aux DividedPowers.dpow_sum_aux

/- (Finset.sum (Finset.sigma (antidiagonal n) fun a ↦ Finset.sym s a.2) fun x_1 ↦
    dp x_1.fst.1 (x a) * Finset.prod s fun i ↦ dp (Multiset.count i ↑x_1.snd) (x i)) =
  Finset.sum (Finset.sym (insert a s) n) fun k ↦ Finset.prod (insert a s) fun i ↦ dp (Multiset.count i ↑k) (x i) -/


/-- A generic “multinomial” theorem for divided powers — but without multinomial coefficients
  — using only dpow_zero, dpow_add and dpow_eval_zero  -/
theorem dpow_sum_aux' {M D : Type _} [AddCommMonoid M] [CommSemiring D] (dp : ℕ → M → D)
    (dpow_zero : ∀ x, dp 0 x = 1)
    (dpow_add : ∀ n x y, dp n (x + y) =
      (antidiagonal n).sum fun (k, l) => dp k x * dp l y)
    --  (dpow_smul : ∀ {n a x}, dp n (a • x) = a ^ n • dp n x)
    (dpow_eval_zero : ∀ {n : ℕ} (_ : n ≠ 0), dp n 0 = 0)
    {ι : Type _} [DecidableEq ι] {s : Finset ι} {x : ι → M} (n : ℕ) :
    dp n (s.sum x) =
      (Finset.sym s n).sum fun k => s.prod fun i => dp (Multiset.count i k) (x i) := by
  simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at dpow_add
  induction s using Finset.induction_on generalizing n with -- a s ha ih
  | empty =>
    rw [sum_empty]
    by_cases hn : n = 0
    · rw [hn]
      haveI : Unique (Sym ι Nat.zero) := Sym.uniqueZero
      rw [dpow_zero, sum_unique_nonempty, prod_empty]
      simp only [Nat.zero_eq, sym_zero, singleton_nonempty]
    · rw [dpow_eval_zero hn]
      apply symm
      convert Finset.sum_empty
      rw [sym_eq_empty]
      exact ⟨hn, rfl⟩
  | @insert a s ha ih =>
    simp_rw [sum_insert ha, dpow_add n, sum_range, ih, mul_sum, sum_sigma']
    apply symm
    apply sum_bij'
      (fun m _ => Sym.filterNe a m)
      (fun m _ => m.2.fill a m.1)
      (fun m hm => Finset.mem_sigma.2 ⟨mem_univ _, _⟩)
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
      rw [Finset.prod_insert ha]
      apply congr_arg₂ _ rfl
      apply Finset.prod_congr rfl
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

    #align divided_powers.dpow_sum_aux' DividedPowers.dpow_sum_aux'

/-- A “multinomial” theorem for divided powers — without multinomial coefficients -/
theorem dpow_sum {ι : Type _} [DecidableEq ι] {s : Finset ι} {x : ι → A} (hx : ∀ i ∈ s, x i ∈ I) :
    ∀ n : ℕ,
      hI.dpow n (s.sum x) =
        (Finset.sym s n).sum fun k => s.prod fun i => hI.dpow (Multiset.count i k) (x i) := by
  refine' dpow_sum_aux hI.dpow _ ?_ _ hx
  · intro x
    exact hI.dpow_zero
  · intro n x y hx hy
    rw [hI.dpow_add n hx hy,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l ↦ hI.dpow k x * hI.dpow l y)]
  · intro n hn
    exact hI.dpow_eval_zero hn
#align divided_powers.dpow_sum DividedPowers.dpow_sum

/-
  let x' : s → I := λ i, ⟨x i, hx i i.prop⟩,
  haveI : fintype s, exact fintype_of_option,
  suffices :  s.sum x = coe(finset.univ.sum x'),  rw this,
  intro n,
--  simp only [submodule.coe_sum, submodule.coe_mk],
  have := @dpow_sum_aux I A _ _ (λ (n : ℕ) (a : I), hI.dpow n a) (λ x, hI.dpow_zero x.prop) _ _
    s _ finset.univ x' n,

  -/
theorem prod_dpow_self {ι : Type _} {s : Finset ι} {n : ι → ℕ} (a : A) (ha : a ∈ I) :
    (s.prod fun i => hI.dpow (n i) a) = Nat.multinomial s n * hI.dpow (s.sum n) a := by
  classical
  induction' s using Finset.induction with i s hi ih
  · rw [Finset.prod_empty, Finset.sum_empty, hI.dpow_zero ha, Nat.multinomial_empty, Nat.cast_one,
      mul_one]
  · rw [Finset.prod_insert hi, ih, ← mul_assoc, mul_comm (hI.dpow _ a), mul_assoc,
      hI.dpow_mul _ _ ha, ← Finset.sum_insert hi, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [mul_comm, Nat.multinomial_insert hi, Finset.sum_insert hi, Nat.cast_mul]
#align divided_powers.prod_dpow_self DividedPowers.prod_dpow_self

end BasicLemmas

section Equiv

variable {A B : Type*} [CommRing A] {I : Ideal A} [CommRing B] {J : Ideal B}
  (e : A ≃+* B) (h : I.map e = J)

example : I.map e = I.comap e.symm := by
  exact Eq.symm (Ideal.comap_symm I e)

#check Ideal.map_symm

theorem mem_aux (b : B) : e.symm b ∈ I ↔ b ∈ J := by
  simp only [← h, ← Ideal.comap_symm]
  rfl

theorem mem_aux' (a : A) : e a ∈ J ↔ a ∈ I := by
  rw [← mem_aux e h]
  simp only [RingEquiv.symm_apply_apply]

/-- Transfer divided powers under an equivalence -/
def ofRingEquiv (hI : DividedPowers I) : DividedPowers J where
  dpow n b := e (hI.dpow n (e.symm b))
  dpow_null {n} {x} hx := by
    rw [AddEquivClass.map_eq_zero_iff, hI.dpow_null]
    rwa [mem_aux e h]
  dpow_zero {x} hx := by
    rw [MulEquivClass.map_eq_one_iff, hI.dpow_zero]
    rwa [mem_aux e h]
  dpow_one {x} hx := by
    simp only
    rw [dpow_one, RingEquiv.apply_symm_apply]
    rwa [mem_aux e h]
  dpow_mem {n} {x} hn hx := by
    simp only
    rw [mem_aux' e h]
    apply hI.dpow_mem hn
    rw [mem_aux e h]
    exact hx
  dpow_add n {x y} hx hy:= by
    simp only [map_add]
    rw [hI.dpow_add n ((mem_aux e h x).mpr hx) ((mem_aux e h y).mpr hy)]
    simp only [map_sum, map_mul]
  dpow_smul n {a x} hx := by
    simp only [map_mul]
    rw [hI.dpow_smul n ((mem_aux e h x).mpr hx)]
    rw [map_mul, map_pow]
    simp only [RingEquiv.apply_symm_apply]
  dpow_mul m n {x} hx := by
    simp only
    rw [← map_mul, hI.dpow_mul, map_mul]
    simp only [map_natCast]
    exact (mem_aux e h x).mpr hx
  dpow_comp m {n x} hn hx := by
    simp only [RingEquiv.symm_apply_apply]
    rw [hI.dpow_comp _ hn]
    simp only [map_mul, map_natCast]
    exact (mem_aux e h x).mpr hx

@[simp]
theorem ofRingEquiv_eq (hI : DividedPowers I) (n : ℕ) (b : B) :
    (ofRingEquiv e h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

theorem ofRingEquiv_eq' (hI : DividedPowers I) (n : ℕ) (a : A) :
    (ofRingEquiv e h hI).dpow n (e a) = e (hI.dpow n a) := by
  simp

/-- Transfer divided powers under an equivalence (Equiv version) -/
def equiv : DividedPowers I ≃ DividedPowers J where
  toFun := ofRingEquiv e h
  invFun := ofRingEquiv e.symm (by
    rw [← h]
    change Ideal.map e.symm.toRingHom (I.map e.toRingHom) = I
    rw [Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, Ideal.map_id])
  left_inv := fun hI ↦ by ext n a; simp [ofRingEquiv]
  right_inv := fun hJ ↦ by ext n b; simp [ofRingEquiv]

def equiv_apply (hI : DividedPowers I) (n : ℕ) (b : B) :
    (equiv e h hI).dpow n b = e (hI.dpow n (e.symm b)) := rfl

def equiv_apply' (hI : DividedPowers I) (n : ℕ) (a : A) :
    (equiv e h hI).dpow n (e a) = e (hI.dpow n a) :=
  ofRingEquiv_eq' e h hI n a

end Equiv


end DividedPowers

/- Comparison with Berthelot, Coho. cristalline

1.1 : done
1.2.1 : follows from 1.2.7 - done (for ℚ-algebras).
1.2.2 (*) : To be added
1.2.4 : To be added if Cohen/Witt vectors rings exist
1.2.7 (M) : done
1.3 (dp -morphism) : done
1.3.1 : To be added (needs colimits of rings)

1.4 : To be added, but difficult
1.5.: depends on 1.4

1.6 : sub-dp-ideal : done
1.6.1 Done !
1.6.2 : Done : dpow_quot]
1.6.4 (A) : to be added
(should we add the remark on page 33)
1.6.5 (A): to be added

1.7 : tensor product, see Roby

1.8 (M). Done!


PRs :
 (M) : ring_inverse, tsub_tsub - DONE
 (A) : submodule_induction, function.extend_apply_first - DONE

Delete obsolete versions
 (A) : rewrite_4_sums -- Done, I think, but how could we simplify these lemmas?

(A) Simplify,
  remove not_eq_or_aux (see REMOVE or MOVE) -- DONE
  Prove uniqueness of dp-structure when possible
    (ideal_add [Done], dpow_quot [Done])
(M) Complete the lattice structure

-/
example (M : Type _) [AddMonoid M] : AddMonoid (WithTop M) := by refine' WithTop.addMonoid

/- Roby (1965):
 - Pregraded algebra (using mathlib's graded_algebra) - with_top unit (later, if needed)
 - Tensor product of graded algebras is a graded algebra
 - Add III' explicitly.
 - Proposition 1 -- I think this is essentially Lemma 3.6 of [BO].
 - Proposition 2
 - Proposition 3

 I just noticed that we are using dp and pd in different names, we should pick a convention.
-/
/-
Idea of generalizing the theory to more general divisors systems
modeling x^n/n!, x^n/p^n, etc.
but it is not clear what to consider
Also, not clear it can really be done…

structure divisor_system {R : Type*} [comm_ring R] :=
(dpow_choose : ℕ → ℕ → R)
(dpow_mchoose : ℕ → ℕ → R)
-- (conditions : Prop)
Two options :
1) dpow n x = x^n/(c n)
Examples : c n = n.factorial,  c n = p ^ n
2) dpow n x = x ^ n / (d 1 * d 2 * ... * d n)
Examples : d n = n,  d n = p

dpow n (x + y) = (x+y)^n / c n
 = sum  (n.choose k) x ^(n -k) y ^k / c n
 = sum [(n.choose k) (c k) (c (n-k)) / c n] dpow (n - k) x * dpow k y

  Case 1 : dpow_choose n k = 1 ;  case 2 : dpow_choose n k = choose

dpow m x * dpow n x = x ^ m * x ^ n / c m * c n
  = dpow (m + n) x * (c (n+m) / c m * c n)

   Case 1 : coeff = (n+m).choose m ; Case 2 :  = 1

dpow m (dpow n x) = (x ^n / c n) ^ m / c m = x ^ (m n) / ((c n ^ m) * c m)
 = [ ] * dpow (m n) x
  with [ ] = c (m n)/ (c n)^m (c m)

  Case 1 : [ ] = mchoose m n, case 2 : p^ (-m)

-/
