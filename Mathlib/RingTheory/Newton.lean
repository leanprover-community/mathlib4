import Mathlib.RingTheory.Nilpotent
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Identities
import Mathlib.Data.Polynomial.Derivative

lemma Nat.self_sub_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp only [Nat.zero_eq, pow_zero, zero_le]
  | succ n ih =>
    rw [pow_succ', two_mul, Nat.succ_eq_add_one]
    apply Nat.add_le_add ih
    exact Nat.one_le_two_pow n

namespace Polynomial

variable {R : Type*} [CommRing R]

variable {P : R[X]} {a b : R}

lemma sub_eval_isNilpotent_of_isNilpotent_sub (h : IsNilpotent (b - a)) :
    IsNilpotent (P.eval b - P.eval a) := by
  have ⟨cj, hc⟩ := evalSubFactor P b a
  rw [hc]
  exact Commute.isNilpotent_mul_right (Commute.all _ _) h

lemma eval_isNilpotent_of_isNilpotent_sub (ha : IsNilpotent (P.eval a))
    (hb : IsNilpotent (b - a)) : IsNilpotent (P.eval b) := by
  rw [← add_sub_cancel'_right (eval a P) (eval b P)]
  exact Commute.isNilpotent_add (Commute.all _ _) ha (sub_eval_isNilpotent_of_isNilpotent_sub hb)

lemma eval_isUnit_of_isNilpotent_sub (ha : IsUnit (P.eval a))
    (hb : IsNilpotent (b - a)) : IsUnit (P.eval b) := by
  rw [← add_sub_cancel'_right (P.eval a) (P.eval b)]
  rw [← ha.choose_spec]
  apply Commute.IsNilpotent.add_isUnit _ (Commute.all _ _)
  rw [ha.choose_spec]
  exact sub_eval_isNilpotent_of_isNilpotent_sub hb

namespace Newton

variable (P)

/-- The Newton iteration of P -/
noncomputable
def iterate (a : R) : R :=
  a - (P.eval a) * Ring.inverse ((P.derivative.eval a))

/-- The condition for the Newton iteration to hold -/
def hyp (a : R) := IsNilpotent (P.eval a) ∧ IsUnit (P.derivative.eval a)

variable {P}

noncomputable
def series (ha : IsNilpotent (P.eval a)) : ℕ → {x : R // IsNilpotent (x - a)}
  | 0 => ⟨a, by simp only [sub_self, IsNilpotent.zero]⟩
  | k + 1 => ⟨iterate P (series ha k), by
      rw [iterate, sub_sub, add_comm, ← sub_sub]
      apply Commute.isNilpotent_sub (Commute.all _ _) (series ha k).prop
      apply Commute.isNilpotent_mul_left (Commute.all _ _)
      apply eval_isNilpotent_of_isNilpotent_sub ha (series ha k).prop⟩

lemma eval_div (ha : hyp P a) (k : ℕ) :
    (P.eval a) ^ (2 ^ k) ∣ (P.eval ↑(series ha.1 k)) := by
  induction k with
  | zero => simp only [Nat.zero_eq, pow_zero, pow_one, series, dvd_refl]
  | succ k hk =>
    simp only [series, iterate._eq_1, sub_eq_add_neg, neg_mul_eq_neg_mul]
    have ⟨d, hd⟩ := binomExpansion P (series ha.1 k) (-eval (↑(series ha.1 k)) P * Ring.inverse (eval (↑(series ha.1 k)) (derivative P)))
    rw [hd]
    apply dvd_add
    convert dvd_zero _
    rw [mul_comm, mul_assoc, Ring.inverse_mul_cancel _, mul_one, add_right_neg]
    exact eval_isUnit_of_isNilpotent_sub ha.2 (series ha.1 k).prop
    apply Dvd.dvd.mul_left
    rw [mul_pow, neg_pow]
    simp only [even_two, Even.neg_pow, one_pow, one_mul]
    apply Dvd.dvd.mul_right
    rw [pow_succ', pow_mul]
    exact pow_dvd_pow_of_dvd hk 2

theorem exists_unique (ha : hyp P a) :
    ∃! (b : R), IsNilpotent (b - a) ∧ eval b P = 0 := by
  apply exists_unique_of_exists_of_unique
  · -- Existence
    suffices : ∃ k, P.eval ↑(series ha.1 k) = 0
    obtain ⟨k, hk⟩ := this
    exact ⟨series ha.1 k, (series ha.1 k).prop, hk⟩
    obtain ⟨n, hn⟩ := ha.1
    use n
    rw [← zero_dvd_iff]
    simp_rw [← pow_eq_zero_of_le (Nat.self_sub_two_pow n) hn]
    exact eval_div ha n
  · -- Uniqueness
    intro b c hb hc
    have ⟨u, hu⟩ := binomExpansion P b (c - b)
    simp only [add_sub_cancel'_right, hc.2, hb.2, zero_add, pow_two, ← mul_assoc, ← add_mul] at hu
    apply symm
    rw [← sub_eq_zero]
    rw [eq_comm, ← smul_eq_mul, IsUnit.smul_eq_zero ?_] at hu
    exact hu
    have hb' : IsUnit (eval b (derivative P)) := eval_isUnit_of_isNilpotent_sub ha.2 hb.1
    rw [← hb'.choose_spec]
    apply Commute.IsNilpotent.add_isUnit _ (Commute.all _ _)
    apply Commute.isNilpotent_mul_right (Commute.all _ _)
    rw [← sub_sub_sub_cancel_right c b a]
    exact Commute.isNilpotent_sub (Commute.all _ _) hc.1 hb.1

end Newton

end Polynomial

#exit

/-- The condition for the Newton iteration to hold -/
def newton_ih (a : R) := IsNilpotent (P.eval a) ∧ IsUnit (P.derivative.eval a)

variable {P}

/-- The Newton condition remains satisfied at each iteration -/
lemma ih_newton (h : newton_ih P a) : newton_ih P (newton_iterate P a) := by
  set b := - (P.eval a) * Ring.inverse (P.derivative.eval a) with hb
  have hb' : IsNilpotent b :=
    Commute.isNilpotent_mul_left (Commute.all _ _) (IsNilpotent.neg h.1)
  rw [newton_iterate, sub_eq_add_neg, neg_mul_eq_neg_mul, ← hb]
  constructor
  · have ⟨c, hc⟩ := binomExpansion P a b
    rw [hc]
    apply Commute.isNilpotent_add (Commute.all _ _)
    apply Commute.isNilpotent_add (Commute.all _ _)  h.1
    exact Commute.isNilpotent_mul_right (Commute.all _ _) hb'
    exact Commute.isNilpotent_mul_right (Commute.all _ _) (IsNilpotent.pow_succ 1 hb')
  · have ⟨d, hd⟩ := binomExpansion (derivative P) a b
    rw [hd]
    rw [← h.2.choose_spec, add_assoc]
    apply Commute.IsNilpotent.add_isUnit _ (Commute.all _ _)
    apply Commute.isNilpotent_add (Commute.all _ _)
    exact Commute.isNilpotent_mul_right (Commute.all _ _) hb'
    exact Commute.isNilpotent_mul_right (Commute.all _ _) (IsNilpotent.pow_succ 1 hb')

noncomputable
def newton_series (ha : newton_ih P a) : ℕ → { x : R // newton_ih P x}
  | 0 => ⟨a, ha⟩
  | k + 1 => ⟨newton_iterate P (newton_series ha k), ih_newton (newton_series ha k).prop⟩

lemma sub_newton_nilpotent (ha : newton_ih P a) (k : ℕ) :
    IsNilpotent (a - newton_series ha k) := by
  induction k with
  | zero => simp only [newton_series, sub_self, IsNilpotent.zero]
  | succ k hk =>
    simp only [newton_series, newton_iterate, ← sub_add]
    apply Commute.isNilpotent_add (Commute.all _ _) hk
    exact Commute.isNilpotent_mul_left (Commute.all _ _) (newton_series ha k).prop.1

lemma eval_newton_div (ha : newton_ih P a) (k : ℕ) :
    (P.eval a) ^ (2 ^ k) ∣ (P.eval ↑(newton_series ha k)) := by
  induction k with
  | zero => simp only [Nat.zero_eq, pow_zero, pow_one, newton_series, dvd_refl]
  | succ k hk =>
    -- rcases hk with ⟨c, hc⟩
    simp only [newton_series, newton_iterate._eq_1, sub_eq_add_neg, neg_mul_eq_neg_mul]
    have ⟨d, hd⟩ := binomExpansion P (newton_series ha k) (-eval (↑(newton_series ha k)) P * Ring.inverse (eval (↑(newton_series ha k)) (derivative P)))
    rw [hd]
    apply dvd_add
    convert dvd_zero _
    rw [mul_comm, mul_assoc, Ring.inverse_mul_cancel _, mul_one, add_right_neg]
    exact (newton_series ha k).prop.2
    apply Dvd.dvd.mul_left
    rw [mul_pow, neg_pow]
    simp only [even_two, Even.neg_pow, one_pow, one_mul]
    apply Dvd.dvd.mul_right
    rw [pow_succ', pow_mul]
    exact pow_dvd_pow_of_dvd hk 2

theorem newton_exists (ha : newton_ih P a) : ∃ (b : R), IsNilpotent (a - b) ∧
  eval b P = 0 := by
  suffices : ∃ k, P.eval ↑(newton_series ha k) = 0
  obtain ⟨k, hk⟩ := this
  exact ⟨newton_series ha k, sub_newton_nilpotent ha k, hk⟩
  obtain ⟨n, hn⟩ := ha.1
  use n
  rw [← zero_dvd_iff, ← pow_eq_zero_of_le (self_sub_two_pow n) hn]
  exact eval_newton_div ha n

theorem newton_unique (ha : newton_ih P a) (b c : R)
    (hb : IsNilpotent (a - b) ∧ eval b P = 0) (hc : IsNilpotent (a - c) ∧ eval c P = 0) :
    b = c := by
  have ⟨u, hu⟩ := binomExpansion P b (c - b)
  simp only [add_sub_cancel'_right, hc.2, hb.2, zero_add] at hu

theorem newton_exists_unique (ha : newton_ih P a) :
    ∃! (b : R), IsNilpotent (a - b) ∧ eval b P = 0 := by
  apply exists_unique_of_exists_of_unique

example (a : R) (m n : ℕ) (h : m ≤ n) (ha : a ^ m = 0) : a ^ n = 0 := by
  exact pow_eq_zero_of_le h ha

example (ha : newton_ih P a) :
