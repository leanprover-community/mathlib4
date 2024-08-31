/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Induction

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/



noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R →+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
irreducible_def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e

theorem eval₂_eq_sum {f : R →+* S} {x : S} : p.eval₂ f x = p.sum fun e a => f a * x ^ e := by
  rw [eval₂_def]

theorem eval₂_congr {R S : Type*} [Semiring R] [Semiring S] {f g : R →+* S} {s t : S}
    {φ ψ : R[X]} : f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ := by
  rintro rfl rfl rfl; rfl

@[simp]
theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by
  simp (config := { contextual := true }) only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero,
    mul_one, sum, Classical.not_not, mem_support_iff, sum_ite_eq', ite_eq_left_iff,
    RingHom.map_zero, imp_true_iff, eq_self_iff_true]

@[simp]
theorem eval₂_zero : (0 : R[X]).eval₂ f x = 0 := by simp [eval₂_eq_sum]

@[simp]
theorem eval₂_C : (C a).eval₂ f x = f a := by simp [eval₂_eq_sum]

@[simp]
theorem eval₂_X : X.eval₂ f x = x := by simp [eval₂_eq_sum]

@[simp]
theorem eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = f r * x ^ n := by
  simp [eval₂_eq_sum]

@[simp]
theorem eval₂_X_pow {n : ℕ} : (X ^ n).eval₂ f x = x ^ n := by
  rw [X_pow_eq_monomial]
  convert eval₂_monomial f x (n := n) (r := 1)
  simp

@[simp]
theorem eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x := by
  simp only [eval₂_eq_sum]
  apply sum_add_index <;> simp [add_mul]

@[simp]
theorem eval₂_one : (1 : R[X]).eval₂ f x = 1 := by rw [← C_1, eval₂_C, f.map_one]

@[simp]
theorem eval₂_smul (g : R →+* S) (p : R[X]) (x : S) {s : R} :
    eval₂ g x (s • p) = g s * eval₂ g x p := by
  have A : p.natDegree < p.natDegree.succ := Nat.lt_succ_self _
  have B : (s • p).natDegree < p.natDegree.succ := (natDegree_smul_le _ _).trans_lt A
  rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B] <;>
    simp [mul_sum, mul_assoc]

@[simp]
theorem eval₂_C_X : eval₂ C X p = p :=
  Polynomial.induction_on' p (fun p q hp hq => by simp [hp, hq]) fun n x => by
    rw [eval₂_monomial, ← smul_X_eq_monomial, C_mul']

/-- `eval₂AddMonoidHom (f : R →+* S) (x : S)` is the `AddMonoidHom` from
`R[X]` to `S` obtained by evaluating the pushforward of `p` along `f` at `x`. -/
@[simps]
def eval₂AddMonoidHom : R[X] →+ S where
  toFun := eval₂ f x
  map_zero' := eval₂_zero _ _
  map_add' _ _ := eval₂_add _ _

@[simp]
theorem eval₂_natCast (n : ℕ) : (n : R[X]).eval₂ f x = n := by
  induction n with
  | zero => simp only [eval₂_zero, Nat.cast_zero]
  | succ n ih => rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

@[deprecated (since := "2024-04-17")]
alias eval₂_nat_cast := eval₂_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma eval₂_ofNat {S : Type*} [Semiring S] (n : ℕ) [n.AtLeastTwo] (f : R →+* S) (a : S) :
    (no_index (OfNat.ofNat n : R[X])).eval₂ f a = OfNat.ofNat n := by
  simp [OfNat.ofNat]

variable [Semiring T]

theorem eval₂_sum (p : T[X]) (g : ℕ → T → R[X]) (x : S) :
    (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x := by
  let T : R[X] →+ S :=
    { toFun := eval₂ f x
      map_zero' := eval₂_zero _ _
      map_add' := fun p q => eval₂_add _ _ }
  have A : ∀ y, eval₂ f x y = T y := fun y => rfl
  simp only [A]
  rw [sum, map_sum, sum]

theorem eval₂_list_sum (l : List R[X]) (x : S) : eval₂ f x l.sum = (l.map (eval₂ f x)).sum :=
  map_list_sum (eval₂AddMonoidHom f x) l

theorem eval₂_multiset_sum (s : Multiset R[X]) (x : S) :
    eval₂ f x s.sum = (s.map (eval₂ f x)).sum :=
  map_multiset_sum (eval₂AddMonoidHom f x) s

theorem eval₂_finset_sum (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∑ i ∈ s, g i).eval₂ f x = ∑ i ∈ s, (g i).eval₂ f x :=
  map_sum (eval₂AddMonoidHom f x) _ _

theorem eval₂_ofFinsupp {f : R →+* S} {x : S} {p : R[ℕ]} :
    eval₂ f x (⟨p⟩ : R[X]) = liftNC (↑f) (powersHom S x) p := by
  simp only [eval₂_eq_sum, sum, toFinsupp_sum, support, coeff]
  rfl

theorem eval₂_mul_noncomm (hf : ∀ k, Commute (f <| q.coeff k) x) :
    eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q := by
  rcases p with ⟨p⟩; rcases q with ⟨q⟩
  simp only [coeff] at hf
  simp only [← ofFinsupp_mul, eval₂_ofFinsupp]
  exact liftNC_mul _ _ p q fun {k n} _hn => (hf k).pow_right n

@[simp]
theorem eval₂_mul_X : eval₂ f x (p * X) = eval₂ f x p * x := by
  refine _root_.trans (eval₂_mul_noncomm _ _ fun k => ?_) (by rw [eval₂_X])
  rcases em (k = 1) with (rfl | hk)
  · simp
  · simp [coeff_X_of_ne_one hk]

@[simp]
theorem eval₂_X_mul : eval₂ f x (X * p) = eval₂ f x p * x := by rw [X_mul, eval₂_mul_X]

theorem eval₂_mul_C' (h : Commute (f a) x) : eval₂ f x (p * C a) = eval₂ f x p * f a := by
  rw [eval₂_mul_noncomm, eval₂_C]
  intro k
  by_cases hk : k = 0
  · simp only [hk, h, coeff_C_zero, coeff_C_ne_zero]
  · simp only [coeff_C_ne_zero hk, RingHom.map_zero, Commute.zero_left]

theorem eval₂_list_prod_noncomm (ps : List R[X])
    (hf : ∀ p ∈ ps, ∀ (k), Commute (f <| coeff p k) x) :
    eval₂ f x ps.prod = (ps.map (Polynomial.eval₂ f x)).prod := by
  induction' ps using List.reverseRecOn with ps p ihp
  · simp
  · simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

/-- `eval₂` as a `RingHom` for noncommutative rings -/
@[simps]
def eval₂RingHom' (f : R →+* S) (x : S) (hf : ∀ a, Commute (f a) x) : R[X] →+* S where
  toFun := eval₂ f x
  map_add' _ _ := eval₂_add _ _
  map_zero' := eval₂_zero _ _
  map_mul' _p q := eval₂_mul_noncomm f x fun k => hf <| coeff q k
  map_one' := eval₂_one _ _

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/


section Eval₂

section

variable [Semiring S] (f : R →+* S) (x : S)

theorem eval₂_eq_sum_range :
    p.eval₂ f x = ∑ i ∈ Finset.range (p.natDegree + 1), f (p.coeff i) * x ^ i :=
  _root_.trans (congr_arg _ p.as_sum_range)
    (_root_.trans (eval₂_finset_sum f _ _ x) (congr_arg _ (by simp)))

theorem eval₂_eq_sum_range' (f : R →+* S) {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    eval₂ f x p = ∑ i ∈ Finset.range n, f (p.coeff i) * x ^ i := by
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn]
  intro i
  rw [f.map_zero, zero_mul]

end

section

variable [CommSemiring S] (f : R →+* S) (x : S)

@[simp]
theorem eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
  eval₂_mul_noncomm _ _ fun _k => Commute.all _ _

theorem eval₂_mul_eq_zero_of_left (q : R[X]) (hp : p.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_left hp (q.eval₂ f x)

theorem eval₂_mul_eq_zero_of_right (p : R[X]) (hq : q.eval₂ f x = 0) : (p * q).eval₂ f x = 0 := by
  rw [eval₂_mul f x]
  exact mul_eq_zero_of_right (p.eval₂ f x) hq

/-- `eval₂` as a `RingHom` -/
def eval₂RingHom (f : R →+* S) (x : S) : R[X] →+* S :=
  { eval₂AddMonoidHom f x with
    map_one' := eval₂_one _ _
    map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]
theorem coe_eval₂RingHom (f : R →+* S) (x) : ⇑(eval₂RingHom f x) = eval₂ f x :=
  rfl

theorem eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n :=
  (eval₂RingHom _ _).map_pow _ _

theorem eval₂_dvd : p ∣ q → eval₂ f x p ∣ eval₂ f x q :=
  (eval₂RingHom f x).map_dvd

theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) :
    eval₂ f x q = 0 :=
  zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

theorem eval₂_list_prod (l : List R[X]) (x : S) : eval₂ f x l.prod = (l.map (eval₂ f x)).prod :=
  map_list_prod (eval₂RingHom f x) l

end

end Eval₂

section Eval

variable {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → R[X] → R :=
  eval₂ (RingHom.id _)

theorem eval_eq_sum : p.eval x = p.sum fun e a => a * x ^ e := by
  rw [eval, eval₂_eq_sum]
  rfl

theorem eval_eq_sum_range {p : R[X]} (x : R) :
    p.eval x = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
  rw [eval_eq_sum, sum_over_range]; simp

theorem eval_eq_sum_range' {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : R) :
    p.eval x = ∑ i ∈ Finset.range n, p.coeff i * x ^ i := by
  rw [eval_eq_sum, p.sum_over_range' _ _ hn]; simp

@[simp]
theorem eval₂_at_apply {S : Type*} [Semiring S] (f : R →+* S) (r : R) :
    p.eval₂ f (f r) = f (p.eval r) := by
  rw [eval₂_eq_sum, eval_eq_sum, sum, sum, map_sum f]
  simp only [f.map_mul, f.map_pow]

@[simp]
theorem eval₂_at_one {S : Type*} [Semiring S] (f : R →+* S) : p.eval₂ f 1 = f (p.eval 1) := by
  convert eval₂_at_apply (p := p) f 1
  simp

@[simp]
theorem eval₂_at_natCast {S : Type*} [Semiring S] (f : R →+* S) (n : ℕ) :
    p.eval₂ f n = f (p.eval n) := by
  convert eval₂_at_apply (p := p) f n
  simp

@[deprecated (since := "2024-04-17")]
alias eval₂_at_nat_cast := eval₂_at_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem eval₂_at_ofNat {S : Type*} [Semiring S] (f : R →+* S) (n : ℕ) [n.AtLeastTwo] :
    p.eval₂ f (no_index (OfNat.ofNat n)) = f (p.eval (OfNat.ofNat n)) := by
  simp [OfNat.ofNat]

@[simp]
theorem eval_C : (C a).eval x = a :=
  eval₂_C _ _

@[simp]
theorem eval_natCast {n : ℕ} : (n : R[X]).eval x = n := by simp only [← C_eq_natCast, eval_C]

@[deprecated (since := "2024-04-17")]
alias eval_nat_cast := eval_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] (a : R) :
    (no_index (OfNat.ofNat n : R[X])).eval a = OfNat.ofNat n := by
  simp only [OfNat.ofNat, eval_natCast]

@[simp]
theorem eval_X : X.eval x = x :=
  eval₂_X _ _

@[simp]
theorem eval_monomial {n a} : (monomial n a).eval x = a * x ^ n :=
  eval₂_monomial _ _

@[simp]
theorem eval_zero : (0 : R[X]).eval x = 0 :=
  eval₂_zero _ _

@[simp]
theorem eval_add : (p + q).eval x = p.eval x + q.eval x :=
  eval₂_add _ _

@[simp]
theorem eval_one : (1 : R[X]).eval x = 1 :=
  eval₂_one _ _

@[simp]
theorem eval_smul [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (s : S) (p : R[X])
    (x : R) : (s • p).eval x = s • p.eval x := by
  rw [← smul_one_smul R s p, eval, eval₂_smul, RingHom.id_apply, smul_one_mul]

@[simp]
theorem eval_C_mul : (C a * p).eval x = a * p.eval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [mul_add, eval_add, ph, qh]
  | h_monomial n b =>
    simp only [mul_assoc, C_mul_monomial, eval_monomial]

/-- A reformulation of the expansion of (1 + y)^d:
$$(d + 1) (1 + y)^d - (d + 1)y^d = \sum_{i = 0}^d {d + 1 \choose i} \cdot i \cdot y^{i - 1}.$$
-/
theorem eval_monomial_one_add_sub [CommRing S] (d : ℕ) (y : S) :
    eval (1 + y) (monomial d (d + 1 : S)) - eval y (monomial d (d + 1 : S)) =
      ∑ x_1 ∈ range (d + 1), ↑((d + 1).choose x_1) * (↑x_1 * y ^ (x_1 - 1)) := by
  have cast_succ : (d + 1 : S) = ((d.succ : ℕ) : S) := by simp only [Nat.cast_succ]
  rw [cast_succ, eval_monomial, eval_monomial, add_comm, add_pow]
  -- Porting note: `apply_congr` hadn't been ported yet, so `congr` & `ext` is used.
  conv_lhs =>
    congr
    · congr
      · skip
      · congr
        · skip
        · ext
          rw [one_pow, mul_one, mul_comm]
  rw [sum_range_succ, mul_add, Nat.choose_self, Nat.cast_one, one_mul, add_sub_cancel_right,
    mul_sum, sum_range_succ', Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun y _hy => ?_
  rw [← mul_assoc, ← mul_assoc, ← Nat.cast_mul, Nat.succ_mul_choose_eq, Nat.cast_mul,
    Nat.add_sub_cancel]

/-- `Polynomial.eval` as linear map -/
@[simps]
def leval {R : Type*} [Semiring R] (r : R) : R[X] →ₗ[R] R where
  toFun f := f.eval r
  map_add' _f _g := eval_add
  map_smul' c f := eval_smul c f r

@[simp]
theorem eval_natCast_mul {n : ℕ} : ((n : R[X]) * p).eval x = n * p.eval x := by
  rw [← C_eq_natCast, eval_C_mul]

@[deprecated (since := "2024-04-17")]
alias eval_nat_cast_mul := eval_natCast_mul

@[simp]
theorem eval_mul_X : (p * X).eval x = p.eval x * x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, eval_add, ph, qh]
  | h_monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, eval_monomial, mul_one, pow_succ,
      mul_assoc]

@[simp]
theorem eval_mul_X_pow {k : ℕ} : (p * X ^ k).eval x = p.eval x * x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

theorem eval_sum (p : R[X]) (f : ℕ → R → R[X]) (x : R) :
    (p.sum f).eval x = p.sum fun n a => (f n a).eval x :=
  eval₂_sum _ _ _ _

theorem eval_finset_sum (s : Finset ι) (g : ι → R[X]) (x : R) :
    (∑ i ∈ s, g i).eval x = ∑ i ∈ s, (g i).eval x :=
  eval₂_finset_sum _ _ _ _

/-- `IsRoot p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def IsRoot (p : R[X]) (a : R) : Prop :=
  p.eval a = 0

instance IsRoot.decidable [DecidableEq R] : Decidable (IsRoot p a) := by
  unfold IsRoot; infer_instance

@[simp]
theorem IsRoot.def : IsRoot p a ↔ p.eval a = 0 :=
  Iff.rfl

theorem IsRoot.eq_zero (h : IsRoot p x) : eval x p = 0 :=
  h

theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 :=
  calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

theorem zero_isRoot_of_coeff_zero_eq_zero {p : R[X]} (hp : p.coeff 0 = 0) : IsRoot p 0 := by
  rwa [coeff_zero_eq_eval_zero] at hp

theorem IsRoot.dvd {R : Type*} [CommSemiring R] {p q : R[X]} {x : R} (h : p.IsRoot x)
    (hpq : p ∣ q) : q.IsRoot x := by
  rwa [IsRoot, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

theorem not_isRoot_C (r a : R) (hr : r ≠ 0) : ¬IsRoot (C r) a := by simpa using hr

theorem eval_surjective (x : R) : Function.Surjective <| eval x := fun y => ⟨C y, eval_C⟩

end Eval

section Comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : R[X]) : R[X] :=
  p.eval₂ C q

theorem comp_eq_sum_left : p.comp q = p.sum fun e a => C a * q ^ e := by rw [comp, eval₂_eq_sum]

@[simp]
theorem comp_X : p.comp X = p := by
  simp only [comp, eval₂_def, C_mul_X_pow_eq_monomial]
  exact sum_monomial_eq _

@[simp]
theorem X_comp : X.comp p = p :=
  eval₂_X _ _

@[simp]
theorem comp_C : p.comp (C a) = C (p.eval a) := by simp [comp, map_sum (C : R →+* _)]

@[simp]
theorem C_comp : (C a).comp p = C a :=
  eval₂_C _ _

@[simp]
theorem natCast_comp {n : ℕ} : (n : R[X]).comp p = n := by rw [← C_eq_natCast, C_comp]

@[deprecated (since := "2024-04-17")]
alias nat_cast_comp := natCast_comp

@[simp]
theorem ofNat_comp (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : R[X]).comp p = n :=
  natCast_comp

@[simp]
theorem comp_zero : p.comp (0 : R[X]) = C (p.eval 0) := by rw [← C_0, comp_C]

@[simp]
theorem zero_comp : comp (0 : R[X]) p = 0 := by rw [← C_0, C_comp]

@[simp]
theorem comp_one : p.comp 1 = C (p.eval 1) := by rw [← C_1, comp_C]

@[simp]
theorem one_comp : comp (1 : R[X]) p = 1 := by rw [← C_1, C_comp]

@[simp]
theorem add_comp : (p + q).comp r = p.comp r + q.comp r :=
  eval₂_add _ _

@[simp]
theorem monomial_comp (n : ℕ) : (monomial n a).comp p = C a * p ^ n :=
  eval₂_monomial _ _

@[simp]
theorem mul_X_comp : (p * X).comp r = p.comp r * r := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp only [hp, hq, add_mul, add_comp]
  | h_monomial n b =>
    simp only [pow_succ, mul_assoc, monomial_mul_X, monomial_comp]

@[simp]
theorem X_pow_comp {k : ℕ} : (X ^ k).comp p = p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, mul_X_comp, ih]

@[simp]
theorem mul_X_pow_comp {k : ℕ} : (p * X ^ k).comp r = p.comp r * r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, mul_X_comp]

@[simp]
theorem C_mul_comp : (C a * p).comp r = C a * p.comp r := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [hp, hq, mul_add]
  | h_monomial n b =>
    simp [mul_assoc]

@[simp]
theorem natCast_mul_comp {n : ℕ} : ((n : R[X]) * p).comp r = n * p.comp r := by
  rw [← C_eq_natCast, C_mul_comp]

@[deprecated (since := "2024-04-17")]
alias nat_cast_mul_comp := natCast_mul_comp

theorem mul_X_add_natCast_comp {n : ℕ} :
    (p * (X + (n : R[X]))).comp q = p.comp q * (q + n) := by
  rw [mul_add, add_comp, mul_X_comp, ← Nat.cast_comm, natCast_mul_comp, Nat.cast_comm, mul_add]

@[deprecated (since := "2024-04-17")]
alias mul_X_add_nat_cast_comp := mul_X_add_natCast_comp

@[simp]
theorem mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]) :
    (p * q).comp r = p.comp r * q.comp r :=
  eval₂_mul _ _

@[simp]
theorem pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) (n : ℕ) :
    (p ^ n).comp q = p.comp q ^ n :=
  (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) one_comp) fun r s => mul_comp r s q).map_pow
    p n

@[simp]
theorem smul_comp [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (s : S) (p q : R[X]) :
    (s • p).comp q = s • p.comp q := by
  rw [← smul_one_smul R s p, comp, comp, eval₂_smul, ← smul_eq_C_mul, smul_assoc, one_smul]

theorem comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : R[X]) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ, ← mul_assoc]

theorem coeff_comp_degree_mul_degree (hqd0 : natDegree q ≠ 0) :
    coeff (p.comp q) (natDegree p * natDegree q) =
    leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [comp, eval₂_def, coeff_sum]
  -- Porting note: `convert` → `refine`
  refine Eq.trans (Finset.sum_eq_single p.natDegree ?h₀ ?h₁) ?h₂
  case h₂ =>
    simp only [coeff_natDegree, coeff_C_mul, coeff_pow_mul_natDegree]
  case h₀ =>
    intro b hbs hbp
    refine coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt ?_)
    rw [natDegree_C, zero_add]
    refine natDegree_pow_le.trans_lt ((mul_lt_mul_right (pos_iff_ne_zero.mpr hqd0)).mpr ?_)
    exact lt_of_le_of_ne (le_natDegree_of_mem_supp _ hbs) hbp
  case h₁ =>
    simp (config := { contextual := true })

@[simp] lemma sum_comp (s : Finset ι) (p : ι → R[X]) (q : R[X]) :
    (∑ i ∈ s, p i).comp q = ∑ i ∈ s, (p i).comp q := Polynomial.eval₂_finset_sum _ _ _ _

end Comp

section Map

variable [Semiring S]
variable (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : R[X] → S[X] :=
  eval₂ (C.comp f) X

@[simp]
theorem map_C : (C a).map f = C (f a) :=
  eval₂_C _ _

@[simp]
theorem map_X : X.map f = X :=
  eval₂_X _ _

@[simp]
theorem map_monomial {n a} : (monomial n a).map f = monomial n (f a) := by
  dsimp only [map]
  rw [eval₂_monomial, ← C_mul_X_pow_eq_monomial]; rfl

@[simp]
protected theorem map_zero : (0 : R[X]).map f = 0 :=
  eval₂_zero _ _

@[simp]
protected theorem map_add : (p + q).map f = p.map f + q.map f :=
  eval₂_add _ _

@[simp]
protected theorem map_one : (1 : R[X]).map f = 1 :=
  eval₂_one _ _

@[simp]
protected theorem map_mul : (p * q).map f = p.map f * q.map f := by
  rw [map, eval₂_mul_noncomm]
  exact fun k => (commute_X _).symm

@[simp]
protected theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map, eval₂_smul, RingHom.comp_apply, C_mul']

-- `map` is a ring-hom unconditionally, and theoretically the definition could be replaced,
-- but this turns out not to be easy because `p.map f` does not resolve to `Polynomial.map`
-- if `map` is a `RingHom` instead of a plain function; the elaborator does not try to coerce
-- to a function before trying field (dot) notation (this may be technically infeasible);
-- the relevant code is (both lines): https://github.com/leanprover-community/
-- lean/blob/487ac5d7e9b34800502e1ddf3c7c806c01cf9d51/src/frontends/lean/elaborator.cpp#L1876-L1913
/-- `Polynomial.map` as a `RingHom`. -/
def mapRingHom (f : R →+* S) : R[X] →+* S[X] where
  toFun := Polynomial.map f
  map_add' _ _ := Polynomial.map_add f
  map_zero' := Polynomial.map_zero f
  map_mul' _ _ := Polynomial.map_mul f
  map_one' := Polynomial.map_one f

@[simp]
theorem coe_mapRingHom (f : R →+* S) : ⇑(mapRingHom f) = map f :=
  rfl

-- This is protected to not clash with the global `map_natCast`.
@[simp]
protected theorem map_natCast (n : ℕ) : (n : R[X]).map f = n :=
  map_natCast (mapRingHom f) n

@[deprecated (since := "2024-04-17")]
alias map_nat_cast := map_natCast

-- See note [no_index around OfNat.ofNat]
@[simp]
protected theorem map_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : R[X]).map f = OfNat.ofNat n :=
  show (n : R[X]).map f = n by rw [Polynomial.map_natCast]

--TODO rename to `map_dvd_map`
theorem map_dvd (f : R →+* S) {x y : R[X]} : x ∣ y → x.map f ∣ y.map f :=
  (mapRingHom f).map_dvd

@[simp]
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by
  rw [map, eval₂_def, coeff_sum, sum]
  conv_rhs => rw [← sum_C_mul_X_pow_eq p, coeff_sum, sum, map_sum]
  refine Finset.sum_congr rfl fun x _hx => ?_
  simp only [RingHom.coe_comp, Function.comp, coeff_C_mul_X_pow]
  split_ifs <;> simp [f.map_zero]

/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps!]
def mapEquiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
  RingEquiv.ofHomInv (mapRingHom (e : R →+* S)) (mapRingHom (e.symm : S →+* R)) (by ext <;> simp)
    (by ext <;> simp)

theorem map_map [Semiring T] (g : S →+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
  ext (by simp [coeff_map])

@[simp]
theorem map_id : p.map (RingHom.id _) = p := by simp [Polynomial.ext_iff, coeff_map]

/-- The polynomial ring over a finite product of rings is isomorphic to
the product of polynomial rings over individual rings. -/
def piEquiv {ι} [Finite ι] (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, R i)[X] ≃+* ∀ i, (R i)[X] :=
  .ofBijective (Pi.ringHom fun i ↦ mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h ↦ by ext n i; simpa using congr_arg (fun p ↦ coeff (p i) n) h,
      fun p ↦ ⟨.ofFinsupp (.ofSupportFinite (fun n i ↦ coeff (p i) n) <|
        (Set.finite_iUnion fun i ↦ (p i).support.finite_toSet).subset fun n hn ↦ by
          simp only [Set.mem_iUnion, Finset.mem_coe, mem_support_iff, Function.mem_support] at hn ⊢
          contrapose! hn; exact funext hn), by ext i n; exact coeff_map _ _⟩⟩

theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp [hp, hq]
  | h_monomial n r =>
    simp

theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := fun p q h =>
  ext fun m => hf <| by rw [← coeff_map f, ← coeff_map f, h]

theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := fun p =>
  Polynomial.induction_on' p
    (fun p q hp hq =>
      let ⟨p', hp'⟩ := hp
      let ⟨q', hq'⟩ := hq
      ⟨p' + q', by rw [Polynomial.map_add f, hp', hq']⟩)
    fun n s =>
    let ⟨r, hr⟩ := hf s
    ⟨monomial n r, by rw [map_monomial f, hr]⟩

theorem degree_map_le (p : R[X]) : degree (p.map f) ≤ degree p := by
  refine (degree_le_iff_coeff_zero _ _).2 fun m hm => ?_
  rw [degree_lt_iff_coeff_zero] at hm
  simp [hm m le_rfl]

theorem natDegree_map_le (p : R[X]) : natDegree (p.map f) ≤ natDegree p :=
  natDegree_le_natDegree (degree_map_le f p)

variable {f}

protected theorem map_eq_zero_iff (hf : Function.Injective f) : p.map f = 0 ↔ p = 0 :=
  map_eq_zero_iff (mapRingHom f) (map_injective f hf)

protected theorem map_ne_zero_iff (hf : Function.Injective f) : p.map f ≠ 0 ↔ p ≠ 0 :=
  (Polynomial.map_eq_zero_iff hf).not

theorem map_monic_eq_zero_iff (hp : p.Monic) : p.map f = 0 ↔ ∀ x, f x = 0 :=
  ⟨fun hfp x =>
    calc
      f x = f x * f p.leadingCoeff := by simp only [mul_one, hp.leadingCoeff, f.map_one]
      _ = f x * (p.map f).coeff p.natDegree := congr_arg _ (coeff_map _ _).symm
      _ = 0 := by simp only [hfp, mul_zero, coeff_zero]
      ,
    fun h => ext fun n => by simp only [h, coeff_map, coeff_zero]⟩

theorem map_monic_ne_zero (hp : p.Monic) [Nontrivial S] : p.map f ≠ 0 := fun h =>
  f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

theorem degree_map_eq_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    degree (p.map f) = degree p :=
  le_antisymm (degree_map_le f _) <| by
    have hp0 : p ≠ 0 :=
      leadingCoeff_ne_zero.mp fun hp0 => hf (_root_.trans (congr_arg _ hp0) f.map_zero)
    rw [degree_eq_natDegree hp0]
    refine le_degree_of_ne_zero ?_
    rw [coeff_map]
    exact hf

theorem natDegree_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    natDegree (p.map f) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_map_eq_of_leadingCoeff_ne_zero f hf)

theorem leadingCoeff_map_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    leadingCoeff (p.map f) = f (leadingCoeff p) := by
  unfold leadingCoeff
  rw [coeff_map, natDegree_map_of_leadingCoeff_ne_zero f hf]

variable (f)

@[simp]
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] :=
  RingHom.ext fun _x => map_id

@[simp]
theorem mapRingHom_comp [Semiring T] (f : S →+* T) (g : R →+* S) :
    (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g) :=
  RingHom.ext <| Polynomial.map_map g f

protected theorem map_list_prod (L : List R[X]) : L.prod.map f = (L.map <| map f).prod :=
  Eq.symm <| List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]
protected theorem map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n :=
  (mapRingHom f).map_pow _ _

theorem mem_map_rangeS {p : S[X]} : p ∈ (mapRingHom f).rangeS ↔ ∀ n, p.coeff n ∈ f.rangeS := by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom, coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom, Polynomial.map_mul, map_C, hc, Polynomial.map_pow, map_X]

theorem mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {p : S[X]} :
    p ∈ (mapRingHom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
  mem_map_rangeS f

theorem eval₂_map [Semiring T] (g : S →+* T) (x : T) :
    (p.map f).eval₂ g x = p.eval₂ (g.comp f) x := by
  rw [eval₂_eq_eval_map, eval₂_eq_eval_map, map_map]

theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
  (eval₂_eq_eval_map f).symm

protected theorem map_sum {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f :=
  map_sum (mapRingHom f) _ _

theorem map_comp (p q : R[X]) : map f (p.comp q) = (map f p).comp (map f q) :=
  Polynomial.induction_on p (by simp only [map_C, forall_const, C_comp, eq_self_iff_true])
    (by
      simp (config := { contextual := true }) only [Polynomial.map_add, add_comp, forall_const,
        imp_true_iff, eq_self_iff_true])
    (by
      simp (config := { contextual := true }) only [pow_succ, ← mul_assoc, comp, forall_const,
        eval₂_mul_X, imp_true_iff, eq_self_iff_true, map_X, Polynomial.map_mul])

@[simp]
theorem eval_zero_map (f : R →+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [← coeff_zero_eq_eval_zero]

@[simp]
theorem eval_one_map (f : R →+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1) := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp only [hp, hq, Polynomial.map_add, RingHom.map_add, eval_add]
  | h_monomial n r =>
    simp only [one_pow, mul_one, eval_monomial, map_monomial]

@[simp]
theorem eval_natCast_map (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).eval (n : S) = f (p.eval n) := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp only [hp, hq, Polynomial.map_add, RingHom.map_add, eval_add]
  | h_monomial n r =>
    simp only [map_natCast f, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[deprecated (since := "2024-04-17")]
alias eval_nat_cast_map := eval_natCast_map

@[simp]
theorem eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (p : R[X]) (i : ℤ) :
    (p.map f).eval (i : S) = f (p.eval i) := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq =>
    simp only [hp, hq, Polynomial.map_add, RingHom.map_add, eval_add]
  | h_monomial n r =>
    simp only [map_intCast, eval_monomial, map_monomial, map_pow, map_mul]

@[deprecated (since := "2024-04-17")]
alias eval_int_cast_map := eval_intCast_map

end Map

/-!
we have made `eval₂` irreducible from the start.

Perhaps we can make also `eval`, `comp`, and `map` irreducible too?
-/


section HomEval₂

variable [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T) (p)

theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by
  rw [← eval₂_map, eval₂_at_apply, eval_map]

end HomEval₂

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [Semiring S] (f : R →+* S)

theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

end

section

variable [Semiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval₂_comp {x : S} : eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p := by
  rw [comp, p.as_sum_range]; simp [eval₂_finset_sum, eval₂_pow]

@[simp]
theorem iterate_comp_eval₂ (k : ℕ) (t : S) :
    eval₂ f t (p.comp^[k] q) = (fun x => eval₂ f x p)^[k] (eval₂ f t q) := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eval₂_comp, IH]

end

section Algebra

variable [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (p q : R[X])

@[simp]
theorem eval₂_mul' :
    (p * q).eval₂ (algebraMap R S) x = p.eval₂ (algebraMap R S) x * q.eval₂ (algebraMap R S) x := by
  exact eval₂_mul_noncomm _ _ fun k => Algebra.commute_algebraMap_left (coeff q k) x

@[simp]
theorem eval₂_pow' (n : ℕ) :
    (p ^ n).eval₂ (algebraMap R S) x = (p.eval₂ (algebraMap R S) x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, eval₂_one]
  | succ n ih => rw [pow_succ, pow_succ, eval₂_mul', ih]

@[simp]
theorem eval₂_comp' : eval₂ (algebraMap R S) x (p.comp q) =
    eval₂ (algebraMap R S) (eval₂ (algebraMap R S) x q) p := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs => simp only [add_comp, eval₂_add, hr, hs]
  | h_monomial n a => simp only [monomial_comp, eval₂_mul', eval₂_C, eval₂_monomial, eval₂_pow']

end Algebra

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

@[simp]
theorem eval_mul : (p * q).eval x = p.eval x * q.eval x :=
  eval₂_mul _ _

/-- `eval r`, regarded as a ring homomorphism from `R[X]` to `R`. -/
def evalRingHom : R → R[X] →+* R :=
  eval₂RingHom (RingHom.id _)

@[simp]
theorem coe_evalRingHom (r : R) : (evalRingHom r : R[X] → R) = eval r :=
  rfl

theorem evalRingHom_zero : evalRingHom 0 = constantCoeff :=
  DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

@[simp]
theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _

@[simp]
theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp [add_comp, hr, hs]
  | h_monomial n a =>
    simp

@[simp]
theorem iterate_comp_eval :
    ∀ (k : ℕ) (t : R), (p.comp^[k] q).eval t = (fun x => p.eval x)^[k] (q.eval t) :=
  iterate_comp_eval₂ _

lemma isRoot_comp {R} [CommSemiring R] {p q : R[X]} {r : R} :
    (p.comp q).IsRoot r ↔ p.IsRoot (q.eval r) := by simp_rw [IsRoot, eval_comp]

/-- `comp p`, regarded as a ring homomorphism from `R[X]` to itself. -/
def compRingHom : R[X] → R[X] →+* R[X] :=
  eval₂RingHom C

@[simp]
theorem coe_compRingHom (q : R[X]) : (compRingHom q : R[X] → R[X]) = fun p => comp p q :=
  rfl

theorem coe_compRingHom_apply (p q : R[X]) : (compRingHom q : R[X] → R[X]) p = comp p q :=
  rfl

theorem root_mul_left_of_isRoot (p : R[X]) {q : R[X]} : IsRoot q a → IsRoot (p * q) a := fun H => by
  rw [IsRoot, eval_mul, IsRoot.def.1 H, mul_zero]

theorem root_mul_right_of_isRoot {p : R[X]} (q : R[X]) : IsRoot p a → IsRoot (p * q) a := fun H =>
  by rw [IsRoot, eval_mul, IsRoot.def.1 H, zero_mul]

theorem eval₂_multiset_prod (s : Multiset R[X]) (x : S) :
    eval₂ f x s.prod = (s.map (eval₂ f x)).prod :=
  map_multiset_prod (eval₂RingHom f x) s

theorem eval₂_finset_prod (s : Finset ι) (g : ι → R[X]) (x : S) :
    (∏ i ∈ s, g i).eval₂ f x = ∏ i ∈ s, (g i).eval₂ f x :=
  map_prod (eval₂RingHom f x) _ _

/-- Polynomial evaluation commutes with `List.prod`
-/
theorem eval_list_prod (l : List R[X]) (x : R) : eval x l.prod = (l.map (eval x)).prod :=
  map_list_prod (evalRingHom x) l

/-- Polynomial evaluation commutes with `Multiset.prod`
-/
theorem eval_multiset_prod (s : Multiset R[X]) (x : R) : eval x s.prod = (s.map (eval x)).prod :=
  (evalRingHom x).map_multiset_prod s

/-- Polynomial evaluation commutes with `Finset.prod`
-/
theorem eval_prod {ι : Type*} (s : Finset ι) (p : ι → R[X]) (x : R) :
    eval x (∏ j ∈ s, p j) = ∏ j ∈ s, eval x (p j) :=
  map_prod (evalRingHom x) _ _

theorem list_prod_comp (l : List R[X]) (q : R[X]) :
    l.prod.comp q = (l.map fun p : R[X] => p.comp q).prod :=
  map_list_prod (compRingHom q) _

theorem multiset_prod_comp (s : Multiset R[X]) (q : R[X]) :
    s.prod.comp q = (s.map fun p : R[X] => p.comp q).prod :=
  map_multiset_prod (compRingHom q) _

theorem prod_comp {ι : Type*} (s : Finset ι) (p : ι → R[X]) (q : R[X]) :
    (∏ j ∈ s, p j).comp q = ∏ j ∈ s, (p j).comp q :=
  map_prod (compRingHom q) _ _

theorem isRoot_prod {R} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι) (p : ι → R[X])
    (x : R) : IsRoot (∏ j ∈ s, p j) x ↔ ∃ i ∈ s, IsRoot (p i) x := by
  simp only [IsRoot, eval_prod, Finset.prod_eq_zero_iff]

theorem eval_dvd : p ∣ q → eval x p ∣ eval x q :=
  eval₂_dvd _ _

theorem eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → eval x p = 0 → eval x q = 0 :=
  eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]
theorem eval_geom_sum {R} [CommSemiring R] {n : ℕ} {x : R} :
    eval x (∑ i ∈ range n, X ^ i) = ∑ i ∈ range n, x ^ i := by simp [eval_finset_sum]

end

end Eval

section Map

theorem support_map_subset [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (map f p).support ⊆ p.support := by
  intro x
  contrapose!
  simp (config := { contextual := true })

theorem support_map_of_injective [Semiring R] [Semiring S] (p : R[X]) {f : R →+* S}
    (hf : Function.Injective f) : (map f p).support = p.support := by
  simp_rw [Finset.ext_iff, mem_support_iff, coeff_map, ← map_zero f, hf.ne_iff,
    forall_const]

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

protected theorem map_multiset_prod (m : Multiset R[X]) : m.prod.map f = (m.map <| map f).prod :=
  Eq.symm <| Multiset.prod_hom _ (mapRingHom f).toMonoidHom

protected theorem map_prod {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∏ i ∈ s, g i).map f = ∏ i ∈ s, (g i).map f :=
  map_prod (mapRingHom f) _ _

theorem IsRoot.map {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [IsRoot, eval_map, eval₂_hom, h.eq_zero, f.map_zero]

theorem IsRoot.of_map {R} [CommRing R] {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by
  rwa [IsRoot, ← (injective_iff_map_eq_zero' f).mp hf, ← eval₂_hom, ← eval_map]

theorem isRoot_map_iff {R : Type*} [CommRing R] {f : R →+* S} {x : R} {p : R[X]}
    (hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x :=
  ⟨fun h => h.of_map hf, fun h => h.map⟩

end Map

end CommSemiring

section Ring

variable [Ring R] {p q r : R[X]}

@[simp]
protected theorem map_sub {S} [Ring S] (f : R →+* S) : (p - q).map f = p.map f - q.map f :=
  (mapRingHom f).map_sub p q

@[simp]
protected theorem map_neg {S} [Ring S] (f : R →+* S) : (-p).map f = -p.map f :=
  (mapRingHom f).map_neg p

@[simp] protected lemma map_intCast {S} [Ring S] (f : R →+* S) (n : ℤ) : map f ↑n = ↑n :=
  map_intCast (mapRingHom f) n

@[deprecated (since := "2024-04-17")]
alias map_int_cast := map_intCast

@[simp]
theorem eval_intCast {n : ℤ} {x : R} : (n : R[X]).eval x = n := by
  simp only [← C_eq_intCast, eval_C]

@[deprecated (since := "2024-04-17")]
alias eval_int_cast := eval_intCast

@[simp]
theorem eval₂_neg {S} [Ring S] (f : R →+* S) {x : S} : (-p).eval₂ f x = -p.eval₂ f x := by
  rw [eq_neg_iff_add_eq_zero, ← eval₂_add, neg_add_cancel, eval₂_zero]

@[simp]
theorem eval₂_sub {S} [Ring S] (f : R →+* S) {x : S} :
    (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x := by
  rw [sub_eq_add_neg, eval₂_add, eval₂_neg, sub_eq_add_neg]

@[simp]
theorem eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval x :=
  eval₂_neg _

@[simp]
theorem eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
  eval₂_sub _

theorem root_X_sub_C : IsRoot (X - C a) b ↔ a = b := by
  rw [IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero, eq_comm]

@[simp]
theorem neg_comp : (-p).comp q = -p.comp q :=
  eval₂_neg _

@[simp]
theorem sub_comp : (p - q).comp r = p.comp r - q.comp r :=
  eval₂_sub _

@[simp]
theorem intCast_comp (i : ℤ) : comp (i : R[X]) p = i := by cases i <;> simp

@[deprecated (since := "2024-05-27")] alias cast_int_comp := intCast_comp

@[simp]
theorem eval₂_at_intCast {S : Type*} [Ring S] (f : R →+* S) (n : ℤ) :
    p.eval₂ f n = f (p.eval n) := by
  convert eval₂_at_apply (p := p) f n
  simp

@[deprecated (since := "2024-04-17")]
alias eval₂_at_int_cast := eval₂_at_intCast

theorem mul_X_sub_intCast_comp {n : ℕ} :
    (p * (X - (n : R[X]))).comp q = p.comp q * (q - n) := by
  rw [mul_sub, sub_comp, mul_X_comp, ← Nat.cast_comm, natCast_mul_comp, Nat.cast_comm, mul_sub]

@[deprecated (since := "2024-04-17")]
alias mul_X_sub_int_cast_comp := mul_X_sub_intCast_comp

end Ring

end Polynomial
