/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic

/-!
# Evaluating a polynomial

## Main definitions
* `Polynomial.eval₂`: evaluate `p : R[X]` in `S` given a ring hom `f : R →+* S` and `x : S`.
* `Polynomial.eval`: evaluate `p : R[X]` given `x : R`.
* `Polynomial.IsRoot`: `x : R` is a root of `p : R[X]`.
* `Polynomial.comp`: compose two polynomials `p q : R[X]` by evaluating `p` at `q`.
* `Polynomial.map`: apply `f : R →+* S` to the coefficients of `p : R[X]`.

We also provide the following bundled versions:
* `Polynomial.eval₂AddMonoidHom`, `Polynomial.eval₂RingHom`
* `Polynomial.evalRingHom`
* `Polynomial.compRingHom`
* `Polynomial.mapRingHom`

We include results on applying the definitions to `C`, `X` and ring operations.

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

@[simp]
lemma eval₂_ofNat {S : Type*} [Semiring S] (n : ℕ) [n.AtLeastTwo] (f : R →+* S) (a : S) :
    (ofNat(n) : R[X]).eval₂ f a = ofNat(n) := by
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
  simp only [eval₂_eq_sum, sum, support, coeff]
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
  · simp only [hk, h, coeff_C_zero]
  · simp only [coeff_C_ne_zero hk, RingHom.map_zero, Commute.zero_left]

theorem eval₂_list_prod_noncomm (ps : List R[X])
    (hf : ∀ p ∈ ps, ∀ (k), Commute (f <| coeff p k) x) :
    eval₂ f x ps.prod = (ps.map (Polynomial.eval₂ f x)).prod := by
  induction ps using List.reverseRecOn with
  | nil => simp
  | append_singleton ps p ihp =>
    simp only [List.forall_mem_append, List.forall_mem_singleton] at hf
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

@[gcongr]
theorem eval₂_dvd : p ∣ q → eval₂ f x p ∣ eval₂ f x q :=
  map_dvd (eval₂RingHom f x)

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
def eval (x : R) (p : R[X]) : R :=
  eval₂ (RingHom.id _) x p

@[simp]
theorem eval₂_id : eval₂ (RingHom.id _) x p = p.eval x := rfl

theorem eval_eq_sum : p.eval x = p.sum fun e a => a * x ^ e := by
  rw [eval, eval₂_eq_sum]
  rfl

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

@[simp]
theorem eval₂_at_ofNat {S : Type*} [Semiring S] (f : R →+* S) (n : ℕ) [n.AtLeastTwo] :
    p.eval₂ f ofNat(n) = f (p.eval (ofNat(n))) := by
  simp [OfNat.ofNat]

@[simp]
theorem eval_C : (C a).eval x = a :=
  eval₂_C _ _

@[simp]
theorem eval_natCast {n : ℕ} : (n : R[X]).eval x = n := by simp only [← C_eq_natCast, eval_C]

@[simp]
lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] (a : R) :
    (ofNat(n) : R[X]).eval a = ofNat(n) := by
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
theorem eval_C_mul : (C a * p).eval x = a * p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q ph qh => simp only [mul_add, eval_add, ph, qh]
  | monomial n b => simp only [mul_assoc, C_mul_monomial, eval_monomial]

@[simp]
theorem eval_natCast_mul {n : ℕ} : ((n : R[X]) * p).eval x = n * p.eval x := by
  rw [← C_eq_natCast, eval_C_mul]

@[simp]
theorem eval_mul_X : (p * X).eval x = p.eval x * x := eval₂_mul_X ..

@[simp]
theorem eval_mul_X_pow {k : ℕ} : (p * X ^ k).eval x = p.eval x * x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

/-- Polynomial evaluation commutes with `List.sum`. -/
theorem eval_listSum (l : List R[X]) (x : R) : eval x l.sum = (l.map (eval x)).sum :=
  eval₂_list_sum ..

/-- Polynomial evaluation commutes with `Multiset.sum`. -/
theorem eval_multisetSum (s : Multiset R[X]) (x : R) : eval x s.sum = (s.map (eval x)).sum :=
  eval₂_multiset_sum ..

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
theorem comp_C : p.comp (C a) = C (p.eval a) := by simp [comp]

@[simp]
theorem C_comp : (C a).comp p = C a :=
  eval₂_C _ _

@[simp]
theorem natCast_comp {n : ℕ} : (n : R[X]).comp p = n := by rw [← C_eq_natCast, C_comp]

@[simp]
theorem ofNat_comp (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R[X]).comp p = n :=
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
  | add p q hp hq => simp only [hp, hq, add_mul, add_comp]
  | monomial n b => simp only [pow_succ, mul_assoc, monomial_mul_X, monomial_comp]

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
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b => simp [mul_assoc]

@[simp]
theorem natCast_mul_comp {n : ℕ} : ((n : R[X]) * p).comp r = n * p.comp r := by
  rw [← C_eq_natCast, C_mul_comp]

theorem mul_X_add_natCast_comp {n : ℕ} :
    (p * (X + (n : R[X]))).comp q = p.comp q * (q + n) := by
  rw [mul_add, add_comp, mul_X_comp, ← Nat.cast_comm, natCast_mul_comp, Nat.cast_comm, mul_add]

@[simp]
theorem mul_comp {R : Type*} [CommSemiring R] (p q r : R[X]) :
    (p * q).comp r = p.comp r * q.comp r :=
  eval₂_mul _ _

@[simp]
theorem pow_comp {R : Type*} [CommSemiring R] (p q : R[X]) (n : ℕ) :
    (p ^ n).comp q = p.comp q ^ n :=
  (MonoidHom.mk (OneHom.mk (fun r : R[X] => r.comp q) one_comp) fun r s => mul_comp r s q).map_pow
    p n

theorem comp_assoc {R : Type*} [CommSemiring R] (φ ψ χ : R[X]) :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  refine Polynomial.induction_on φ ?_ ?_ ?_ <;>
    · intros
      simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ, ← mul_assoc]

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

@[simp]
protected theorem map_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : R[X]).map f = ofNat(n) :=
  show (n : R[X]).map f = n by rw [Polynomial.map_natCast]

--TODO rename to `map_dvd_map`
theorem map_dvd (f : R →+* S) {x y : R[X]} : x ∣ y → x.map f ∣ y.map f :=
  _root_.map_dvd (mapRingHom f)

lemma mapRingHom_comp_C {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) :
    (mapRingHom f).comp C = C.comp f := by ext; simp

theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n r => simp

protected theorem map_list_prod (L : List R[X]) : L.prod.map f = (L.map <| map f).prod :=
  Eq.symm <| List.prod_hom _ (mapRingHom f).toMonoidHom

@[simp]
protected theorem map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n :=
  (mapRingHom f).map_pow _ _

theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
  (eval₂_eq_eval_map f).symm

protected theorem map_sum {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f :=
  map_sum (mapRingHom f) _ _

theorem map_comp (p q : R[X]) : map f (p.comp q) = (map f p).comp (map f q) :=
  Polynomial.induction_on p (by simp only [map_C, forall_const, C_comp])
    (by
      simp +contextual only [Polynomial.map_add, add_comp, forall_const,
        imp_true_iff])
    (by
      simp +contextual only [pow_succ, ← mul_assoc, comp, forall_const,
        eval₂_mul_X, imp_true_iff, map_X, Polynomial.map_mul])

end Map

end Semiring

section CommSemiring

section Eval

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

@[simp]
theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _

theorem eval_X_pow (n : ℕ) : (X ^ n : R[X]).eval x = x ^ n := by
  simp

@[simp]
theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp [add_comp, hr, hs]
  | monomial n a => simp

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

theorem isRoot_prod {R} [CommSemiring R] [IsDomain R] {ι : Type*} (s : Finset ι) (p : ι → R[X])
    (x : R) : IsRoot (∏ j ∈ s, p j) x ↔ ∃ i ∈ s, IsRoot (p i) x := by
  simp only [IsRoot, eval_prod, Finset.prod_eq_zero_iff]

@[gcongr]
theorem eval_dvd : p ∣ q → eval x p ∣ eval x q :=
  eval₂_dvd _ _

theorem eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → eval x p = 0 → eval x q = 0 :=
  eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]
theorem eval_geom_sum {R} [CommSemiring R] {n : ℕ} {x : R} :
    eval x (∑ i ∈ range n, X ^ i) = ∑ i ∈ range n, x ^ i := by simp [eval_finset_sum]

variable [NoZeroDivisors R]

lemma root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [IsRoot, eval_mul, mul_eq_zero]

lemma root_or_root_of_root_mul (h : IsRoot (p * q) a) : IsRoot p a ∨ IsRoot q a :=
  root_mul.1 h

end

end Eval

section Map

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

protected theorem map_multiset_prod (m : Multiset R[X]) : m.prod.map f = (m.map <| map f).prod :=
  Eq.symm <| Multiset.prod_hom _ (mapRingHom f).toMonoidHom

protected theorem map_prod {ι : Type*} (g : ι → R[X]) (s : Finset ι) :
    (∏ i ∈ s, g i).map f = ∏ i ∈ s, (g i).map f :=
  map_prod (mapRingHom f) _ _

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

@[simp]
theorem eval_intCast {n : ℤ} {x : R} : (n : R[X]).eval x = n := by
  simp only [← C_eq_intCast, eval_C]

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

@[simp]
theorem eval₂_at_intCast {S : Type*} [Ring S] (f : R →+* S) (n : ℤ) :
    p.eval₂ f n = f (p.eval n) := by
  convert eval₂_at_apply (p := p) f n
  simp

theorem mul_X_sub_intCast_comp {n : ℕ} :
    (p * (X - (n : R[X]))).comp q = p.comp q * (q - n) := by
  rw [mul_sub, sub_comp, mul_X_comp, ← Nat.cast_comm, natCast_mul_comp, Nat.cast_comm, mul_sub]

end Ring

end Polynomial
