/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Multivariate polynomials

This file defines functions for evaluating multivariate polynomials.
These include generically evaluating a polynomial given a valuation of all its variables,
and more advanced evaluations that allow one to map the coefficients to different rings.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.
* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`
* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`
* `aeval (g : σ → S₁) p` : evaluates the multivariate polynomial obtained from `p` by the change
  of coefficient semiring corresponding to `g` (`a` stands for `Algebra`)

-/

@[expose] public section

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Eval₂

variable (f : R →+* S₁) (g : σ → S₁)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  p.sum fun s a => f a * s.prod fun n e => g n ^ e

theorem eval₂_eq (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i ∈ d.support, X i ^ d i :=
  rfl

theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i, X i ^ d i := by
  simp only [eval₂_eq, ← Finsupp.prod_pow]
  rfl

@[simp]
theorem eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g = 0 :=
  Finsupp.sum_zero_index

section

@[simp]
theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g := by
  classical exact Finsupp.sum_add_index (by simp [f.map_zero]) (by simp [add_mul, f.map_add])

@[simp]
theorem eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e :=
  Finsupp.sum_single_index (by simp [f.map_zero])

@[simp]
theorem eval₂_C (a) : (C a).eval₂ f g = f a := by
  rw [C_apply, eval₂_monomial, prod_zero_index, mul_one]

@[simp]
theorem eval₂_one : (1 : MvPolynomial σ R).eval₂ f g = 1 :=
  (eval₂_C _ _ _).trans f.map_one

@[simp] theorem eval₂_natCast (n : Nat) : (n : MvPolynomial σ R).eval₂ f g = n :=
  (eval₂_C _ _ _).trans (map_natCast f n)

@[simp] theorem eval₂_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval₂ f g = ofNat(n) :=
  eval₂_natCast f g n

@[simp]
theorem eval₂_X (n) : (X n).eval₂ f g = g n := by
  simp [eval₂_monomial, f.map_one, X, prod_single_index, pow_one]

theorem eval₂_X_pow {s : σ} {n : ℕ} : ((X s) ^ n).eval₂ f g = (g s) ^ n := by
  simp [X_pow_eq_monomial, eval₂_monomial f g]

theorem eval₂_mul_monomial :
    ∀ {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod fun n e => g n ^ e := by
  classical
  apply MvPolynomial.induction_on p
  · intro a' s a
    simp [C_mul_monomial, eval₂_monomial, f.map_mul]
  · intro p q ih_p ih_q
    simp [add_mul, eval₂_add, ih_p, ih_q]
  · intro p n ih s a
    exact
      calc (p * X n * monomial s a).eval₂ f g
        _ = (p * monomial (Finsupp.single n 1 + s) a).eval₂ f g := by
          rw [monomial_single_add, pow_one, mul_assoc]
        _ = (p * monomial (Finsupp.single n 1) 1).eval₂ f g * f a * s.prod fun n e => g n ^ e := by
          simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
            f.map_one]

theorem eval₂_mul_C : (p * C a).eval₂ f g = p.eval₂ f g * f a :=
  (eval₂_mul_monomial _ _).trans <| by simp

@[simp]
theorem eval₂_mul : ∀ {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_mul_monomial, ← mul_assoc]

theorem eval₂_mul_eq_zero_of_left (hp : p.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hp]

theorem eval₂_mul_eq_zero_of_right (hq : q.eval₂ f g = 0) : (p * q).eval₂ f g = 0 := by
  simp [eval₂_mul f g, hq]

@[simp]
theorem eval₂_pow {p : MvPolynomial σ R} : ∀ {n : ℕ}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
  | 0 => by
    rw [pow_zero, pow_zero]
    exact eval₂_one _ _
  | n + 1 => by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

/-- `MvPolynomial.eval₂` as a `RingHom`. -/
def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁ where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[gcongr]
lemma eval₂_dvd (f : R →+* S₁) (g : σ → S₁) {p q : MvPolynomial σ R} (h : p ∣ q) :
    p.eval₂ f g ∣ q.eval₂ f g :=
  map_dvd (eval₂Hom f g) h

@[simp]
theorem coe_eval₂Hom (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂Hom f g) = eval₂ f g :=
  rfl

theorem eval₂Hom_congr {f₁ f₂ : R →+* S₁} {g₁ g₂ : σ → S₁} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ → g₁ = g₂ → p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by
  rintro rfl rfl rfl; rfl

end

@[simp]
theorem eval₂Hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) : eval₂Hom f g (C r) = f r :=
  eval₂_C f g r

@[simp]
theorem eval₂Hom_X' (f : R →+* S₁) (g : σ → S₁) (i : σ) : eval₂Hom f g (X i) = g i :=
  eval₂_X f g i

@[simp]
theorem comp_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
    φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f) fun i => φ (g i) := by
  ext <;> simp

theorem map_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl

theorem eval₂Hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k := by
  simp only [coe_eval₂Hom, eval₂_monomial]

@[simp]
theorem eval₂Hom_smul (f : R →+* S₁) (g : σ → S₁) (r : R) (P : MvPolynomial σ R) :
    eval₂Hom f g (r • P) = f r • eval₂Hom f g P := by
  simp [smul_eq_C_mul]

section

theorem eval₂_comp_left {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

end

@[simp]
theorem eval₂_eta (p : MvPolynomial σ R) : eval₂ C X p = p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, eval₂_mul]

theorem eval₂_congr (g₁ g₂ : σ → S₁)
    (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

@[simp] theorem eval₂_sum (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∑ x ∈ s, p x) = ∑ x ∈ s, eval₂ f g (p x) :=
  map_sum (eval₂Hom f g) _ s

@[simp] theorem eval₂_prod (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∏ x ∈ s, p x) = ∏ x ∈ s, eval₂ f g (p x) :=
  map_prod (eval₂Hom f g) _ s

theorem eval₂_assoc (q : S₂ → MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    eval₂ f (fun t => eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) := by
  change _ = eval₂Hom f g (eval₂ C q p)
  rw [eval₂_comp_left (eval₂Hom f g)]; congr with a; simp

end Eval₂

section Eval

variable {f : σ → R}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → R) : MvPolynomial σ R →+* R :=
  eval₂Hom (RingHom.id _) f

theorem eval_eq (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i ∈ d.support, X i ^ d i :=
  rfl

theorem eval_eq' [Fintype σ] (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i, X i ^ d i :=
  eval₂_eq' (RingHom.id R) X f

theorem eval_monomial : eval f (monomial s a) = a * s.prod fun n e => f n ^ e :=
  eval₂_monomial _ _

@[simp]
theorem eval_C : ∀ a, eval f (C a) = a :=
  eval₂_C _ _

@[simp]
theorem eval_X : ∀ n, eval f (X n) = f n :=
  eval₂_X _ _

@[simp] theorem eval_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval f = ofNat(n) :=
  map_ofNat _ n

@[simp]
theorem smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p := by
  rw [smul_eq_C_mul, (eval x).map_mul, eval_C]

theorem eval_add : eval f (p + q) = eval f p + eval f q :=
  eval₂_add _ _

theorem eval_mul : eval f (p * q) = eval f p * eval f q :=
  eval₂_mul _ _

theorem eval_pow : ∀ n, eval f (p ^ n) = eval f p ^ n :=
  fun _ => eval₂_pow _ _

theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∑ i ∈ s, f i) = ∑ i ∈ s, eval g (f i) :=
  map_sum (eval g) _ _

theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∏ i ∈ s, f i) = ∏ i ∈ s, eval g (f i) :=
  map_prod (eval g) _ _

theorem eval_assoc {τ} (f : σ → MvPolynomial τ R) (g : τ → R) (p : MvPolynomial σ R) :
    eval (eval g ∘ f) p = eval g (eval₂ C f p) := by
  rw [eval₂_comp_left (eval g)]
  unfold eval; simp only [coe_eval₂Hom]
  congr with a; simp

@[simp]
theorem eval₂_id {g : σ → R} (p : MvPolynomial σ R) : eval₂ (RingHom.id _) g p = eval g p :=
  rfl

theorem eval_eval₂ {S τ : Type*} {x : τ → S} [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S) (p : MvPolynomial σ R) :
    eval x (eval₂ f g p) = eval₂ ((eval x).comp f) (fun s => eval x (g s)) p := by
  apply induction_on p
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    simp [hp]

end Eval

section Map

variable (f : R →+* S₁)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : MvPolynomial σ R →+* MvPolynomial σ S₁ :=
  eval₂Hom (C.comp f) X

@[simp]
theorem map_monomial (s : σ →₀ ℕ) (a : R) : map f (monomial s a) = monomial s (f a) :=
  (eval₂_monomial _ _).trans monomial_eq.symm

@[simp]
theorem map_C : ∀ a : R, map f (C a : MvPolynomial σ R) = C (f a) :=
  map_monomial _ _

@[simp] protected theorem map_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).map f = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
theorem map_X : ∀ n : σ, map f (X n : MvPolynomial σ R) = X n :=
  eval₂_X _ _

theorem map_id : ∀ p : MvPolynomial σ R, map (RingHom.id R) p = p :=
  eval₂_eta

theorem map_map [CommSemiring S₂] (g : S₁ →+* S₂) (p : MvPolynomial σ R) :
    map g (map f p) = map (g.comp f) p :=
  (eval₂_comp_left (map g) (C.comp f) X p).trans <| by
    congr
    · ext1 a
      simp only [map_C, comp_apply, RingHom.coe_comp]
    · ext1 n
      simp only [map_X, comp_apply]

theorem eval₂_eq_eval_map (g : σ → S₁) (p : MvPolynomial σ R) : p.eval₂ f g = eval g (map f p) := by
  unfold map eval; simp only [coe_eval₂Hom]
  have h := eval₂_comp_left (eval₂Hom (RingHom.id S₁) g) (C.comp f) X p
  dsimp only [coe_eval₂Hom] at h
  rw [h]
  congr
  · ext1 a
    simp
  · ext1 n
    simp only [comp_apply, eval₂_X]

theorem eval₂_comp_right {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, eval₂_C]
  · intro p q hp hq
    rw [eval₂_add, k.map_add, (map f).map_add, eval₂_add, hp, hq]
  · intro p s hp
    rw [eval₂_mul, k.map_mul, (map f).map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X, comp_apply]

theorem map_eval₂ (f : R →+* S₁) (g : S₂ → MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, map_C, eval₂_C]
  · intro p q hp hq
    rw [eval₂_add, (map f).map_add, hp, hq, (map f).map_add, eval₂_add]
  · intro p s hp
    rw [eval₂_mul, (map f).map_mul, hp, (map f).map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X,
      comp_apply]

lemma eval₂_map_comp_C {ι : Type*} (f : R →+* S₁) (h : ι → MvPolynomial σ S₁)
    (p : MvPolynomial ι R) : eval₂ ((map f).comp C) h p = eval₂ C h (map f p) := by
  induction p using MvPolynomial.induction_on <;> simp_all

lemma map_eval {S₂ : Type*} [CommSemiring S₂] (q : S₁ →+* S₂) (g : σ → S₁) (p : MvPolynomial σ S₁) :
    q (eval g p) = eval (q ∘ g) (map q p) := by
  rw [← eval₂_eq_eval_map, ← eval₂_id, eval₂_comp_right, map_id]

theorem coeff_map (p : MvPolynomial σ R) : ∀ m : σ →₀ ℕ, coeff m (map f p) = f (coeff m p) := by
  classical
  apply MvPolynomial.induction_on p <;> clear p
  · intro r m
    simp_rw [map_C, coeff_C, apply_ite f, f.map_zero]
  · intro p q hp hq m
    simp only [hp, hq, (map f).map_add, coeff_add, f.map_add]
  · intro p i hp m
    simp only [(map f).map_mul, map_X, hp, coeff_mul_X', f.map_zero, apply_ite f]

theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := by
  intro p q h
  simp only [MvPolynomial.ext_iff, coeff_map] at h ⊢
  intro m
  exact hf (h m)

theorem map_injective_iff : Function.Injective (map (σ := σ) f) ↔ Function.Injective f :=
  ⟨fun h r r' eq ↦ by simpa using h (a₁ := C r) (a₂ := C r') (by simpa), map_injective f⟩

theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩

theorem map_surjective_iff : Function.Surjective (map (σ := σ) f) ↔ Function.Surjective f :=
  ⟨fun h s ↦ let ⟨p, h⟩ := h (C s); ⟨p.coeff 0, by simpa [coeff_map] using congr(coeff 0 $h)⟩,
    map_surjective f⟩

/-- If `f` is a left-inverse of `g` then `map f` is a left-inverse of `map g`. -/
theorem map_leftInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) := fun X => by
  rw [map_map, (RingHom.ext hf : f.comp g = RingHom.id _), map_id]

/-- If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`. -/
theorem map_rightInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) :=
  (map_leftInverse hf.leftInverse).rightInverse

@[simp]
theorem eval_map (f : R →+* S₁) (g : σ → S₁) (p : MvPolynomial σ R) :
    eval g (map f p) = eval₂ f g p := by
  apply MvPolynomial.induction_on p <;> · simp +contextual

theorem eval₂_comp (f : R →+* S₁) (g : σ → R) (p : MvPolynomial σ R) :
    f (eval g p) = eval₂ f (f ∘ g) p := by
  rw [← p.map_id, eval_map, eval₂_comp_right]

@[simp]
theorem eval₂_map [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ (φ.comp f) g p := by
  rw [← eval_map, ← eval_map, map_map]

@[simp]
theorem eval₂Hom_map_hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂Hom φ g (map f p) = eval₂Hom (φ.comp f) g p :=
  eval₂_map f g φ p

@[simp]
theorem constantCoeff_map (f : R →+* S₁) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ) :=
  coeff_map f φ 0

theorem constantCoeff_comp_map (f : R →+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ →+* S₁).comp (MvPolynomial.map f) =
      f.comp constantCoeff := by
  ext <;> simp

theorem support_map_subset (p : MvPolynomial σ R) : (map f p).support ⊆ p.support := by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose! hx
  rw [coeff_map, hx, map_zero]

theorem support_map_of_injective (p : MvPolynomial σ R) {f : R →+* S₁} (hf : Injective f) :
    (map f p).support = p.support := by
  apply Finset.Subset.antisymm
  · exact MvPolynomial.support_map_subset _ _
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose! hx
  rw [coeff_map, ← f.map_zero] at hx
  exact hf hx

theorem C_dvd_iff_map_hom_eq_zero (q : R →+* S₁) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
    (φ : MvPolynomial σ R) : C r ∣ φ ↔ map q φ = 0 := by
  rw [C_dvd_iff_dvd_coeff, MvPolynomial.ext_iff]
  simp only [coeff_map, coeff_zero, hr]

theorem map_mapRange_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    map f (Finsupp.mapRange g hg φ) = φ ↔ ∀ d, f (g (coeff d φ)) = coeff d φ := by
  simp_rw [MvPolynomial.ext_iff, coeff_map, coeff_mapRange]

lemma coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) [DecidableEq S₁] :
    (map f p).coeffs ⊆ p.coeffs.image f := by
  classical
  induction p using induction_on'' with
  | C a => aesop (add simp coeffs_C)
  | mul_X p n ih => simpa
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add (disjoint_support_monomial ha hs), map_add, coeffs_add]
    · rw [Finset.image_union, Finset.union_subset_iff]
      exact ⟨ih.trans (by simp), hp.trans (by simp)⟩
    · exact Finset.disjoint_of_subset_left (support_map_subset _ _) <|
        Finset.disjoint_of_subset_right (support_map_subset _ _) <|
          disjoint_support_monomial ha hs

@[simp]
lemma coe_coeffs_map (f : R →+* S₁) (p : MvPolynomial σ R) :
    ((map f p).coeffs : Set S₁) ⊆ f '' p.coeffs := by
  classical
  exact mod_cast coeffs_map f p

lemma mem_range_map_iff_coeffs_subset {f : R →+* S₁} {x : MvPolynomial σ S₁} :
    x ∈ Set.range (MvPolynomial.map f) ↔ (x.coeffs : Set _) ⊆ .range f := by
  classical
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := hx
    exact subset_trans (coe_coeffs_map f p) (by simp)
  · induction x using induction_on'' with
    | C a =>
      by_cases h : a = 0
      · subst h
        exact ⟨0, by simp⟩
      · simp only [coeffs_C, h, reduceIte, Finset.coe_singleton, Set.singleton_subset_iff] at hx
        obtain ⟨b, rfl⟩ := hx
        exact ⟨C b, by simp⟩
    | mul_X p n ih =>
      rw [coeffs_mul_X] at hx
      obtain ⟨q, rfl⟩ := ih hx
      exact ⟨q * X n, by simp⟩
    | monomial_add a s p ha hs hp ih =>
      rw [coeffs_add (disjoint_support_monomial ha hs)] at hx
      simp only [Finset.coe_union, Set.union_subset_iff] at hx
      obtain ⟨q, hq⟩ := ih hx.1
      obtain ⟨u, hu⟩ := hp hx.2
      exact ⟨q + u, by simp [hq, hu]⟩

section Algebra

variable [Algebra R S₁] (g : σ → S₁)

variable (R) in
/-- `MvPolynomial.eval₂ (algebraMap R S) g` as an `R`-algebra homomorphism. -/
def eval₂AlgHom : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) g with
    commutes' r := by simp }

theorem eval₂AlgHom_apply (P : MvPolynomial σ R) :
    eval₂AlgHom R g P = eval₂Hom (algebraMap R S₁) g P := rfl

@[simp]
theorem coe_eval₂AlgHom : ⇑(eval₂AlgHom R g) = eval₂ (algebraMap R S₁) g := rfl

@[simp]
theorem eval₂AlgHom_X (i : σ) :
    eval₂AlgHom R g (X i : MvPolynomial σ R) = g i := eval₂_X (algebraMap R S₁) g i

end Algebra

/-- If `f : S₁ →ₐ[R] S₂` is a morphism of `R`-algebras, then so is `MvPolynomial.map f`. -/
@[simps!]
def mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    MvPolynomial σ S₁ →ₐ[R] MvPolynomial σ S₂ :=
  { map (↑f : S₁ →+* S₂) with
    commutes' r := by simp }

@[simp]
theorem mapAlgHom_id [Algebra R S₁] :
    mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) :=
  AlgHom.ext map_id

@[simp]
theorem mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    ↑(mapAlgHom f : _ →ₐ[R] MvPolynomial σ S₂) =
      (map ↑f : MvPolynomial σ S₁ →+* MvPolynomial σ S₂) :=
  RingHom.mk_coe _ _ _ _ _

lemma range_mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    (mapAlgHom f).range.toSubmodule = coeffsIn σ f.range.toSubmodule := by
  ext
  rw [Subalgebra.mem_toSubmodule, ← SetLike.mem_coe, AlgHom.coe_range, mapAlgHom, AlgHom.coe_mk,
    mem_range_map_iff_coeffs_subset, mem_coeffsIn_iff_coeffs_subset]
  simp [Set.subset_def]

end Map

section Aeval

/-! ### The algebra of multivariate polynomials -/


variable [Algebra R S₁] [CommSemiring S₂]
variable (f : σ → S₁)

/-- A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism
from multivariate polynomials over `σ` to `S₁`. -/
def aeval : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }

theorem aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  rfl

theorem aeval_eq_eval₂Hom (p : MvPolynomial σ R) : aeval f p = eval₂Hom (algebraMap R S₁) f p :=
  rfl

@[simp]
lemma coe_aeval_eq_eval :
    RingHomClass.toRingHom (aeval f : MvPolynomial σ S₁ →ₐ[S₁] S₁) = eval f :=
  rfl

@[simp]
lemma aeval_eq_eval : (aeval f : MvPolynomial σ S₁ → S₁) = eval f := rfl

@[simp]
theorem aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R) = f s :=
  eval₂_X _ _ _

theorem aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ r :=
  eval₂_C _ _ _

@[simp] theorem aeval_ofNat (n : Nat) [n.AtLeastTwo] :
    aeval f (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  map_ofNat _ _

theorem aeval_unique (φ : MvPolynomial σ R →ₐ[R] S₁) : φ = aeval (φ ∘ X) := by
  ext i
  simp

theorem aeval_X_left : aeval X = AlgHom.id R (MvPolynomial σ R) :=
  (aeval_unique (AlgHom.id R _)).symm

theorem aeval_X_left_apply (p : MvPolynomial σ R) : aeval X p = p :=
  AlgHom.congr_fun aeval_X_left p

theorem comp_aeval {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B) :
    φ.comp (aeval f) = aeval fun i => φ (f i) := by
  ext i
  simp

lemma comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B)
    (p : MvPolynomial σ R) :
    φ (aeval f p) = aeval (fun i ↦ φ (f i)) p := by
  rw [← comp_aeval, AlgHom.coe_comp, comp_apply]

@[simp]
theorem map_aeval {B : Type*} [CommSemiring B] (g : σ → S₁) (φ : S₁ →+* B) (p : MvPolynomial σ R) :
    φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl

theorem aeval_range : (aeval f).range = Algebra.adjoin R (Set.range f) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    induction p using induction_on with
    | C a => exact aeval_C f a ▸ Subsemiring.subset_closure (Or.inl (Set.mem_range_self a))
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | mul_X p n h =>
      simp only [map_mul, aeval_X]
      exact Subalgebra.mul_mem _ h (Algebra.subset_adjoin (Set.mem_range_self n))
  · rw [Algebra.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    use X i, by aesop

@[simp]
theorem eval₂Hom_zero (f : R →+* S₂) : eval₂Hom f (0 : σ → S₂) = f.comp constantCoeff := by
  ext <;> simp

@[simp]
theorem eval₂Hom_zero' (f : R →+* S₂) : eval₂Hom f (fun _ => 0 : σ → S₂) = f.comp constantCoeff :=
  eval₂Hom_zero f

theorem eval₂Hom_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (0 : σ → S₂) p = f (constantCoeff p) :=
  RingHom.congr_fun (eval₂Hom_zero f) p

theorem eval₂Hom_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply f p

@[simp]
theorem eval₂_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂Hom_zero_apply _ _

@[simp]
theorem eval₂_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂_zero_apply f p

@[simp]
theorem aeval_zero (p : MvPolynomial σ R) :
    aeval (0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_zero_apply (algebraMap R S₁) p

@[simp]
theorem aeval_zero' (p : MvPolynomial σ R) :
    aeval (fun _ => 0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  aeval_zero p

@[simp]
theorem eval_zero : eval (0 : σ → R) = constantCoeff :=
  eval₂Hom_zero _

@[simp]
theorem eval_zero' : eval (fun _ => 0 : σ → R) = constantCoeff :=
  eval₂Hom_zero _

theorem aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ k :=
  eval₂Hom_monomial _ _ _ _

theorem eval₂Hom_eq_zero (f : R →+* S₂) (g : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, g i = 0) : eval₂Hom f g φ = 0 := by
  rw [φ.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : ∃ i ∈ d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial, Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
  rw [hgi, zero_pow]
  rwa [← Finsupp.mem_support_iff]

theorem aeval_eq_zero [Algebra R S₂] (f : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, f i = 0) : aeval f φ = 0 :=
  eval₂Hom_eq_zero _ _ _ h

theorem aeval_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∑ i ∈ s, φ i) = ∑ i ∈ s, aeval f (φ i) :=
  map_sum (MvPolynomial.aeval f) _ _

theorem aeval_prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∏ i ∈ s, φ i) = ∏ i ∈ s, aeval f (φ i) :=
  map_prod (MvPolynomial.aeval f) _ _

variable (R)

theorem _root_.Algebra.adjoin_range_eq_range_aeval :
    Algebra.adjoin R (Set.range f) = (MvPolynomial.aeval f).range := by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

theorem _root_.Algebra.adjoin_eq_range (s : Set S₁) :
    Algebra.adjoin R s = (MvPolynomial.aeval ((↑) : s → S₁)).range := by
  rw [← Algebra.adjoin_range_eq_range_aeval, Subtype.range_coe]

end Aeval

section AevalTower

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
variable [Algebra S R] [Algebra S A] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `MvPolynomial σ R` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A) (X : σ → A) : MvPolynomial σ R →ₐ[S] A :=
  { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

variable (g : R →ₐ[S] A) (y : σ → A)

@[simp]
theorem aevalTower_X (i : σ) : aevalTower g y (X i) = y i :=
  eval₂_X _ _ _

@[simp]
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  eval₂_C _ _ _

@[simp]
theorem aevalTower_ofNat (n : Nat) [n.AtLeastTwo] :
    aevalTower g y (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
theorem aevalTower_comp_C : (aevalTower g y : MvPolynomial σ R →+* A).comp C = g :=
  RingHom.ext <| aevalTower_C _ _

theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x :=
  eval₂_C _ _ _

theorem aevalTower_comp_algebraMap :
    (aevalTower g y : MvPolynomial σ R →+* A).comp (algebraMap R (MvPolynomial σ R)) = g :=
  aevalTower_comp_C _ _

theorem aevalTower_toAlgHom (x : R) :
    aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
theorem aevalTower_comp_toAlgHom :
    (aevalTower g y).comp (IsScalarTower.toAlgHom S R (MvPolynomial σ R)) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _

@[simp]
theorem aevalTower_id :
    aevalTower (AlgHom.id S S) = (aeval : (σ → S) → MvPolynomial σ S →ₐ[S] S) := by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]
theorem aevalTower_ofId :
    aevalTower (Algebra.ofId S A) = (aeval : (σ → A) → MvPolynomial σ S →ₐ[S] A) := by
  ext
  simp only [aeval_X, aevalTower_X]

end AevalTower

section EvalMem

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

theorem eval₂_mem {f : R →+* S} {p : MvPolynomial σ R} {s : subS}
    (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s) {v : σ → S} (hv : ∀ i, v i ∈ s) :
    MvPolynomial.eval₂ f v p ∈ s := by
  classical
  replace hs : ∀ i, f (p.coeff i) ∈ s := by
    intro i
    by_cases hi : i ∈ p.support
    · exact hs i hi
    · rw [MvPolynomial.notMem_support_iff.1 hi, f.map_zero]
      exact zero_mem s
  induction p using MvPolynomial.monomial_add_induction_on with
  | C a =>
    simpa using hs 0
  | monomial_add a b f ha _ ih =>
    rw [eval₂_add, eval₂_monomial]
    refine add_mem (mul_mem ?_ <| prod_mem fun i _ => pow_mem (hv _) _) (ih fun i => ?_)
    · simpa [MvPolynomial.notMem_support_iff.1 ha] using hs a
    have := hs i
    rw [coeff_add, coeff_monomial] at this
    split_ifs at this with h
    · subst h
      rw [MvPolynomial.notMem_support_iff.1 ha, map_zero]
      exact zero_mem _
    · rwa [zero_add] at this

theorem eval_mem {p : MvPolynomial σ S} {s : subS} (hs : ∀ i ∈ p.support, p.coeff i ∈ s) {v : σ → S}
    (hv : ∀ i, v i ∈ s) : MvPolynomial.eval v p ∈ s :=
  eval₂_mem hs hv

end EvalMem

variable {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

lemma aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (g : σ → T) :
    (aeval (Sum.elim g (algebraMap S T ∘ f))) p =
      (aeval g) ((aeval (Sum.elim X (C ∘ f))) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [← IsScalarTower.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

end CommSemiring

section Algebra

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/--
If `S` is an `R`-algebra, then `MvPolynomial σ S` is a `MvPolynomial σ R` algebra.

Warning: This produces a diamond for
`Algebra (MvPolynomial σ R) (MvPolynomial σ (MvPolynomial σ S))`. That's why it is not a
global instance.
-/
@[instance_reducible]
noncomputable def algebraMvPolynomial : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
  (MvPolynomial.map (algebraMap R S)).toAlgebra

attribute [local instance] algebraMvPolynomial

@[simp]
lemma algebraMap_def :
    algebraMap (MvPolynomial σ R) (MvPolynomial σ S) = MvPolynomial.map (algebraMap R S) :=
  rfl

instance : IsScalarTower R (MvPolynomial σ R) (MvPolynomial σ S) :=
  IsScalarTower.of_algebraMap_eq' (by ext; simp)

instance [FaithfulSMul R S] : FaithfulSMul (MvPolynomial σ R) (MvPolynomial σ S) :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr
    (map_injective _ <| FaithfulSMul.algebraMap_injective ..)

end Algebra

end MvPolynomial
