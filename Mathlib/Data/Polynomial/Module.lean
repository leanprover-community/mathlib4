/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.FiniteType

#align_import data.polynomial.module from "leanprover-community/mathlib"@"63417e01fbc711beaf25fa73b6edb395c0cfddd0"

/-!
# Polynomial module

In this file, we define the polynomial module for an `R`-module `M`, i.e. the `R[X]`-module `M[X]`.

This is defined as a type alias `PolynomialModule R M := ℕ →₀ M`, since there might be different
module structures on `ℕ →₀ M` of interest. See the docstring of `PolynomialModule` for details.

-/


universe u v

open Polynomial

open Polynomial BigOperators



/-- The `R[X]`-module `M[X]` for an `R`-module `M`.
This is isomorphic (as an `R`-module) to `M[X]` when `M` is a ring.

We require all the module instances `Module S (PolynomialModule R M)` to factor through `R` except
`Module R[X] (PolynomialModule R M)`.
In this constraint, we have the following instances for example :
- `R` acts on `PolynomialModule R R[X]`
- `R[X]` acts on `PolynomialModule R R[X]` as `R[Y]` acting on `R[X][Y]`
- `R` acts on `PolynomialModule R[X] R[X]`
- `R[X]` acts on `PolynomialModule R[X] R[X]` as `R[X]` acting on `R[X][Y]`
- `R[X][X]` acts on `PolynomialModule R[X] R[X]` as `R[X][Y]` acting on itself

This is also the reason why `R` is included in the alias, or else there will be two different
instances of `Module R[X] (PolynomialModule R[X])`.

See https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.2315065.20polynomial.20modules
for the full discussion.
-/
@[nolint unusedArguments]
def PolynomialModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] := ℕ →₀ M
#align polynomial_module PolynomialModule

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)

--porting note: stated instead of deriving
noncomputable instance : Inhabited (PolynomialModule R M) := Finsupp.inhabited
noncomputable instance : AddCommGroup (PolynomialModule R M) := Finsupp.addCommGroup

variable {M}

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

namespace PolynomialModule

/-- This is required to have the `IsScalarTower S R M` instance to avoid diamonds. -/
@[nolint unusedArguments]
noncomputable instance : Module S (PolynomialModule R M) :=
  Finsupp.module ℕ M

instance funLike : FunLike (PolynomialModule R M) ℕ fun _ => M :=
  Finsupp.funLike

instance : CoeFun (PolynomialModule R M) fun _ => ℕ → M :=
  Finsupp.coeFun

theorem zero_apply (i : ℕ) : (0 : PolynomialModule R M) i = 0 :=
  Finsupp.zero_apply

theorem add_apply (g₁ g₂ : PolynomialModule R M) (a : ℕ) : (g₁ + g₂) a = g₁ a + g₂ a :=
  Finsupp.add_apply g₁ g₂ a

/-- The monomial `m * x ^ i`. This is defeq to `Finsupp.singleAddHom`, and is redefined here
so that it has the desired type signature.  -/
noncomputable def single (i : ℕ) : M →+ PolynomialModule R M :=
  Finsupp.singleAddHom i
#align polynomial_module.single PolynomialModule.single

theorem single_apply (i : ℕ) (m : M) (n : ℕ) : single R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply
#align polynomial_module.single_apply PolynomialModule.single_apply

/-- `PolynomialModule.single` as a linear map. -/
noncomputable def lsingle (i : ℕ) : M →ₗ[R] PolynomialModule R M :=
  Finsupp.lsingle i
#align polynomial_module.lsingle PolynomialModule.lsingle

theorem lsingle_apply (i : ℕ) (m : M) (n : ℕ) : lsingle R i m n = ite (i = n) m 0 :=
  Finsupp.single_apply
#align polynomial_module.lsingle_apply PolynomialModule.lsingle_apply

theorem single_smul (i : ℕ) (r : R) (m : M) : single R i (r • m) = r • single R i m :=
  (lsingle R i).map_smul r m
#align polynomial_module.single_smul PolynomialModule.single_smul

variable {R}

theorem induction_linear {P : PolynomialModule R M → Prop} (f : PolynomialModule R M) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsingle : ∀ a b, P (single R a b)) : P f :=
  Finsupp.induction_linear f h0 hadd hsingle
#align polynomial_module.induction_linear PolynomialModule.induction_linear

@[semireducible]
noncomputable instance polynomialModule : Module R[X] (PolynomialModule R M) :=
  modulePolynomialOfEndo (Finsupp.lmapDomain _ _ Nat.succ)
#align polynomial_module.polynomial_module PolynomialModule.polynomialModule

instance (M : Type u) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (PolynomialModule R M) :=
  Finsupp.isScalarTower _ _

instance isScalarTower' (M : Type u) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] : IsScalarTower S R[X] (PolynomialModule R M) := by
  haveI : IsScalarTower R R[X] (PolynomialModule R M) := modulePolynomialOfEndo.isScalarTower _
  -- ⊢ IsScalarTower S R[X] (PolynomialModule R M)
  constructor
  -- ⊢ ∀ (x : S) (y : R[X]) (z : PolynomialModule R M), (x • y) • z = x • y • z
  intro x y z
  -- ⊢ (x • y) • z = x • y • z
  rw [← @IsScalarTower.algebraMap_smul S R, ← @IsScalarTower.algebraMap_smul S R, smul_assoc]
  -- 🎉 no goals
#align polynomial_module.is_scalar_tower' PolynomialModule.isScalarTower'

@[simp]
theorem monomial_smul_single (i : ℕ) (r : R) (j : ℕ) (m : M) :
    monomial i r • single R j m = single R (i + j) (r • m) := by
  simp only [LinearMap.mul_apply, Polynomial.aeval_monomial, LinearMap.pow_apply,
    Module.algebraMap_end_apply, modulePolynomialOfEndo_smul_def]
  induction i generalizing r j m with
  | zero =>
    rw [Nat.zero_eq, Function.iterate_zero, zero_add]
    exact Finsupp.smul_single r j m
  | succ n hn =>
    rw [Function.iterate_succ, Function.comp_apply, Nat.succ_eq_add_one, add_assoc, ← hn]
    congr 2
    rw [← Nat.succ_eq_one_add]
    exact Finsupp.mapDomain_single
#align polynomial_module.monomial_smul_single PolynomialModule.monomial_smul_single

@[simp]
theorem monomial_smul_apply (i : ℕ) (r : R) (g : PolynomialModule R M) (n : ℕ) :
    (monomial i r • g) n = ite (i ≤ n) (r • g (n - i)) 0 := by
  induction' g using PolynomialModule.induction_linear with p q hp hq
  · simp only [smul_zero, zero_apply, ite_self]
    -- 🎉 no goals
  · simp only [smul_add, add_apply, hp, hq]
    -- ⊢ ((if i ≤ n then r • ↑p (n - i) else 0) + if i ≤ n then r • ↑q (n - i) else 0 …
    split_ifs
    -- ⊢ r • ↑p (n - i) + r • ↑q (n - i) = r • ↑p (n - i) + r • ↑q (n - i)
    exacts [rfl, zero_add 0]
    -- 🎉 no goals
  · rw [monomial_smul_single, single_apply, single_apply, smul_ite, smul_zero, ← ite_and]
    -- ⊢ (if i + a✝ = n then r • b✝ else 0) = if i ≤ n ∧ a✝ = n - i then r • b✝ else 0
    congr
    -- ⊢ (i + a✝ = n) = (i ≤ n ∧ a✝ = n - i)
    rw [eq_iff_iff]
    -- ⊢ i + a✝ = n ↔ i ≤ n ∧ a✝ = n - i
    constructor
    -- ⊢ i + a✝ = n → i ≤ n ∧ a✝ = n - i
    · rintro rfl
      -- ⊢ i ≤ i + a✝ ∧ a✝ = i + a✝ - i
      simp
      -- 🎉 no goals
    · rintro ⟨e, rfl⟩
      -- ⊢ i + (n - i) = n
      rw [add_comm, tsub_add_cancel_of_le e]
      -- 🎉 no goals
#align polynomial_module.monomial_smul_apply PolynomialModule.monomial_smul_apply

@[simp]
theorem smul_single_apply (i : ℕ) (f : R[X]) (m : M) (n : ℕ) :
    (f • single R i m) n = ite (i ≤ n) (f.coeff (n - i) • m) 0 := by
  induction' f using Polynomial.induction_on' with p q hp hq
  -- ⊢ ↑((p + q) • ↑(single R i) m) n = if i ≤ n then coeff (p + q) (n - i) • m els …
  · rw [add_smul, Finsupp.add_apply, hp, hq, coeff_add, add_smul]
    -- ⊢ ((if i ≤ n then coeff p (n - i) • m else 0) + if i ≤ n then coeff q (n - i)  …
    split_ifs
    -- ⊢ coeff p (n - i) • m + coeff q (n - i) • m = coeff p (n - i) • m + coeff q (n …
    exacts [rfl, zero_add 0]
    -- 🎉 no goals
  · rw [monomial_smul_single, single_apply, coeff_monomial, ite_smul, zero_smul]
    -- ⊢ (if n✝ + i = n then a✝ • m else 0) = if i ≤ n then if n✝ = n - i then a✝ • m …
    by_cases h : i ≤ n
    -- ⊢ (if n✝ + i = n then a✝ • m else 0) = if i ≤ n then if n✝ = n - i then a✝ • m …
    · simp_rw [eq_tsub_iff_add_eq_of_le h, if_pos h]
      -- 🎉 no goals
    · rw [if_neg h, ite_eq_right_iff]
      -- ⊢ n✝ + i = n → a✝ • m = 0
      intro e
      -- ⊢ a✝ • m = 0
      exfalso
      -- ⊢ False
      linarith
      -- 🎉 no goals
#align polynomial_module.smul_single_apply PolynomialModule.smul_single_apply

theorem smul_apply (f : R[X]) (g : PolynomialModule R M) (n : ℕ) :
    (f • g) n = ∑ x in Finset.Nat.antidiagonal n, f.coeff x.1 • g x.2 := by
  induction' f using Polynomial.induction_on' with p q hp hq f_n f_a
  -- ⊢ ↑((p + q) • g) n = ∑ x in Finset.Nat.antidiagonal n, coeff (p + q) x.fst • ↑ …
  · rw [add_smul, Finsupp.add_apply, hp, hq, ← Finset.sum_add_distrib]
    -- ⊢ ∑ x in Finset.Nat.antidiagonal n, (coeff p x.fst • ↑g x.snd + coeff q x.fst  …
    congr
    -- ⊢ (fun x => coeff p x.fst • ↑g x.snd + coeff q x.fst • ↑g x.snd) = fun x => co …
    ext
    -- ⊢ coeff p x✝.fst • ↑g x✝.snd + coeff q x✝.fst • ↑g x✝.snd = coeff (p + q) x✝.f …
    rw [coeff_add, add_smul]
    -- 🎉 no goals
  · rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => (monomial f_n f_a).coeff i • g j,
      monomial_smul_apply]
    simp_rw [Polynomial.coeff_monomial, ← Finset.mem_range_succ_iff]
    -- ⊢ (if f_n ∈ Finset.range (Nat.succ n) then f_a • ↑g (n - f_n) else 0) = ∑ x in …
    rw [← Finset.sum_ite_eq (Finset.range (Nat.succ n)) f_n (fun x => f_a • g (n - x))]
    -- ⊢ (∑ x in Finset.range (Nat.succ n), if f_n = x then f_a • ↑g (n - x) else 0)  …
    congr
    -- ⊢ (fun x => if f_n = x then f_a • ↑g (n - x) else 0) = fun x => (if f_n = x th …
    ext x
    -- ⊢ (if f_n = x then f_a • ↑g (n - x) else 0) = (if f_n = x then f_a else 0) • ↑ …
    split_ifs
    -- ⊢ f_a • ↑g (n - x) = f_a • ↑g (n - x)
    exacts [rfl, (zero_smul R _).symm]
    -- 🎉 no goals
#align polynomial_module.smul_apply PolynomialModule.smul_apply

/-- `PolynomialModule R R` is isomorphic to `R[X]` as an `R[X]` module. -/
noncomputable def equivPolynomialSelf : PolynomialModule R R ≃ₗ[R[X]] R[X] :=
  { (Polynomial.toFinsuppIso R).symm with
    map_smul' := fun r x => by
      dsimp
      -- ⊢ ↑(↑(toFinsuppIso R)).symm (r • x) = r * ↑(↑(toFinsuppIso R)).symm x
      rw [← RingEquiv.coe_toEquiv_symm, RingEquiv.coe_toEquiv]
      -- ⊢ ↑(RingEquiv.symm (toFinsuppIso R)) (r • x) = r * ↑(RingEquiv.symm (toFinsupp …
      induction' x using induction_linear with _ _ hp hq n a
      · rw [smul_zero, map_zero, mul_zero]
        -- 🎉 no goals
      · rw [smul_add, map_add, map_add, mul_add, hp, hq]
        -- 🎉 no goals
      · ext i
        -- ⊢ coeff (↑(RingEquiv.symm (toFinsuppIso R)) (r • ↑(single R n) a)) i = coeff ( …
        simp only [coeff_ofFinsupp, smul_single_apply, toFinsuppIso_symm_apply, coeff_ofFinsupp,
        single_apply, ge_iff_le, smul_eq_mul, Polynomial.coeff_mul, mul_ite, mul_zero]
        split_ifs with hn
        -- ⊢ coeff r (i - n) * a = ∑ x in Finset.Nat.antidiagonal i, if n = x.snd then co …
        · rw [Finset.sum_eq_single (i - n, n)]
          simp only [ite_true]
          -- ⊢ ∀ (b : ℕ × ℕ), b ∈ Finset.Nat.antidiagonal i → b ≠ (i - n, n) → (if n = b.sn …
          · rintro ⟨p, q⟩ hpq1 hpq2
            -- ⊢ (if n = (p, q).snd then coeff r (p, q).fst * a else 0) = 0
            rw [Finset.Nat.mem_antidiagonal] at hpq1
            -- ⊢ (if n = (p, q).snd then coeff r (p, q).fst * a else 0) = 0
            split_ifs with H
            -- ⊢ coeff r (p, q).fst * a = 0
            · dsimp at H
              -- ⊢ coeff r (p, q).fst * a = 0
              exfalso
              -- ⊢ False
              apply hpq2
              -- ⊢ (p, q) = (i - n, n)
              rw [←hpq1, H]
              -- ⊢ (p, q) = ((p, q).fst + (p, q).snd - q, q)
              simp only [add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
              -- 🎉 no goals
            · rfl
              -- 🎉 no goals
          · intro H
            -- ⊢ (if n = (i - n, n).snd then coeff r (i - n, n).fst * a else 0) = 0
            exfalso
            -- ⊢ False
            apply H
            -- ⊢ (i - n, n) ∈ Finset.Nat.antidiagonal i
            rw [Finset.Nat.mem_antidiagonal, tsub_add_cancel_of_le hn]
            -- 🎉 no goals
        · symm
          -- ⊢ (∑ x in Finset.Nat.antidiagonal i, if n = x.snd then coeff r x.fst * a else  …
          rw [Finset.sum_ite_of_false, Finset.sum_const_zero]
          -- ⊢ ∀ (x : ℕ × ℕ), x ∈ Finset.Nat.antidiagonal i → ¬n = x.snd
          simp_rw [Finset.Nat.mem_antidiagonal]
          -- ⊢ ∀ (x : ℕ × ℕ), x.fst + x.snd = i → ¬n = x.snd
          intro x hx
          -- ⊢ ¬n = x.snd
          contrapose! hn
          -- ⊢ n ≤ i
          rw [add_comm, ← hn] at hx
          -- ⊢ n ≤ i
          exact Nat.le.intro hx }
          -- 🎉 no goals
#align polynomial_module.equiv_polynomial_self PolynomialModule.equivPolynomialSelf

/-- `PolynomialModule R S` is isomorphic to `S[X]` as an `R` module. -/
noncomputable def equivPolynomial {S : Type*} [CommRing S] [Algebra R S] :
    PolynomialModule R S ≃ₗ[R] S[X] :=
  { (Polynomial.toFinsuppIso S).symm with map_smul' := fun _ _ => rfl }
#align polynomial_module.equiv_polynomial PolynomialModule.equivPolynomial

variable (R' : Type*) {M' : Type*} [CommRing R'] [AddCommGroup M'] [Module R' M']

variable [Algebra R R'] [Module R M'] [IsScalarTower R R' M']

/-- The image of a polynomial under a linear map. -/
noncomputable def map (f : M →ₗ[R] M') : PolynomialModule R M →ₗ[R] PolynomialModule R' M' :=
  Finsupp.mapRange.linearMap f
#align polynomial_module.map PolynomialModule.map

@[simp]
theorem map_single (f : M →ₗ[R] M') (i : ℕ) (m : M) : map R' f (single R i m) = single R' i (f m) :=
  Finsupp.mapRange_single (hf := f.map_zero)
#align polynomial_module.map_single PolynomialModule.map_single

theorem map_smul (f : M →ₗ[R] M') (p : R[X]) (q : PolynomialModule R M) :
    map R' f (p • q) = p.map (algebraMap R R') • map R' f q := by
  apply induction_linear q
  · rw [smul_zero, map_zero, smul_zero]
    -- 🎉 no goals
  · intro f g e₁ e₂
    -- ⊢ ↑(map R' f✝) (p • (f + g)) = Polynomial.map (algebraMap R R') p • ↑(map R' f …
    rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
    -- 🎉 no goals
  intro i m
  -- ⊢ ↑(map R' f) (p • ↑(single R i) m) = Polynomial.map (algebraMap R R') p • ↑(m …
  induction' p using Polynomial.induction_on' with _ _ e₁ e₂
  -- ⊢ ↑(map R' f) ((p✝ + q✝) • ↑(single R i) m) = Polynomial.map (algebraMap R R') …
  · rw [add_smul, map_add, e₁, e₂, Polynomial.map_add, add_smul]
    -- 🎉 no goals
  · rw [monomial_smul_single, map_single, Polynomial.map_monomial, map_single, monomial_smul_single,
      f.map_smul, algebraMap_smul]
#align polynomial_module.map_smul PolynomialModule.map_smul

/-- Evaluate a polynomial `p : PolynomialModule R M` at `r : R`. -/
@[simps! (config := .lemmasOnly)]
def eval (r : R) : PolynomialModule R M →ₗ[R] M where
  toFun p := p.sum fun i m => r ^ i • m
  map_add' x y := Finsupp.sum_add_index' (fun _ => smul_zero _) fun _ _ _ => smul_add _ _ _
  map_smul' s m := by
    refine' (Finsupp.sum_smul_index' _).trans _
    -- ⊢ ∀ (i : ℕ), r ^ i • 0 = 0
    · exact fun i => smul_zero _
      -- 🎉 no goals
    · simp_rw [RingHom.id_apply, Finsupp.smul_sum]
      -- ⊢ (Finsupp.sum m fun i c => r ^ i • s • c) = Finsupp.sum m fun a b => s • r ^  …
      congr
      -- ⊢ (fun i c => r ^ i • s • c) = fun a b => s • r ^ a • b
      ext i c
      -- ⊢ r ^ i • s • c = s • r ^ i • c
      rw [smul_comm]
      -- 🎉 no goals
#align polynomial_module.eval PolynomialModule.eval

@[simp]
theorem eval_single (r : R) (i : ℕ) (m : M) : eval r (single R i m) = r ^ i • m :=
  Finsupp.sum_single_index (smul_zero _)
#align polynomial_module.eval_single PolynomialModule.eval_single

@[simp]
theorem eval_lsingle (r : R) (i : ℕ) (m : M) : eval r (lsingle R i m) = r ^ i • m :=
  eval_single r i m
#align polynomial_module.eval_lsingle PolynomialModule.eval_lsingle

theorem eval_smul (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (p • q) = p.eval r • eval r q := by
  apply induction_linear q
  · rw [smul_zero, map_zero, smul_zero]
    -- 🎉 no goals
  · intro f g e₁ e₂
    -- ⊢ ↑(eval r) (p • (f + g)) = Polynomial.eval r p • ↑(eval r) (f + g)
    rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
    -- 🎉 no goals
  intro i m
  -- ⊢ ↑(eval r) (p • ↑(single R i) m) = Polynomial.eval r p • ↑(eval r) (↑(single  …
  induction' p using Polynomial.induction_on' with _ _ e₁ e₂
  -- ⊢ ↑(eval r) ((p✝ + q✝) • ↑(single R i) m) = Polynomial.eval r (p✝ + q✝) • ↑(ev …
  · rw [add_smul, map_add, Polynomial.eval_add, e₁, e₂, add_smul]
    -- 🎉 no goals
  · rw [monomial_smul_single, eval_single, Polynomial.eval_monomial, eval_single, smul_comm, ←
      smul_smul, pow_add, mul_smul]
#align polynomial_module.eval_smul PolynomialModule.eval_smul

@[simp]
theorem eval_map (f : M →ₗ[R] M') (q : PolynomialModule R M) (r : R) :
    eval (algebraMap R R' r) (map R' f q) = f (eval r q) := by
  apply induction_linear q
  · simp_rw [map_zero]
    -- 🎉 no goals
  · intro f g e₁ e₂
    -- ⊢ ↑(eval (↑(algebraMap R R') r)) (↑(map R' f✝) (f + g)) = ↑f✝ (↑(eval r) (f +  …
    simp_rw [map_add, e₁, e₂]
    -- 🎉 no goals
  · intro i m
    -- ⊢ ↑(eval (↑(algebraMap R R') r)) (↑(map R' f) (↑(single R i) m)) = ↑f (↑(eval  …
    rw [map_single, eval_single, eval_single, f.map_smul, ← map_pow, algebraMap_smul]
    -- 🎉 no goals
#align polynomial_module.eval_map PolynomialModule.eval_map

@[simp]
theorem eval_map' (f : M →ₗ[R] M) (q : PolynomialModule R M) (r : R) :
    eval r (map R f q) = f (eval r q) :=
  eval_map R f q r
#align polynomial_module.eval_map' PolynomialModule.eval_map'

-- Porting note: Synthesized `RingHomCompTriple (RingHom.id R) (RingHom.id R) (RingHom.id R)`
-- in a very ugly way.
/-- `comp p q` is the composition of `p : R[X]` and `q : M[X]` as `q(p(x))`.  -/
@[simps!]
noncomputable def comp (p : R[X]) : PolynomialModule R M →ₗ[R] PolynomialModule R M :=
  @LinearMap.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (@RingHomInvPair.triples _ _ _ _ _ _ RingHomInvPair.ids)
    ((eval p).restrictScalars R) (map R[X] (lsingle R 0))
#align polynomial_module.comp PolynomialModule.comp

theorem comp_single (p : R[X]) (i : ℕ) (m : M) : comp p (single R i m) = p ^ i • single R 0 m := by
  rw [comp_apply]
  -- ⊢ ↑(eval p) (↑(map R[X] (lsingle R 0)) (↑(single R i) m)) = p ^ i • ↑(single R …
  erw [map_single, eval_single]
  -- ⊢ p ^ i • ↑(lsingle R 0) m = p ^ i • ↑(single R 0) m
  rfl
  -- 🎉 no goals
#align polynomial_module.comp_single PolynomialModule.comp_single

theorem comp_eval (p : R[X]) (q : PolynomialModule R M) (r : R) :
    eval r (comp p q) = eval (p.eval r) q := by
  rw [← LinearMap.comp_apply]
  -- ⊢ ↑(LinearMap.comp (eval r) (comp p)) q = ↑(eval (Polynomial.eval r p)) q
  apply induction_linear q
  · simp_rw [map_zero]
    -- 🎉 no goals
  · intro _ _ e₁ e₂
    -- ⊢ ↑(LinearMap.comp (eval r) (comp p)) (f✝ + g✝) = ↑(eval (Polynomial.eval r p) …
    simp_rw [map_add, e₁, e₂]
    -- 🎉 no goals
  · intro i m
    -- ⊢ ↑(LinearMap.comp (eval r) (comp p)) (↑(single R i) m) = ↑(eval (Polynomial.e …
    rw [LinearMap.comp_apply, comp_single, eval_single, eval_smul, eval_single, pow_zero, one_smul,
      Polynomial.eval_pow]
#align polynomial_module.comp_eval PolynomialModule.comp_eval

theorem comp_smul (p p' : R[X]) (q : PolynomialModule R M) :
    comp p (p' • q) = p'.comp p • comp p q := by
  rw [comp_apply, map_smul, eval_smul, Polynomial.comp, Polynomial.eval_map, comp_apply]
  -- ⊢ eval₂ (algebraMap R R[X]) p p' • ↑(eval p) (↑(map R[X] (lsingle R 0)) q) = e …
  rfl
  -- 🎉 no goals
#align polynomial_module.comp_smul PolynomialModule.comp_smul

end PolynomialModule
