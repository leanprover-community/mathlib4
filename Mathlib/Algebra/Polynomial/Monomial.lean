/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Module

/-!
# `monomial`, `X` and `C`

This file defines the basic constructions of polynomials from coefficients.

## Main definitions
* `Polynomial.monomial s a`: `a * X^s`
* `Polynomial.C a`: the constant polynomial with value `a`
* `Polynomial.X`: the polynomial variable (aka indeterminate)
-/

noncomputable section

open AddMonoidAlgebra Finset
open Finsupp hiding single
open Function hiding Commute

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q : R[X]}

section AddMonoidAlgebra

variable (R)

end AddMonoidAlgebra

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] where
  toFun t := ⟨Finsupp.single n t⟩
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp`.
  map_add' x y := by simp; rw [ofFinsupp_add]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [← ofFinsupp_smul]`.
  map_smul' r x := by simp; rw [← ofFinsupp_smul, smul_single']

@[simp]
theorem toFinsupp_monomial (n : ℕ) (r : R) : (monomial n r).toFinsupp = Finsupp.single n r := by
  simp [monomial]

@[simp]
theorem ofFinsupp_single (n : ℕ) (r : R) : (⟨Finsupp.single n r⟩ : R[X]) = monomial n r := by
  simp [monomial]

@[simp]
theorem monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 :=
  (monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl

-- TODO: can't we just delete this one?
theorem monomial_add (n : ℕ) (r s : R) : monomial n (r + s) = monomial n r + monomial n s :=
  (monomial n).map_add _ _

theorem monomial_mul_monomial (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * s) :=
  toFinsupp_injective <| by
    simp only [toFinsupp_monomial, toFinsupp_mul, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r ^ k = monomial (n * k) (r ^ k) := by
  induction k with
  | zero => simp [pow_zero, monomial_zero_one]
  | succ k ih => simp [pow_succ, ih, monomial_mul_monomial, mul_add, add_comm]

theorem smul_monomial {S} [SMulZeroClass S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  toFinsupp_injective <| by simp; rw [smul_single]

theorem monomial_injective (n : ℕ) : Function.Injective (monomial n : R → R[X]) :=
  (toFinsuppIso R).symm.injective.comp (single_injective n)

@[simp]
theorem monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

theorem monomial_eq_monomial_iff {m n : ℕ} {a b : R} :
    monomial m a = monomial n b ↔ m = n ∧ a = b ∨ a = 0 ∧ b = 0 := by
  rw [← toFinsupp_inj, toFinsupp_monomial, toFinsupp_monomial, Finsupp.single_eq_single_iff]

/-- `C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
  { monomial 0 with
    map_one' := by simp [monomial_zero_one]
    map_mul' := by simp [monomial_mul_monomial]
    map_zero' := by simp }

@[simp]
theorem monomial_zero_left (a : R) : monomial 0 a = C a :=
  rfl

@[simp]
theorem toFinsupp_C (a : R) : (C a).toFinsupp = single 0 a :=
  rfl

theorem C_0 : C (0 : R) = 0 := by simp

theorem C_1 : C (1 : R) = 1 :=
  rfl

theorem C_mul : C (a * b) = C a * C b :=
  C.map_mul a b

theorem C_add : C (a + b) = C a + C b :=
  C.map_add a b

@[simp]
theorem smul_C {S} [SMulZeroClass S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r

theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n

theorem C_eq_natCast (n : ℕ) : C (n : R) = (n : R[X]) :=
  map_natCast C n

@[deprecated (since := "2024-04-17")]
alias C_eq_nat_cast := C_eq_natCast

@[simp]
theorem C_mul_monomial : C a * monomial n b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp]
theorem monomial_mul_C : monomial n a * C b = monomial n (a * b) := by
  simp only [← monomial_zero_left, monomial_mul_monomial, add_zero]

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] :=
  monomial 1 1

theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl

theorem monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n := by
  induction n with
  | zero => simp [monomial_zero_one]
  | succ n ih => rw [pow_succ, ← ih, ← monomial_one_one_eq_X, monomial_mul_monomial, mul_one]

@[simp]
theorem toFinsupp_X : X.toFinsupp = Finsupp.single 1 (1 : R) :=
  rfl

theorem X_ne_C [Nontrivial R] (a : R) : X ≠ C a := by
  intro he
  simpa using monomial_eq_monomial_iff.1 he

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
theorem X_mul : X * p = p * X := by
  rcases p with ⟨⟩
  -- Porting note: `ofFinsupp.injEq` is required.
  simp only [X, ← ofFinsupp_single, ← ofFinsupp_mul, LinearMap.coe_mk, ofFinsupp.injEq]
  -- Porting note: Was `ext`.
  refine Finsupp.ext fun _ => ?_
  simp [AddMonoidAlgebra.mul_apply, AddMonoidAlgebra.sum_single_index, add_comm]

theorem X_pow_mul {n : ℕ} : X ^ n * p = p * X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ]

/-- Prefer putting constants to the left of `X`.

This lemma is the loop-avoiding `simp` version of `Polynomial.X_mul`. -/
@[simp]
theorem X_mul_C (r : R) : X * C r = C r * X :=
  X_mul

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul`. -/
@[simp]
theorem X_pow_mul_C (r : R) (n : ℕ) : X ^ n * C r = C r * X ^ n :=
  X_pow_mul

theorem X_pow_mul_assoc {n : ℕ} : p * X ^ n * q = p * q * X ^ n := by
  rw [mul_assoc, X_pow_mul, ← mul_assoc]

/-- Prefer putting constants to the left of `X ^ n`.

This lemma is the loop-avoiding `simp` version of `X_pow_mul_assoc`. -/
@[simp]
theorem X_pow_mul_assoc_C {n : ℕ} (r : R) : p * X ^ n * C r = p * C r * X ^ n :=
  X_pow_mul_assoc

theorem commute_X (p : R[X]) : Commute X p :=
  X_mul

theorem commute_X_pow (p : R[X]) (n : ℕ) : Commute (X ^ n) p :=
  X_pow_mul

@[simp]
theorem monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n + 1) r := by
  erw [monomial_mul_monomial, mul_one]

@[simp]
theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) :
    monomial n r * X ^ k = monomial (n + k) r := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, add_assoc]

@[simp]
theorem X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n + 1) r := by
  rw [X_mul, monomial_mul_X]

@[simp]
theorem X_pow_mul_monomial (k n : ℕ) (r : R) : X ^ k * monomial n r = monomial (n + k) r := by
  rw [X_pow_mul, monomial_mul_X_pow]

theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 := by
  simp [coeff, Finsupp.single_apply]

@[simp]
theorem coeff_monomial_same (n : ℕ) (c : R) : (monomial n c).coeff n = c :=
  Finsupp.single_eq_same

theorem coeff_monomial_of_ne {m n : ℕ} (c : R) (h : n ≠ m) : (monomial n c).coeff m = 0 :=
  Finsupp.single_eq_of_ne h

theorem coeff_one {n : ℕ} : coeff (1 : R[X]) n = if n = 0 then 1 else 0 := by
  simp_rw [eq_comm (a := n) (b := 0)]
  exact coeff_monomial

@[simp]
theorem coeff_one_zero : coeff (1 : R[X]) 0 = 1 := by
  simp [coeff_one]

@[simp]
theorem coeff_X_one : coeff (X : R[X]) 1 = 1 :=
  coeff_monomial

@[simp]
theorem coeff_X_zero : coeff (X : R[X]) 0 = 0 :=
  coeff_monomial

@[simp]
theorem coeff_monomial_succ : coeff (monomial (n + 1) a) 0 = 0 := by simp [coeff_monomial]

theorem coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 :=
  coeff_monomial

theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : R[X]) n = 0 := by
  rw [coeff_X, if_neg hn.symm]

theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 := by
  convert coeff_monomial (a := a) (m := n) (n := 0) using 2
  simp [eq_comm]

@[simp]
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial

theorem coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 := by rw [coeff_C, if_neg h]

@[simp]
lemma coeff_C_succ {r : R} {n : ℕ} : coeff (C r) (n + 1) = 0 := by simp [coeff_C]

@[simp]
theorem coeff_natCast_ite : (Nat.cast m : R[X]).coeff n = ite (n = 0) m 0 := by
  simp only [← C_eq_natCast, coeff_C, Nat.cast_ite, Nat.cast_zero]

@[deprecated (since := "2024-04-17")]
alias coeff_nat_cast_ite := coeff_natCast_ite

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem coeff_ofNat_zero (a : ℕ) [a.AtLeastTwo] :
    coeff (no_index (OfNat.ofNat a : R[X])) 0 = OfNat.ofNat a :=
  coeff_monomial

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem coeff_ofNat_succ (a n : ℕ) [h : a.AtLeastTwo] :
    coeff (no_index (OfNat.ofNat a : R[X])) (n + 1) = 0 := by
  rw [← Nat.cast_eq_ofNat]
  simp

theorem C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, C a * X ^ n = monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, X, monomial_mul_monomial, mul_one]

@[simp high]
theorem toFinsupp_C_mul_X_pow (a : R) (n : ℕ) :
    Polynomial.toFinsupp (C a * X ^ n) = Finsupp.single n a := by
  rw [C_mul_X_pow_eq_monomial, toFinsupp_monomial]

theorem C_mul_X_eq_monomial : C a * X = monomial 1 a := by rw [← C_mul_X_pow_eq_monomial, pow_one]

@[simp high]
theorem toFinsupp_C_mul_X (a : R) : Polynomial.toFinsupp (C a * X) = Finsupp.single 1 a := by
  rw [C_mul_X_eq_monomial, toFinsupp_monomial]

theorem C_injective : Injective (C : R → R[X]) :=
  monomial_injective 0

@[simp]
theorem C_inj : C a = C b ↔ a = b :=
  C_injective.eq_iff

@[simp]
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  C_injective.eq_iff' (map_zero C)

theorem C_ne_zero : C a ≠ 0 ↔ a ≠ 0 :=
  C_eq_zero.not

theorem subsingleton_iff_subsingleton : Subsingleton R[X] ↔ Subsingleton R :=
  ⟨@Injective.subsingleton _ _ _ C_injective, by
    intro
    infer_instance⟩

theorem Nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R :=
  (subsingleton_or_nontrivial R).resolve_left fun _hI => h <| Subsingleton.elim _ _

theorem forall_eq_iff_forall_eq : (∀ f g : R[X], f = g) ↔ ∀ a b : R, a = b := by
  simpa only [← subsingleton_iff] using subsingleton_iff_subsingleton

/-- Monomials generate the additive monoid of polynomials. -/
theorem addSubmonoid_closure_setOf_eq_monomial :
    AddSubmonoid.closure { p : R[X] | ∃ n a, p = monomial n a } = ⊤ := by
  apply top_unique
  rw [← AddSubmonoid.map_equiv_top (toFinsuppIso R).symm.toAddEquiv, ←
    Finsupp.add_closure_setOf_eq_single, AddMonoidHom.map_mclosure]
  refine AddSubmonoid.closure_mono (Set.image_subset_iff.2 ?_)
  rintro _ ⟨n, a, rfl⟩
  exact ⟨n, a, Polynomial.ofFinsupp_single _ _⟩

theorem addHom_ext {M : Type*} [AddMonoid M] {f g : R[X] →+ M}
    (h : ∀ n a, f (monomial n a) = g (monomial n a)) : f = g :=
  AddMonoidHom.eq_of_eqOn_denseM addSubmonoid_closure_setOf_eq_monomial <| by
    rintro p ⟨n, a, rfl⟩
    exact h n a

@[ext high]
theorem addHom_ext' {M : Type*} [AddMonoid M] {f g : R[X] →+ M}
    (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  addHom_ext fun n => DFunLike.congr_fun (h n)

@[ext high]
theorem lhom_ext' {M : Type*} [AddCommMonoid M] [Module R M] {f g : R[X] →ₗ[R] M}
    (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
  LinearMap.toAddMonoidHom_injective <| addHom_ext fun n => LinearMap.congr_fun (h n)

-- this has the same content as the subsingleton
theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 := by
  rw [← one_smul R p, ← h, zero_smul]

section Fewnomials

theorem support_monomial (n) {a : R} (H : a ≠ 0) : (monomial n a).support = singleton n := by
  rw [← ofFinsupp_single, support]; exact Finsupp.support_single_ne_zero _ H

theorem support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n := by
  rw [← ofFinsupp_single, support]
  exact Finsupp.support_single_subset

theorem support_C_mul_X {c : R} (h : c ≠ 0) : Polynomial.support (C c * X) = singleton 1 := by
  rw [C_mul_X_eq_monomial, support_monomial 1 h]

theorem support_C_mul_X' (c : R) : Polynomial.support (C c * X) ⊆ singleton 1 := by
  simpa only [C_mul_X_eq_monomial] using support_monomial' 1 c

theorem support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) :
    Polynomial.support (C c * X ^ n) = singleton n := by
  rw [C_mul_X_pow_eq_monomial, support_monomial n h]

theorem support_C_mul_X_pow' (n : ℕ) (c : R) : Polynomial.support (C c * X ^ n) ⊆ singleton n := by
  simpa only [C_mul_X_pow_eq_monomial] using support_monomial' n c

open Finset

theorem support_binomial' (k m : ℕ) (x y : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m) ⊆ {k, m} :=
  support_add.trans
    (union_subset
      ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m})))
      ((support_C_mul_X_pow' m y).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_singleton_self m)))))

theorem support_trinomial' (k m n : ℕ) (x y z : R) :
    Polynomial.support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ {k, m, n} :=
  support_add.trans
    (union_subset
      (support_add.trans
        (union_subset
          ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m, n})))
          ((support_C_mul_X_pow' m y).trans
            (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n}))))))
      ((support_C_mul_X_pow' n z).trans
        (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))))))

end Fewnomials

theorem X_pow_eq_monomial (n) : X ^ n = monomial n (1 : R) := by
  induction n with
  | zero => rw [pow_zero, monomial_zero_one]
  | succ n hn => rw [pow_succ, hn, X, monomial_mul_monomial, one_mul]

@[simp high]
theorem toFinsupp_X_pow (n : ℕ) : (X ^ n).toFinsupp = Finsupp.single n (1 : R) := by
  rw [X_pow_eq_monomial, toFinsupp_monomial]

theorem smul_X_eq_monomial {n} : a • X ^ n = monomial n (a : R) := by
  rw [X_pow_eq_monomial, smul_monomial, smul_eq_mul, mul_one]

theorem support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (X ^ n : R[X]).support = singleton n := by
  convert support_monomial n H
  exact X_pow_eq_monomial n

theorem support_X_empty (H : (1 : R) = 0) : (X : R[X]).support = ∅ := by
  rw [X, H, monomial_zero_right, support_zero]

theorem support_X (H : ¬(1 : R) = 0) : (X : R[X]).support = singleton 1 := by
  rw [← pow_one X, support_X_pow H 1]

theorem monomial_left_inj {a : R} (ha : a ≠ 0) {i j : ℕ} :
    monomial i a = monomial j a ↔ i = j := by
  simp only [← ofFinsupp_single, ofFinsupp.injEq, Finsupp.single_left_inj ha]

theorem binomial_eq_binomial {k l m n : ℕ} {u v : R} (hu : u ≠ 0) (hv : v ≠ 0) :
    C u * X ^ k + C v * X ^ l = C u * X ^ m + C v * X ^ n ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n := by
  simp_rw [C_mul_X_pow_eq_monomial, ← toFinsupp_inj, toFinsupp_add, toFinsupp_monomial]
  exact Finsupp.single_add_single_eq_single_add_single hu hv

theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} :
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  -- Porting note: `ofFinsupp.injEq` is required.
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff

instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi, coeff_monomial]
    · have : f.coeff i = 0 := by
        rw [← not_mem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_card
    exact support_monomial' _ _

theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g := by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C' : g = g'.comp (toFinsuppIso R) := by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B, C', A]

@[ext high]
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂

end Semiring

section Ring

variable [Ring R]

@[simp]
theorem monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -monomial n a := by
  rw [eq_neg_iff_add_eq_zero, ← monomial_add, neg_add_cancel, monomial_zero_right]

theorem monomial_sub (n : ℕ) : monomial n (a - b) = monomial n a - monomial n b := by
  rw [sub_eq_add_neg, monomial_add, monomial_neg, sub_eq_add_neg]

theorem C_eq_intCast (n : ℤ) : C (n : R) = n := by simp

@[deprecated (since := "2024-04-17")]
alias C_eq_int_cast := C_eq_intCast

theorem C_neg : C (-a) = -C a :=
  RingHom.map_neg C a

theorem C_sub : C (a - b) = C a - C b :=
  RingHom.map_sub C a b

end Ring

section NonzeroSemiring

variable [Semiring R]

@[simp]
theorem X_ne_zero [Nontrivial R] : (X : R[X]) ≠ 0 :=
  mt (congr_arg fun p => coeff p 1) (by simp)

end NonzeroSemiring

section DivisionSemiring
variable [DivisionSemiring R]

lemma nnqsmul_eq_C_mul (q : ℚ≥0) (f : R[X]) : q • f = Polynomial.C (q : R) * f := by
  rw [← NNRat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionSemiring

section DivisionRing

variable [DivisionRing R]

theorem qsmul_eq_C_mul (a : ℚ) (f : R[X]) : a • f = Polynomial.C (a : R) * f := by
  rw [← Rat.smul_one_eq_cast, ← Polynomial.smul_C, C_1, smul_one_mul]

end DivisionRing

@[simp]
theorem nontrivial_iff [Semiring R] : Nontrivial R[X] ↔ Nontrivial R :=
  ⟨fun h =>
    let ⟨_r, _s, hrs⟩ := @exists_pair_ne _ h
    Nontrivial.of_polynomial_ne hrs,
    fun h => @Polynomial.nontrivial _ _ h⟩

end Polynomial
