/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!
# The Möbius function and Möbius inversion

## Main Definitions

* `μ` is the Möbius function (spelled `moebius` in code; the notation `μ` is available by opening
  the namespace `ArithmeticFunction.Moebius`).

## Main Results

* Several forms of Möbius inversion:
* `sum_eq_iff_sum_mul_moebius_eq` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `CommGroupWithZero`
* And variants that apply when the equalities only hold on a set `S : Set ℕ` such that
  `m ∣ n → n ∈ S → m ∈ S`:
* `sum_eq_iff_sum_mul_moebius_eq_on` for functions to a `CommRing`
* `sum_eq_iff_sum_smul_moebius_eq_on` for functions to an `AddCommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on` for functions to a `CommGroup`
* `prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero` for functions to a `CommGroupWithZero`

## Tags

arithmetic functions, dirichlet convolution, divisors

-/

@[expose] public section

open Finset Nat

variable {R : Type*}

namespace ArithmeticFunction

open scoped zeta

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : ArithmeticFunction ℤ :=
  ⟨fun n => if Squarefree n then (-1) ^ cardFactors n else 0, by simp⟩

@[inherit_doc]
scoped[ArithmeticFunction.Moebius] notation "μ" => ArithmeticFunction.moebius

open scoped Moebius

@[simp]
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1) ^ cardFactors n :=
  if_pos h

@[simp]
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h

theorem moebius_apply_one : μ 1 = 1 := by simp

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n := by
  constructor <;> intro h
  · contrapose! h
    simp [h]
  · simp [h]

theorem moebius_eq_or (n : ℕ) : μ n = 0 ∨ μ n = 1 ∨ μ n = -1 := by
  simp only [moebius, coe_mk]
  split_ifs
  · right
    exact neg_one_pow_eq_or ..
  · left
    rfl

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 := by
  have := moebius_eq_or n
  lia

theorem moebius_sq_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : μ l ^ 2 = 1 := by
  rw [moebius_apply_of_squarefree hl, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem abs_moebius_eq_one_of_squarefree {l : ℕ} (hl : Squarefree l) : |μ l| = 1 := by
  simp only [moebius_apply_of_squarefree hl, abs_pow, abs_neg, abs_one, one_pow]

theorem moebius_sq {n : ℕ} :
    μ n ^ 2 = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact moebius_sq_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, zero_pow (show 2 ≠ 0 by simp)]

theorem abs_moebius {n : ℕ} :
    |μ n| = if Squarefree n then 1 else 0 := by
  split_ifs with h
  · exact abs_moebius_eq_one_of_squarefree h
  · simp only [moebius_eq_zero_of_not_squarefree h, abs_zero]

theorem abs_moebius_le_one {n : ℕ} : |μ n| ≤ 1 := by
  rw [abs_moebius, apply_ite (· ≤ 1)]
  simp

theorem moebius_apply_prime {p : ℕ} (hp : p.Prime) : μ p = -1 := by
  rw [moebius_apply_of_squarefree hp.squarefree, cardFactors_apply_prime hp, pow_one]

theorem moebius_apply_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    μ (p ^ k) = if k = 1 then -1 else 0 := by
  split_ifs with h
  · rw [h, pow_one, moebius_apply_prime hp]
  rw [moebius_eq_zero_of_not_squarefree]
  rw [squarefree_pow_iff hp.ne_one hk, not_and_or]
  exact Or.inr h

theorem moebius_apply_isPrimePow_not_prime {n : ℕ} (hn : IsPrimePow n) (hn' : ¬n.Prime) :
    μ n = 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  rw [moebius_apply_prime_pow hp hk.ne', if_neg]
  rintro rfl
  exact hn' (by simpa)

@[arith_mult]
theorem isMultiplicative_moebius : IsMultiplicative μ := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp, fun {n m} hn hm hnm => ?_⟩
  simp only [moebius, coe_mk, squarefree_mul hnm, ite_zero_mul_ite_zero, cardFactors_mul hn hm,
    pow_add]

theorem IsMultiplicative.prodPrimeFactors_one_add_of_squarefree [CommSemiring R]
    {f : ArithmeticFunction R} (h_mult : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 + f p) = ∑ d ∈ n.divisors, f d := by
  trans (∏ᵖ p ∣ n, ((ζ : ArithmeticFunction R) + f) p)
  · simp_rw [prodPrimeFactors_apply hn.ne_zero, add_apply, natCoe_apply]
    apply prod_congr rfl; intro p hp
    rw [zeta_apply_ne (prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_zero, cast_one]
  rw [isMultiplicative_zeta.natCast.prodPrimeFactors_add_of_squarefree h_mult hn,
    coe_zeta_mul_apply]

theorem IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree [CommRing R]
    (f : ArithmeticFunction R) (hf : f.IsMultiplicative) {n : ℕ} (hn : Squarefree n) :
    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d := by
  trans (∏ p ∈ n.primeFactors, (1 + (ArithmeticFunction.pmul (μ : ArithmeticFunction R) f) p))
  · apply prod_congr rfl; intro p hp
    rw [pmul_apply, intCoe_apply, ArithmeticFunction.moebius_apply_prime
        (prime_of_mem_primeFactorsList (List.mem_toFinset.mp hp))]
    ring
  · rw [(isMultiplicative_moebius.intCast.pmul hf).prodPrimeFactors_one_add_of_squarefree hn]
    simp_rw [pmul_apply, intCoe_apply]

open UniqueFactorizationMonoid

@[simp]
theorem moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1 := by
  ext n
  induction n using recOnPosPrimePosCoprime with
  | zero => rw [map_zero, map_zero]
  | one => simp
  | prime_pow p n hp hn =>
    rw [coe_mul_zeta_apply, sum_divisors_prime_pow hp, sum_range_succ']
    simp_rw [pow_zero, moebius_apply_one, moebius_apply_prime_pow hp (succ_ne_zero _), succ_inj,
      sum_ite_eq', mem_range, if_pos hn, neg_add_cancel]
    rw [one_apply_ne]
    rw [Ne, pow_eq_one_iff hn.ne']
    exact hp.ne_one
  | coprime a b _ha _hb hab ha' hb' =>
    rw [IsMultiplicative.map_mul_of_coprime _ hab, ha', hb',
      IsMultiplicative.map_mul_of_coprime isMultiplicative_one hab]
    exact isMultiplicative_moebius.mul isMultiplicative_zeta.natCast

@[simp]
theorem coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1 := by
  rw [mul_comm, moebius_mul_coe_zeta]

@[simp]
theorem coe_moebius_mul_coe_zeta [Ring R] : (μ * ζ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, moebius_mul_coe_zeta, intCoe_one]

@[simp]
theorem coe_zeta_mul_coe_moebius [Ring R] : (ζ * μ : ArithmeticFunction R) = 1 := by
  rw [← coe_coe, ← intCoe_mul, coe_zeta_mul_moebius, intCoe_one]

section CommRing

variable [CommRing R]

instance : Invertible (ζ : ArithmeticFunction R) where
  invOf := μ
  invOf_mul_self := coe_moebius_mul_coe_zeta
  mul_invOf_self := coe_zeta_mul_coe_moebius

/-- A unit in `ArithmeticFunction R` that evaluates to `ζ`, with inverse `μ`. -/
def zetaUnit : (ArithmeticFunction R)ˣ :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
theorem coe_zetaUnit : ((zetaUnit : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = ζ :=
  rfl

@[simp]
theorem inv_zetaUnit : ((zetaUnit⁻¹ : (ArithmeticFunction R)ˣ) : ArithmeticFunction R) = μ :=
  rfl

end CommRing

/-- Möbius inversion for functions to an `AddCommGroup`. -/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd = f n := by
  let f' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
  let g' : ArithmeticFunction R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
  trans (ζ : ArithmeticFunction ℤ) • f' = g'
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      rw [coe_zeta_smul_apply]
      simp only [forall_prop_of_true, succ_pos', f', g', coe_mk, succ_ne_zero, ite_false]
      rw [sum_congr rfl fun x hx => if_neg (pos_of_mem_divisors hx).ne']
  trans μ • g' = f'
  · constructor <;> intro h <;>
      simp only [← h, ← mul_smul, moebius_mul_coe_zeta, coe_zeta_mul_moebius, one_smul]
  · rw [ArithmeticFunction.ext_iff]
    apply forall_congr'
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [forall_prop_of_true, succ_pos', smul_apply, f', g', coe_mk, succ_ne_zero,
        ite_false]
      rw [sum_congr rfl fun x hx => ?_]
      rw [if_neg (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)).ne']

/-- Möbius inversion for functions to a `Ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq]
  apply forall_congr'
  refine fun a => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroup R] {f g : ℕ → R} :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

/-- Möbius inversion for functions to a `CommGroupWithZero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R}
    (hf : ∀ n : ℕ, 0 < n → f n ≠ 0) (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
    (∀ n > 0, ∏ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1) fun n =>
            if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)), Units.coeHom_apply,
      Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Möbius inversion for functions to an `AddCommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem sum_eq_iff_sum_smul_moebius_eq_on [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  constructor
  · intro h
    let G := fun (n : ℕ) => (∑ i ∈ n.divisors, f i)
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, μ (n/d) • G d = f n by
      rw [sum_divisorsAntidiagonal' (f := fun x y => μ x • g y), ← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    rw [← sum_divisorsAntidiagonal' (f := fun x y => μ x • G y)]
    apply sum_eq_iff_sum_smul_moebius_eq.mp _ n hn
    intro _ _; rfl
  · intro h
    let F := fun (n : ℕ) => ∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd
    intro n hn hnP
    suffices ∑ d ∈ n.divisors, F d = g n by
      rw [← this, sum_congr rfl]
      intro d hd
      rw [← h d (pos_of_mem_divisors hd) <| hs d n (dvd_of_mem_divisors hd) hnP]
    apply sum_eq_iff_sum_smul_moebius_eq.mpr _ n hn
    intro _ _; rfl

theorem sum_eq_iff_sum_smul_moebius_eq_on' [AddCommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) (hs₀ : 0 ∉ s) :
    (∀ n ∈ s, (∑ i ∈ n.divisors, f i) = g n) ↔
     ∀ n ∈ s, (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • g x.snd) = f n := by
  have : ∀ P : ℕ → Prop, ((∀ n ∈ s, P n) ↔ (∀ n > 0, n ∈ s → P n)) := fun P ↦ by
    refine forall_congr' (fun n ↦ ⟨fun h _ ↦ h, fun h hn ↦ h ?_ hn⟩)
    contrapose! hs₀
    simpa [nonpos_iff_eq_zero.mp hs₀] using hn
  simpa only [this] using sum_eq_iff_sum_smul_moebius_eq_on s hs

/-- Möbius inversion for functions to a `Ring`, where the equalities only hold on a well-behaved
set. -/
theorem sum_eq_iff_sum_mul_moebius_eq_on [NonAssocRing R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∑ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s →
        (∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd) = f n := by
  rw [sum_eq_iff_sum_smul_moebius_eq_on s hs]
  apply forall_congr'
  intro a; refine imp_congr_right ?_
  refine fun _ => imp_congr_right fun _ => (sum_congr rfl fun x _hx => ?_).congr_left
  rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `CommGroup`, where the equalities only hold on a
well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on [CommGroup R] {f g : ℕ → R}
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq_on (Additive R) _ _ _ s hs

/-- Möbius inversion for functions to a `CommGroupWithZero`, where the equalities only hold on
a well-behaved set. -/
theorem prod_eq_iff_prod_pow_moebius_eq_on_of_nonzero [CommGroupWithZero R]
    (s : Set ℕ) (hs : ∀ m n, m ∣ n → n ∈ s → m ∈ s) {f g : ℕ → R}
    (hf : ∀ n > 0, f n ≠ 0) (hg : ∀ n > 0, g n ≠ 0) :
    (∀ n > 0, n ∈ s → (∏ i ∈ n.divisors, f i) = g n) ↔
      ∀ n > 0, n ∈ s → (∏ x ∈ n.divisorsAntidiagonal, g x.snd ^ μ x.fst) = f n := by
  refine
      Iff.trans
        (Iff.trans (forall_congr' fun n => ?_)
          (@prod_eq_iff_prod_pow_moebius_eq_on Rˣ _
            (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
            (fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1)
            s hs))
        (forall_congr' fun n => ?_) <;>
    refine imp_congr_right fun hn => ?_
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors hx), Units.coeHom_apply, Units.val_mk0]
  · dsimp
    rw [dif_pos hn, ← Units.val_inj, ← Units.coeHom_apply, map_prod, Units.val_mk0,
      prod_congr rfl _]
    intro x hx
    rw [dif_pos (pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)),
      Units.coeHom_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]

end ArithmeticFunction
