/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

This will be done in the following steps:

1. Some auxiliary lemmas on infinite products and sums
2. Results on the von Mangoldt function restricted to a residue class
3. (TODO) Results on its L-series and an auxiliary function related to it
4. (TODO) Derivation of Dirichlet's Theorem
-/

/-!
### Auxiliary statements

An infinite product or sum over a function supported in prime powers can be written
as an iterated product or sum over primes and natural numbers.
-/

section auxiliary

variable {α β γ : Type*} [CommGroup α] [UniformSpace α] [UniformGroup α] [CompleteSpace α]
  [T0Space α]

open Nat.Primes in
@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1)) := by
  have hfm' : Multipliable fun pk : Nat.Primes × ℕ ↦ f (pk.fst ^ (pk.snd + 1)) :=
    prodNatEquiv.symm.multipliable_iff.mp <| by
      simpa only [← coe_prodNatEquiv_apply, Prod.eta, Function.comp_def, Equiv.apply_symm_apply]
        using hfm.subtype _
  simp only [← tprod_subtype_eq_of_mulSupport_subset hf, Set.coe_setOf, ← prodNatEquiv.tprod_eq,
    ← tprod_prod hfm']
  refine tprod_congr fun (p, k) ↦ congrArg f <| coe_prodNatEquiv_apply ..

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = (∏' p : Nat.Primes, f p) *  ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k : ℕ ↦ f (p ^ (k + 1)) :=
    hfm.comp_injective <| (strictMono_nat_of_lt_succ
      fun k ↦ pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one (k + 1)).injective
  conv_lhs =>
    enter [1, p]; rw [tprod_eq_zero_mul (hfs' p), zero_add, pow_one]
    enter [2, 1, k]; rw [add_assoc, one_add_one_eq_two]
  exact tprod_mul (Multipliable.subtype hfm _) <|
    Multipliable.prod (f := fun (pk : Nat.Primes × ℕ) ↦ f (pk.1 ^ (pk.2 + 2))) <|
    hfm.comp_injective <| Subtype.val_injective |>.comp
    Nat.Primes.prodNatEquiv.injective |>.comp <|
    Function.Injective.prodMap (fun ⦃_ _⦄ a ↦ a) <| add_left_injective 1

end auxiliary

/-!
### The L-series of the von Mangoldt function restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction.vonMangoldt

open Complex LSeries DirichletCharacter

open scoped LSeries.notation

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
  Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg

lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ vonMangoldt_nonneg)

@[simp]
lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_zero, map_zero, ofReal_zero,
    implies_true]

lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  unfold LSeriesSummable
  have := LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert this.indicator {n : ℕ | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +contextual only [term, Set.indicator, Set.mem_setOf_eq, hn, ↓reduceIte, apply_ite,
      ite_self]
  · simp +contextual only [term, Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_not_mem,
      ofReal_zero, zero_div, ite_self]

/-- The set we are interested in (prime numbers in the residue class `a`) is the same as the support
of `ArithmeticFunction.vonMangoldt.residueClass` restricted to primes (and divided by `n`;
this is how this result is used later). -/
lemma support_residueClass_prime_div :
    Function.support (fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n) =
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by
  simp only [Function.support, ne_eq, div_eq_zero_iff, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_eq_zero, not_or, Classical.not_imp]
  ext1 p
  simp only [Set.mem_setOf_eq]
  exact ⟨fun H ↦ ⟨H.1.1, H.1.2.1⟩,
    fun H ↦ ⟨⟨H.1, H.2, vonMangoldt_ne_zero_iff.mpr H.1.isPrimePow⟩, H.1.ne_zero⟩⟩

private noncomputable def F₀ (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / n

private noncomputable def F' (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))

private noncomputable def F'' : Nat.Primes × ℕ → ℝ := F' ∘ (Prod.map _root_.id (· + 1))

private lemma F''_le (p : Nat.Primes) (k : ℕ) : F'' (p, k) ≤ 2 * (p : ℝ)⁻¹ ^ (k + 3 / 2 : ℝ) :=
  calc _
    _ = Real.log p * (p : ℝ)⁻¹ ^ (k + 2) := by
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow, div_eq_mul_inv,
        inv_pow (p : ℝ) (k + 2)]
    _ ≤ (p: ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (p : ℝ)⁻¹ ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div p.val.cast_nonneg one_half_pos)
          (pow_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg ↑p)) (k + 2))
    _ = 2 * (p : ℝ)⁻¹ ^ (-1 / 2 : ℝ) * (p : ℝ)⁻¹ ^ (k + 2) := by
      simp only [← div_mul, div_one, mul_comm, neg_div, Real.inv_rpow p.val.cast_nonneg,
        ← Real.rpow_neg p.val.cast_nonneg, neg_neg]
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast,
        ← Real.rpow_add <| by have := p.prop.pos; positivity, Nat.cast_add, Nat.cast_two,
        add_comm, add_assoc]
      norm_num

open Nat.Primes

private lemma summable_F'' : Summable F'' := by
  have hp₀ (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ := inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ <| mod_cast p.prop.pos).mpr <| Nat.one_lt_cast.mpr <| p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × ℕ) ↦ (pk.1 : ℝ)⁻¹ ^ (pk.2 + 3 / 2 : ℝ) by
    refine (Summable.mul_left 2 this).of_nonneg_of_le (fun pk ↦ ?_) (fun pk ↦ F''_le pk.1 pk.2)
    simp only [F'', Function.comp_apply, F', F₀, Prod.map_fst, id_eq, Prod.map_snd, Nat.cast_pow]
    have := vonMangoldt_nonneg (n := (pk.1 : ℕ) ^ (pk.2 + 2))
    positivity
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun _ ↦ by positivity)).mpr ⟨(fun p ↦ ?_), ?_⟩
  · dsimp only -- otherwise the `exact` below times out
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    refine (summable_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
      |>.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    · have := sub_pos.mpr (hp₁ p)
      positivity
    · rw [Real.inv_rpow p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg]
      gcongr
      rw [inv_le_comm₀ (sub_pos.mpr (hp₁ p)) zero_lt_two, le_sub_comm,
        show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
      exact Nat.ofNat_le_cast.mpr p.prop.two_le

/-- The function `n ↦ Λ n / n`, restriced to non-primes in a residue class, is summable.
This is used to convert results on `ArithmeticFunction.vonMangoldt.residueClass` to results
on primes in an arithmetic progression. -/
lemma summable_residueClass_non_primes_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n := by
  have h₀ (n : ℕ) : 0 ≤ (if n.Prime then 0 else residueClass a n) / n := by
    have := residueClass_nonneg a n
    positivity
  have hleF₀ (n : ℕ) : (if n.Prime then 0 else residueClass a n) / n ≤ F₀ n := by
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs; exacts [le_rfl, residueClass_le a n]
  refine Summable.of_nonneg_of_le h₀ hleF₀ ?_
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
  swap
  · simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, Nat.cast_eq_zero, true_or, F₀]
  have hFF' :
      F₀ ∘ Subtype.val (p := fun n ↦ n ∈ {n | IsPrimePow n}) = F' ∘ ⇑prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F').mpr ?_
    ext1 n
    simp only [Function.comp_apply, F']
    congr
  rw [hFF']
  refine (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F')).mpr ?_
  have hF'₀ (p : Nat.Primes) : F' (p, 0) = 0 := by simp only [zero_add, pow_one, hF₀, F']
  have hF'₁ : F'' = F' ∘ (Prod.map _root_.id (· + 1)) := by
    ext1
    simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, F'', F']
  refine (Function.Injective.summable_iff ?_ fun u hu ↦ ?_).mp <| hF'₁ ▸ summable_F''
  · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
  · simp only [Set.range_prod_map, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1, ← hu]

variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_setOf_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function with Dirichlet charaters. -/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/-- The L-series of the von Mangoldt function restricted to the residue class `a` mod `q`
with `a` invertible in `ZMod q` is a linear combination of logarithmic derivatives of
L-functions of the Dirichlet characters mod `q` (on `re s > 1`). -/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
    ← LSeries_sum <| fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr s fun {n} _ ↦ ?_
  simp only [Pi.smul_apply, residueClass_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

end ArithmeticFunction.vonMangoldt

end arith_prog
