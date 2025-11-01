/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.ZMod.Coprime
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

The main steps of the proof are as follows.
1. Define `ArithmeticFunction.vonMangoldt.residueClass a` for `a : ZMod q`, which is
   a function `ℕ → ℝ` taking the value zero when `(n : ℤMod q) ≠ a` and `Λ n` else
   (where `Λ` is the von Mangoldt function `ArithmeticFunction.vonMangoldt`; we have
   `Λ (p^k) = log p` for prime powers and `Λ n = 0` otherwise.)
2. Show that this function can be written as a linear combination of functions
   of the form `χ * Λ` (pointwise product) with Dirichlet characters `χ` mod `q`.
   See `ArithmeticFunction.vonMangoldt.residueClass_eq`.
3. This implies that the L-series of `ArithmeticFunction.vonMangoldt.residueClass a`
   agrees (on `re s > 1`) with the corresponding linear combination of negative logarithmic
   derivatives of Dirichlet L-functions.
   See `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`.
4. Define an auxiliary function `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a` that is
   this linear combination of negative logarithmic derivatives of L-functions minus
   `(q.totient)⁻¹/(s-1)`, which cancels the pole at `s = 1`.
   See `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` for the statement
   that the auxiliary function agrees with the L-series of
   `ArithmeticFunction.vonMangoldt.residueClass` up to the term `(q.totient)⁻¹/(s-1)`.
5. Show that the auxiliary function is continuous on `re s ≥ 1`;
   see `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux`.
   This relies heavily on the non-vanishing of Dirichlet L-functions on the *closed*
   half-plane `re s ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), which
   in turn can only be stated since we know that the L-series of a Dirichlet character
   extends to an entire function (unless the character is trivial; then there is a
   simple pole at `s = 1`); see `DirichletCharacter.LFunction_eq_LSeries`
   (contributed by David Loeffler).
6. Show that the sum of `Λ n / n` over any residue class, but *excluding* the primes, converges.
   See `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.
7. Combining these ingredients, we can deduce that the sum of `Λ n / n` over
   the *primes* in a residue class must diverge.
   See `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`.
8. This finally easily implies that there must be infinitely many primes in the residue class.

## Definitions

* `ArithmeticFunction.vonMangoldt.residueClass a` (see above).
* `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` (see above).

## Main Result

We give two versions of **Dirichlet's Theorem**:
* `Nat.setOf_prime_and_eq_mod_infinite` states that the set of primes `p`
  such that `(p : ZMod q) = a` is infinite (when `a` is invertible in `ZMod q`).
* `Nat.forall_exists_prime_gt_and_eq_mod` states that for any natural number `n`
  there is a prime `p > n` such that `(p : ZMod q) = a`.

## Tags

prime number, arithmetic progression, residue class, Dirichlet's Theorem
-/

/-!
### Auxiliary statements

An infinite product or sum over a function supported in prime powers can be written
as an iterated product or sum over primes and natural numbers.
-/

section auxiliary

variable {α β γ : Type*} [CommGroup α] [UniformSpace α] [IsUniformGroup α] [CompleteSpace α]
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
    ← hfm'.tprod_prod]
  refine tprod_congr fun (p, k) ↦ congrArg f <| coe_prodNatEquiv_apply ..

@[to_additive tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = (∏' p : Nat.Primes, f p) * ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by
  rw [tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers hfm hf]
  have hfs' (p : Nat.Primes) : Multipliable fun k : ℕ ↦ f (p ^ (k + 1)) :=
    hfm.comp_injective <| (strictMono_nat_of_lt_succ
      fun k ↦ pow_lt_pow_right₀ p.prop.one_lt <| lt_add_one (k + 1)).injective
  conv_lhs =>
    enter [1, p]; rw [(hfs' p).tprod_eq_zero_mul, zero_add, pow_one]
    enter [2, 1, k]; rw [add_assoc, one_add_one_eq_two]
  exact (Multipliable.subtype hfm _).tprod_mul <|
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
  simp only [Set.indicator_apply_eq_zero, Set.mem_setOf_eq, Nat.cast_zero, map_zero,
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
  · simp +contextual only [term, Set.mem_setOf_eq, hn, not_false_eq_true, Set.indicator_of_notMem,
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
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (p : ℝ)⁻¹ ^ (k + 2) :=
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
    positivity [vonMangoldt_nonneg (n := (pk.1 : ℕ) ^ (pk.2 + 2))]
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun _ ↦ by positivity)).mpr ⟨(fun p ↦ ?_), ?_⟩
  · dsimp only -- otherwise the `exact` below times out
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    refine (summable_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
      |>.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    · positivity [sub_pos.mpr (hp₁ p)]
    · rw [Real.inv_rpow p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg]
      gcongr
      rw [inv_le_comm₀ (sub_pos.mpr (hp₁ p)) zero_lt_two, le_sub_comm,
        show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
      exact Nat.ofNat_le_cast.mpr p.prop.two_le

/-- The function `n ↦ Λ n / n`, restricted to non-primes in a residue class, is summable.
This is used to convert results on `ArithmeticFunction.vonMangoldt.residueClass` to results
on primes in an arithmetic progression. -/
lemma summable_residueClass_non_primes_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n := by
  have h₀ (n : ℕ) : 0 ≤ (if n.Prime then 0 else residueClass a n) / n := by
    positivity [residueClass_nonneg a n]
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
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1, ← hu]

variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_setOf_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
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
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  simp only [Pi.smul_apply, residueClass_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

variable (a)

open Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`;
see `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`. -/
noncomputable
abbrev LFunctionResidueClassAux (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

/-- The auxiliary function is continuous away from the zeros of the L-functions of the Dirichlet
characters mod `q` (including at `s = 1`). -/
lemma continuousOn_LFunctionResidueClassAux' :
    ContinuousOn (LFunctionResidueClassAux a)
      {s | s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0} := by
  rw [show LFunctionResidueClassAux a = fun s ↦ _ from rfl]
  simp only [LFunctionResidueClassAux, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs ↦ ?_
    have := LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ q) (s := s)
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finset_sum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    refine (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs ↦ ?_
    simp only [ne_eq, Set.mem_setOf_eq] at hs
    rcases hs with rfl | hs
    · simp only [ne_eq, Set.mem_setOf_eq, one_re, le_refl,
        LFunction_ne_zero_of_one_le_re χ (.inl hχ), not_false_eq_true]
    · exact hs χ

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a simple pole at `s = 1` with residue `(q.totient)⁻¹`.
The statement as given here in terms of `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux`
is equivalent. -/
lemma continuousOn_LFunctionResidueClassAux :
    ContinuousOn (LFunctionResidueClassAux a) {s | 1 ≤ s.re} := by
  refine (continuousOn_LFunctionResidueClassAux' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_setOf_eq, true_or]
  · simp only [ne_eq, Set.mem_setOf_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_setOf.mp hs

variable {a}

open scoped LSeries.notation

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
    Set.EqOn (LFunctionResidueClassAux a)
      (fun s ↦ L ↗(residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  replace hs := Set.mem_setOf.mp hs
  simp only [LSeries_residueClass_eq ha hs, LFunctionResidueClassAux]
  rw [neg_div, ← neg_add', mul_neg, ← neg_mul, div_eq_mul_one_div (q.totient : ℂ)⁻¹,
    sub_eq_add_neg, ← neg_mul, ← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  classical -- for `Fintype.sum_eq_add_sum_compl`
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply ha', one_mul, add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s ≠ 1 := fun h ↦ ((h ▸ hs).trans_eq one_re).false
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁,
    Function.update_of_ne hs₁, LFunctionTrivChar, add_div,
    mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1, mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

/-- The auxiliary function takes real values for real arguments `x > 1`. -/
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    LFunctionResidueClassAux a x = (LFunctionResidueClassAux a x).re := by
  rw [eqOn_LFunctionResidueClassAux ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast]
    push_cast
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, zero_re, ofReal_zero]
    · simp only [term_of_ne_zero hn, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg, ← ofReal_div,
        ofReal_re]
  · rw [← ofReal_natCast, ← ofReal_one, ← ofReal_sub, ← ofReal_inv,
      ← ofReal_div, ofReal_re]

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹/(x-1) - C`. -/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, residueClass a n / (n : ℝ) ^ x := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_setOf.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_setOf_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := bddBelow_def.mp <| IsCompact.bddBelow_image isCompact_Icc this
  replace hC {x : ℝ} (hx : x ∈ Set.Icc 1 2) : C ≤ (LFunctionResidueClassAux a x).re :=
    hC (LFunctionResidueClassAux a x).re <|
      Set.mem_image_of_mem (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) hx
  refine ⟨-C, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm, sub_neg_eq_add, add_le_add_iff_left]
  exact hC <| Set.mem_Icc_of_Ioc hx

open vonMangoldt Filter Topology in
/-- The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such primes. -/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n := by
  intro H
  have key : Summable fun n : ℕ ↦ residueClass a n / n := by
    convert (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : ℝ} (hx : 1 < x) : ∑' n, residueClass a n / (n : ℝ) ^ x ≤ C := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ key
    · rcases n.eq_zero_or_pos with rfl | hn
      · simp only [Nat.cast_zero, Real.zero_rpow (zero_lt_one.trans hx).ne', div_zero, le_refl]
      · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (mod_cast hn) ?_
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.le
    · exact summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have H₁ {x} (hx : x ∈ Set.Ioc 1 2) : (q.totient : ℝ)⁻¹ ≤ (C + C') * (x - 1) :=
    (div_le_iff₀ <| sub_pos.mpr hx.1).mp <|
      sub_le_iff_le_add.mp <| (hC' hx).trans (H₁ hx.1)
  have hq : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  rcases le_or_gt (C + C') 0 with h₀ | h₀
  · have := hq.trans_le (H₁ (Set.right_mem_Ioc.mpr one_lt_two))
    rw [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at this
    exact (this.trans_le h₀).false
  · obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ ∈ Set.Ioc 1 2, (C + C') * (ξ - 1) < (q.totient : ℝ)⁻¹ := by
      refine ⟨min (1 + (q.totient : ℝ)⁻¹ / (C + C') / 2) 2, ⟨?_, min_le_right ..⟩, ?_⟩
      · simpa only [lt_inf_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
          Nat.one_lt_ofNat, and_true] using div_pos hq h₀
      · rw [← min_sub_sub_right, add_sub_cancel_left, ← lt_div_iff₀' h₀]
        exact (min_le_left ..).trans_lt <| div_lt_self (div_pos hq h₀) one_lt_two
    exact ((H₁ hξ₁).trans_lt hξ₂).false

end ArithmeticFunction.vonMangoldt

end arith_prog

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem setOf_prime_and_eq_mod_infinite (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by
  by_contra H
  rw [Set.not_infinite] at H
  exact not_summable_residueClass_prime_div ha <|
    summable_of_finite_support <| support_residueClass_prime_div a ▸ H

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (setOf_prime_and_eq_mod_infinite ha) n
  exact ⟨p, hp₂.gt, Set.mem_setOf.mp hp₁⟩

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℤ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
theorem forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] := by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℕ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
theorem forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] := by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

open Filter in
lemma frequently_atTop_prime_and_modEq_one {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] := by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩

lemma infinite_setOf_prime_and_modEq_one {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq_one hq h)

end Nat

end DirichletsTheorem
