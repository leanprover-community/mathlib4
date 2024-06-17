/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Tactic.ApplyFun

#align_import field_theory.finite.basic from "leanprover-community/mathlib"@"12a85fac627bea918960da036049d611b1a3ee43"

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `RingTheory.IntegralDomain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`Fintype.fieldOfDomain`).

## Main results

1. `Fintype.card_units`: The unit group of a finite field has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `FiniteField.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `FiniteField.card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `Fintype Kˣ` can be inferred from `Fintype K` in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.

-/


variable {K : Type*} {R : Type*}

local notation "q" => Fintype.card K

open Finset

open scoped Polynomial

namespace FiniteField

section Polynomial

variable [CommRing R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * (univ.image fun x => eval x p).card :=
  Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = (p - C a).roots.toFinset.card :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ ≤ Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots_sub_C' hp)
#align finite_field.card_image_polynomial_eval FiniteField.card_image_polynomial_eval

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
  letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push_neg at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_self]⟩
  fun hd : Disjoint _ _ =>
  lt_irrefl (2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card) <|
    calc 2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card
        ≤ 2 * Fintype.card R := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
      _ = Fintype.card R + Fintype.card R := two_mul _
      _ < natDegree f * (univ.image fun x : R => eval x f).card +
            natDegree (-g) * (univ.image fun x : R => eval x (-g)).card :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card := by
        rw [card_union_of_disjoint hd];
          simp [natDegree_eq_of_degree_eq_some hf2, natDegree_eq_of_degree_eq_some hg2, mul_add]

#align finite_field.exists_root_sum_quadratic FiniteField.exists_root_sum_quadratic

end Polynomial

theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  classical
    have : (∏ x ∈ (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp (config := { contextual := true }) [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (not_mem_erase _ _), this, mul_one]
#align finite_field.prod_univ_units_id_eq_neg_one FiniteField.prod_univ_units_id_eq_neg_one

set_option backward.synthInstance.canonInstances false in -- See https://github.com/leanprover-community/mathlib4/issues/12532
theorem card_cast_subgroup_card_ne_zero [Ring K] [NoZeroDivisors K] [Nontrivial K]
    (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) ≠ 0 := by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists K
  have hd : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp nzero
  cases CharP.char_is_prime_or_zero K p with
  | inr pzero =>
    exact (Fintype.card_pos).ne' <| Nat.eq_zero_of_zero_dvd <| pzero ▸ hd
  | inl pprime =>
    have fact_pprime := Fact.mk pprime
    -- G has an element x of order p by Cauchy's theorem
    have ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hd
    -- F has an element u (= ↑↑x) of order p
    let u := ((x : Kˣ) : K)
    have hu : orderOf u = p := by rwa [orderOf_units, Subgroup.orderOf_coe]
    -- u ^ p = 1 implies (u - 1) ^ p = 0 and hence u = 1 ...
    have h : u = 1 := by
      rw [← sub_left_inj, sub_self 1]
      apply pow_eq_zero (n := p)
      rw [sub_pow_char_of_commute, one_pow, ← hu, pow_orderOf_eq_one, sub_self]
      exact Commute.one_right u
    -- ... meaning x didn't have order p after all, contradiction
    apply pprime.one_lt.ne
    rw [← hu, h, orderOf_one]

/-- The sum of a nontrivial subgroup of the units of a field is zero. -/
theorem sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] (hg : G ≠ ⊥) :
    ∑ x : G, (x.val : K) = 0 := by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := by simp
  -- Therefore the sum of x over a G is the sum of a x over G
  have h_sum_map := Finset.univ.sum_map a_mul_emb fun x => ((x : Kˣ) : K)
  -- ... and the former is the sum of x over G.
  -- By algebraic manipulation, we have Σ G, x = ∑ G, a x = a ∑ G, x
  simp only [a_mul_emb, h_unchanged, Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe,
    mulLeftEmbedding_apply, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul,
    ← Finset.mul_sum] at h_sum_map
  -- thus one of (a - 1) or ∑ G, x is zero
  have hzero : (((a : Kˣ) : K) - 1) = 0 ∨ ∑ x : ↥G, ((x : Kˣ) : K) = 0 := by
    rw [← mul_eq_zero, sub_mul, ← h_sum_map, one_mul, sub_self]
  apply Or.resolve_left hzero
  contrapose! ha
  ext
  rwa [← sub_eq_zero]

/-- The sum of a subgroup of the units of a field is 1 if the subgroup is trivial and 1 otherwise -/
@[simp]
theorem sum_subgroup_units [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0 := by
  by_cases G_bot : G = ⊥
  · subst G_bot
    simp only [ite_true, Subgroup.mem_bot, Fintype.card_ofSubsingleton, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, univ_unique, Set.default_coe_singleton, sum_singleton, Units.val_one]
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := by
  nontriviality K
  have := NoZeroDivisors.to_isDomain K
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k) =
      Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) := by
    simp_rw [← mul_pow]
    have as_comp :
      (fun x : ↥G => (((x : Kˣ) : K) * ((a : Kˣ) : K)) ^ k)
        = (fun x : ↥G => ((x : Kˣ) : K) ^ k) ∘ fun x : ↥G => x * a := by
      funext x
      simp only [Function.comp_apply, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul]
    rw [as_comp, ← Multiset.map_map]
    congr
    rw [eq_comm]
    exact Multiset.map_univ_val_equiv (Equiv.mulRight a)
  have h_multiset_map_sum : (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k) Finset.univ.val).sum =
    (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) Finset.univ.val).sum := by
    rw [h_multiset_map]
  rw [Multiset.sum_map_mul_right] at h_multiset_map_sum
  have hzero : (((a : Kˣ) : K) ^ k - 1 : K)
                  * (Multiset.map (fun i : G => (i.val : K) ^ k) Finset.univ.val).sum = 0 := by
    rw [sub_mul, mul_comm, ← h_multiset_map_sum, one_mul, sub_self]
  rw [mul_eq_zero] at hzero
  refine hzero.resolve_left fun h => ha ?_
  ext
  rw [← sub_eq_zero]
  simp_rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, h]

section

variable [GroupWithZero K] [Fintype K]

theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 := by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units, pow_card_eq_one]
        rfl
#align finite_field.pow_card_sub_one_eq_one FiniteField.pow_card_sub_one_eq_one

theorem pow_card (a : K) : a ^ q = a := by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos, pow_succ, Nat.pred_eq_sub_one,
    pow_card_sub_one_eq_one a h, one_mul]
#align finite_field.pow_card FiniteField.pow_card

theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by
  induction' n with n ih
  · simp
  · simp [pow_succ, pow_mul, ih, pow_card]
#align finite_field.pow_card_pow FiniteField.pow_card_pow

end

variable (K) [Field K] [Fintype K]

theorem card (p : ℕ) [CharP K p] : ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  letI : Module (ZMod p) K := { (ZMod.castHom dvd_rfl K : ZMod p →+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) K
  rw [ZMod.card] at h
  refine ⟨⟨n, ?_⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  rintro rfl
  rw [pow_zero] at h
  have : (0 : K) = 1 := by apply Fintype.card_le_one_iff.mp (le_of_eq h)
  exact absurd this zero_ne_one
#align finite_field.card FiniteField.card

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
theorem card' : ∃ (p : ℕ) (n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, @FiniteField.card K _ _ p hc⟩
#align finite_field.card' FiniteField.card'

-- Porting note: this was a `simp` lemma with a 5 lines proof.
theorem cast_card_eq_zero : (q : K) = 0 := by
  simp
#align finite_field.cast_card_eq_zero FiniteField.cast_card_eq_zero

theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
    rw [← Fintype.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro h; apply h
    · intro h y
      simp_rw [← mem_powers_iff_mem_zpowers] at hx
      rcases hx y with ⟨j, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
#align finite_field.forall_pow_eq_one_iff FiniteField.forall_pow_eq_one_iff

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
theorem sum_pow_units [DecidableEq K] (i : ℕ) :
    (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  let φ : Kˣ →* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by intros; simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := by
        suffices q - 1 ∣ i ↔ φ = 1 by
          simp only [this]
          split_ifs; swap
          · exact Nat.cast_zero
          · rw [Fintype.card_units, Nat.cast_sub,
              cast_card_eq_zero, Nat.cast_one, zero_sub]
            show 1 ≤ q; exact Fintype.card_pos_iff.mpr ⟨0⟩
        rw [← forall_pow_eq_one_iff, DFunLike.ext_iff]
        apply forall_congr'; intro x; simp [φ, Units.ext_iff]
#align finite_field.sum_pow_units FiniteField.sum_pow_units

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
theorem sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by
  by_cases hi : i = 0
  · simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero]
  classical
    have hiq : ¬q - 1 ∣ i := by contrapose! h; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
    let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.ext⟩
    have : univ.map φ = univ \ {0} := by
      ext x
      simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and_iff, mem_sdiff,
        mem_singleton, φ] using isUnit_iff_ne_zero
    calc
      ∑ x : K, x ^ i = ∑ x ∈ univ \ {(0 : K)}, x ^ i := by
        rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero]
      _ = ∑ x : Kˣ, (x ^ i : K) := by simp [φ, ← this, univ.sum_map φ]
      _ = 0 := by rw [sum_pow_units K i, if_neg]; exact hiq
#align finite_field.sum_pow_lt_card_sub_one FiniteField.sum_pow_lt_card_sub_one

open Polynomial

section

variable (K' : Type*) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow, degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), natDegree_X_pow]
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_sub_X_nat_degree_eq FiniteField.X_pow_card_sub_X_natDegree_eq

theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_natDegree_eq K' <| Nat.one_lt_pow hn hp
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_pow_sub_X_nat_degree_eq FiniteField.X_pow_card_pow_sub_X_natDegree_eq

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt <|
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_sub_X_ne_zero FiniteField.X_pow_card_sub_X_ne_zero

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' <| Nat.one_lt_pow hn hp
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_pow_sub_X_ne_zero FiniteField.X_pow_card_pow_sub_X_ne_zero

end

variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) K]

theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by
  classical
    have aux : (X ^ q - X : K[X]) ≠ 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
    have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
      rw [eq_univ_iff_forall]
      intro x
      rw [Multiset.mem_toFinset, mem_roots aux, IsRoot.def, eval_sub, eval_pow, eval_X,
        sub_eq_zero, pow_card]
    rw [← this, Multiset.toFinset_val, eq_comm, Multiset.dedup_eq_self]
    apply nodup_roots
    rw [separable_def]
    convert isCoprime_one_right.neg_right (R := K[X]) using 1
    rw [derivative_sub, derivative_X, derivative_X_pow, Nat.cast_card_eq_zero K, C_0,
      zero_mul, zero_sub]
set_option linter.uppercaseLean3 false in
#align finite_field.roots_X_pow_card_sub_X FiniteField.roots_X_pow_card_sub_X

variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction' n with n hn
  · simp
  · rw [pow_succ', pow_succ, pow_mul, RingHom.mul_def, RingHom.comp_apply, frobenius_def, hn]
#align finite_field.frobenius_pow FiniteField.frobenius_pow

open Polynomial

theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
  cases' CharP.exists K with p hp
  letI := hp
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, RingHom.one_def, map_id]
#align finite_field.expand_card FiniteField.expand_card

end FiniteField

namespace ZMod

open FiniteField Polynomial

theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x := by
  cases' hp.1.eq_two_or_odd with hp2 hp_odd
  · subst p
    change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _)
      (by rw [ZMod.card, hp_odd])
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [f, g, eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab
#align zmod.sq_add_sq ZMod.sq_add_sq

end ZMod

/-- If `p` is a prime natural number and `x` is an integer number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [ZMOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
theorem Nat.sq_add_sq_zmodEq (p : ℕ) [Fact p.Prime] (x : ℤ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ≡ x [ZMOD p] := by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs, ← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs, sq_abs, ← ZMod.intCast_eq_intCast_iff]
  exact mod_cast hx

/-- If `p` is a prime natural number and `x` is a natural number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [MOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
theorem Nat.sq_add_sq_modEq (p : ℕ) [Fact p.Prime] (x : ℕ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p] := by
  simpa only [← Int.natCast_modEq_iff] using Nat.sq_add_sq_zmodEq p x

namespace CharP

theorem sq_add_sq (R : Type*) [CommRing R] [IsDomain R] (p : ℕ) [NeZero p] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x := by
  haveI := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab
#align char_p.sq_add_sq CharP.sq_add_sq

end CharP

open scoped Nat

open ZMod

/-- The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
theorem ZMod.pow_totient {n : ℕ} (x : (ZMod n)ˣ) : x ^ φ n = 1 := by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]
#align zmod.pow_totient ZMod.pow_totient

/-- The **Fermat-Euler totient theorem**. `ZMod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.eq_iff_modEq_nat]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) → ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]
#align nat.modeq.pow_totient Nat.ModEq.pow_totient

/-- For each `n ≥ 0`, the unit group of `ZMod n` is finite. -/
instance instFiniteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
| 0     => Finite.of_fintype ℤˣ
| _ + 1 => inferInstance

section

variable {V : Type*} [Fintype K] [DivisionRing K] [AddCommGroup V] [Module K V]

-- should this go in a namespace?
-- finite_dimensional would be natural,
-- but we don't assume it...
theorem card_eq_pow_finrank [Fintype V] : Fintype.card V = q ^ FiniteDimensional.finrank K V := by
  let b := IsNoetherian.finsetBasis K V
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b]
#align card_eq_pow_finrank card_eq_pow_finrank

end

open FiniteField

namespace ZMod

/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card {p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ p = x := by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h
#align zmod.pow_card ZMod.pow_card

@[simp]
theorem pow_card_pow {n p : ℕ} [Fact p.Prime] (x : ZMod p) : x ^ p ^ n = x := by
  induction' n with n ih
  · simp
  · simp [pow_succ, pow_mul, ih, pow_card]
#align zmod.pow_card_pow ZMod.pow_card_pow

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, ZMod.pow_card, RingHom.id_apply]
#align zmod.frobenius_zmod ZMod.frobenius_zmod

-- Porting note: this was a `simp` lemma, but now the LHS simplify to `φ p`.
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]
#align zmod.card_units ZMod.card_units

/-- **Fermat's Little Theorem**: for every unit `a` of `ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
#align zmod.units_pow_card_sub_one_eq_one ZMod.units_pow_card_sub_one_eq_one

/-- **Fermat's Little Theorem**: for all nonzero `a : ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rwa [ZMod.card p] at h
#align zmod.pow_card_sub_one_eq_one ZMod.pow_card_sub_one_eq_one

theorem orderOf_units_dvd_card_sub_one {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| units_pow_card_sub_one_eq_one _ _
#align zmod.order_of_units_dvd_card_sub_one ZMod.orderOf_units_dvd_card_sub_one

theorem orderOf_dvd_card_sub_one {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    orderOf a ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| pow_card_sub_one_eq_one ha
#align zmod.order_of_dvd_card_sub_one ZMod.orderOf_dvd_card_sub_one

open Polynomial

theorem expand_card {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h
#align zmod.expand_card ZMod.expand_card

end ZMod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
theorem Int.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.intCast_eq_zero_iff _ p, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.intCast_eq_intCast_iff] using ZMod.pow_card_sub_one_eq_one this
#align int.modeq.pow_card_sub_one_eq_one Int.ModEq.pow_card_sub_one_eq_one

section

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  haveI hF' : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a
#align finite_field.is_square_of_char_two FiniteField.isSquare_of_char_two

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F ↦ x * x := fun h ↦
    h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) <| by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h
#align finite_field.exists_nonsquare FiniteField.exists_nonsquare

end Finite

variable [Fintype F]

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, ← Nat.even_iff, Nat.even_pow, hp.even_iff]
  simp
#align finite_field.even_card_iff_char_two FiniteField.even_card_iff_char_two

theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF
#align finite_field.even_card_of_char_two FiniteField.even_card_of_char_two

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)
#align finite_field.odd_card_of_char_ne_two FiniteField.odd_card_of_char_ne_two

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF), mul_comm, pow_mul,
    pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁
#align finite_field.pow_dichotomy FiniteField.pow_dichotomy

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
theorem unit_isSquare_iff (hF : ringChar F ≠ 2) (a : Fˣ) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  classical
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    obtain ⟨n, hn⟩ : a ∈ Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
    have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
    constructor
    · rintro ⟨y, rfl⟩
      rw [← pow_two, ← pow_mul, hodd]
      apply_fun Units.val using Units.ext
      push_cast
      exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
    · subst a; intro h
      have key : 2 * (Fintype.card F / 2) ∣ n * (Fintype.card F / 2) := by
        rw [← pow_mul] at h
        rw [hodd, ← Fintype.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
        apply orderOf_dvd_of_pow_eq_one h
      have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card (by norm_num)
      obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right this key
      refine ⟨g ^ m, ?_⟩
      dsimp
      rw [mul_comm, pow_mul, pow_two]
#align finite_field.unit_is_square_iff FiniteField.unit_isSquare_iff

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
theorem isSquare_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; simp at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp
#align finite_field.is_square_iff FiniteField.isSquare_iff

end FiniteField

end
