/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain

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
    Fintype.card R ≤ natDegree p * #(univ.image fun x => eval x p) :=
  Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ ≤ Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
  letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push_neg at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_cancel]⟩
  fun hd : Disjoint _ _ =>
  lt_irrefl (2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))) <|
    calc 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))
        ≤ 2 * Fintype.card R := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
      _ = Fintype.card R + Fintype.card R := two_mul _
      _ < natDegree f * #(univ.image fun x : R => eval x f) +
            natDegree (-g) * #(univ.image fun x : R => eval x (-g)) :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)) := by
        rw [card_union_of_disjoint hd]
        simp [natDegree_eq_of_degree_eq_some hf2, natDegree_eq_of_degree_eq_some hg2, mul_add]

end Polynomial

theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  classical
    have : (∏ x ∈ (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (notMem_erase _ _), this, mul_one]

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
  simp only [h_unchanged, mulLeftEmbedding_apply, Subgroup.coe_mul, Units.val_mul, ← mul_sum,
    a_mul_emb] at h_sum_map
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
    simp only [univ_unique, sum_singleton, ↓reduceIte, Units.val_eq_one, OneMemClass.coe_eq_one]
    rw [Set.default_coe_singleton]
    rfl
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := by
  rw [← Nat.card_eq_fintype_card] at k_lt_card_G
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
      simp only [Function.comp_apply, Subgroup.coe_mul, Units.val_mul]
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

theorem pow_card (a : K) : a ^ q = a := by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos, pow_succ, Nat.pred_eq_sub_one,
    pow_card_sub_one_eq_one a h, one_mul]

theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

end

variable (K) [Field K] [Fintype K]

/-- The cardinality `q` is a power of the characteristic of `K`. -/
@[stacks 09HY "first part"]
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

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
theorem card' : ∃ (p : ℕ), CharP K p ∧ ∃ (n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩

lemma isPrimePow_card : IsPrimePow (Fintype.card K) := by
  obtain ⟨p, _, n, hp, hn⟩ := card' K
  exact ⟨p, n, Nat.prime_iff.mp hp, n.prop, hn.symm⟩

theorem cast_card_eq_zero : (q : K) = 0 := by
  simp

theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro h; apply h
    · intro h y
      simp_rw [← mem_powers_iff_mem_zpowers] at hx
      rcases hx y with ⟨j, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

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
      simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
        mem_singleton, φ] using isUnit_iff_ne_zero
    calc
      ∑ x : K, x ^ i = ∑ x ∈ univ \ {(0 : K)}, x ^ i := by
        rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero]
      _ = ∑ x : Kˣ, (x ^ i : K) := by simp [φ, ← this, univ.sum_map φ]
      _ = 0 := by rw [sum_pow_units K i, if_neg]; exact hiq

section frobenius

variable (R) [CommRing R] [Algebra K R]

/-- If `R` is an algebra over a finite field `K`, the Frobenius `K`-algebra endomorphism of `R` is
  given by raising every element of `R` to its `#K`-th power. -/
@[simps!] def frobeniusAlgHom : R →ₐ[K] R where
  __ := powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by
    obtain ⟨p, _, _, hp, card_eq⟩ := card' K
    nontriviality R
    have : CharP R p := charP_of_injective_algebraMap' K R p
    have : ExpChar R p := .prime hp
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, powMonoidHom_apply, card_eq]
    exact add_pow_expChar_pow ..
  commutes' _ := by simp [← RingHom.map_pow, pow_card]

theorem coe_frobeniusAlgHom : ⇑(frobeniusAlgHom K R) = (· ^ q) := rfl

/-- If `R` is a perfect ring and an algebra over a finite field `K`, the Frobenius `K`-algebra
  endomorphism of `R` is an automorphism. -/
@[simps!] noncomputable def frobeniusAlgEquiv (p : ℕ) [ExpChar R p] [PerfectRing R p] : R ≃ₐ[K] R :=
  .ofBijective (frobeniusAlgHom K R) <| by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom, card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
    apply bijective_iterateFrobenius

variable (L : Type*) [Field L] [Algebra K L]

/-- If `L/K` is an algebraic extension of a finite field, the Frobenius `K`-algebra endomorphism
  of `L` is an automorphism. -/
@[simps!] noncomputable def frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : L ≃ₐ[K] L :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)

theorem coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] :
    ⇑(frobeniusAlgEquivOfAlgebraic K L) = (· ^ q) := rfl

variable [Finite L]

open Polynomial in
theorem orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K L :=
  (orderOf_eq_iff Module.finrank_pos).mpr <| by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x ↦ ?_, fun m lt pos eq ↦ ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_subset_roots (R := L) (p := X ^ q ^ m - X) (Z := univ) fun x _ ↦ by
      simp_rw [mem_roots', IsRoot, eval_sub, eval_pow, eval_X]
      have := DFunLike.congr_fun eq x
      rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply, ← sub_eq_zero] at this
      refine ⟨fun h ↦ ?_, this⟩
      simpa [if_neg (Nat.one_lt_pow pos.ne' Fintype.one_lt_card).ne] using congr_arg (coeff · 1) h
    refine this.not_gt (((natDegree_sub_le ..).trans_eq ?_).trans_lt <|
      (Nat.pow_lt_pow_right Fintype.one_lt_card lt).trans_eq Module.card_eq_pow_finrank.symm)
    simp [Nat.one_le_pow _ _ Fintype.card_pos]

theorem orderOf_frobeniusAlgEquivOfAlgebraic :
    orderOf (frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L := by
  simpa [orderOf_eq_iff Module.finrank_pos, DFunLike.ext_iff] using orderOf_frobeniusAlgHom K L

theorem bijective_frobeniusAlgHom_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgHom K L ^ n.1 :=
  let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans <|
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)

theorem bijective_frobeniusAlgEquivOfAlgebraic_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgEquivOfAlgebraic K L ^ n.1 :=
  ((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp <| by
    simpa only [Function.comp_def, map_pow] using bijective_frobeniusAlgHom_pow K L

instance (K L) [Finite L] [Field K] [Field L] [Algebra K L] : IsCyclic (L ≃ₐ[K] L) where
  exists_zpow_surjective :=
    have := Finite.of_injective _ (algebraMap K L).injective
    have := Fintype.ofFinite K
    ⟨frobeniusAlgEquivOfAlgebraic K L,
      fun f ↦ have ⟨n, hn⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f; ⟨n, hn⟩⟩

end frobenius

open Polynomial

section

variable [Fintype K] (K' : Type*) [Field K'] {p n : ℕ}

theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow, degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), natDegree_X_pow]

theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_natDegree_eq K' <| Nat.one_lt_pow hn hp

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt <|
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' <| Nat.one_lt_pow hn hp

end

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

variable {K}

theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', pow_succ, pow_mul, RingHom.mul_def, RingHom.comp_apply, frobenius_def, hn]

open Polynomial

theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  letI := hp
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  haveI : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, RingHom.one_def, map_id]

end FiniteField

namespace ZMod

open FiniteField Polynomial

theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x := by
  rcases hp.1.eq_two_or_odd with hp2 | hp_odd
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

theorem sq_add_sq (R : Type*) [Ring R] [IsDomain R] (p : ℕ) [NeZero p] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x := by
  haveI := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab

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

/-- The **Fermat-Euler totient theorem**. `ZMod.pow_totient` is an alternative statement
  of the same theorem. -/
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.eq_iff_modEq_nat]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) → ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]

/-- For each `n ≥ 0`, the unit group of `ZMod n` is finite. -/
instance instFiniteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
| 0     => Finite.of_fintype ℤˣ
| _ + 1 => inferInstance

open FiniteField

namespace ZMod

variable {p : ℕ} [Fact p.Prime]

instance : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_bot_eq_top <| top_unique (a := ⊥) fun n _ ↦
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this

theorem fieldRange_castHom_eq_bot (p : ℕ) [Fact p.Prime] [DivisionRing K] [CharP K p] :
    (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K) := by
  rw [RingHom.fieldRange_eq_map, ← Subfield.map_bot (K := ZMod p), Subsingleton.elim ⊥]

/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/
@[simp]
theorem pow_card (x : ZMod p) : x ^ p = x := by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h

@[simp]
theorem pow_card_pow {n : ℕ} (x : ZMod p) : x ^ p ^ n = x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

@[simp]
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, ZMod.pow_card, RingHom.id_apply]

-- This was a `simp` lemma, but now the LHS simplifies to `φ p`.
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]

/-- **Fermat's Little Theorem**: for every unit `a` of `ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]

/-- **Fermat's Little Theorem**: for all nonzero `a : ZMod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h

lemma pow_card_sub_one (a : ZMod p) :
    a ^ (p - 1) = if a ≠ 0 then 1 else 0 := by
  split_ifs with ha
  · exact pow_card_sub_one_eq_one ha
  · simp [of_not_not ha, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]

theorem orderOf_units_dvd_card_sub_one (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| units_pow_card_sub_one_eq_one _ _

theorem orderOf_dvd_card_sub_one {a : ZMod p} (ha : a ≠ 0) :
    orderOf a ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| pow_card_sub_one_eq_one ha

open Polynomial

theorem expand_card (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

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

theorem pow_pow_modEq_one (p m a : ℕ) : (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m] := by
  induction m with
  | zero => exact Nat.modEq_one
  | succ m hm =>
    rw [Nat.ModEq.comm, add_comm, Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _), add_comm] at hd
    rw [pow_succ, pow_mul, hd, add_pow, Finset.sum_range_succ', pow_zero, one_mul, one_pow,
      one_mul, Nat.choose_zero_right, Nat.cast_one]
    refine Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr ?_)
    simp_rw [one_pow, mul_one, pow_succ', mul_assoc, ← Finset.mul_sum]
    refine mul_dvd_mul_left (p ^ m) (dvd_mul_of_dvd_right (Finset.dvd_sum fun k hk ↦ ?_) d)
    cases m
    · rw [pow_zero, pow_one, one_mul, add_comm, add_left_inj] at hd
      cases k <;> simp [← hd, mul_assoc, pow_succ']
    · cases k <;> simp [mul_assoc, pow_succ']

theorem ZMod.eq_one_or_isUnit_sub_one {n p k : ℕ} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n)
    (ha : (orderOf a).Coprime n) : a = 1 ∨ IsUnit (a - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← orderOf_eq_one_iff, or_iff_not_imp_right]
  refine fun h ↦ ha.eq_one_of_dvd ?_
  rw [orderOf_dvd_iff_pow_eq_one, ← Nat.cast_pow, ← Nat.cast_one, ZMod.eq_iff_modEq_nat, hn]
  replace ha0 : 1 ≤ a := by
    contrapose! ha0
    rw [Nat.lt_one_iff.mp ha0, Nat.cast_zero]
  rw [← Nat.cast_one, ← Nat.cast_sub ha0, ZMod.isUnit_iff_coprime, hn] at h
  obtain ⟨b, hb⟩ := not_imp_comm.mp (Nat.Prime.coprime_pow_of_not_dvd Fact.out) h
  rw [tsub_eq_iff_eq_add_of_le ha0, add_comm] at hb
  exact hb ▸ pow_pow_modEq_one p k b

section prime_subfield

variable {F : Type*} [Field F]

theorem mem_bot_iff_intCast (p : ℕ) [Fact p.Prime] (K) [DivisionRing K] [CharP K p] {x : K} :
    x ∈ (⊥ : Subfield K) ↔ ∃ n : ℤ, n = x := by
  simp [← fieldRange_castHom_eq_bot p, ZMod.intCast_surjective.exists]

variable (F) (p : ℕ) [Fact p.Prime] [CharP F p]

theorem Subfield.card_bot : Nat.card (⊥ : Subfield F) = p := by
  rw [← fieldRange_castHom_eq_bot p,
    ← Nat.card_eq_of_bijective _ (RingHom.rangeRestrictField_bijective _), Nat.card_zmod]

/-- The prime subfield is finite. -/
def Subfield.fintypeBot : Fintype (⊥ : Subfield F) :=
  Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ ↦ by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

open Polynomial

theorem Subfield.roots_X_pow_char_sub_X_bot :
    letI := Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by
  let _ := Subfield.fintypeBot F p
  conv_lhs => rw [← card_bot F p, ← Fintype.card_eq_nat_card]
  exact FiniteField.roots_X_pow_card_sub_X _

theorem Subfield.splits_bot :
    Splits (RingHom.id (⊥ : Subfield F)) (X ^ p - X) := by
  let _ := Subfield.fintypeBot F p
  rw [splits_iff_card_roots, roots_X_pow_char_sub_X_bot, ← Finset.card_def, Finset.card_univ,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out (p := p.Prime)).one_lt,
    Fintype.card_eq_nat_card, card_bot F p]

theorem Subfield.mem_bot_iff_pow_eq_self {x : F} : x ∈ (⊥ : Subfield F) ↔ x ^ p = x := by
  have := roots_X_pow_char_sub_X_bot F p ▸
      Polynomial.roots_map (Subfield.subtype _) (splits_bot F p) ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, FiniteField.X_pow_card_sub_X_ne_zero F (Fact.out : p.Prime).one_lt]

end prime_subfield

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  haveI hF' : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F ↦ x * x := fun h ↦
    h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) <| by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h

end Finite

variable [Fintype F]

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, ← Nat.even_iff, Nat.even_pow, hp.even_iff]
  simp

theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF), mul_comm, pow_mul,
    pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

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
      rw [← Nat.card_eq_fintype_card] at hodd h
      have key : 2 * (Nat.card F / 2) ∣ n * (Nat.card F / 2) := by
        rw [← pow_mul] at h
        rw [hodd, ← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
        apply orderOf_dvd_of_pow_eq_one h
      have : 0 < Nat.card F / 2 := Nat.div_pos Finite.one_lt_card (by norm_num)
      obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right this key
      refine ⟨g ^ m, ?_⟩
      dsimp
      rw [mul_comm, pow_mul, pow_two]

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

end FiniteField
