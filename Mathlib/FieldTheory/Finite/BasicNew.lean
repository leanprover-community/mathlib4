/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.CharAndCard -- REVIEWERS: leaf import
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IntegralDomain
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

While `Fintype Kˣ` can be inferred from `Fintype K`  in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.
-- REVIEWERS: this needs a library note, this is a general design principle

In this file, we use `K` for a general ring; because in this case, all "general rings" are actually
fields, just not assumed to be such by Lean; this follows by Wedderburn's Little Theorem,
but it is overkill to import this into this file; we use the weak form instead to lift some results.

-/

/-

CHANGES apart from moving and re-sorting:

* `FiniteField.{pow_card_sub_one_eq_one, pow_card, pow_card_pow, exists_root_sum_quadratic, prod_univ_units_id_eq_neg_one, sum_subgroup_pow_eq_zero, sum_subgroup_units{_eq_zero}}` → `Fintype.*`
* `FiniteField.{X_pow_card_sub_X_natDegree_eq, X_pow_card_pow_sub_X_natDegree_eq, X_pow_card_sub_X_ne_zero, X_pow_card_pow_sub_X_ne_zero}` → `Polynomial.*`, generalised from `Field` to `Ring` + `Nontrivial`.
* `FiniteField.card_image_polynomial_eval` → `Fintype.card_le_deg_mul_card_image_polynomial_eval`, added `nontriviality`.
* `ZMod.sq_add_sq` generalised to be for all finite fields (no longer requires that char ≠ 2)
* `sum_pow_units`: changed to use `Fintype Kˣ`
* Also turned a bunch of `Field K` into cancellative `K` by using the weak Wedderburn; similarly for
  `DivisionRing K` etc

Note that NoZeroDivisors + Nontrivial is no longer equivalent to IsDomain (for semirings)

-/

section ToMove

open scoped BigOperators

-- REVIEWERS: I don't like this name but what am I meant to do.
-- note: `to_additive` does _not_ make the correct lemma in this case, so we make it by hand.
lemma Subgroup.finset_prod_top {β α : Type*} [Group α] [Fintype α] [Fintype (⊤ : Subgroup α)]
  [CommMonoid β] (f : α → β) : ∏ x : (⊤ : Subgroup α), f x = ∏ x : α, f x :=
  by simp [Finset.prod_set_coe]

lemma AddSubgroup.finset_prod_top {β α : Type*} [AddGroup α] [Fintype α]
  [Fintype (⊤ : AddSubgroup α)] [CommMonoid β] (f : α → β) :
    ∏ x : (⊤ : AddSubgroup α), f x = ∏ x : α, f x :=
  by simp [Finset.prod_set_coe]
-- Subgroup.finset_prod_top (α := Multiplicative α) f
-- fails with an instance error that makes no sense to me - the `Fintype`s are specified for this reason.

attribute [to_additive existing AddSubgroup.finset_prod_top] Subgroup.finset_prod_top

@[to_additive]
lemma Subgroup.sum_top {β α : Type*} [Group α] [Fintype α] [Fintype (⊤ : Subgroup α)]
  [AddCommMonoid β] (f : α → β) : ∑ x : (⊤ : Subgroup α), f x = ∑ x : α, f x :=
  by simp [Finset.sum_set_coe]

lemma prod_units_nonunits {α β : Type*} [Monoid α] [CommMonoid β] [Fintype α] [Fintype αˣ]
  [Fintype <| nonunits α] (f : α → β) :
    (∏ x : αˣ, f x) * ∏ x in (nonunits α).toFinset, f x = ∏ x : α, f x := by
  rw [←Finset.prod_set_coe, ←Fintype.prod_sum_elim]
  apply Fintype.prod_bijective (Sum.elim (· : αˣ → α) (· : nonunits α → α))
  swap; aesop
  refine ⟨?_, fun x ↦ ?_⟩
  · rintro (u | nu) (u | nu) h
    · exact congr(Sum.inl $(Units.ext h))
    · refine (nu.2 ?_).elim
      dsimp at h
      rw [←h]
      exact u.isUnit
    · refine (nu.2 ?_).elim
      dsimp at h
      rw [h]
      exact u.isUnit
    · refine congr(Sum.inr $(Subtype.ext h))
  · by_cases h : IsUnit x
    · exact ⟨.inl h.unit, rfl⟩
    · exact ⟨.inr ⟨x, h⟩, rfl⟩

lemma sum_units_nonunits {α β : Type*} [Monoid α] [AddCommMonoid β] [Fintype α] [Fintype αˣ]
  [Fintype <| nonunits α] (f : α → β) :
    (∑ x : αˣ, f x) + ∑ x in (nonunits α).toFinset, f x = ∑ x : α, f x :=
prod_units_nonunits (β := Multiplicative β) f

attribute [to_additive existing sum_units_nonunits] prod_units_nonunits

@[simp] lemma nonunits_eq_zero {G : Type*} [GroupWithZero G] : nonunits G = {0} :=
  Set.ext <| fun x ↦ by simpa [nonunits] using (isUnit_iff_ne_zero (a := x)).not

lemma ringChar_is_prime_or_zero (R) [NonAssocSemiring R] [NoZeroDivisors R] [Nontrivial R] :
    (ringChar R).Prime ∨ ringChar R = 0 :=
CharP.char_is_prime_or_zero R _

lemma ringChar_is_prime (R) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] [Finite R] :
    (ringChar R).Prime :=
(ringChar_is_prime_or_zero R).resolve_right <| CharP.char_ne_zero_of_finite R _

end ToMove

-- I think? Lean has been clever enough to choose when it needs `Fintype` vs `Finite`.
variable {R S K : Type*} [Finite R] [Finite K] [Fintype R] [Fintype K] {p n k : ℕ}

open Polynomial Finset
open scoped BigOperators

section GroupWithZero

local notation "q" => Fintype.card K

variable [GroupWithZero K]

theorem Fintype.pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 := by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units, pow_card_eq_one]
        rfl
#align finite_field.pow_card_sub_one_eq_one Fintype.pow_card_sub_one_eq_one

theorem Fintype.pow_card (a : K) : a ^ q = a := by
  have hq : 0 < q := lt_trans zero_lt_one Fintype.one_lt_card
  rcases eq_or_ne a 0 with rfl | h
  · apply zero_pow hq
  rw [← Nat.succ_pred_eq_of_pos hq, pow_succ, Nat.pred_eq_sub_one, pow_card_sub_one_eq_one a h,
    mul_one]
#align finite_field.pow_card Fintype.pow_card

theorem Fintype.pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by
  induction' n with n ih
  · simp
  · simp [pow_succ, pow_mul, ih, pow_card]
#align finite_field.pow_card_pow Fintype.pow_card_pow

end GroupWithZero

section Ring

local notation "q" => Fintype.card R

variable [Ring R]

namespace Polynomial

variable (R) [Nontrivial R]

theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) :
  (X ^ p - X : R[X]).natDegree = p :=
(natDegree_sub_eq_left_of_natDegree_lt <| by simpa).trans <| natDegree_X_pow p
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_sub_X_nat_degree_eq Polynomial.X_pow_card_sub_X_natDegree_eq

theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : R[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_natDegree_eq R <| n.one_lt_pow _ hn.bot_lt hp
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_pow_sub_X_nat_degree_eq Polynomial.X_pow_card_pow_sub_X_natDegree_eq

theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : R[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt <| by rwa [X_pow_card_sub_X_natDegree_eq R hp]
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_sub_X_ne_zero Polynomial.X_pow_card_sub_X_ne_zero

theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : R[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero R <| n.one_lt_pow _ hn.bot_lt hp
set_option linter.uppercaseLean3 false in
#align finite_field.X_pow_card_pow_sub_X_ne_zero Polynomial.X_pow_card_pow_sub_X_ne_zero

end Polynomial

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- The sum of a nontrivial subgroup of the units of a field is zero. -/
theorem Fintype.sum_subgroup_units_eq_zero {G : Subgroup Rˣ} [Fintype G] (hg : G ≠ ⊥) :
    ∑ x : G, (x.val : R) = 0 := by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := univ_map_embedding _
  -- Therefore the sum of x over a G is the sum of a x over G
  have h_sum_map := Finset.univ.sum_map a_mul_emb fun x => ((x : Rˣ) : R)
  -- ... and the former is the sum of x over G.
  -- By algebraic manipulation, we have Σ G, x = ∑ G, a x = a ∑ G, x
  simp only [h_unchanged, Function.Embedding.coeFn_mk, Function.Embedding.toFun_eq_coe,
    mulLeftEmbedding_apply, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul,
    ← Finset.mul_sum] at h_sum_map
  -- thus one of (a - 1) or ∑ G, x is zero
  have hzero : (((a : Rˣ) : R) - 1) = 0 ∨ ∑ x : ↥G, ((x : Rˣ) : R) = 0 := by
    rw [←mul_eq_zero, sub_mul, ← h_sum_map, one_mul, sub_self]
  apply Or.resolve_left hzero
  contrapose! ha
  ext
  rwa [←sub_eq_zero]

/-- The sum of a subgroup of the units of a field is 1 if the subgroup is trivial and 1 otherwise -/
@[simp]
theorem Fintype.sum_subgroup_units {G : Subgroup Rˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : R) = if G = ⊥ then 1 else 0 := by
  rcases eq_or_ne G ⊥ with rfl | h
  · simp only [ite_true, Subgroup.mem_bot, Fintype.card_ofSubsingleton, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, univ_unique, Set.default_coe_singleton, sum_singleton, Units.val_one]
  · rw [if_neg h, sum_subgroup_units_eq_zero h]

end NoZeroDivisors

section IsDomain

variable [IsDomain R]

theorem card_cast_subgroup_card_ne_zero (G : Subgroup Rˣ) [Fintype G] :
    (Fintype.card G : R) ≠ 0 := by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists R
  have hd : p ∣ n := (CharP.cast_eq_zero_iff R p n).mp nzero
  cases CharP.char_is_prime_or_zero R p with
  | inr pzero =>
    exact (Fintype.card_pos).ne' <| Nat.eq_zero_of_zero_dvd <| pzero ▸ hd
  | inl pprime =>
    have fact_pprime := Fact.mk pprime
    -- G has an element x of order p by Cauchy's theorem
    have ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hd
    -- F has an element u (= ↑↑x) of order p
    let u := ((x : Rˣ) : R)
    have hu : orderOf u = p := by rwa [orderOf_units, orderOf_subgroup]
    -- u ^ p = 1 implies (u - 1) ^ p = 0 and hence u = 1 ...
    have h : u = 1 := by
      rw [← sub_left_inj, sub_self 1]
      apply pow_eq_zero (n := p)
      rw [sub_pow_char_of_commute, one_pow, ← hu, pow_orderOf_eq_one, sub_self]
      exact Commute.one_right u
    -- ... meaning x didn't have order p after all, contradiction
    apply pprime.one_lt.ne
    rw [← hu, h, orderOf_one]

variable (R)

-- REVIEWERS: not sure what to name these two.
theorem FiniteField.card (p : ℕ) [CharP R p] :
    ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime R p⟩
  letI : Module (ZMod p) R := { (ZMod.castHom dvd_rfl R : ZMod p →+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) R
  rw [ZMod.card] at h
  refine' ⟨⟨n, _⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  rintro rfl
  rw [pow_zero] at h
  have : (0 : R) = 1 := by apply Fintype.card_le_one_iff.mp (le_of_eq h)
  exact absurd this zero_ne_one
#align finite_field.card FiniteField.card

theorem FiniteField.card' : ∃ (p : ℕ) (n : ℕ+), Nat.Prime p ∧ Fintype.card R = p ^ (n : ℕ) :=
  let ⟨p, _⟩ := CharP.exists R
  ⟨p, FiniteField.card R p⟩
#align finite_field.card' FiniteField.card'

end IsDomain

end Ring

section DivisionRing

local notation "q" => Fintype.card K

variable [DivisionRing K]

end DivisionRing

section CommRing

local notation "q" => Fintype.card R

variable [CommRing R]

section NoZeroDivisors

variable [NoZeroDivisors R]

theorem Fintype.card_le_deg_mul_card_image_polynomial_eval [DecidableEq R] {p : R[X]}
  (hp : 0 < p.degree) : Fintype.card R ≤ natDegree p * (univ.image (p.eval ·)).card := by
  cases' subsingleton_or_nontrivial R with h h
  · rw [degree_of_subsingleton] at hp
    contradiction
  have := NoZeroDivisors.to_isDomain R
  refine Finset.card_le_mul_card_image _ _ (fun a _ => ?_)
  calc
    _ = (p - C a).roots.toFinset.card :=
      congr_arg Finset.card <| by simp [Finset.ext_iff, ← mem_roots_sub_C hp]
    _ ≤ Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
    _ ≤ _ := card_roots_sub_C' hp
#align finite_field.card_image_polynomial_eval Fintype.card_le_deg_mul_card_image_polynomial_eval

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
theorem Fintype.exists_root_sum_quadratic {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
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
      _ = Fintype.card R + Fintype.card R := (two_mul _)
      _ < natDegree f * (univ.image fun x : R => eval x f).card +
            natDegree (-g) * (univ.image fun x : R => eval x (-g)).card :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (Fintype.card_le_deg_mul_card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (Fintype.card_le_deg_mul_card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * ((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)).card := by
        rw [card_disjoint_union hd];
          simp [natDegree_eq_of_degree_eq_some hf2, natDegree_eq_of_degree_eq_some hg2, mul_add]
#align finite_field.exists_root_sum_quadratic Fintype.exists_root_sum_quadratic

theorem Fintype.prod_univ_units_id_eq_neg_one [Fintype Rˣ] :
    ∏ x : Rˣ, x = (-1 : Rˣ) := by
  classical
  have : (∏ x in (@univ Rˣ _).erase (-1), x) = 1 :=
    prod_involution (fun x _ => x⁻¹) (by simp)
      (fun a => by simp (config := { contextual := true }) [Units.inv_eq_self_iff])
      (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
  rw [← insert_erase (mem_univ (-1 : Rˣ)), prod_insert (not_mem_erase _ _), this, mul_one]
#align finite_field.prod_univ_units_id_eq_neg_one Fintype.prod_univ_units_id_eq_neg_one

@[simp]
theorem Fintype.sum_subgroup_pow_eq_zero
    {G : Subgroup Rˣ} [Fintype G] (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Rˣ) : R) ^ k = 0 := by
  nontriviality R
  have := NoZeroDivisors.to_isDomain R
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Rˣ) : R) ^ k) =
      Finset.univ.val.map (fun x : G => ((x : Rˣ) : R) ^ k * ((a : Rˣ) : R) ^ k) := by
    simp_rw [← mul_pow]
    have as_comp :
      (fun x : ↥G => (((x : Rˣ) : R) * ((a : Rˣ) : R)) ^ k)
        = (fun x : ↥G => ((x : Rˣ) : R) ^ k) ∘ fun x : ↥G => x * a := by
      funext x
      simp only [Function.comp_apply, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul]
    rw [as_comp, ← Multiset.map_map]
    congr
    rw [eq_comm]
    exact Multiset.map_univ_val_equiv (Equiv.mulRight a)
  have h_multiset_map_sum :
    (Multiset.map (fun x : G => ((x : Rˣ) : R) ^ k) Finset.univ.val).sum =
      (Multiset.map (fun x : G => ((x : Rˣ) : R) ^ k * ((a : Rˣ) : R) ^ k) Finset.univ.val).sum
  rw [h_multiset_map]
  rw [Multiset.sum_map_mul_right] at h_multiset_map_sum
  have hzero : (((a : Rˣ) : R) ^ k - 1 : R)
                  * (Multiset.map (fun i : G => (i.val : R) ^ k) Finset.univ.val).sum = 0 := by
    rw [sub_mul, mul_comm, ← h_multiset_map_sum, one_mul, sub_self]
  rw [mul_eq_zero] at hzero
  rcases hzero with h | h
  · contrapose! ha
    ext
    rw [←sub_eq_zero]
    simp_rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one, h]
  · exact h

theorem Finite.exists_sq_add_sq (x : R) : ∃ a b : R, a ^ 2 + b ^ 2 = x := by
  nontriviality R
  cases nonempty_fintype R
  cases' em' (q % 2 = 1) with h h
  · rw [Nat.mod_two_ne_one, ← Nat.dvd_iff_mod_eq_zero, ←prime_dvd_char_iff_dvd_card,
        (ringChar_is_prime R).dvd_iff_eq <| by norm_num] at h
    have t : CharP R 2 := h ▸ ringChar.charP R
    -- another workaround for another caching bug
    --have := this
    -- REVIEWERS: if I do it without the `@ + _` it won't infer the instance?
    obtain ⟨x, rfl⟩ := isSquare_of_charTwo' x
    exact ⟨x, 0, by simp [sq]⟩
  let f : R[X] := X ^ 2
  let g : R[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    Fintype.exists_root_sum_quadratic (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _) h
  refine' ⟨a, b, _⟩
  rw [← sub_eq_zero]
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab
#align zmod.sq_add_sq Finite.exists_sq_add_sq

-- REVIEWERS: check every theorem has the correct signature
variable (R)

-- edit Chevalley-Warning
theorem FiniteField.sum_pow_lt_card_sub_one {i : ℕ} (h : i < q - 1) :
    ∑ x : R, x ^ i = 0 := by
  nontriviality R
  have := NoZeroDivisors.to_isDomain R
  -- this proof is _very_ delicate about how it wants `classical` to be used; moving `classical!`
  -- up here fails, and so does using just `classical` instead of it without extreme care.
  -- note also that deleting `Field R` causes this not to be placed in the instance cache.
  let inst : Field R := by classical exact Fintype.fieldOfDomain R
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [nsmul_one, sum_const, pow_zero, card_univ, CharP.cast_card_eq_zero]
  classical!
  rw [←Fintype.card_units, ←Subgroup.card_top] at h
  have key := Fintype.sum_subgroup_pow_eq_zero (R := R) (G := ⊤) hi (by convert h)
  erw [Subgroup.sum_top ((· : Rˣ → R) ^ i : Rˣ → R)] at key
  rw [←sum_units_nonunits, ← key]
  simp [hi]

-- can be finished!
theorem sum_pow_units [Fintype Rˣ] (i : ℕ) :
    (∑ x : Rˣ, (x ^ i : R)) = if q - 1 ∣ i then -1 else 0 := by
  nontriviality R
  classical
  have := FiniteField.sum_pow_lt_card_sub_one R (Nat.mod_lt i <| by simpa using Fintype.one_lt_card)
  rw [←sum_units_nonunits] at this
  sorry
  --have := pow_eq_mod_card -- need this for finite fields; grr
  --split_ifs


theorem FiniteField.frobenius_pow [Fact p.Prime] [CharP R p] (hcard : q = p ^ n) :
    frobenius R p ^ n = 1 := by
  ext x
  nontriviality R
  classical
  have := NoZeroDivisors.to_isDomain R
  let inst := Fintype.fieldOfDomain R
  conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← Fintype.pow_card x, hcard]
  clear hcard
  induction' n with n hn
  · simp
  · rw [pow_succ, pow_succ', pow_mul, RingHom.mul_def, RingHom.comp_apply, frobenius_def, hn]
#align finite_field.frobenius_pow FiniteField.frobenius_pow

open Polynomial in
theorem FiniteField.expand_card (f : R[X]) : expand R q f = f ^ q := by
  nontriviality R
  have := NoZeroDivisors.to_isDomain R
  cases' CharP.exists R with p hp
  rcases FiniteField.card R p with ⟨n, hp, hn⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, RingHom.one_def, map_id]
#align finite_field.expand_card FiniteField.expand_card

end NoZeroDivisors

section IsDomain

variable [IsDomain R]

-- REVIEWERS: sort this out first - the issue is basically `card_units` so this can be
-- generalised appropriately
-- second note: I have absolutely no clue what I meant with the note above,
-- if anyone does then please let me know :)
theorem FiniteField.forall_pow_eq_one_iff (i : ℕ) : (∀ x : Rˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  classical
  let inst := Fintype.fieldOfDomain R
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Rˣ)
  rw [← Fintype.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h; apply h
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    rcases hx y with ⟨j, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
#align finite_field.forall_pow_eq_one_iff FiniteField.forall_pow_eq_one_iff

theorem FiniteField.roots_X_pow_card_sub_X : (X ^ q - X : R[X]).roots = Finset.univ.val := by
  classical
  let inst := Fintype.fieldOfDomain R
  have aux : (X ^ q - X : R[X]) ≠ 0 := X_pow_card_sub_X_ne_zero R Fintype.one_lt_card
  have : (roots (X ^ q - X : R[X])).toFinset = Finset.univ := by
    rw [eq_univ_iff_forall]
    intro x
    rw [Multiset.mem_toFinset, mem_roots aux, IsRoot.def, eval_sub, eval_pow, eval_X,
      sub_eq_zero, Fintype.pow_card]
  rw [← this, Multiset.toFinset_val, eq_comm, Multiset.dedup_eq_self]
  apply nodup_roots
  rw [separable_def]
  convert isCoprime_one_right.neg_right (R := R[X]) using 1
  rw [derivative_sub, derivative_X, derivative_X_pow, CharP.cast_card_eq_zero R, C_0,
    zero_mul, zero_sub]
set_option linter.uppercaseLean3 false in
#align finite_field.roots_X_pow_card_sub_X FiniteField.roots_X_pow_card_sub_X

end IsDomain

end CommRing

section Field

end Field


#exit --check notes to REVIEWERS!
