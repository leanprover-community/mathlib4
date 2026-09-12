/-
Copyright (c) 2026 Alessandro Iraci, Giovanni Paolini, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Giovanni Paolini, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.QAnalog.Binomial
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.Ring

/-!
# `q`-binomial coefficients count subspaces of a finite vector space

If `K` is a finite field with `q` elements and `V` is a finite-dimensional `K`-vector space of
dimension `n`, then the number of `k`-dimensional subspaces of `V` is the `q`-binomial
coefficient `[n choose k]_q`.

## Main results

* `card_submodule_finrank_eq_qBinomial`: the number of `k`-dimensional subspaces of `V` is
  `[n choose k]_q`.
-/

open Finset Module

namespace QAnalog

/-! ### An arithmetic identity for `q`-binomial coefficients

Unlike the rest of the library, this section assumes commutativity, since the statement is
phrased with a `Finset` product; it is only ever used with `q : ℤ`. -/

section Arithmetic

variable {R : Type*} [CommRing R]

/-- The number of linearly independent `k`-tuples in an `n`-dimensional space over a field with
`q` elements, expressed through `q`-factorials. -/
theorem prod_pow_sub_pow_mul_qFactorial (q : R) (n k : ℕ) (h : k ≤ n) :
    (∏ i ∈ range k, (q ^ n - q ^ i)) * qFactorial q (n - k)
      = q ^ (k.choose 2) * (q - 1) ^ k * qFactorial q n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ n := by omega
    have hnk : n - k = n - (k + 1) + 1 := by omega
    have hpow : q ^ n - q ^ k = q ^ k * ((q - 1) * qNat q (n - k)) := by
      rw [← neg_sub 1 q, neg_mul, one_sub_mul_qNat, neg_sub, mul_sub, mul_one, ← pow_add,
        Nat.add_sub_cancel' hk]
    have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    rw [prod_range_succ, hpow, hchoose]
    calc (∏ i ∈ range k, (q ^ n - q ^ i)) * (q ^ k * ((q - 1) * qNat q (n - k)))
          * qFactorial q (n - (k + 1))
        = ((∏ i ∈ range k, (q ^ n - q ^ i))
            * (qNat q (n - k) * qFactorial q (n - (k + 1)))) * (q ^ k * (q - 1)) := by ring
      _ = ((∏ i ∈ range k, (q ^ n - q ^ i)) * qFactorial q (n - k)) * (q ^ k * (q - 1)) := by
          rw [hnk, qFactorial_succ, ← hnk]
      _ = q ^ (k.choose 2 + k) * (q - 1) ^ (k + 1) * qFactorial q n := by
          rw [ih hk, pow_add, pow_succ]; ring

end Arithmetic

private lemma qFactorial_int_pos {Q : ℕ} (hQ : 1 ≤ Q) (m : ℕ) : 0 < qFactorial (Q : ℤ) m := by
  rw [qFactorial_eq_prod_range]
  refine Finset.prod_pos fun i _ => ?_
  rw [qNat_eq_sum_range]
  refine Finset.sum_pos (fun j _ => pow_pos (by exact_mod_cast hQ) j) ⟨0, by simp⟩

/-- The `q`-binomial coefficient times the number of bases of a `k`-dimensional space is the
number of linearly independent `k`-tuples in an `n`-dimensional space. -/
theorem qBinomial_mul_prod_pow_sub_pow (Q n k : ℕ) (hQ : 1 ≤ Q) (h : k ≤ n) :
    qBinomial Q n k * ∏ i ∈ range k, (Q ^ k - Q ^ i) = ∏ i ∈ range k, (Q ^ n - Q ^ i) := by
  have cast_prod : ∀ m : ℕ, k ≤ m → ((∏ i ∈ range k, (Q ^ m - Q ^ i) : ℕ) : ℤ)
      = ∏ i ∈ range k, ((Q : ℤ) ^ m - (Q : ℤ) ^ i) := by
    intro m hm
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [Nat.cast_sub (Nat.pow_le_pow_right hQ (by omega))]
    push_cast
    ring
  have hqb : ((qBinomial Q n k : ℕ) : ℤ) = qBinomial (Q : ℤ) n k :=
    map_qBinomial (Nat.castRingHom ℤ) Q n k
  have hA := prod_pow_sub_pow_mul_qFactorial (Q : ℤ) n k h
  have hB := prod_pow_sub_pow_mul_qFactorial (Q : ℤ) k k le_rfl
  have hC := qBinomial_mul_qFactorial_mul_qFactorial (Q : ℤ) n k h
  rw [Nat.sub_self, qFactorial_zero, mul_one] at hB
  have key : ((qBinomial Q n k * ∏ i ∈ range k, (Q ^ k - Q ^ i) : ℕ) : ℤ)
      = ((∏ i ∈ range k, (Q ^ n - Q ^ i) : ℕ) : ℤ) := by
    rw [Nat.cast_mul, cast_prod k le_rfl, cast_prod n h, hqb]
    refine mul_right_cancel₀ (ne_of_gt (qFactorial_int_pos hQ (n - k))) ?_
    calc qBinomial (Q : ℤ) n k * (∏ i ∈ range k, ((Q : ℤ) ^ k - (Q : ℤ) ^ i))
          * qFactorial (Q : ℤ) (n - k)
        = qBinomial (Q : ℤ) n k * (qFactorial (Q : ℤ) k * qFactorial (Q : ℤ) (n - k))
            * ((Q : ℤ) ^ (k.choose 2) * ((Q : ℤ) - 1) ^ k) := by rw [hB]; ring
      _ = qFactorial (Q : ℤ) n * ((Q : ℤ) ^ (k.choose 2) * ((Q : ℤ) - 1) ^ k) := by rw [hC]
      _ = (∏ i ∈ range k, ((Q : ℤ) ^ n - (Q : ℤ) ^ i)) * qFactorial (Q : ℤ) (n - k) := by
          rw [hA]; ring
  exact_mod_cast key

/-! ### Counting subspaces -/

section Subspace

variable {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

/-- The linearly independent `k`-tuples of vectors spanning a fixed `k`-dimensional subspace `W`
correspond to the linearly independent `k`-tuples of `W`. -/
def spanEquiv {k : ℕ} {W : Submodule K V} (hW : finrank K W = k) :
    {s : Fin k → V // LinearIndependent K s ∧ Submodule.span K (Set.range s) = W}
      ≃ {t : Fin k → W // LinearIndependent K t} where
  toFun := fun ⟨s, hs, hspan⟩ =>
    ⟨fun i => ⟨s i, hspan ▸ Submodule.subset_span (Set.mem_range_self i)⟩,
      LinearIndependent.of_comp W.subtype hs⟩
  invFun := fun ⟨t, ht⟩ => ⟨fun i => (t i : V), ht.map' W.subtype (Submodule.ker_subtype W), by
    have h1 : Submodule.span K (Set.range t) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_eq_card ht, Fintype.card_fin, hW]
    calc Submodule.span K (Set.range fun i => (t i : V))
        = Submodule.map W.subtype (Submodule.span K (Set.range t)) := by
          rw [Submodule.map_span, ← Set.range_comp]; rfl
      _ = W := by rw [h1, Submodule.map_top, Submodule.range_subtype]⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

/-- **The `q`-binomial coefficient counts subspaces.**  The number of `k`-dimensional subspaces
of an `n`-dimensional vector space over a field with `q` elements is `[n choose k]_q`. -/
theorem card_submodule_finrank_eq_qBinomial (k : ℕ) :
    Nat.card {W : Submodule K V // finrank K W = k}
      = qBinomial (Fintype.card K) (finrank K V) k := by
  classical
  letI : Finite (Submodule K V) :=
    Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
  letI : Fintype {W : Submodule K V // finrank K W = k} := Fintype.ofFinite _
  rcases le_or_gt k (finrank K V) with hk | hk
  · have hQ : 1 < Fintype.card K := Fintype.one_lt_card
    have hpos : 0 < ∏ i ∈ range k, (Fintype.card K ^ k - Fintype.card K ^ i) :=
      Finset.prod_pos fun i hi => Nat.sub_pos_of_lt
        (Nat.pow_lt_pow_right hQ (mem_range.1 hi))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [qBinomial_mul_prod_pow_sub_pow _ _ _ hQ.le hk]
    -- both sides now count the linearly independent `k`-tuples of `V`
    let f : {s : Fin k → V // LinearIndependent K s} → {W : Submodule K V // finrank K W = k} :=
      fun s => ⟨Submodule.span K (Set.range s.1), by
        rw [finrank_span_eq_card s.2, Fintype.card_fin]⟩
    have hfib : ∀ W : {W : Submodule K V // finrank K W = k},
        Nat.card {s // f s = W} = ∏ i ∈ range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
      intro W
      have e1 : {s : {s : Fin k → V // LinearIndependent K s} // f s = W}
          ≃ {s : Fin k → V // LinearIndependent K s ∧ Submodule.span K (Set.range s) = W.1} :=
        { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr (e1.trans (spanEquiv W.2)), card_linearIndependent (le_of_eq W.2.symm),
        Fin.prod_univ_eq_prod_range (fun i => Fintype.card K ^ finrank K W.1
          - Fintype.card K ^ i) k, W.2]
    symm
    calc ∏ i ∈ range k, (Fintype.card K ^ finrank K V - Fintype.card K ^ i)
        = Nat.card {s : Fin k → V // LinearIndependent K s} := by
          rw [card_linearIndependent hk, Fin.prod_univ_eq_prod_range
            (fun i => Fintype.card K ^ finrank K V - Fintype.card K ^ i) k]
      _ = ∑ _W : {W : Submodule K V // finrank K W = k},
            ∏ i ∈ range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
          rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
          exact Finset.sum_congr rfl fun W _ => hfib W
      _ = Nat.card {W : Submodule K V // finrank K W = k}
            * ∏ i ∈ range k, (Fintype.card K ^ k - Fintype.card K ^ i) := by
          rw [Finset.sum_const, Nat.card_eq_fintype_card, Finset.card_univ, smul_eq_mul]
  · have : IsEmpty {W : Submodule K V // finrank K W = k} :=
      ⟨fun W => absurd (W.2 ▸ Submodule.finrank_le W.1) (by omega)⟩
    rw [Nat.card_of_isEmpty, qBinomial_eq_zero_of_lt _ hk]

end Subspace

end QAnalog
