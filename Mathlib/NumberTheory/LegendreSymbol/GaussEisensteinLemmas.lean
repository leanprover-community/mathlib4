/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

#align_import number_theory.legendre_symbol.gauss_eisenstein_lemmas from "leanprover-community/mathlib"@"c471da714c044131b90c133701e51b877c246677"

/-!
# Lemmas of Gauss and Eisenstein

This file contains the Lemmas of Gauss and Eisenstein on the Legendre symbol.
The main results are `ZMod.gauss_lemma` and `ZMod.eisenstein_lemma`.
-/


open Finset Nat

open scoped BigOperators Nat

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

section GaussEisenstein

namespace ZMod

/-- The image of the map sending a nonzero natural number `x ≤ p / 2` to the absolute value
  of the integer in `(-p/2, p/2]` that is congruent to `a * x mod p` is the set
  of nonzero natural numbers `x` such that `x ≤ p / 2`. -/
theorem Ico_map_valMinAbs_natAbs_eq_Ico_map_id (p : ℕ) [hp : Fact p.Prime] (a : ZMod p)
    (hap : a ≠ 0) : ((Ico 1 (p / 2).succ).1.map fun (x : ℕ) => (a * x).valMinAbs.natAbs) =
    (Ico 1 (p / 2).succ).1.map fun a => a := by
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2 := by
    simp (config := { contextual := true }) [Nat.lt_succ_iff, Nat.succ_le_iff, pos_iff_ne_zero]
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p := fun hx =>
    lt_of_le_of_lt (he hx).2 (Nat.div_lt_self hp.1.pos (by decide))
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬p ∣ x := fun hx hpx =>
    not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)
  have hmem : ∀ (x : ℕ) (hx : x ∈ Ico 1 (p / 2).succ),
      (a * x : ZMod p).valMinAbs.natAbs ∈ Ico 1 (p / 2).succ := by
    intro x hx
    simp [hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hx, lt_succ_iff, succ_le_iff, pos_iff_ne_zero,
      natAbs_valMinAbs_le _]
  have hsurj : ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ),
      ∃ x ∈ Ico 1 (p / 2).succ, b = (a * x : ZMod p).valMinAbs.natAbs := by
    intro b hb
    refine' ⟨(b / a : ZMod p).valMinAbs.natAbs, mem_Ico.mpr ⟨_, _⟩, _⟩
    · apply Nat.pos_of_ne_zero
      simp only [div_eq_mul_inv, hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hb, not_false_iff,
        valMinAbs_eq_zero, inv_eq_zero, Int.natAbs_eq_zero, Ne.def, _root_.mul_eq_zero, or_self_iff]
    · apply lt_succ_of_le; apply natAbs_valMinAbs_le
    · rw [nat_cast_natAbs_valMinAbs]
      split_ifs
      · erw [mul_div_cancel' _ hap, valMinAbs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_ofNat]
      · erw [mul_neg, mul_div_cancel' _ hap, natAbs_valMinAbs_neg, valMinAbs_def_pos,
          val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_ofNat]
  simp only [← exists_prop] at hsurj
  -- ⊢ Multiset.map (fun x => Int.natAbs (valMinAbs (a * ↑x))) (Ico 1 (succ (p / 2) …
  exact Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
    (fun x _ => (a * x : ZMod p).valMinAbs.natAbs) hmem (fun _ _ => rfl)
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj
#align zmod.Ico_map_val_min_abs_nat_abs_eq_Ico_map_id ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id

private theorem gauss_lemma_aux₁ (p : ℕ) [Fact p.Prime] {a : ℤ}
    (hap : (a : ZMod p) ≠ 0) : (a ^ (p / 2) * (p / 2)! : ZMod p) =
    (-1 : ZMod p) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ =>
      ¬(a * x : ZMod p).val ≤ p / 2).card * (p / 2)! :=
  calc
    (a ^ (p / 2) * (p / 2)! : ZMod p) = ∏ x in Ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib, ← prod_natCast, prod_Ico_id_eq_factorial, prod_const, card_Ico,
        succ_sub_one]; simp
                       -- 🎉 no goals
    _ = ∏ x in Ico 1 (p / 2).succ, ↑((a * x : ZMod p).val) := by simp
                                                                 -- 🎉 no goals
    _ = ∏ x in Ico 1 (p / 2).succ, (if (a * x : ZMod p).val ≤ p / 2 then (1 : ZMod p) else -1) *
        (a * x : ZMod p).valMinAbs.natAbs :=
      (prod_congr rfl fun _ _ => by
        simp only [nat_cast_natAbs_valMinAbs]
        -- ⊢ ↑(val (↑a * ↑x✝¹)) = (if val (↑a * ↑x✝¹) ≤ p / 2 then 1 else -1) * if val (↑ …
        split_ifs <;> simp)
        -- ⊢ ↑(val (↑a * ↑x✝¹)) = 1 * (↑a * ↑x✝¹)
                      -- 🎉 no goals
                      -- 🎉 no goals
    _ = (-1 : ZMod p) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ =>
        ¬(a * x : ZMod p).val ≤ p / 2).card * ∏ x in Ico 1 (p / 2).succ,
          ↑((a * x : ZMod p).valMinAbs.natAbs) := by
      have :
          (∏ x in Ico 1 (p / 2).succ, if (a * x : ZMod p).val ≤ p / 2 then (1 : ZMod p) else -1) =
          ∏ x in (Ico 1 (p / 2).succ).filter fun x : ℕ => ¬(a * x : ZMod p).val ≤ p / 2, -1 :=
        prod_bij_ne_one (fun x _ _ => x)
          (fun x => by split_ifs <;> simp_all (config := { contextual := true }))
          (fun _ _ _ _ _ _ => id) (fun b h _ => ⟨b, by simp_all [-not_le]⟩)
          (by intros; split_ifs at * <;> simp_all)
      rw [prod_mul_distrib, this]; simp
      -- ⊢ (∏ x in filter (fun x => ¬val (↑a * ↑x) ≤ p / 2) (Ico 1 (succ (p / 2))), -1) …
                                   -- 🎉 no goals
    _ = (-1 : ZMod p) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ =>
        ¬(a * x : ZMod p).val ≤ p / 2).card * (p / 2)! := by
      rw [← prod_natCast, Finset.prod_eq_multiset_prod,
        Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap, ← Finset.prod_eq_multiset_prod,
        prod_Ico_id_eq_factorial]

theorem gauss_lemma_aux (p : ℕ) [hp : Fact p.Prime] {a : ℤ}
    (hap : (a : ZMod p) ≠ 0) : (↑a ^ (p / 2) : ZMod p) =
    (-1) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : ZMod p).val).card :=
  (mul_left_inj' (show ((p / 2)! : ZMod p) ≠ 0 by
    rw [Ne.def, CharP.cast_eq_zero_iff (ZMod p) p, hp.1.dvd_factorial, not_le]
    -- ⊢ p / 2 < p
    exact Nat.div_lt_self hp.1.pos (by decide))).1 <| by
    -- 🎉 no goals
      simpa using gauss_lemma_aux₁ p hap
      -- 🎉 no goals
#align zmod.gauss_lemma_aux ZMod.gauss_lemma_aux

/-- Gauss' lemma. The Legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2`. -/
theorem gauss_lemma {p : ℕ} [h : Fact p.Prime] {a : ℤ} (hp : p ≠ 2) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = (-1) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ =>
      p / 2 < (a * x : ZMod p).val).card := by
  replace hp : Odd p := h.out.odd_of_ne_two hp
  -- ⊢ legendreSym p a = (-1) ^ Finset.card (filter (fun x => p / 2 < val (↑a * ↑x) …
  have : (legendreSym p a : ZMod p) = (((-1) ^ ((Ico 1 (p / 2).succ).filter fun x : ℕ =>
      p / 2 < (a * x : ZMod p).val).card : ℤ) : ZMod p) := by
    rw [legendreSym.eq_pow, gauss_lemma_aux p ha0]
  cases legendreSym.eq_one_or_neg_one p ha0 <;>
  -- ⊢ legendreSym p a = (-1) ^ Finset.card (filter (fun x => p / 2 < val (↑a * ↑x) …
  cases neg_one_pow_eq_or ℤ
    ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : ZMod p).val).card <;>
  simp_all [ne_neg_self hp one_ne_zero, (ne_neg_self hp one_ne_zero).symm]
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align zmod.gauss_lemma ZMod.gauss_lemma

private theorem eisenstein_lemma_aux₁ (p : ℕ) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : ℕ}
    (hap : (a : ZMod p) ≠ 0) : ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
    ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : ZMod p).val).card +
      ∑ x in Ico 1 (p / 2).succ, x + (∑ x in Ico 1 (p / 2).succ, a * x / p : ℕ) :=
  have hp2 : (p : ZMod 2) = (1 : ℕ) := (eq_iff_modEq_nat _).2 hp2.1
  calc
    ((∑ x in Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
        ((∑ x in Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : ℕ) : ZMod 2) := by
      simp only [mod_add_div]
      -- 🎉 no goals
    _ = (∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) +
        (∑ x in Ico 1 (p / 2).succ, a * x / p : ℕ) := by
      simp only [val_nat_cast]
      -- ⊢ ↑(∑ x in Ico 1 (succ (p / 2)), (a * x % p + p * (a * x / p))) = ↑(∑ x in Ico …
      simp [sum_add_distrib, mul_sum.symm, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
      -- 🎉 no goals
    _ = _ :=
      congr_arg₂ (· + ·)
        (calc
          ((∑ x in Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) : ZMod 2) =
              ∑ x in Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val ≤ p / 2 then 0 else p : ℤ) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
            -- ⊢ ↑(∑ x in Ico 1 (succ (p / 2)), val ↑(a * x)) = ∑ x in Ico 1 (succ (p / 2)),  …
                                                       -- 🎉 no goals
          _ = ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : ZMod p).val).card +
              (∑ x in Ico 1 (p / 2).succ, (a * x : ZMod p).valMinAbs.natAbs : ℕ) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
            -- 🎉 no goals
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum, Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap, ←
              Finset.sum_eq_multiset_sum])
        rfl

theorem eisenstein_lemma_aux (p : ℕ) [Fact p.Prime] [Fact (p % 2 = 1)] {a : ℕ} (ha2 : a % 2 = 1)
    (hap : (a : ZMod p) ≠ 0) :
    ((Ico 1 (p / 2).succ).filter fun x : ℕ => p / 2 < (a * x : ZMod p).val).card ≡
      ∑ x in Ico 1 (p / 2).succ, x * a / p [MOD 2] :=
  have ha2 : (a : ZMod 2) = (1 : ℕ) := (eq_iff_modEq_nat _).2 ha2
  (eq_iff_modEq_nat 2).1 <| sub_eq_zero.1 <| by
    simpa [add_left_comm, sub_eq_add_neg, Finset.mul_sum.symm, mul_comm, ha2, Nat.cast_sum,
      add_neg_eq_iff_eq_add.symm, neg_eq_self_mod_two, add_assoc] using
      Eq.symm (eisenstein_lemma_aux₁ p hap)
#align zmod.eisenstein_lemma_aux ZMod.eisenstein_lemma_aux

theorem div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
    a / b = ((Ico 1 c.succ).filter fun x => x * b ≤ a).card :=
  calc
    a / b = (Ico 1 (a / b).succ).card := by simp
                                            -- 🎉 no goals
    _ = ((Ico 1 c.succ).filter fun x => x * b ≤ a).card :=
      congr_arg _ <| Finset.ext fun x => by
        have : x * b ≤ a → x ≤ c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        -- ⊢ x ∈ Ico 1 (succ (a / b)) ↔ x ∈ filter (fun x => x * b ≤ a) (Ico 1 (succ c))
        simp [lt_succ_iff, le_div_iff_mul_le hb0]; tauto
        -- ⊢ x * b ≤ a → 1 ≤ x → x ≤ c
                                                   -- 🎉 no goals
#align zmod.div_eq_filter_card ZMod.div_eq_filter_card

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`. -/
private theorem sum_Ico_eq_card_lt {p q : ℕ} :
    ∑ a in Ico 1 (p / 2).succ, a * q / p =
    ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ =>
      x.2 * p ≤ x.1 * q).card :=
  if hp0 : p = 0 then by simp [hp0, Finset.ext_iff]
                         -- 🎉 no goals
  else
    calc
      ∑ a in Ico 1 (p / 2).succ, a * q / p =
          ∑ a in Ico 1 (p / 2).succ, ((Ico 1 (q / 2).succ).filter fun x => x * p ≤ a * q).card :=
        Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0)
          (calc
            x * q / p ≤ p / 2 * q / p := Nat.div_le_div_right
              (mul_le_mul_of_nonneg_right (le_of_lt_succ <| (mem_Ico.mp hx).2) (Nat.zero_le _))
            _ ≤ _ := Nat.div_mul_div_le_div _ _ _)
      _ = _ := by
        rw [← card_sigma]
        -- ⊢ Finset.card (Finset.sigma (Ico 1 (succ (p / 2))) fun a => filter (fun x => x …
        exact card_congr (fun a _ => ⟨a.1, a.2⟩) (by
          simp (config := { contextual := true }) only [mem_filter, mem_sigma, and_self_iff,
            forall_true_iff, mem_product])
          (fun ⟨_, _⟩ ⟨_, _⟩ => by
            simp (config := { contextual := true }) only [Prod.mk.inj_iff, eq_self_iff_true,
              and_self_iff, heq_iff_eq, forall_true_iff])
          fun ⟨b₁, b₂⟩ h => ⟨⟨b₁, b₂⟩, by
            revert h
            simp (config := { contextual := true }) only [mem_filter, eq_self_iff_true,
              exists_prop_of_true, mem_sigma, and_self_iff, forall_true_iff, mem_product]⟩

/-- Each of the sums in this lemma is the cardinality of the set of integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
theorem sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : Fact p.Prime] (hq0 : (q : ZMod p) ≠ 0) :
    ∑ a in Ico 1 (p / 2).succ, a * q / p + ∑ a in Ico 1 (q / 2).succ, a * p / q =
    p / 2 * (q / 2) := by
  have hswap :
    ((Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ).filter fun x : ℕ × ℕ => x.2 * q ≤ x.1 * p).card =
      ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ =>
        x.1 * q ≤ x.2 * p).card :=
    card_congr (fun x _ => Prod.swap x)
      (fun ⟨_, _⟩ => by
        simp (config := { contextual := true }) only [mem_filter, and_self_iff, Prod.swap_prod_mk,
          forall_true_iff, mem_product])
      (fun ⟨_, _⟩ ⟨_, _⟩ => by
        simp (config := { contextual := true }) only [Prod.mk.inj_iff, eq_self_iff_true,
          and_self_iff, Prod.swap_prod_mk, forall_true_iff])
      fun ⟨x₁, x₂⟩ h => ⟨⟨x₂, x₁⟩, by
        revert h
        simp (config := { contextual := true }) only [mem_filter, eq_self_iff_true, and_self_iff,
          exists_prop_of_true, Prod.swap_prod_mk, forall_true_iff, mem_product]⟩
  have hdisj :
    Disjoint ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ => x.2 * p ≤ x.1 * q)
      ((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ => x.1 * q ≤ x.2 * p) := by
    apply disjoint_filter.2 fun x hx hpq hqp => ?_
    have hxp : x.1 < p := lt_of_le_of_lt
      (show x.1 ≤ p / 2 by simp_all only [lt_succ_iff, mem_Ico, mem_product])
      (Nat.div_lt_self hp.1.pos (by decide))
    have : (x.1 : ZMod p) = 0 := by
      simpa [hq0] using congr_arg ((↑) : ℕ → ZMod p) (le_antisymm hpq hqp)
    apply_fun ZMod.val at this
    rw [val_cast_of_lt hxp, val_zero] at this
    simp only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and_iff, mem_product] at hx
  have hunion :
      (((Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ => x.2 * p ≤ x.1 * q) ∪
        (Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ).filter fun x : ℕ × ℕ => x.1 * q ≤ x.2 * p) =
      Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * p) (x.1 * q)
      simp only [mem_union, mem_filter, mem_Ico, mem_product]
      tauto
  rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_disjoint_union hdisj, hunion,
    card_product]
  simp only [card_Ico, tsub_zero, succ_sub_succ_eq_sub]
  -- 🎉 no goals
#align zmod.sum_mul_div_add_sum_mul_div_eq_mul ZMod.sum_mul_div_add_sum_mul_div_eq_mul

theorem eisenstein_lemma {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1)
    (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = (-1) ^ ∑ x in Ico 1 (p / 2).succ, x * a / p := by
  haveI hp' : Fact (p % 2 = 1) := ⟨Nat.Prime.mod_two_eq_one_iff_ne_two.mpr hp⟩
  -- ⊢ legendreSym p ↑a = (-1) ^ ∑ x in Ico 1 (succ (p / 2)), x * a / p
  have ha0' : ((a : ℤ) : ZMod p) ≠ 0 := by norm_cast
  -- ⊢ legendreSym p ↑a = (-1) ^ ∑ x in Ico 1 (succ (p / 2)), x * a / p
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma hp ha0', neg_one_pow_eq_pow_mod_two,
    (by norm_cast : ((a : ℤ) : ZMod p) = (a : ZMod p)),
    show _ = _ from eisenstein_lemma_aux p ha1 ha0]
#align zmod.eisenstein_lemma ZMod.eisenstein_lemma

end ZMod

end GaussEisenstein
