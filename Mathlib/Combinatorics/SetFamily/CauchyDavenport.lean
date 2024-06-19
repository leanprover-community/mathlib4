/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.GroupTheory.Order.Min

/-!
# The Cauchy-Davenport theorem

This file proves a generalisation of the Cauchy-Davenport theorem to arbitrary groups.

Cauchy-Davenport provides a lower bound on the size of `s + t` in terms of the sizes of `s` and `t`,
where `s` and `t` are nonempty finite sets in a monoid. Precisely, it says that
`|s + t| ≥ |s| + |t| - 1` unless the RHS is bigger than the size of the smallest nontrivial subgroup
(in which case taking `s` and `t` to be that subgroup would yield a counterexample). The motivating
example is `s = {0, ..., m}`, `t = {0, ..., n}` in the integers, which gives
`s + t = {0, ..., m + n}` and `|s + t| = m + n + 1 = |s| + |t| - 1`.

There are two kinds of proof of Cauchy-Davenport:
* The first one works in linear orders by writing `a₁ < ... < aₖ` the elements of `s`,
  `b₁ < ... < bₗ` the elements of `t`, and arguing that `a₁ + b₁ < ... < aₖ + b₁ < ... < aₖ + bₗ`
  are distinct elements of `s + t`.
* The second one works in groups by performing an "e-transform". In an abelian group, the
  e-transform replaces `s` and `t` by `s ∩ g • s` and `t ∪ g⁻¹ • t`. For a suitably chosen `g`, this
  decreases `|s + t|` and keeps `|s| + |t|` the same. In a general group, we use a trickier
  e-transform (in fact, a pair of e-transforms), but the idea is the same.

## Main declarations

* `Finset.min_le_card_mul`: A generalisation of the Cauchy-Davenport theorem to arbitrary groups.
* `Monoid.IsTorsionFree.card_add_card_sub_one_le_card_mul`: The Cauchy-Davenport theorem in
  torsion-free groups.
* `ZMod.min_le_card_add`: The Cauchy-Davenport theorem.
* `Finset.card_add_card_sub_one_le_card_mul`: The Cauchy-Davenport theorem in linear ordered
  cancellative semigroups.

## TODO

Version for `circle`.

## References

* Matt DeVos, *On a generalization of the Cauchy-Davenport theorem*

## Tags

additive combinatorics, number theory, sumset, cauchy-davenport
-/

open Finset Function Monoid MulOpposite Subgroup
open scoped Pointwise

variable {α : Type*}

/-! ### General case -/

section General
variable [Group α] [DecidableEq α] {x y : Finset α × Finset α} {s t : Finset α}

/-- The relation we induct along in the proof by DeVos of the Cauchy-Davenport theorem.
`(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ * t₁| < |s₂ * t₂|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ * t₁| = |s₂ * t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`. -/
@[to_additive
"The relation we induct along in the proof by DeVos of the Cauchy-Davenport theorem.
`(s₁, t₁) < (s₂, t₂)` iff
* `|s₁ + t₁| < |s₂ + t₂|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₂| + |t₂| < |s₁| + |t₁|`
* or `|s₁ + t₁| = |s₂ + t₂|` and `|s₁| + |t₁| = |s₂| + |t₂|` and `|s₁| < |s₂|`."]
private def DevosMulRel : Finset α × Finset α → Finset α × Finset α → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· > ·) (· < ·)) on fun x ↦
    ((x.1 * x.2).card, x.1.card + x.2.card, x.1.card)

@[to_additive]
private lemma devosMulRel_iff :
    DevosMulRel x y ↔
      (x.1 * x.2).card < (y.1 * y.2).card ∨
        (x.1 * x.2).card = (y.1 * y.2).card ∧ y.1.card + y.2.card < x.1.card + x.2.card ∨
          (x.1 * x.2).card = (y.1 * y.2).card ∧
            x.1.card + x.2.card = y.1.card + y.2.card ∧ x.1.card < y.1.card := by
  simp [DevosMulRel, Prod.lex_iff, and_or_left]

@[to_additive]
private lemma devosMulRel_of_le (mul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
    (hadd : y.1.card + y.2.card < x.1.card + x.2.card) : DevosMulRel x y :=
  devosMulRel_iff.2 <| mul.lt_or_eq.imp_right fun h ↦ Or.inl ⟨h, hadd⟩

@[to_additive]
private lemma devosMulRel_of_le_of_le (mul : (x.1 * x.2).card ≤ (y.1 * y.2).card)
    (hadd : y.1.card + y.2.card ≤ x.1.card + x.2.card) (hone : x.1.card < y.1.card) :
    DevosMulRel x y :=
  devosMulRel_iff.2 <|
    mul.lt_or_eq.imp_right fun h ↦ hadd.gt_or_eq.imp (And.intro h) fun h' ↦ ⟨h, h', hone⟩

@[to_additive]
private lemma wellFoundedOn_devosMulRel :
    {x : Finset α × Finset α | x.1.Nonempty ∧ x.2.Nonempty}.WellFoundedOn
      (DevosMulRel : Finset α × Finset α → Finset α × Finset α → Prop) := by
  refine wellFounded_lt.onFun.wellFoundedOn.prod_lex_of_wellFoundedOn_fiber fun n ↦
    Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber ?_ fun n ↦
      wellFounded_lt.onFun.wellFoundedOn
  exact wellFounded_lt.onFun.wellFoundedOn.mono' fun x hx y _ ↦ tsub_lt_tsub_left_of_le <|
    add_le_add ((card_le_card_mul_right _ hx.1.2).trans_eq hx.2) <|
      (card_le_card_mul_left _ hx.1.1).trans_eq hx.2

/-- A generalisation of the **Cauchy-Davenport theorem** to arbitrary groups. The size of `s * t` is
lower-bounded by `|s| + |t| - 1` unless this quantity is greater than the size of the smallest
subgroup. -/
@[to_additive "A generalisation of the **Cauchy-Davenport theorem** to arbitrary groups. The size of
`s + t` is lower-bounded by `|s| + |t| - 1` unless this quantity is greater than the size of the
smallest subgroup."]
lemma Finset.min_le_card_mul (hs : s.Nonempty) (ht : t.Nonempty) :
    min (minOrder α) ↑(s.card + t.card - 1) ≤ (s * t).card := by
  -- Set up the induction on `x := (s, t)` along the `DevosMulRel` relation.
  set x := (s, t) with hx
  clear_value x
  simp only [Prod.ext_iff] at hx
  obtain ⟨rfl, rfl⟩ := hx
  refine wellFoundedOn_devosMulRel.induction (P := fun x : Finset α × Finset α ↦
    min (minOrder α) ↑(card x.1 + card x.2 - 1) ≤ card (x.1 * x.2)) ⟨hs, ht⟩ ?_
  clear! x
  rintro ⟨s, t⟩ ⟨hs, ht⟩ ih
  simp only [min_le_iff, tsub_le_iff_right, Prod.forall, Set.mem_setOf_eq, and_imp,
    Nat.cast_le] at *
  -- If `t.card < s.card`, we're done by the induction hypothesis on `(t⁻¹, s⁻¹)`.
  obtain hts | hst := lt_or_le t.card s.card
  · simpa only [← mul_inv_rev, add_comm, card_inv] using
      ih _ _ ht.inv hs.inv
        (devosMulRel_iff.2 <| Or.inr <| Or.inr <| by
          simpa only [← mul_inv_rev, add_comm, card_inv, true_and])
  -- If `s` is a singleton, then the result is trivial.
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · simp [add_comm]
  -- Else, we have `a, b ∈ s` distinct. So `g := b⁻¹ * a` is a non-identity element such that `s`
  -- intersects its right translate by `g`.
  obtain ⟨g, hg, hgs⟩ : ∃ g : α, g ≠ 1 ∧ (s ∩ op g • s).Nonempty :=
    ⟨b⁻¹ * a, inv_mul_eq_one.not.2 hab.symm, _,
      mem_inter.2 ⟨ha, mem_smul_finset.2 ⟨_, hb, by simp⟩⟩⟩
  -- If `s` is equal to its right translate by `g`, then it contains a nontrivial subgroup, namely
  -- the subgroup generated by `g`. So `s * t` has size at least the size of a nontrivial subgroup,
  -- as wanted.
  obtain hsg | hsg := eq_or_ne (op g • s) s
  · have hS : (zpowers g : Set α) ⊆ a⁻¹ • (s : Set α) := by
      refine forall_mem_zpowers.2 <| @zpow_induction_right _ _ _ (· ∈ a⁻¹ • (s : Set α))
        ⟨_, ha, inv_mul_self _⟩ (fun c hc ↦ ?_) fun c hc ↦ ?_
      · rw [← hsg, coe_smul_finset, smul_comm]
        exact Set.smul_mem_smul_set hc
      · simp only
        rwa [← op_smul_eq_mul, op_inv, ← Set.mem_smul_set_iff_inv_smul_mem, smul_comm,
          ← coe_smul_finset, hsg]
    refine Or.inl ((minOrder_le_natCard (zpowers_ne_bot.2 hg) <|
      s.finite_toSet.smul_set.subset hS).trans <| WithTop.coe_le_coe.2 <|
        ((Nat.card_mono s.finite_toSet.smul_set hS).trans_eq <| ?_).trans <|
          card_le_card_mul_right _ ht)
    rw [← coe_smul_finset]
    simp [-coe_smul_finset]
  -- Else, we can transform `s`, `t` to `s'`, `t'` and `s''`, `t''`, such that one of `(s', t')` and
  -- `(s'', t'')` is strictly smaller than `(s, t)` according to `DevosMulRel`.
  replace hsg : (s ∩ op g • s).card < s.card := card_lt_card ⟨inter_subset_left, fun h ↦
    hsg <| eq_of_superset_of_card_ge (h.trans inter_subset_right) (card_smul_finset _ _).le⟩
  replace aux1 := card_mono <| mulETransformLeft.fst_mul_snd_subset g (s, t)
  replace aux2 := card_mono <| mulETransformRight.fst_mul_snd_subset g (s, t)
  -- If the left translate of `t` by `g⁻¹` is disjoint from `t`, then we're easily done.
  obtain hgt | hgt := disjoint_or_nonempty_inter t (g⁻¹ • t)
  · rw [← card_smul_finset g⁻¹ t]
    refine Or.inr ((add_le_add_right hst _).trans ?_)
    rw [← card_union_of_disjoint hgt]
    exact (card_le_card_mul_left _ hgs).trans (le_add_of_le_left aux1)
  -- Else, we're done by induction on either `(s', t')` or `(s'', t'')` depending on whether
  -- `|s| + |t| ≤ |s'| + |t'|` or `|s| + |t| < |s''| + |t''|`. One of those two inequalities must
  -- hold since `2 * (|s| + |t|) = |s'| + |t'| + |s''| + |t''|`.
  obtain hstg | hstg := le_or_lt_of_add_le_add (MulETransform.card g (s, t)).ge
  · exact (ih _ _ hgs (hgt.mono inter_subset_union) <| devosMulRel_of_le_of_le aux1 hstg hsg).imp
      (WithTop.coe_le_coe.2 aux1).trans' fun h ↦ hstg.trans <| h.trans <| add_le_add_right aux1 _
  · exact (ih _ _ (hgs.mono inter_subset_union) hgt <| devosMulRel_of_le aux2 hstg).imp
      (WithTop.coe_le_coe.2 aux2).trans' fun h ↦
        hstg.le.trans <| h.trans <| add_le_add_right aux2 _

/-- The **Cauchy-Davenport Theorem** for torsion-free groups. The size of `s * t` is lower-bounded
by `|s| + |t| - 1`. -/
@[to_additive "The **Cauchy-Davenport theorem** for torsion-free groups. The size of `s + t` is
lower-bounded by `|s| + |t| - 1`."]
lemma Monoid.IsTorsionFree.card_add_card_sub_one_le_card_mul (h : IsTorsionFree α)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.card + t.card - 1 ≤ (s * t).card := by
  simpa only [h.minOrder, min_eq_right, le_top, Nat.cast_le] using Finset.min_le_card_mul hs ht

end General

/-! ### $$ℤ/nℤ$$ -/

/-- The **Cauchy-Davenport Theorem**. If `s`, `t` are nonempty sets in $$ℤ/pℤ$$, then the size of
`s + t` is lower-bounded by `|s| + |t| - 1`, unless this quantity is greater than `p`. -/
lemma ZMod.min_le_card_add {p : ℕ} (hp : p.Prime) {s t : Finset (ZMod p)} (hs : s.Nonempty)
    (ht : t.Nonempty) : min p (s.card + t.card - 1) ≤ (s + t).card := by
  simpa only [ZMod.minOrder_of_prime hp, min_le_iff, Nat.cast_le] using Finset.min_le_card_add hs ht

/-! ### Linearly ordered cancellative semigroups -/

/-- The **Cauchy-Davenport Theorem** for linearly ordered cancellative semigroups. The size of
`s * t` is lower-bounded by `|s| + |t| - 1`. -/
@[to_additive
"The **Cauchy-Davenport theorem** for linearly ordered additive cancellative semigroups. The size of
`s + t` is lower-bounded by `|s| + |t| - 1`."]
lemma Finset.card_add_card_sub_one_le_card_mul [LinearOrder α] [Semigroup α] [IsCancelMul α]
    [CovariantClass α α (· * ·) (· ≤ ·)] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    {s t : Finset α} (hs : s.Nonempty) (ht : t.Nonempty) : s.card + t.card - 1 ≤ (s * t).card := by
  suffices s * {t.min' ht} ∩ ({s.max' hs} * t) = {s.max' hs * t.min' ht} by
    rw [← card_singleton_mul t (s.max' hs), ← card_mul_singleton s (t.min' ht),
      ← card_union_add_card_inter, ← card_singleton _, ← this, Nat.add_sub_cancel]
    exact card_mono (union_subset (mul_subset_mul_left <| singleton_subset_iff.2 <| min'_mem _ _) <|
      mul_subset_mul_right <| singleton_subset_iff.2 <| max'_mem _ _)
  refine eq_singleton_iff_unique_mem.2 ⟨mem_inter.2 ⟨mul_mem_mul (max'_mem _ _) <|
    mem_singleton_self _, mul_mem_mul (mem_singleton_self _) <| min'_mem _ _⟩, ?_⟩
  simp only [mem_inter, and_imp, mem_mul, mem_singleton, exists_and_left, exists_eq_left,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mul_left_inj]
  exact fun a' ha' b' hb' h ↦ (le_max' _ _ ha').eq_of_not_lt fun ha ↦
    ((mul_lt_mul_right' ha _).trans_eq' h).not_le <| mul_le_mul_left' (min'_le _ _ hb') _
