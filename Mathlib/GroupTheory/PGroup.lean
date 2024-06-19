/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases

#align_import group_theory.p_group from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/


open Fintype MulAction

variable (p : ℕ) (G : Type*) [Group G]

/-- A p-group is a group in which every element has prime power order -/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1
#align is_p_group IsPGroup

variable {p} {G}

namespace IsPGroup

theorem iff_orderOf [hp : Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k :=
  forall_congr' fun g =>
    ⟨fun ⟨k, hk⟩ =>
      Exists.imp (fun _ h => h.right)
        ((Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)),
      Exists.imp fun k hk => by rw [← hk, pow_orderOf_eq_one]⟩
#align is_p_group.iff_order_of IsPGroup.iff_orderOf

theorem of_card [Fintype G] {n : ℕ} (hG : card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by rw [← hG, pow_card_eq_one]⟩
#align is_p_group.of_card IsPGroup.of_card

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (Subgroup.card_bot.trans (pow_zero p).symm)
#align is_p_group.of_bot IsPGroup.of_bot

theorem iff_card [Fact p.Prime] [Fintype G] : IsPGroup p G ↔ ∃ n : ℕ, card G = p ^ n := by
  have hG : card G ≠ 0 := card_ne_zero
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card hn⟩
  suffices ∀ q ∈ Nat.factors (card G), q = p by
    use (card G).factors.length
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem this, Nat.prod_factors hG]
  intro q hq
  obtain ⟨hq1, hq2⟩ := (Nat.mem_factors hG).mp hq
  haveI : Fact q.Prime := ⟨hq1⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card q hq2
  obtain ⟨k, hk⟩ := (iff_orderOf.mp h) g
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm
#align is_p_group.iff_card IsPGroup.iff_card

alias ⟨exists_card_eq, _⟩ := iff_card

section GIsPGroup

variable (hG : IsPGroup p G)

theorem of_injective {H : Type*} [Group H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)
#align is_p_group.of_injective IsPGroup.of_injective

theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective
#align is_p_group.to_subgroup IsPGroup.to_subgroup

theorem of_surjective {H : Type*} [Group H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H := by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]
#align is_p_group.of_surjective IsPGroup.of_surjective

theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.surjective_Quotient_mk''
#align is_p_group.to_quotient IsPGroup.to_quotient

theorem of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.toMonoidHom ϕ.surjective
#align is_p_group.of_equiv IsPGroup.of_equiv

theorem orderOf_coprime {n : ℕ} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
#align is_p_group.order_of_coprime IsPGroup.orderOf_coprime

/-- If `gcd(p,n) = 1`, then the `n`th power map is a bijection. -/
noncomputable def powEquiv {n : ℕ} (hn : p.Coprime n) : G ≃ G :=
  let h : ∀ g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
      Subtype.ext_iff.1 <|
        (powCoprime (h (g ^ n))).left_inv
          ⟨g, _, Subtype.ext_iff.1 <| (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
      Subtype.ext_iff.1 <| (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }
#align is_p_group.pow_equiv IsPGroup.powEquiv

@[simp]
theorem powEquiv_apply {n : ℕ} (hn : p.Coprime n) (g : G) : hG.powEquiv hn g = g ^ n :=
  rfl
#align is_p_group.pow_equiv_apply IsPGroup.powEquiv_apply

@[simp]
theorem powEquiv_symm_apply {n : ℕ} (hn : p.Coprime n) (g : G) :
    (hG.powEquiv hn).symm g = g ^ (orderOf g).gcdB n := by rw [← Nat.card_zpowers]; rfl
#align is_p_group.pow_equiv_symm_apply IsPGroup.powEquiv_symm_apply

variable [hp : Fact p.Prime]

/-- If `p ∤ n`, then the `n`th power map is a bijection. -/
noncomputable abbrev powEquiv' {n : ℕ} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)
#align is_p_group.pow_equiv' IsPGroup.powEquiv'

theorem index (H : Subgroup G) [H.FiniteIndex] : ∃ n : ℕ, H.index = p ^ n := by
  haveI := H.normalCore.fintypeQuotientOfFiniteIndex
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩
#align is_p_group.index IsPGroup.index

theorem card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G := by
  cases fintypeOrInfinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [Nat.card_eq_fintype_card, hn]
    cases' n with n n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩
#align is_p_group.card_eq_or_dvd IsPGroup.card_eq_or_dvd

theorem nontrivial_iff_card [Fintype G] : Nontrivial G ↔ ∃ n > 0, card G = p ^ n :=
  ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0, pow_zero] at hk; exact Fintype.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨k, hk0, hk⟩ =>
    one_lt_card_iff_nontrivial.1 <|
      hk.symm ▸ one_lt_pow (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩
#align is_p_group.nontrivial_iff_card IsPGroup.nontrivial_iff_card

variable {α : Type*} [MulAction G α]

theorem card_orbit (a : α) [Fintype (orbit G a)] : ∃ n : ℕ, card (orbit G a) = p ^ n := by
  let ϕ := orbitEquivQuotientStabilizer G a
  haveI := Fintype.ofEquiv (orbit G a) ϕ
  haveI := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [card_congr ϕ, ← Subgroup.index_eq_card]
  exact hG.index (stabilizer G a)
#align is_p_group.card_orbit IsPGroup.card_orbit

variable (α) [Fintype α]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
theorem card_modEq_card_fixedPoints [Fintype (fixedPoints G α)] :
    card α ≡ card (fixedPoints G α) [MOD p] := by
  classical
    calc
      card α = card (Σy : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.eq_iff_modEq_nat p, Nat.cast_sum, Nat.cast_sum]
    have key :
      ∀ x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.eq (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    have : k = 0 :=
      Nat.le_zero.1
        (Nat.le_of_lt_succ
          (lt_of_not_ge
            (mt (pow_dvd_pow p)
              (by
                rwa [pow_one, ← hk, ← Nat.modEq_zero_iff_dvd, ← ZMod.eq_iff_modEq_nat, ← key,
                  Nat.cast_zero]))))
    exact
      ⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 <| by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩
#align is_p_group.card_modeq_card_fixed_points IsPGroup.card_modEq_card_fixedPoints

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
theorem nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬p ∣ card α) [Finite (fixedPoints G α)] :
    (fixedPoints G α).Nonempty :=
  @Set.nonempty_of_nonempty_subtype _ _
    (by
      cases nonempty_fintype (fixedPoints G α)
      rw [← card_pos_iff, pos_iff_ne_zero]
      contrapose! hpα
      rw [← Nat.modEq_zero_iff_dvd, ← hpα]
      exact hG.card_modEq_card_fixedPoints α)
#align is_p_group.nonempty_fixed_point_of_prime_not_dvd_card IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ card α) {a : α}
    (ha : a ∈ fixedPoints G α) : ∃ b, b ∈ fixedPoints G α ∧ a ≠ b := by
  cases nonempty_fintype (fixedPoints G α)
  have hpf : p ∣ card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩
#align is_p_group.exists_fixed_point_of_prime_dvd_card_of_fixed_point IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point

theorem center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) := by
  classical
    cases nonempty_fintype G
    have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
    rw [ConjAct.fixedPoints_eq_center] at this
    have dvd : p ∣ card G := by
      obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
      exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
    obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
    exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩
#align is_p_group.center_nontrivial IsPGroup.center_nontrivial

theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G := by
  haveI := center_nontrivial hG
  cases nonempty_fintype G
  classical exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Fintype.one_lt_card)
#align is_p_group.bot_lt_center IsPGroup.bot_lt_center

end GIsPGroup

theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)
#align is_p_group.to_le IsPGroup.to_le

theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hH.to_le inf_le_left
#align is_p_group.to_inf_left IsPGroup.to_inf_left

theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hK.to_le inf_le_right
#align is_p_group.to_inf_right IsPGroup.to_inf_right

theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G →* K) :
    IsPGroup p (H.map ϕ) := by
  rw [← H.subtype_range, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.restrict H).rangeRestrict (ϕ.restrict H).rangeRestrict_surjective
#align is_p_group.map IsPGroup.map

theorem comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K]
    (ϕ : K →* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) := by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ← pow_mul, ← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩
#align is_p_group.comap_of_ker_is_p_group IsPGroup.comap_of_ker_isPGroup

theorem ker_isPGroup_of_injective {K : Type*} [Group K] {ϕ : K →* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot_iff.mpr hϕ)).mpr IsPGroup.of_bot
#align is_p_group.ker_is_p_group_of_injective IsPGroup.ker_isPGroup_of_injective

theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K →* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)
#align is_p_group.comap_of_injective IsPGroup.comap_of_injective

theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} :
    IsPGroup p (H.comap K.subtype) :=
  hH.comap_of_injective K.subtype Subtype.coe_injective
#align is_p_group.comap_subtype IsPGroup.comap_subtype

theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := by
  rw [← QuotientGroup.ker_mk' K, ← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']
#align is_p_group.to_sup_of_normal_right IsPGroup.to_sup_of_normal_right

theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := sup_comm H K ▸ to_sup_of_normal_right hK hH
#align is_p_group.to_sup_of_normal_left IsPGroup.to_sup_of_normal_left

theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : H ≤ K.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup K.normalizer => IsPGroup p H)
            (Subgroup.sup_subgroupOf_eq hHK Subgroup.le_normalizer)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))
#align is_p_group.to_sup_of_normal_right' IsPGroup.to_sup_of_normal_right'

theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K ≤ H.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK
#align is_p_group.to_sup_of_normal_left' IsPGroup.to_sup_of_normal_left'

/-- finite p-groups with different p have coprime orders -/
theorem coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Fintype H₁]
    [Fintype H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.Coprime (Fintype.card H₁) (Fintype.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne
#align is_p_group.coprime_card_of_ne IsPGroup.coprime_card_of_ne

/-- p-groups with different p are disjoint -/
theorem disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂)
    (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ := by
  rw [Subgroup.disjoint_def]
  intro x hx₁ hx₂
  obtain ⟨n₁, hn₁⟩ := iff_orderOf.mp hH₁ ⟨x, hx₁⟩
  obtain ⟨n₂, hn₂⟩ := iff_orderOf.mp hH₂ ⟨x, hx₂⟩
  rw [Subgroup.orderOf_mk] at hn₁ hn₂
  have : p₁ ^ n₁ = p₂ ^ n₂ := by rw [← hn₁, ← hn₂]
  rcases n₁.eq_zero_or_pos with (rfl | hn₁)
  · simpa using hn₁
  · exact absurd (eq_of_prime_pow_eq hp₁.out.prime hp₂.out.prime hn₁ this) hne
#align is_p_group.disjoint_of_ne IsPGroup.disjoint_of_ne

section P2comm

variable [Fintype G] [Fact p.Prime] {n : ℕ} (hGpn : card G = p ^ n)

open Subgroup

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
theorem card_center_eq_prime_pow (hn : 0 < n) [Fintype (center G)] :
    ∃ k > 0, card (center G) = p ^ k := by
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  haveI : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))
#align is_p_group.card_center_eq_prime_pow IsPGroup.card_center_eq_prime_pow

/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
theorem cyclic_center_quotient_of_card_eq_prime_sq (hG : card G = p ^ 2) :
    IsCyclic (G ⧸ center G) := by
  classical
    rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
    rw [card_eq_card_quotient_mul_card_subgroup (center G), mul_comm, hk] at hG
    have hk2 := (Nat.pow_dvd_pow_iff_le_right (Fact.out (p := p.Prime)).one_lt).1 ⟨_, hG.symm⟩
    interval_cases k
    · rw [sq, pow_one, mul_right_inj' (Fact.out (p := p.Prime)).ne_zero] at hG
      exact isCyclic_of_prime_card hG
    · exact
        @isCyclic_of_subsingleton _ _
          ⟨Fintype.card_le_one_iff.1
              (mul_right_injective₀ (pow_ne_zero 2 (NeZero.ne p))
                  (hG.trans (mul_one (p ^ 2)).symm)).le⟩
#align is_p_group.cyclic_center_quotient_of_card_eq_prime_sq IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
def commGroupOfCardEqPrimeSq (hG : card G = p ^ 2) : CommGroup G :=
  @commGroupOfCycleCenterQuotient _ _ _ _ (cyclic_center_quotient_of_card_eq_prime_sq hG) _
    (QuotientGroup.ker_mk' (center G)).le
#align is_p_group.comm_group_of_card_eq_prime_sq IsPGroup.commGroupOfCardEqPrimeSq

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commGroupOfCardEqPrimeSq`
for the `CommGroup` instance. -/
theorem commutative_of_card_eq_prime_sq (hG : card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  (commGroupOfCardEqPrimeSq hG).mul_comm
#align is_p_group.commutative_of_card_eq_prime_sq IsPGroup.commutative_of_card_eq_prime_sq

end P2comm

end IsPGroup
