/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic

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

variable {p} {G}

namespace IsPGroup

theorem iff_orderOf [hp : Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k : ℕ, orderOf g = p ^ k :=
  forall_congr' fun g =>
    ⟨fun ⟨_, hk⟩ =>
      Exists.imp (fun _ h => h.right)
        ((Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)),
      Exists.imp fun k hk => by rw [← hk, pow_orderOf_eq_one]⟩

theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G := fun g =>
  ⟨n, by rw [← hG, pow_card_eq_one']⟩

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])

theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := by
  have hG : Nat.card G ≠ 0 := Nat.card_pos.ne'
  refine ⟨fun h => ?_, fun ⟨n, hn⟩ => of_card hn⟩
  suffices ∀ q ∈ (Nat.card G).primeFactorsList, q = p by
    use (Nat.card G).primeFactorsList.length
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem this, Nat.prod_primeFactorsList hG]
  intro q hq
  obtain ⟨hq1, hq2⟩ := (Nat.mem_primeFactorsList hG).mp hq
  haveI : Fact q.Prime := ⟨hq1⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hq2
  obtain ⟨k, hk⟩ := (iff_orderOf.mp h) g
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm

alias ⟨exists_card_eq, _⟩ := iff_card

section GIsPGroup

variable (hG : IsPGroup p G)
include hG

theorem of_injective {H : Type*} [Group H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)

theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective

theorem of_surjective {H : Type*} [Group H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H := by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]

theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective

theorem of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.toMonoidHom ϕ.surjective

theorem orderOf_coprime {n : ℕ} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

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

@[simp]
theorem powEquiv_apply {n : ℕ} (hn : p.Coprime n) (g : G) : hG.powEquiv hn g = g ^ n :=
  rfl

@[simp]
theorem powEquiv_symm_apply {n : ℕ} (hn : p.Coprime n) (g : G) :
    (hG.powEquiv hn).symm g = g ^ (orderOf g).gcdB n := by rw [← Nat.card_zpowers]; rfl

variable [hp : Fact p.Prime]

/-- If `p ∤ n`, then the `n`th power map is a bijection. -/
noncomputable abbrev powEquiv' {n : ℕ} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)

theorem index (H : Subgroup G) [H.FiniteIndex] : ∃ n : ℕ, H.index = p ^ n := by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩

theorem card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G := by
  cases finite_or_infinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [hn]
    rcases n with - | n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩

theorem nontrivial_iff_card [Finite G] : Nontrivial G ↔ ∃ n > 0, Nat.card G = p ^ n :=
  ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0, pow_zero] at hk; exact Finite.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨_, hk0, hk⟩ =>
    Finite.one_lt_card_iff_nontrivial.1 <|
      hk.symm ▸ one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩

variable {α : Type*} [MulAction G α]

theorem card_orbit (a : α) [Finite (orbit G a)] : ∃ n : ℕ, Nat.card (orbit G a) = p ^ n := by
  let ϕ := orbitEquivQuotientStabilizer G a
  haveI := Finite.of_equiv (orbit G a) ϕ
  haveI := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [Nat.card_congr ϕ]
  exact hG.index (stabilizer G a)

variable (α) [Finite α]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
theorem card_modEq_card_fixedPoints : Nat.card α ≡ Nat.card (fixedPoints G α) [MOD p] := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (fixedPoints G α)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  classical
    calc
      card α = card (Σ y : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.natCast_eq_natCast_iff _ _ p, Nat.cast_sum, Nat.cast_sum]
    have key :
      ∀ x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    rw [Nat.card_eq_fintype_card] at hk
    have : k = 0 := by
      contrapose! hb
      simp [-Quotient.eq, key, hk, hb]
    exact
      ⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 <| by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
theorem nonempty_fixed_point_of_prime_not_dvd_card (α) [MulAction G α] (hpα : ¬p ∣ Nat.card α) :
    (fixedPoints G α).Nonempty :=
  have : Finite α := Nat.finite_of_card_ne_zero (fun h ↦ (h ▸ hpα) (dvd_zero p))
  @Set.Nonempty.of_subtype _ _
    (by
      rw [← Finite.card_pos_iff, pos_iff_ne_zero]
      contrapose! hpα
      rw [← Nat.modEq_zero_iff_dvd, ← hpα]
      exact hG.card_modEq_card_fixedPoints α)

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ Nat.card α) {a : α}
    (ha : a ∈ fixedPoints G α) : ∃ b, b ∈ fixedPoints G α ∧ a ≠ b := by
  have hpf : p ∣ Nat.card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < Nat.card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  rw [Finite.one_lt_card_iff_nontrivial] at hα
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, ha⟩ : fixedPoints G α)
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩

theorem center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) := by
  classical
    have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
    rw [ConjAct.fixedPoints_eq_center] at this
    have dvd : p ∣ Nat.card G := by
      obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
      exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
    obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
    exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩

theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G := by
  haveI := center_nontrivial hG
  classical exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Finite.one_lt_card)

end GIsPGroup

theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)

theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hH.to_le inf_le_left

theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hK.to_le inf_le_right

theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G →* K) :
    IsPGroup p (H.map ϕ) := by
  rw [← H.range_subtype, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.restrict H).rangeRestrict (ϕ.restrict H).rangeRestrict_surjective

theorem comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K]
    (ϕ : K →* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) := by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ← pow_mul, ← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩

theorem ker_isPGroup_of_injective {K : Type*} [Group K] {ϕ : K →* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot_iff.mpr hϕ)).mpr IsPGroup.of_bot

theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K →* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)

theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} :
    IsPGroup p (H.comap K.subtype) :=
  hH.comap_of_injective K.subtype Subtype.coe_injective

theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := by
  rw [← QuotientGroup.ker_mk' K, ← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']

theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := sup_comm H K ▸ to_sup_of_normal_right hK hH

theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : H ≤ K.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup K.normalizer => IsPGroup p H)
            (Subgroup.sup_subgroupOf_eq hHK Subgroup.le_normalizer)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))

theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K ≤ H.normalizer) : IsPGroup p (H ⊔ K : Subgroup G) :=
  sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

/-- finite p-groups with different p have coprime orders -/
theorem coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Finite H₁]
    [Finite H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.Coprime (Nat.card H₁) (Nat.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

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

theorem le_or_disjoint_of_coprime [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    {H : Subgroup G} [H.Normal] (h_cop : (Nat.card H).Coprime H.index) :
    P ≤ H ∨ Disjoint H P := by
  by_cases h1 : Nat.card H = 0
  · rw [h1, Nat.coprime_zero_left, Subgroup.index_eq_one] at h_cop
    rw [h_cop]
    exact Or.inl le_top
  by_cases h2 : H.index = 0
  · rw [h2, Nat.coprime_zero_right, Subgroup.card_eq_one] at h_cop
    rw [h_cop]
    exact Or.inr disjoint_bot_left
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← H.card_mul_index]
    exact mul_ne_zero h1 h2
  have h3 : (Nat.card H).Coprime (Nat.card P) ∨ H.index.Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine hk ▸ Or.imp hp.out.coprime_pow_of_not_dvd hp.out.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, h_cop⟩
  refine h3.symm.imp (fun h4 ↦ ?_) (fun h4 ↦ ?_)
  · rw [← Subgroup.relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes h4 (H.relIndex_dvd_index_of_normal P)
      (Subgroup.relIndex_dvd_card H P)
  · exact disjoint_iff.mpr (Subgroup.inf_eq_bot_of_coprime h4)

section P2comm

variable [Fact p.Prime] {n : ℕ}

open Subgroup

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
theorem card_center_eq_prime_pow (hGpn : Nat.card G = p ^ n) (hn : 0 < n) :
    ∃ k > 0, Nat.card (center G) = p ^ k := by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  haveI : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))

/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
theorem cyclic_center_quotient_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) :
    IsCyclic (G ⧸ center G) := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← mul_dvd_mul_iff_left (NeZero.ne p), ← sq, ← hG, ← (center G).card_mul_index]
  apply mul_dvd_mul_right
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
  rw [hk]
  exact dvd_pow_self p hk0.ne'

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
def commGroupOfCardEqPrimeSq (hG : Nat.card G = p ^ 2) : CommGroup G :=
  @commGroupOfCyclicCenterQuotient _ _ _ _ (cyclic_center_quotient_of_card_eq_prime_sq hG) _
    (QuotientGroup.ker_mk' (center G)).le

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commGroupOfCardEqPrimeSq`
for the `CommGroup` instance. -/
theorem commutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  (commGroupOfCardEqPrimeSq hG).mul_comm

end P2comm

end IsPGroup

namespace ZModModule
variable {n : ℕ} {G : Type*} [AddCommGroup G] [Module (ZMod n) G]

lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ ↦ ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

end ZModModule
