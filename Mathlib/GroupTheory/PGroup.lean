/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning, Snir Broshi
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

@[expose] public section

open Fintype MulAction

variable (p : ℕ) (G : Type*) [Group G]

/-- A p-group is a group in which the order of every element is a power of `p`. -/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

variable {p} {G}

namespace IsPGroup

theorem _root_.isPGroup_iff_pow_pow_eq_one : IsPGroup p G ↔ ∀ g : G, ∃ k, g ^ p ^ k = 1 :=
  .rfl

alias ⟨exists_pow_pow_eq_one, _⟩ := isPGroup_iff_pow_pow_eq_one

theorem _root_.isPGroup_iff_orderOf_dvd_pow : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g ∣ p ^ k := by
  simp_rw [isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

alias ⟨exists_orderOf_dvd_pow, _⟩ := isPGroup_iff_orderOf_dvd_pow

theorem iff_orderOf [Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g = p ^ k := by
  simp_rw [isPGroup_iff_orderOf_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact forall_congr' fun g ↦ ⟨by grind, .imp <| by grind⟩

alias ⟨exists_orderOf_eq_pow, _⟩ := iff_orderOf

theorem of_card_dvd_pow {n : ℕ} (hG : Nat.card G ∣ p ^ n) : IsPGroup p G := by
  refine fun g ↦ ⟨n, ?_⟩
  grw [← orderOf_dvd_iff_pow_eq_one, ← hG, orderOf_dvd_natCard]

theorem _root_.isPGroup_iff_card_dvd_pow [Finite G] : IsPGroup p G ↔ ∃ n, Nat.card G ∣ p ^ n := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ of_card_dvd_pow hn⟩
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp⟩
  refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out hp |>.mpr fun q hq ↦ ?_⟩
  have ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
  have ⟨k, hk⟩ := h.exists_orderOf_dvd_pow g
  exact Nat.mem_primeFactors.mpr ⟨hqp, hqp.dvd_of_dvd_pow <| hg ▸ hk, hp⟩

alias ⟨exists_card_dvd_pow, _⟩ := isPGroup_iff_card_dvd_pow

theorem dvd_orderOf [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g ≠ 1) : p ∣ orderOf g := by
  have ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rw [hk]
  refine dvd_pow_self _ fun hk0 ↦ hg ?_
  rw [← orderOf_eq_one_iff, hk, hk0, pow_zero]

theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G :=
  of_card_dvd_pow hG.dvd

variable (p G) in
theorem of_subsingleton [Subsingleton G] : IsPGroup p G :=
  of_card (n := 0) (by simp)

theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  .of_subsingleton p _

variable (G) in
@[simp]
protected theorem zero : IsPGroup 0 G :=
  fun g ↦ ⟨1, by simp⟩

@[simp]
theorem _root_.isPGroup_one_iff_subsingleton : IsPGroup 1 G ↔ Subsingleton G := by
  refine ⟨?_, fun h ↦ .of_subsingleton 1 G⟩
  simpa [isPGroup_iff_pow_pow_eq_one] using subsingleton_of_forall_eq 1

protected theorem card : IsPGroup (Nat.card G) G :=
  fun g ↦ ⟨1, by simp⟩

@[gcongr]
protected theorem mono {q : ℕ} (hpq : p ∣ q) (hp : IsPGroup p G) : IsPGroup q G := by
  rw [isPGroup_iff_orderOf_dvd_pow] at hp ⊢
  exact fun g ↦ (hp g).imp fun k hk ↦ hk.trans <| pow_dvd_pow_of_dvd hpq k

theorem of_pow {n : ℕ} (h : IsPGroup (p ^ n) G) : IsPGroup p G :=
  fun g ↦ (h g).imp' (n * ·) <| by simp [pow_mul]

theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := by
  simp_rw [isPGroup_iff_card_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_card_eq, _⟩ := iff_card

theorem _root_.isPGroup_iff_exists_orderOf_dvd_pow [Finite G] :
    IsPGroup p G ↔ ∃ k, ∀ g : G, orderOf g ∣ p ^ k := by
  refine isPGroup_iff_orderOf_dvd_pow.trans ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ fun g ↦ ⟨k, hk g⟩⟩
  choose k hk using h
  have := Fintype.ofFinite G
  have ⟨g, _, hg⟩ := Finset.exists_max_image .univ k Finset.univ_nonempty
  refine ⟨k g, fun g' ↦ ?_⟩
  grw [← Nat.pow_dvd_pow p <| hg g' <| Finset.mem_univ g']
  exact hk g'

theorem _root_.isPGroup_iff_exists_pow_pow_eq_one [Finite G] :
    IsPGroup p G ↔ ∃ k, ∀ g : G, g ^ p ^ k = 1 := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one]

theorem of_exponent_dvd_pow {n : ℕ} (h : Monoid.exponent G ∣ p ^ n) : IsPGroup p G :=
  fun g ↦ ⟨n, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h g⟩

theorem _root_.isPGroup_iff_exponent_dvd_pow [Finite G] :
    IsPGroup p G ↔ ∃ n, Monoid.exponent G ∣ p ^ n := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, Monoid.exponent_dvd]

alias ⟨exists_exponent_dvd_pow, _⟩ := isPGroup_iff_exponent_dvd_pow

theorem _root_.isPGroup_iff_exponent_eq_pow [Finite G] [Fact p.Prime] :
    IsPGroup p G ↔ ∃ n, Monoid.exponent G = p ^ n := by
  simp_rw [isPGroup_iff_exponent_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_exponent_eq_pow, _⟩ := isPGroup_iff_exponent_eq_pow

theorem _root_.isPGroup_iff_isPGroup_prod_primeFactors (h : p ≠ 0) :
    IsPGroup p G ↔ IsPGroup (p.primeFactors.prod id) G :=
  ⟨(.of_pow <| ·.mono <| p.dvd_prod_primeFactors_pow_self h), .mono p.prod_primeFactors_dvd⟩

theorem _root_.isPGroup_iff_primeFactors_card_subset [Finite G] (h : p ≠ 0) :
    IsPGroup p G ↔ (Nat.card G).primeFactors ⊆ p.primeFactors := by
  refine isPGroup_iff_card_dvd_pow.trans ⟨fun ⟨n, hn⟩ ↦ ?_, fun hG ↦ ?_⟩
  · rcases eq_or_ne n 0 with (rfl | hn0)
    · simp_all
    grw [← Nat.primeFactors_pow p hn0, Nat.primeFactors_mono hn <| pow_ne_zero n h]
  · refine ⟨Nat.card G, Nat.dvd_prod_primeFactors_pow_self NeZero.out |>.trans ?_⟩
    grw [Finset.prod_dvd_prod_of_subset _ _ (·) hG, p.prod_primeFactors_dvd]

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

theorem isOfFinOrder (hp : p ≠ 0) (g : G) : IsOfFinOrder g :=
  hG g |>.elim (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, pow_ne_zero · hp |>.pos, ·⟩)

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
  have := Finite.of_equiv (orbit G a) ϕ
  have := (stabilizer G a).finiteIndex_of_finite_quotient
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
      simp [key, hk, hb]
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
      contrapose hpα
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
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at this
  have dvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩

theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G := by
  have := center_nontrivial hG
  exact
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
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

set_option backward.isDefEq.respectTransparency false in
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
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot hϕ)).mpr IsPGroup.of_bot

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
    (hHK : H ≤ Subgroup.normalizer K) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup (Subgroup.normalizer K) => IsPGroup p H)
            ((Subgroup.subgroupOf_sup hHK Subgroup.le_normalizer).symm)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))

theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K ≤ Subgroup.normalizer H) : IsPGroup p (H ⊔ K : Subgroup G) :=
  sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

/-- finite p-groups with different p have coprime orders -/
theorem coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Finite H₁]
    [Finite H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.Coprime (Nat.card H₁) (Nat.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne

theorem disjoint_of_coprime {p₁ p₂ : ℕ} {H₁ H₂ : Subgroup G} (hH₁ : IsPGroup p₁ H₁)
    (hH₂ : IsPGroup p₂ H₂) (h : p₁.Coprime p₂) : Disjoint H₁ H₂ := by
  refine Subgroup.disjoint_def.mpr fun {g} hg₁ hg₂ ↦ ?_
  have ⟨k₁, hk₁⟩ := hH₁ ⟨g, hg₁⟩
  have hg₁ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₁
  have ⟨k₂, hk₂⟩ := hH₂ ⟨g, hg₂⟩
  have hg₂ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₂
  exact orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes (h.pow k₁ k₂) hg₁ hg₂

/-- p-groups with different p are disjoint -/
theorem disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂)
    (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ :=
  disjoint_of_coprime hH₁ hH₂ <| Nat.coprime_primes hp₁.elim hp₂.elim |>.mpr hne

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
  · exact Subgroup.disjoint_of_coprime_natCard h4

section P2comm

variable [Fact p.Prime] {n : ℕ}

open Subgroup

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
theorem card_center_eq_prime_pow (hGpn : Nat.card G = p ^ n) (hn : 0 < n) :
    ∃ k > 0, Nat.card (center G) = p ^ k := by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  have : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
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

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commGroupOfCardEqPrimeSq`
for the `CommGroup` instance. -/
theorem isMulCommutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsMulCommutative G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  isMulCommutative_of_isCyclic_quotient_center_self G

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
@[instance_reducible]
def commGroupOfCardEqPrimeSq (hG : Nat.card G = p ^ 2) : CommGroup G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  commGroupOfCyclicCenterQuotient _ (QuotientGroup.ker_mk' <| center G).le

@[deprecated isMulCommutative_of_card_eq_prime_sq (since := "2026-05-26")]
theorem commutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  isMulCommutative_of_card_eq_prime_sq hG |>.is_comm.comm

end P2comm

end IsPGroup

namespace ZModModule
variable {n : ℕ} {G : Type*} [AddCommGroup G] [Module (ZMod n) G]

lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ ↦ ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

end ZModModule
