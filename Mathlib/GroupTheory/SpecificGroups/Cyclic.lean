/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Exponent

/-!
# Cyclic groups

A group `G` is called cyclic if there exists an element `g : G` such that every element of `G` is of
the form `g ^ n` for some `n : ℕ`. This file only deals with the predicate on a group to be cyclic.
For the concrete cyclic group of order `n`, see `Data.ZMod.Basic`.

## Main definitions

* `IsCyclic` is a predicate on a group stating that the group is cyclic.

## Main statements

* `isCyclic_of_prime_card` proves that a finite group of prime order is cyclic.
* `isSimpleGroup_of_prime_card`, `IsSimpleGroup.isCyclic`,
  and `IsSimpleGroup.prime_card` classify finite simple abelian groups.
* `IsCyclic.exponent_eq_card`: For a finite cyclic group `G`, the exponent is equal to
  the group's cardinality.
* `IsCyclic.exponent_eq_zero_of_infinite`: Infinite cyclic groups have exponent zero.
* `IsCyclic.iff_exponent_eq_card`: A finite commutative group is cyclic iff its exponent
  is equal to its cardinality.

## Tags

cyclic group
-/


universe u

variable {α : Type u} {a : α}

section Cyclic

attribute [local instance] setFintype

open Subgroup

@[to_additive]
theorem IsCyclic.exists_generator [Group α] [IsCyclic α] : ∃ g : α, ∀ x, x ∈ Subgroup.zpowers g :=
  exists_zpow_surjective α

@[to_additive]
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α :=
  ⟨⟨1, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

@[simp]
theorem isCyclic_multiplicative_iff [AddGroup α] : IsCyclic (Multiplicative α) ↔ IsAddCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplicative α) :=
  isCyclic_multiplicative_iff.mpr inferInstance

@[simp]
theorem isAddCyclic_additive_iff [Group α] : IsAddCyclic (Additive α) ↔ IsCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α) :=
  isAddCyclic_additive_iff.mpr inferInstance

/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive
      "A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`."]
def IsCyclic.commGroup [hg : Group α] [IsCyclic α] : CommGroup α :=
  { hg with
    mul_comm := fun x y =>
      let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
      let ⟨_, hn⟩ := hg x
      let ⟨_, hm⟩ := hg y
      hm ▸ hn ▸ zpow_mul_comm _ _ _ }

variable [Group α]

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive "A non-cyclic additive group is non-trivial."]
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact @isCyclic_of_subsingleton _ _ (not_nontrivial_iff_subsingleton.mp nc)

@[to_additive]
theorem MonoidHom.map_cyclic {G : Type*} [Group G] [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [MonoidHom.map_zpow, ← hm, ← zpow_mul, ← zpow_mul']
@[deprecated (since := "2024-02-21")] alias
MonoidAddHom.map_add_cyclic := AddMonoidHom.map_addCyclic

@[to_additive]
theorem isCyclic_of_orderOf_eq_card [Fintype α] (x : α) (hx : orderOf x = Fintype.card α) :
    IsCyclic α := by
  use x
  rw [← Set.range_iff_surjective, ← coe_zpowers]
  rw [← Fintype.card_congr (Equiv.Set.univ α), ← Fintype.card_zpowers] at hx
  #adaptation_note
  /--
  After lean4#5020, many instances for Lie algebras and manifolds are no longer found.
  See https://leanprover.zulipchat.com/#narrow/stream/428973-nightly-testing/topic/.2316244.20adaptations.20for.20nightly-2024-08-28/near/466219124
  -/
  letI : Fintype (zpowers x) := (Subgroup.zpowers x).instFintypeSubtypeMemOfDecidablePred
  exact Set.eq_of_subset_of_card_le (Set.subset_univ _) (ge_of_eq hx)
@[deprecated (since := "2024-02-21")]
alias isAddCyclic_of_orderOf_eq_card := isAddCyclic_of_addOrderOf_eq_card

@[to_additive]
theorem Subgroup.eq_bot_or_eq_top_of_prime_card {G : Type*} [Group G] {_ : Fintype G}
    (H : Subgroup G) [hp : Fact (Fintype.card G).Prime] : H = ⊥ ∨ H = ⊤ := by
  classical
  have := card_subgroup_dvd_card H
  rwa [Nat.card_eq_fintype_card (α := G), Nat.dvd_prime hp.1, ← Nat.card_eq_fintype_card,
    ← eq_bot_iff_card, card_eq_iff_eq_top] at this

/-- Any non-identity element of a finite group of prime order generates the group. -/
@[to_additive "Any non-identity element of a finite group of prime order generates the group."]
theorem zpowers_eq_top_of_prime_card {G : Type*} [Group G] {_ : Fintype G} {p : ℕ}
    [hp : Fact p.Prime] (h : Fintype.card G = p) {g : G} (hg : g ≠ 1) : zpowers g = ⊤ := by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]
theorem mem_zpowers_of_prime_card {G : Type*} [Group G] {_ : Fintype G} {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ zpowers g := by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]
theorem mem_powers_of_prime_card {G : Type*} [Group G] {_ : Fintype G} {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ Submonoid.powers g := by
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]
theorem powers_eq_top_of_prime_card {G : Type*} [Group G] {_ : Fintype G} {p : ℕ}
    [hp : Fact p.Prime] (h : Fintype.card G = p) {g : G} (hg : g ≠ 1) : Submonoid.powers g = ⊤ := by
  ext x
  simp [mem_powers_of_prime_card h hg]

/-- A finite group of prime order is cyclic. -/
@[to_additive "A finite group of prime order is cyclic."]
theorem isCyclic_of_prime_card {α : Type u} [Group α] [Fintype α] {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card α = p) : IsCyclic α := by
  obtain ⟨g, hg⟩ : ∃ g, g ≠ 1 := Fintype.exists_ne_of_one_lt_card (h.symm ▸ hp.1.one_lt) 1
  exact ⟨g, fun g' ↦ mem_zpowers_of_prime_card h hg⟩

/-- A finite group of order dividing a prime is cyclic. -/
@[to_additive "A finite group of order dividing a prime is cyclic."]
theorem isCyclic_of_card_dvd_prime {α : Type u} [Group α] {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α ∣ p) : IsCyclic α := by
  have : Finite α := Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero hp.1.ne_zero h)
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · have : Fintype α := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card] at h
    exact isCyclic_of_prime_card h

@[to_additive]
theorem isCyclic_of_surjective {H G F : Type*} [Group H] [Group G] [hH : IsCyclic H]
    [FunLike F H G] [MonoidHomClass F H G] (f : F) (hf : Function.Surjective f) :
    IsCyclic G := by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]
theorem orderOf_eq_card_of_forall_mem_zpowers [Fintype α] {g : α} (hx : ∀ x, x ∈ zpowers g) :
    orderOf g = Fintype.card α := by
  classical
    rw [← Fintype.card_zpowers]
    apply Fintype.card_of_finset'
    simpa using hx

@[to_additive]
lemma orderOf_generator_eq_natCard (h : ∀ x, x ∈ Subgroup.zpowers a) : orderOf a = Nat.card α :=
  Nat.card_zpowers a ▸ (Nat.card_congr <| Equiv.subtypeUnivEquiv h)

@[to_additive]
theorem exists_pow_ne_one_of_isCyclic {G : Type*} [Group G] [Fintype G] [G_cyclic : IsCyclic G]
    {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) : ∃ a : G, a ^ k ≠ 1 := by
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_eq_fintype_card, ← Nat.card_zpowers, eq_comm, card_eq_iff_eq_top, eq_top_iff]
  exact fun x _ ↦ ha x

@[to_additive]
theorem Infinite.orderOf_eq_zero_of_forall_mem_zpowers [Infinite α] {g : α}
    (h : ∀ x, x ∈ zpowers g) : orderOf g = 0 := by
  classical
    rw [orderOf_eq_zero_iff']
    refine fun n hn hgn => ?_
    have ho := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hgn⟩
    obtain ⟨x, hx⟩ :=
      Infinite.exists_not_mem_finset
        (Finset.image (fun x => g ^ x) <| Finset.range <| orderOf g)
    apply hx
    rw [← ho.mem_powers_iff_mem_range_orderOf, Submonoid.mem_powers_iff]
    obtain ⟨k, hk⟩ := h x
    dsimp at hk
    obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
    · exact ⟨k, mod_cast hk⟩
    rw [← zpow_mod_orderOf] at hk
    have : 0 ≤ (-k % orderOf g : ℤ) := Int.emod_nonneg (-k) (mod_cast ho.orderOf_pos.ne')
    refine ⟨(-k % orderOf g : ℤ).toNat, ?_⟩
    rwa [← zpow_natCast, Int.toNat_of_nonneg this]

@[to_additive]
instance Bot.isCyclic {α : Type u} [Group α] : IsCyclic (⊥ : Subgroup α) :=
  ⟨⟨1, fun x => ⟨0, Subtype.eq <| (zpow_zero (1 : α)).trans <| Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]
instance Subgroup.isCyclic {α : Type u} [Group α] [IsCyclic α] (H : Subgroup α) : IsCyclic H :=
  haveI := Classical.propDecidable
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  if hx : ∃ x : α, x ∈ H ∧ x ≠ (1 : α) then
    let ⟨x, hx₁, hx₂⟩ := hx
    let ⟨k, hk⟩ := hg x
    have hk : g ^ k = x := hk
    have hex : ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H :=
      ⟨k.natAbs,
        Nat.pos_of_ne_zero fun h => hx₂ <| by
          rw [← hk, Int.natAbs_eq_zero.mp h, zpow_zero], by
            cases' k with k k
            · rw [Int.ofNat_eq_coe, Int.natAbs_cast k, ← zpow_natCast, ← Int.ofNat_eq_coe, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ H :=
          (Subgroup.mul_mem_cancel_right H hk₂).1 <| by
            rw [← zpow_add, Int.emod_add_ediv, hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.natCast_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ H := by rwa [← zpow_natCast, ← hk₄]
        have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.natCast_pos.2 (Nat.find_spec hex).1))
              ⟨Nat.pos_of_ne_zero h, hk₅⟩
        ⟨k / (Nat.find hex : ℤ),
          Subtype.ext_iff_val.2
            (by
              suffices g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) = x by simpa [zpow_mul]
              rw [Int.mul_ediv_cancel'
                  (Int.dvd_of_emod_eq_zero (Int.natAbs_eq_zero.mp hk₆)),
                hk])⟩⟩⟩
  else by
    have : H = (⊥ : Subgroup α) :=
      Subgroup.ext fun x =>
        ⟨fun h => by simp at *; tauto, fun h => by rw [Subgroup.mem_bot.1 h]; exact H.one_mem⟩
    subst this; infer_instance

open Finset Nat

section Classical

open scoped Classical

@[to_additive IsAddCyclic.card_nsmul_eq_zero_le]
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    (univ.filter fun a : α => a ^ n = 1).card ≤ n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    (univ.filter fun a : α => a ^ n = 1).card ≤
        (zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset.card :=
      card_le_card fun x hx =>
        let ⟨m, hm⟩ := show x ∈ Submonoid.powers g from mem_powers_iff_mem_zpowers.2 <| hg x
        Set.mem_toFinset.2
          ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : ℕ), by
            dsimp at hm
            have hgmn : g ^ (m * Nat.gcd n (Fintype.card α)) = 1 := by
              rw [pow_mul, hm, ← pow_gcd_card_eq_one_iff]; exact (mem_filter.1 hx).2
            dsimp only
            rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel_left', hm]
            refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
            conv_lhs =>
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ←
                orderOf_eq_card_of_forall_mem_zpowers hg]
            exact orderOf_dvd_of_pow_eq_one hgmn⟩
    _ ≤ n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers, orderOf_pow g, orderOf_eq_card_of_forall_mem_zpowers hg]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0), gcd_mul_left_left, hm,
        Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)
@[deprecated (since := "2024-02-21")]
alias IsAddCyclic.card_pow_eq_one_le := IsAddCyclic.card_nsmul_eq_zero_le

end Classical

@[to_additive]
theorem IsCyclic.exists_monoid_generator [Finite α] [IsCyclic α] :
    ∃ x : α, ∀ y : α, y ∈ Submonoid.powers x := by
  simp_rw [mem_powers_iff_mem_zpowers]
  exact IsCyclic.exists_generator

@[to_additive]
lemma IsCyclic.exists_ofOrder_eq_natCard [h : IsCyclic α] : ∃ g : α, orderOf g = Nat.card α := by
  obtain ⟨g, hg⟩ := h.exists_generator
  use g
  rw [← card_zpowers g, (eq_top_iff' (zpowers g)).mpr hg]
  exact Nat.card_congr (Equiv.Set.univ α)

@[to_additive]
lemma isCyclic_iff_exists_ofOrder_eq_natCard [Finite α] :
    IsCyclic α ↔ ∃ g : α, orderOf g = Nat.card α := by
  refine ⟨fun h ↦ h.exists_ofOrder_eq_natCard, fun h ↦ ?_⟩
  obtain ⟨g, hg⟩ := h
  cases nonempty_fintype α
  refine isCyclic_of_orderOf_eq_card g ?_
  simp [hg]

@[to_additive (attr := deprecated (since := "2024-04-20"))]
protected alias IsCyclic.iff_exists_ofOrder_eq_natCard_of_Fintype :=
  isCyclic_iff_exists_ofOrder_eq_natCard

section

variable [Fintype α]

@[to_additive]
theorem IsCyclic.unique_zpow_zmod (ha : ∀ x : α, x ∈ zpowers a) (x : α) :
    ∃! n : ZMod (Fintype.card α), x = a ^ n.val := by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) ↦ ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

variable [DecidableEq α]

@[to_additive]
theorem IsCyclic.image_range_orderOf (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (orderOf a)) = univ := by
  simp_rw [← SetLike.mem_coe] at ha
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]
theorem IsCyclic.image_range_card (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (Fintype.card α)) = univ := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha, IsCyclic.image_range_orderOf ha]

@[to_additive]
lemma IsCyclic.ext {G : Type*} [Group G] [Fintype G] [IsCyclic G] {d : ℕ} {a b : ZMod d}
    (hGcard : Fintype.card G = d) (h : ∀ t : G, t ^ a.val = t ^ b.val) : a = b := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers hg,
    ← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

end

section Totient

variable [DecidableEq α] [Fintype α]
  (hn : ∀ n : ℕ, 0 < n → (univ.filter fun a : α => a ^ n = 1).card ≤ n)
include hn

@[to_additive]
private theorem card_pow_eq_one_eq_orderOf_aux (a : α) :
    (Finset.univ.filter fun b : α => b ^ orderOf a = 1).card = orderOf a :=
  le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ ≤
          @Fintype.card (↑(univ.filter fun b : α => b ^ orderOf a = 1) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injective (zpowers a)
          (↑(univ.filter fun b : α => b ^ orderOf a = 1) : Set α) (id _) (id _)
          (fun b =>
            ⟨b.1,
              mem_filter.2
                ⟨mem_univ _, by
                  let ⟨i, hi⟩ := b.2
                  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
                    pow_orderOf_eq_one, one_zpow]⟩⟩)
          fun _ _ h => Subtype.eq (Subtype.mk.inj h))
      _ = (univ.filter fun b : α => b ^ orderOf a = 1).card := Fintype.card_ofFinset _ _
      )

-- Use φ for `Nat.totient`
open Nat
@[to_additive]
private theorem card_orderOf_eq_totient_aux₁ :
    ∀ {d : ℕ},
      d ∣ Fintype.card α →
        0 < (univ.filter fun a : α => orderOf a = d).card →
          (univ.filter fun a : α => orderOf a = d).card = φ d := by
  intro d hd hpos
  induction' d using Nat.strongRec' with d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m ∈ d.properDivisors, (univ.filter fun a : α => orderOf a = m).card) =
      ∑ m ∈ d.properDivisors, φ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [mem_filter, mem_range, mem_properDivisors] at hm
    refine IH m hm.2 (hm.1.trans hd) (Finset.card_pos.2 ⟨a ^ (d / m), ?_⟩)
    simp only [mem_filter, mem_univ, orderOf_pow a, ha, true_and_iff,
      Nat.gcd_eq_right (div_dvd_of_dvd hm.1), Nat.div_div_self hm.1 hd0]
  have h2 :
    (∑ m ∈ d.divisors, (univ.filter fun a : α => orderOf a = m).card) =
      ∑ m ∈ d.divisors, φ m := by
    rw [← filter_dvd_eq_divisors hd0, sum_card_orderOf_eq_card_pow_eq_one hd0,
      filter_dvd_eq_divisors hd0, sum_totient, ← ha, card_pow_eq_one_eq_orderOf_aux hn a]
  simpa [← cons_self_properDivisors hd0, ← h1] using h2

@[to_additive]
theorem card_orderOf_eq_totient_aux₂ {d : ℕ} (hd : d ∣ Fintype.card α) :
    (univ.filter fun a : α => orderOf a = d).card = φ d := by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of leanprover/lean4#2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  apply lt_irrefl c
  calc
    c = ∑ m ∈ c.divisors, (univ.filter fun a : α => orderOf a = m).card := by
      simp only [← filter_dvd_eq_divisors hc0.ne', sum_card_orderOf_eq_card_pow_eq_one hc0.ne']
      apply congr_arg card
      simp [c]
    _ = ∑ m ∈ c.divisors.erase d, (univ.filter fun a : α => orderOf a = m).card := by
      rw [eq_comm]
      refine sum_subset (erase_subset _ _) fun m hm₁ hm₂ => ?_
      have : m = d := by
        contrapose! hm₂
        exact mem_erase_of_ne_of_mem hm₂ hm₁
      simp [this, h0]
    _ ≤ ∑ m ∈ c.divisors.erase d, φ m := by
      refine sum_le_sum fun m hm => ?_
      have hmc : m ∣ c := by
        simp only [mem_erase, mem_divisors] at hm
        tauto
      rcases (filter (fun a : α => orderOf a = m) univ).card.eq_zero_or_pos with (h1 | h1)
      · simp [h1]
      · simp [card_orderOf_eq_totient_aux₁ hn hmc h1]
    _ < ∑ m ∈ c.divisors, φ m :=
      sum_erase_lt_of_pos (mem_divisors.2 ⟨hd, hc0.ne'⟩) (totient_pos.2 (pos_of_dvd_of_pos hd hc0))
    _ = c := sum_totient _

@[to_additive isAddCyclic_of_card_nsmul_eq_zero_le]
theorem isCyclic_of_card_pow_eq_one_le : IsCyclic α :=
  have : (univ.filter fun a : α => orderOf a = Fintype.card α).Nonempty :=
    card_pos.1 <| by
      rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl, totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

@[deprecated (since := "2024-02-21")]
alias isAddCyclic_of_card_pow_eq_one_le := isAddCyclic_of_card_nsmul_eq_zero_le

end Totient

@[to_additive]
theorem IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : ℕ}
    (hd : d ∣ Fintype.card α) : (univ.filter fun a : α => orderOf a = d).card = totient d := by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

@[deprecated (since := "2024-02-21")]
alias IsAddCyclic.card_orderOf_eq_totient := IsAddCyclic.card_addOrderOf_eq_totient

/-- A finite group of prime order is simple. -/
@[to_additive "A finite group of prime order is simple."]
theorem isSimpleGroup_of_prime_card {α : Type u} [Group α] [Fintype α] {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card α = p) : IsSimpleGroup α := by
  subst h
  have : Nontrivial α := by
    have h' := Nat.Prime.one_lt hp.out
    exact Fintype.one_lt_card_iff_nontrivial.1 h'
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

end Cyclic

section QuotientCenter

open Subgroup

variable {G : Type*} {H : Type*} [Group G] [Group H]

/-- A group is commutative if the quotient by the center is cyclic.
  Also see `commGroup_of_cycle_center_quotient` for the `CommGroup` instance. -/
@[to_additive
      "A group is commutative if the quotient by the center is cyclic.
      Also see `addCommGroup_of_cycle_center_quotient` for the `AddCommGroup` instance."]
theorem commutative_of_cyclic_center_quotient [IsCyclic H] (f : G →* H) (hf : f.ker ≤ center G)
    (a b : G) : a * b = b * a :=
  let ⟨⟨x, y, (hxy : f y = x)⟩, (hx : ∀ a : f.range, a ∈ zpowers _)⟩ :=
    IsCyclic.exists_generator (α := f.range)
  let ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  let ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ n = f b := by simpa [Subtype.ext_iff] using hn
  have ha : y ^ (-m) * a ∈ center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x m, hm, inv_mul_cancel])
  have hb : y ^ (-n) * b ∈ center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x n, hn, inv_mul_cancel])
  calc
    a * b = y ^ m * (y ^ (-m) * a * y ^ n) * (y ^ (-n) * b) := by simp [mul_assoc]
    _ = y ^ m * (y ^ n * (y ^ (-m) * a)) * (y ^ (-n) * b) := by rw [mem_center_iff.1 ha]
    _ = y ^ m * y ^ n * y ^ (-m) * (a * (y ^ (-n) * b)) := by simp [mul_assoc]
    _ = y ^ m * y ^ n * y ^ (-m) * (y ^ (-n) * b * a) := by rw [mem_center_iff.1 hb]
    _ = b * a := by group

@[deprecated (since := "2024-02-21")]
alias commutative_of_add_cyclic_center_quotient := commutative_of_addCyclic_center_quotient

/-- A group is commutative if the quotient by the center is cyclic. -/
@[to_additive commutativeOfAddCycleCenterQuotient
      "A group is commutative if the quotient by the center is cyclic."]
def commGroupOfCycleCenterQuotient [IsCyclic H] (f : G →* H) (hf : f.ker ≤ center G) :
    CommGroup G :=
  { show Group G by infer_instance with mul_comm := commutative_of_cyclic_center_quotient f hf }

end QuotientCenter

namespace IsSimpleGroup

section CommGroup

variable [CommGroup α] [IsSimpleGroup α]

@[to_additive]
instance (priority := 100) isCyclic : IsCyclic α := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_ne (1 : α)
  have : Subgroup.zpowers g = ⊤ :=
    (eq_bot_or_eq_top (Subgroup.zpowers g)).resolve_left (Subgroup.zpowers_ne_bot.2 hg)
  exact ⟨⟨g, (Subgroup.eq_top_iff' _).1 this⟩⟩

@[to_additive]
theorem prime_card [Fintype α] : (Fintype.card α).Prime := by
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 (by infer_instance)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  rw [Nat.prime_def_lt'']
  refine ⟨Fintype.one_lt_card_iff_nontrivial.2 inferInstance, fun n hn => ?_⟩
  refine (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers (g ^ n))).symm.imp ?_ ?_
  · intro h
    have hgo := orderOf_pow (n := n) g
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.gcd_eq_right_iff_dvd.1 hn,
      orderOf_eq_card_of_forall_mem_zpowers, eq_comm,
      Nat.div_eq_iff_eq_mul_left (Nat.pos_of_dvd_of_pos hn h0) hn] at hgo
    · exact (mul_left_cancel₀ (ne_of_gt h0) ((mul_one (Fintype.card α)).trans hgo)).symm
    · intro x
      rw [h]
      exact Subgroup.mem_top _
  · intro h
    apply le_antisymm (Nat.le_of_dvd h0 hn)
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    apply orderOf_le_of_pow_eq_one (Nat.pos_of_dvd_of_pos hn h0)
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_zpowers _

end CommGroup

end IsSimpleGroup

@[to_additive]
theorem CommGroup.is_simple_iff_isCyclic_and_prime_card [Fintype α] [CommGroup α] :
    IsSimpleGroup α ↔ IsCyclic α ∧ (Fintype.card α).Prime := by
  constructor
  · intro h
    exact ⟨IsSimpleGroup.isCyclic, IsSimpleGroup.prime_card⟩
  · rintro ⟨_, hp⟩
    haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
    exact isSimpleGroup_of_prime_card rfl

section SpecificInstances

instance : IsAddCyclic ℤ := ⟨1, fun n ↦ ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩

instance ZMod.instIsAddCyclic (n : ℕ) : IsAddCyclic (ZMod n) :=
  isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective

instance ZMod.instIsSimpleAddGroup {p : ℕ} [Fact p.Prime] : IsSimpleAddGroup (ZMod p) :=
  AddCommGroup.is_simple_iff_isAddCyclic_and_prime_card.2
    ⟨inferInstance, by simpa using (Fact.out : p.Prime)⟩

end SpecificInstances

section Exponent

open Monoid

@[to_additive]
theorem IsCyclic.exponent_eq_card [Group α] [IsCyclic α] [Fintype α] :
    exponent α = Fintype.card α := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  apply Nat.dvd_antisymm
  · rw [← lcm_orderOf_eq_exponent, Finset.lcm_dvd_iff]
    exact fun b _ => orderOf_dvd_card
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact order_dvd_exponent _

@[to_additive]
theorem IsCyclic.of_exponent_eq_card [CommGroup α] [Fintype α] (h : exponent α = Fintype.card α) :
    IsCyclic α :=
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
  isCyclic_of_orderOf_eq_card g <| hg.trans <| exponent_eq_max'_orderOf.symm.trans h

@[to_additive]
theorem IsCyclic.iff_exponent_eq_card [CommGroup α] [Fintype α] :
    IsCyclic α ↔ exponent α = Fintype.card α :=
  ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]
theorem IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] :
    exponent α = 0 :=
  let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
  exponent_eq_zero_of_order_zero <| Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]
protected theorem ZMod.exponent (n : ℕ) : AddMonoid.exponent (ZMod n) = n := by
  cases n
  · rw [IsAddCyclic.exponent_eq_zero_of_infinite]
  · rw [IsAddCyclic.exponent_eq_card, card]

/-- A group of order `p ^ 2` is not cyclic if and only if its exponent is `p`. -/
@[to_additive]
lemma not_isCyclic_iff_exponent_eq_prime [Group α] {p : ℕ} (hp : p.Prime)
    (hα : Nat.card α = p ^ 2) : ¬ IsCyclic α ↔ Monoid.exponent α = p := by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  let _inst : Fintype α := @Fintype.ofFinite α <| Nat.finite_of_card_ne_zero <| by aesop
  have hα' : Fintype.card α = p ^ 2 := by simpa using hα
  have := (Fintype.one_lt_card_iff_nontrivial (α := α)).mp <|
    hα' ▸ one_lt_pow hp.one_lt two_ne_zero
  /- in the forward direction, we apply `exponent_eq_prime_iff`, and the reverse direction follows
  immediately because if `α` has exponent `p`, it has no element of order `p ^ 2`. -/
  refine ⟨fun h_cyc ↦ (Monoid.exponent_eq_prime_iff hp).mpr fun g hg ↦ ?_, fun h_exp h_cyc ↦ by
    obtain (rfl|rfl) := eq_zero_or_one_of_sq_eq_self <| hα' ▸ h_exp ▸ (h_cyc.exponent_eq_card).symm
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp⟩
  /- we must show every non-identity element has order `p`. By Lagrange's theorem, the only possible
  orders of `g` are `1`, `p`, or `p ^ 2`. It can't be the former because `g ≠ 1`, and it can't
  the latter because the group isn't cyclic. -/
  have := (Nat.mem_divisors (m := p ^ 2)).mpr ⟨hα' ▸ orderOf_dvd_card (x := g), by aesop⟩
  simp? [Nat.divisors_prime_pow hp 2] at this says
    simp only [Nat.divisors_prime_pow hp 2, Nat.reduceAdd, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk] at this
  obtain ⟨a, ha, ha'⟩ := this
  interval_cases a
  · exact False.elim <| hg <| orderOf_eq_one_iff.mp <| by aesop
  · aesop
  · exact False.elim <| h_cyc <| isCyclic_of_orderOf_eq_card g <| by aesop

end Exponent

section ZMod

open Subgroup AddSubgroup

variable {G H : Type*}

/-- The kernel of `zmultiplesHom G g` is equal to the additive subgroup generated by
    `addOrderOf g`. -/
theorem zmultiplesHom_ker_eq [AddGroup G] (g : G) :
    (zmultiplesHom G g).ker = zmultiples ↑(addOrderOf g) := by
  ext
  simp_rw [AddMonoidHom.mem_ker, mem_zmultiples_iff, zmultiplesHom_apply,
    ← addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul', Int.cast_id, dvd_def, eq_comm]

/-- The kernel of `zpowersHom G g` is equal to the subgroup generated by `orderOf g`. -/
theorem zpowersHom_ker_eq [Group G] (g : G) :
    (zpowersHom G g).ker = zpowers (Multiplicative.ofAdd ↑(orderOf g)) :=
  congr_arg AddSubgroup.toSubgroup <| zmultiplesHom_ker_eq (Additive.ofMul g)

/-- The isomorphism from `ZMod n` to any cyclic additive group of `Nat.card` equal to `n`. -/
noncomputable def zmodAddCyclicAddEquiv [AddGroup G] (h : IsAddCyclic G) :
    ZMod (Nat.card G) ≃+ G := by
  let n := Nat.card G
  let ⟨g, surj⟩ := Classical.indefiniteDescription _ h.exists_generator
  have kereq : ((zmultiplesHom G) g).ker = zmultiples ↑(Nat.card G) := by
    rw [zmultiplesHom_ker_eq]
    congr
    rw [← Nat.card_zmultiples]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv surj)
  exact Int.quotientZMultiplesNatEquivZMod n
    |>.symm.trans <| QuotientAddGroup.quotientAddEquivOfEq kereq
    |>.symm.trans <| QuotientAddGroup.quotientKerEquivOfSurjective (zmultiplesHom G g) surj

/-- The isomorphism from `Multiplicative (ZMod n)` to any cyclic group of `Nat.card` equal to `n`.
-/
noncomputable def zmodCyclicMulEquiv [Group G] (h : IsCyclic G) :
    Multiplicative (ZMod (Nat.card G)) ≃* G :=
  AddEquiv.toMultiplicative <| zmodAddCyclicAddEquiv <| isAddCyclic_additive_iff.2 h

/-- Two cyclic additive groups of the same cardinality are isomorphic. -/
noncomputable def addEquivOfAddCyclicCardEq [AddGroup G] [AddGroup H] [hG : IsAddCyclic G]
    [hH : IsAddCyclic H] (hcard : Nat.card G = Nat.card H) : G ≃+ H := hcard ▸
  zmodAddCyclicAddEquiv hG |>.symm.trans (zmodAddCyclicAddEquiv hH)

/-- Two cyclic groups of the same cardinality are isomorphic. -/
@[to_additive existing]
noncomputable def mulEquivOfCyclicCardEq [Group G] [Group H] [hG : IsCyclic G]
    [hH : IsCyclic H] (hcard : Nat.card G = Nat.card H) : G ≃* H := hcard ▸
  zmodCyclicMulEquiv hG |>.symm.trans (zmodCyclicMulEquiv hH)

/-- Two groups of the same prime cardinality are isomorphic. -/
@[to_additive "Two additive groups of the same prime cardinality are isomorphic."]
noncomputable def mulEquivOfPrimeCardEq {p : ℕ} [Fintype G] [Fintype H] [Group G] [Group H]
    [Fact p.Prime] (hG : Fintype.card G = p) (hH : Fintype.card H = p) : G ≃* H := by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  rw [← Nat.card_eq_fintype_card] at hG hH
  exact hG.trans hH.symm

end ZMod

section generator

/-!
### Groups with a given generator

We state some results in terms of an explicitly given generator.
The generating property is given as in `IsCyclic.exists_generator`.

The main statements are about the existence and uniqueness of homomorphisms and isomorphisms
specified by the image of the given generator.
-/

open Subgroup

variable {G G' : Type*} [Group G] [Group G'] {g : G} (hg : ∀ x, x ∈ zpowers g) {g' : G'}

section monoidHom

variable (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a homomorphism `G →* G'` mapping `g` to `g'`. -/
@[to_additive
   "If `g` generates the additive group `G` and `g'` is an element of another additive group `G'`
   whose order divides that of `g`, then there is a homomorphism `G →+ G'` mapping `g` to `g'`."]
noncomputable
def monoidHomOfForallMemZpowers : G →* G' where
  toFun x := g' ^ (Classical.choose <| mem_zpowers_iff.mp <| hg x)
  map_one' := orderOf_dvd_iff_zpow_eq_one.mp <|
                (Int.natCast_dvd_natCast.mpr hg').trans <| orderOf_dvd_iff_zpow_eq_one.mpr <|
                Classical.choose_spec <| mem_zpowers_iff.mp <| hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
    rw [← zpow_eq_zpow_iff_modEq, zpow_add]
    simp only [fun x ↦ Classical.choose_spec <| mem_zpowers_iff.mp <| hg x]

@[to_additive (attr := simp)]
lemma monoidHomOfForallMemZpowers_apply_gen :
    monoidHomOfForallMemZpowers hg hg' g = g' := by
  simp only [monoidHomOfForallMemZpowers, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq, zpow_one]
  exact Classical.choose_spec <| mem_zpowers_iff.mp <| hg g

end monoidHom

include hg

/-- Two group homomorphisms `G →* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
   "Two homomorphisms `G →+ G'` of additive groups are equal if and only if they agree
   on a generator of `G`."]
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp <| hg x
  rw [← hn, map_zpow, map_zpow, H]

/-- Two group isomorphisms `G ≃* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
   "Two isomorphisms `G ≃+ G'` of additive groups are equal if and only if they agree
   on a generator of `G`."]
lemma MulEquiv.eq_iff_eq_on_generator (f₁ f₂ : G ≃* G') : f₁ = f₂ ↔ f₁ g = f₂ g :=
  (Function.Injective.eq_iff toMonoidHom_injective).symm.trans <|
    MonoidHom.eq_iff_eq_on_generator hg ..

section mulEquiv

variable (hg' : ∀ x, x ∈ zpowers g') (h : orderOf g = orderOf g')

/-- Given two groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/
@[to_additive
   "Given two additive groups that are generated by elements `g` and `g'` of the same order,
   we obtain an isomorphism sending `g` to `g'`."]
noncomputable
def mulEquivOfOrderOfEq : G ≃* G' := by
  refine MonoidHom.toMulEquiv (monoidHomOfForallMemZpowers hg h.symm.dvd)
    (monoidHomOfForallMemZpowers hg' h.dvd) ?_ ?_ <;>
  refine (MonoidHom.eq_iff_eq_on_generator (by assumption) _ _).mpr ?_ <;>
  simp only [MonoidHom.coe_comp, Function.comp_apply, monoidHomOfForallMemZpowers_apply_gen,
    MonoidHom.id_apply]

@[to_additive (attr := simp)]
lemma mulEquivOfOrderOfEq_apply_gen : mulEquivOfOrderOfEq hg hg' h g = g' :=
  monoidHomOfForallMemZpowers_apply_gen hg h.symm.dvd

@[to_additive (attr := simp)]
lemma mulEquivOfOrderOfEq_symm :
    (mulEquivOfOrderOfEq hg hg' h).symm = mulEquivOfOrderOfEq hg' hg h.symm := rfl

@[to_additive] -- `simp` can prove this by a combination of the two preceding lemmas
lemma mulEquivOfOrderOfEq_symm_apply_gen : (mulEquivOfOrderOfEq hg hg' h).symm g' = g :=
  monoidHomOfForallMemZpowers_apply_gen hg' h.dvd

end mulEquiv

end generator
