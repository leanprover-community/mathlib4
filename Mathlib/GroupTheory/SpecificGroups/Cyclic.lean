/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Aut
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group

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

assert_not_exists Ideal TwoSidedIdeal

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

@[to_additive]
theorem IsCyclic.exists_generator [Group α] [IsCyclic α] : ∃ g : α, ∀ x, x ∈ zpowers g :=
  exists_zpow_surjective α

@[to_additive]
theorem isCyclic_iff_exists_zpowers_eq_top [Group α] : IsCyclic α ↔ ∃ g : α, zpowers g = ⊤ := by
  simp only [eq_top_iff', mem_zpowers_iff]
  exact ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

@[to_additive]
protected theorem Subgroup.isCyclic_iff_exists_zpowers_eq_top [Group α] (H : Subgroup α) :
    IsCyclic H ↔ ∃ g : α, Subgroup.zpowers g = H := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  simp_rw [← (map_injective H.subtype_injective).eq_iff, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g ↦ and_iff_right_of_imp fun h ↦ h ▸ mem_zpowers g

@[to_additive]
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α :=
  ⟨⟨1, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩⟩

@[simp]
theorem isCyclic_multiplicative_iff [SubNegMonoid α] :
    IsCyclic (Multiplicative α) ↔ IsAddCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isCyclic_multiplicative [AddGroup α] [IsAddCyclic α] : IsCyclic (Multiplicative α) :=
  isCyclic_multiplicative_iff.mpr inferInstance

@[simp]
theorem isAddCyclic_additive_iff [DivInvMonoid α] : IsAddCyclic (Additive α) ↔ IsCyclic α :=
  ⟨fun H ↦ ⟨H.1⟩, fun H ↦ ⟨H.1⟩⟩

instance isAddCyclic_additive [Group α] [IsCyclic α] : IsAddCyclic (Additive α) :=
  isAddCyclic_additive_iff.mpr inferInstance

@[to_additive]
instance IsCyclic.commutative [Group α] [IsCyclic α] :
    Std.Commutative (· * · : α → α → α) where
  comm x y :=
    let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm _ _ _

/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive
      /-- A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`. -/]
def IsCyclic.commGroup [hg : Group α] [IsCyclic α] : CommGroup α :=
  { hg with mul_comm := commutative.comm }

instance [Group G] (H : Subgroup G) [IsCyclic H] : IsMulCommutative H :=
  ⟨IsCyclic.commutative⟩

variable [Group α] [Group G] [Group G']

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive /-- A non-cyclic additive group is non-trivial. -/]
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact @isCyclic_of_subsingleton _ _ (not_nontrivial_iff_subsingleton.mp nc)

@[to_additive]
theorem MonoidHom.map_cyclic [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [MonoidHom.map_zpow, ← hm, ← zpow_mul, ← zpow_mul']

@[to_additive]
lemma isCyclic_iff_exists_orderOf_eq_natCard [Finite α] :
    IsCyclic α ↔ ∃ g : α, orderOf g = Nat.card α := by
  simp_rw [isCyclic_iff_exists_zpowers_eq_top, ← card_eq_iff_eq_top, Nat.card_zpowers]

@[to_additive]
lemma isCyclic_iff_exists_natCard_le_orderOf [Finite α] :
    IsCyclic α ↔ ∃ g : α, Nat.card α ≤ orderOf g := by
  rw [isCyclic_iff_exists_orderOf_eq_natCard]
  apply exists_congr
  intro g
  exact ⟨Eq.ge, le_antisymm orderOf_le_card⟩

@[to_additive]
theorem isCyclic_of_orderOf_eq_card [Finite α] (x : α) (hx : orderOf x = Nat.card α) :
    IsCyclic α :=
  isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hx⟩

@[to_additive]
theorem isCyclic_of_card_le_orderOf [Finite α] (x : α) (hx : Nat.card α ≤ orderOf x) :
    IsCyclic α :=
  isCyclic_iff_exists_natCard_le_orderOf.mpr ⟨x, hx⟩

@[to_additive]
theorem Subgroup.eq_bot_or_eq_top_of_prime_card
    (H : Subgroup G) [hp : Fact (Nat.card G).Prime] : H = ⊥ ∨ H = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have := card_subgroup_dvd_card H
  rwa [Nat.dvd_prime hp.1, ← eq_bot_iff_card, card_eq_iff_eq_top] at this

/-- Any non-identity element of a finite group of prime order generates the group. -/
@[to_additive /-- Any non-identity element of a finite group of prime order generates the group. -/]
theorem zpowers_eq_top_of_prime_card {p : ℕ}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g ≠ 1) : zpowers g = ⊤ := by
  subst h
  have := (zpowers g).eq_bot_or_eq_top_of_prime_card
  rwa [zpowers_eq_bot, or_iff_right hg] at this

@[to_additive]
theorem mem_zpowers_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ zpowers g := by
  simp_rw [zpowers_eq_top_of_prime_card h hg, Subgroup.mem_top]

@[to_additive]
theorem mem_powers_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card G = p) {g g' : G} (hg : g ≠ 1) : g' ∈ Submonoid.powers g := by
  have : Finite G := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  rw [mem_powers_iff_mem_zpowers]
  exact mem_zpowers_of_prime_card h hg

@[to_additive]
theorem powers_eq_top_of_prime_card {p : ℕ}
    [hp : Fact p.Prime] (h : Nat.card G = p) {g : G} (hg : g ≠ 1) : Submonoid.powers g = ⊤ := by
  ext x
  simp [mem_powers_of_prime_card h hg]

/-- A finite group of prime order is cyclic. -/
@[to_additive /-- A finite group of prime order is cyclic. -/]
theorem isCyclic_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsCyclic α := by
  have : Finite α := Nat.finite_of_card_ne_zero (h ▸ hp.1.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (h ▸ hp.1.one_lt)
  obtain ⟨g, hg⟩ : ∃ g : α, g ≠ 1 := exists_ne 1
  exact ⟨g, fun g' ↦ mem_zpowers_of_prime_card h hg⟩

/-- A finite group of order dividing a prime is cyclic. -/
@[to_additive /-- A finite group of order dividing a prime is cyclic. -/]
theorem isCyclic_of_card_dvd_prime {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α ∣ p) : IsCyclic α := by
  rcases (Nat.dvd_prime hp.out).mp h with h | h
  · exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h).1
  · exact isCyclic_of_prime_card h

@[to_additive]
theorem isCyclic_of_surjective {F : Type*} [hH : IsCyclic G']
    [FunLike F G' G] [MonoidHomClass F G' G] (f : F) (hf : Function.Surjective f) :
    IsCyclic G := by
  obtain ⟨x, hx⟩ := hH
  refine ⟨f x, fun a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨n, rfl⟩ := hx a
  exact ⟨n, (map_zpow _ _ _).symm⟩

@[to_additive]
theorem MulEquiv.isCyclic (e : G ≃* G') :
    IsCyclic G ↔ IsCyclic G' :=
  ⟨fun _ ↦ isCyclic_of_surjective e e.surjective,
    fun _ ↦ isCyclic_of_surjective e.symm e.symm.surjective⟩

@[to_additive]
theorem orderOf_eq_card_of_forall_mem_zpowers {g : α} (hx : ∀ x, x ∈ zpowers g) :
    orderOf g = Nat.card α := by
  rw [← Nat.card_zpowers, (zpowers g).eq_top_iff'.mpr hx, card_top]

@[to_additive]
theorem orderOf_eq_card_of_zpowers_eq_top {g : G} (h : Subgroup.zpowers g = ⊤) :
    orderOf g = Nat.card G :=
  orderOf_eq_card_of_forall_mem_zpowers fun _ ↦ h.ge (Subgroup.mem_top _)

@[to_additive]
theorem exists_pow_ne_one_of_isCyclic [G_cyclic : IsCyclic G]
    {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Nat.card G) : ∃ a : G, a ^ k ≠ 1 := by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt k_lt_card_G)
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [← Nat.card_zpowers, eq_comm, card_eq_iff_eq_top, eq_top_iff]
  exact fun x _ ↦ ha x

@[to_additive]
theorem Infinite.orderOf_eq_zero_of_forall_mem_zpowers [Infinite α] {g : α}
    (h : ∀ x, x ∈ zpowers g) : orderOf g = 0 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers h, Nat.card_eq_zero_of_infinite]

@[to_additive]
instance Bot.isCyclic : IsCyclic (⊥ : Subgroup α) :=
  ⟨⟨1, fun x => ⟨0, Subtype.eq <| (zpow_zero (1 : α)).trans <| Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

@[to_additive]
instance Subgroup.isCyclic [IsCyclic α] (H : Subgroup α) : IsCyclic H :=
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
            rcases k with k | k
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

@[to_additive]
theorem isCyclic_of_injective [IsCyclic G'] (f : G →* G') (hf : Function.Injective f) :
    IsCyclic G :=
  isCyclic_of_surjective (MonoidHom.ofInjective hf).symm (MonoidHom.ofInjective hf).symm.surjective

@[to_additive]
lemma Subgroup.isCyclic_of_le {H H' : Subgroup G} (h : H ≤ H') [IsCyclic H'] : IsCyclic H :=
  isCyclic_of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

open Finset Nat

section Classical

open scoped Classical in
@[to_additive IsAddCyclic.card_nsmul_eq_zero_le]
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} ≤
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset :=
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
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ← Nat.card_eq_fintype_card,
                ← orderOf_eq_card_of_forall_mem_zpowers hg]
            exact orderOf_dvd_of_pow_eq_one hgmn⟩
    _ ≤ n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [Fintype.card_zpowers, orderOf_pow g, orderOf_eq_card_of_forall_mem_zpowers hg,
        Nat.card_eq_fintype_card]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0), gcd_mul_left_left, hm,
        Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)

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

variable (G) in
/-- A distributive action of a monoid on a finite cyclic group of order `n` factors through an
action on `ZMod n`. -/
noncomputable def MulDistribMulAction.toMonoidHomZModOfIsCyclic (M : Type*) [Monoid M]
    [IsCyclic G] [MulDistribMulAction M G] {n : ℕ} (hn : Nat.card G = n) : M →* ZMod n where
  toFun m := (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose
  map_one' := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff, ← hn, ← hg, ← zpow_eq_zpow_iff_modEq,
      zpow_one, ← (MulDistribMulAction.toMonoidHom G 1).map_cyclic.choose_spec,
      MulDistribMulAction.toMonoidHom_apply, one_smul]
  map_mul' m n := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff, ← hn, ← hg, ← zpow_eq_zpow_iff_modEq,
      zpow_mul', ← (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec,
      ← (MulDistribMulAction.toMonoidHom G n).map_cyclic.choose_spec,
      ← (MulDistribMulAction.toMonoidHom G (m * n)).map_cyclic.choose_spec,
      MulDistribMulAction.toMonoidHom_apply, MulDistribMulAction.toMonoidHom_apply,
      MulDistribMulAction.toMonoidHom_apply, mul_smul]

theorem MulDistribMulAction.toMonoidHomZModOfIsCyclic_apply {M : Type*} [Monoid M] [IsCyclic G]
    [MulDistribMulAction M G] {n : ℕ} (hn : Nat.card G = n) (m : M) (g : G) (k : ℤ)
    (h : toMonoidHomZModOfIsCyclic G M hn m = k) : m • g = g ^ k := by
  rw [← MulDistribMulAction.toMonoidHom_apply,
    (MulDistribMulAction.toMonoidHom G m).map_cyclic.choose_spec g, zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (orderOf_dvd_natCard g))
  rwa [hn, ← ZMod.intCast_eq_intCast_iff]

section

variable [Fintype α]

@[to_additive]
theorem IsCyclic.unique_zpow_zmod (ha : ∀ x : α, x ∈ zpowers a) (x : α) :
    ∃! n : ZMod (Fintype.card α), x = a ^ n.val := by
  obtain ⟨n, rfl⟩ := ha x
  refine ⟨n, (?_ : a ^ n = _), fun y (hy : a ^ n = _) ↦ ?_⟩
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Int.modEq_comm, Int.modEq_iff_add_fac, Nat.card_eq_fintype_card, ← ZMod.intCast_eq_iff]
  · rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers ha,
      Nat.card_eq_fintype_card, ← ZMod.intCast_eq_intCast_iff] at hy
    simp [hy]

variable [DecidableEq α]

@[to_additive]
theorem IsCyclic.image_range_orderOf (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (orderOf a)) = univ := by
  simp_rw [← SetLike.mem_coe] at ha
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr ha, Set.toFinset_univ]

@[to_additive]
theorem IsCyclic.image_range_card (ha : ∀ x : α, x ∈ zpowers a) :
    Finset.image (fun i => a ^ i) (range (Nat.card α)) = univ := by
  rw [← orderOf_eq_card_of_forall_mem_zpowers ha, IsCyclic.image_range_orderOf ha]

@[to_additive]
lemma IsCyclic.ext [Finite G] [IsCyclic G] {d : ℕ} {a b : ZMod d}
    (hGcard : Nat.card G = d) (h : ∀ t : G, t ^ a.val = t ^ b.val) : a = b := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  specialize h g
  subst hGcard
  rw [pow_eq_pow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers hg,
    ← ZMod.natCast_eq_natCast_iff] at h
  simpa [ZMod.natCast_val, ZMod.cast_id'] using h

end

section Totient

variable [DecidableEq α] [Fintype α] (hn : ∀ n : ℕ, 0 < n → #{a : α | a ^ n = 1} ≤ n)
include hn

@[to_additive]
private theorem card_pow_eq_one_eq_orderOf_aux (a : α) : #{b : α | b ^ orderOf a = 1} = orderOf a :=
  le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ ≤
          @Fintype.card (({b : α | b ^ orderOf a = 1} : Finset _) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injective (zpowers a)
          (({b : α | b ^ orderOf a = 1} : Finset _) : Set α) (id _) (id _)
          (fun b =>
            ⟨b.1,
              mem_filter.2
                ⟨mem_univ _, by
                  let ⟨i, hi⟩ := b.2
                  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
                    pow_orderOf_eq_one, one_zpow]⟩⟩)
          fun _ _ h => Subtype.eq (Subtype.mk.inj h))
      _ = #{b : α | b ^ orderOf a = 1} := Fintype.card_ofFinset _ _
      )

-- Use φ for `Nat.totient`
open Nat
@[to_additive]
private theorem card_orderOf_eq_totient_aux₁ {d : ℕ} (hd : d ∣ Fintype.card α)
    (hpos : 0 < #{a : α | orderOf a = d}) : #{a : α | orderOf a = d} = φ d := by
  induction d using Nat.strongRec' with | _ d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases Finset.card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m ∈ d.properDivisors, #{a : α | orderOf a = m}) =
      ∑ m ∈ d.properDivisors, φ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [mem_properDivisors] at hm
    refine IH m hm.2 (hm.1.trans hd) (Finset.card_pos.2 ⟨a ^ (d / m), ?_⟩)
    rw [mem_filter_univ, orderOf_pow a, ha, Nat.gcd_eq_right (div_dvd_of_dvd hm.1),
      Nat.div_div_self hm.1 hd0]
  have h2 :
    (∑ m ∈ d.divisors, #{a : α | orderOf a = m}) =
      ∑ m ∈ d.divisors, φ m := by
    rw [sum_card_orderOf_eq_card_pow_eq_one hd0, sum_totient,
      ← ha, card_pow_eq_one_eq_orderOf_aux hn a]
  simpa [← cons_self_properDivisors hd0, ← h1] using h2

@[to_additive]
theorem card_orderOf_eq_totient_aux₂ {d : ℕ} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = φ d := by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of https://github.com/leanprover/lean4/issues/2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  apply lt_irrefl c
  calc
    c = ∑ m ∈ c.divisors, #{a : α | orderOf a = m} := by
      simp only [sum_card_orderOf_eq_card_pow_eq_one hc0.ne']
      apply congr_arg card
      simp [c]
    _ = ∑ m ∈ c.divisors.erase d, #{a : α | orderOf a = m} := by
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
      obtain h1 | h1 := (#{a : α | orderOf a = m}).eq_zero_or_pos
      · simp [h1]
      · simp [card_orderOf_eq_totient_aux₁ hn hmc h1]
    _ < ∑ m ∈ c.divisors, φ m :=
      sum_erase_lt_of_pos (mem_divisors.2 ⟨hd, hc0.ne'⟩) (totient_pos.2 (pos_of_dvd_of_pos hd hc0))
    _ = c := sum_totient _

@[to_additive isAddCyclic_of_card_nsmul_eq_zero_le, stacks 09HX "This theorem is stronger than \
09HX. It removes the abelian condition, and requires only `≤` instead of `=`."]
theorem isCyclic_of_card_pow_eq_one_le : IsCyclic α :=
  have : Finset.Nonempty {a : α | orderOf a = Nat.card α} :=
    card_pos.1 <| by
      rw [Nat.card_eq_fintype_card, card_orderOf_eq_totient_aux₂ hn dvd_rfl, totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

end Totient

@[to_additive]
lemma IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : ℕ} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = totient d := by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

/-- A finite group of prime order is simple. -/
@[to_additive /-- A finite group of prime order is simple. -/]
theorem isSimpleGroup_of_prime_card {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsSimpleGroup α := by
  subst h
  have : Finite α := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hp.1.one_lt
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

end Cyclic

section QuotientCenter

open Subgroup

variable [Group G] [Group G']

/-- A group is commutative if the quotient by the center is cyclic.
  Also see `commGroupOfCyclicCenterQuotient` for the `CommGroup` instance. -/
@[to_additive
      /-- A group is commutative if the quotient by the center is cyclic.
      Also see `addCommGroupOfCyclicCenterQuotient` for the `AddCommGroup` instance. -/]
theorem commutative_of_cyclic_center_quotient [IsCyclic G'] (f : G →* G') (hf : f.ker ≤ center G)
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

/-- A group is commutative if the quotient by the center is cyclic. -/
@[to_additive
      /-- A group is commutative if the quotient by the center is cyclic. -/]
def commGroupOfCyclicCenterQuotient [IsCyclic G'] (f : G →* G') (hf : f.ker ≤ center G) :
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
theorem prime_card [Finite α] : (Nat.card α).Prime := by
  have h0 : 0 < Nat.card α := Nat.card_pos
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  rw [Nat.prime_def]
  refine ⟨Finite.one_lt_card_iff_nontrivial.2 inferInstance, fun n hn => ?_⟩
  refine (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers (g ^ n))).symm.imp ?_ ?_
  · intro h
    have hgo := orderOf_pow (n := n) g
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.gcd_eq_right_iff_dvd.2 hn,
      orderOf_eq_card_of_forall_mem_zpowers, eq_comm,
      Nat.div_eq_iff_eq_mul_left (Nat.pos_of_dvd_of_pos hn h0) hn] at hgo
    · exact (mul_left_cancel₀ (ne_of_gt h0) ((mul_one (Nat.card α)).trans hgo)).symm
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
theorem CommGroup.is_simple_iff_isCyclic_and_prime_card [Finite α] [CommGroup α] :
    IsSimpleGroup α ↔ IsCyclic α ∧ (Nat.card α).Prime := by
  constructor
  · intro h
    exact ⟨IsSimpleGroup.isCyclic, IsSimpleGroup.prime_card⟩
  · rintro ⟨_, hp⟩
    haveI : Fact (Nat.card α).Prime := ⟨hp⟩
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
theorem IsCyclic.exponent_eq_card [Group α] [IsCyclic α] :
    exponent α = Nat.card α := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← hg]
  exact order_dvd_exponent _

@[to_additive]
theorem IsCyclic.of_exponent_eq_card [CommGroup α] [Finite α] (h : exponent α = Nat.card α) :
    IsCyclic α :=
  let ⟨_⟩ := nonempty_fintype α
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
  isCyclic_of_orderOf_eq_card g <| hg.trans <| exponent_eq_max'_orderOf.symm.trans h

@[to_additive]
theorem IsCyclic.iff_exponent_eq_card [CommGroup α] [Finite α] :
    IsCyclic α ↔ exponent α = Nat.card α :=
  ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]
theorem IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] :
    exponent α = 0 :=
  let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
  exponent_eq_zero_of_order_zero <| Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]
protected theorem ZMod.exponent (n : ℕ) : AddMonoid.exponent (ZMod n) = n := by
  rw [IsAddCyclic.exponent_eq_card, Nat.card_zmod]

/-- A group of order `p ^ 2` is not cyclic if and only if its exponent is `p`. -/
@[to_additive]
lemma not_isCyclic_iff_exponent_eq_prime [Group α] {p : ℕ} (hp : p.Prime)
    (hα : Nat.card α = p ^ 2) : ¬ IsCyclic α ↔ Monoid.exponent α = p := by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  have : Finite α := Nat.finite_of_card_ne_zero (hα ▸ pow_ne_zero 2 hp.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp
    (hα ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  /- in the forward direction, we apply `exponent_eq_prime_iff`, and the reverse direction follows
  immediately because if `α` has exponent `p`, it has no element of order `p ^ 2`. -/
  refine ⟨fun h_cyc ↦ (Monoid.exponent_eq_prime_iff hp).mpr fun g hg ↦ ?_, fun h_exp h_cyc ↦ by
    obtain (rfl | rfl) := eq_zero_or_one_of_sq_eq_self <| hα ▸ h_exp ▸ (h_cyc.exponent_eq_card).symm
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp⟩
  /- we must show every non-identity element has order `p`. By Lagrange's theorem, the only possible
  orders of `g` are `1`, `p`, or `p ^ 2`. It can't be the former because `g ≠ 1`, and it can't
  the latter because the group isn't cyclic. -/
  have := (Nat.mem_divisors (m := p ^ 2)).mpr ⟨hα ▸ orderOf_dvd_natCard (x := g), by aesop⟩
  simp? [Nat.divisors_prime_pow hp 2] at this says
    simp only [Nat.divisors_prime_pow hp 2, Nat.reduceAdd, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk] at this
  obtain ⟨a, ha, ha'⟩ := this
  interval_cases a
  · exact False.elim <| hg <| orderOf_eq_one_iff.mp <| by aesop
  · aesop
  · exact False.elim <| h_cyc <| isCyclic_of_orderOf_eq_card g <| by omega

end Exponent

section ZMod

open Subgroup AddSubgroup

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
noncomputable def addEquivOfAddCyclicCardEq [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G]
    [hH : IsAddCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃+ G' := hcard ▸
  zmodAddCyclicAddEquiv hG |>.symm.trans (zmodAddCyclicAddEquiv hH)

/-- Two cyclic groups of the same cardinality are isomorphic. -/
@[to_additive existing]
noncomputable def mulEquivOfCyclicCardEq [Group G] [Group G'] [hG : IsCyclic G]
    [hH : IsCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃* G' := hcard ▸
  zmodCyclicMulEquiv hG |>.symm.trans (zmodCyclicMulEquiv hH)

/-- Two groups of the same prime cardinality are isomorphic. -/
@[to_additive /-- Two additive groups of the same prime cardinality are isomorphic. -/]
noncomputable def mulEquivOfPrimeCardEq {p : ℕ} [Group G] [Group G']
    [Fact p.Prime] (hG : Nat.card G = p) (hH : Nat.card G' = p) : G ≃* G' := by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  exact hG.trans hH.symm

variable (G) in
/-- The automorphism group of a cyclic group is isomorphic to the multiplicative group of ZMod. -/
@[simps!]
noncomputable def IsCyclic.mulAutMulEquiv [Group G] [h : IsCyclic G] :
    MulAut G ≃* (ZMod (Nat.card G))ˣ :=
  ((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans (ZMod.AddAutEquivUnits (Nat.card G))

variable (G) in
theorem IsCyclic.card_mulAut [Group G] [Finite G] [h : IsCyclic G] :
    Nat.card (MulAut G) = Nat.totient (Nat.card G) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulAutMulEquiv G)

end ZMod

section powMonoidHom

variable (G)

-- Note. Even though cyclic groups only require `[Group G]`, we need `[CommGroup G]` for
-- `powMonoidHom` to be defined.

@[to_additive]
theorem IsCyclic.card_powMonoidHom_range [CommGroup G] [hG : IsCyclic G] [Finite G] (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).range = Nat.card G / (Nat.card G).gcd d := by
  obtain ⟨g, h⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  rw [MonoidHom.range_eq_map, ← h, MonoidHom.map_zpowers, Nat.card_zpowers, powMonoidHom_apply,
    orderOf_pow, orderOf_eq_card_of_zpowers_eq_top h]

@[to_additive]
theorem IsCyclic.index_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    (powMonoidHom d : G →* G).ker.index = Nat.card G / (Nat.card G).gcd d := by
  rw [Subgroup.index_ker, card_powMonoidHom_range]

@[to_additive]
theorem IsCyclic.card_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    Nat.card (powMonoidHom d : G →* G).ker = (Nat.card G).gcd d := by
  have h : (powMonoidHom d : G →* G).ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← mul_left_inj' h, Subgroup.card_mul_index, index_powMonoidHom_ker, Nat.mul_div_cancel']
  exact Nat.gcd_dvd_left (Nat.card G) d

@[to_additive]
theorem IsCyclic.index_powMonoidHom_range [CommGroup G] [IsCyclic G] [Finite G] (d : ℕ) :
    (powMonoidHom d : G →* G).range.index = (Nat.card G).gcd d := by
  rw [Subgroup.index_range, card_powMonoidHom_ker]

end powMonoidHom

section generator

/-!
### Groups with a given generator

We state some results in terms of an explicitly given generator.
The generating property is given as in `IsCyclic.exists_generator`.

The main statements are about the existence and uniqueness of homomorphisms and isomorphisms
specified by the image of the given generator.
-/

open Subgroup

variable [Group G] [Group G'] {g : G} (hg : ∀ x, x ∈ zpowers g) {g' : G'}

section monoidHom

variable (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a homomorphism `G →* G'` mapping `g` to `g'`. -/
@[to_additive
/-- If `g` generates the additive group `G` and `g'` is an element of another additive group `G'`
whose order divides that of `g`, then there is a homomorphism `G →+ G'` mapping `g` to `g'`. -/]
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
/-- Two homomorphisms `G →+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp <| hg x
  rw [← hn, map_zpow, map_zpow, H]

/-- Two group isomorphisms `G ≃* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two isomorphisms `G ≃+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
lemma MulEquiv.eq_iff_eq_on_generator (f₁ f₂ : G ≃* G') : f₁ = f₂ ↔ f₁ g = f₂ g :=
  (Function.Injective.eq_iff toMonoidHom_injective).symm.trans <|
    MonoidHom.eq_iff_eq_on_generator hg ..

section mulEquiv

variable (hg' : ∀ x, x ∈ zpowers g') (h : orderOf g = orderOf g')

/-- Given two groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/
@[to_additive
/-- Given two additive groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/]
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

section prod

@[to_additive] theorem Group.isCyclic_of_coprime_card_range_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M →* N) (h : (Nat.card f.ker).Coprime (Nat.card f.range))
    [IsCyclic f.ker] [IsCyclic f.range] : IsCyclic M := by
  cases (finite_or_infinite f.ker).symm
  · rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
    rw [← f.range.eq_bot_iff_card, f.range_eq_bot_iff, ← f.ker_eq_top_iff] at h
    rwa [← Subgroup.topEquiv.isCyclic, ← h]
  cases (finite_or_infinite f.range).symm
  · rw [Nat.card_eq_zero_of_infinite (α := f.range), Nat.coprime_zero_right] at h
    rwa [(f.ofInjective (f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq h))).isCyclic]
  have := f.finite_iff_finite_ker_range.mpr ⟨‹_›, ‹_›⟩
  rw [IsCyclic.iff_exponent_eq_card]
  apply dvd_antisymm Group.exponent_dvd_nat_card
  rw [← f.ker.card_mul_index, Subgroup.index_ker]
  apply h.mul_dvd_of_dvd_of_dvd <;> rw [← IsCyclic.exponent_eq_card]
  · exact Monoid.exponent_dvd_of_monoidHom _ f.ker.subtype_injective
  · exact MonoidHom.exponent_dvd f.rangeRestrict_surjective

@[to_additive] theorem Group.isCyclic_of_coprime_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M →* N) (h : (Nat.card f.ker).Coprime (Nat.card N))
    [IsCyclic f.ker] [hN : IsCyclic N] (hf : Function.Surjective f) : IsCyclic M := by
  rw [← Subgroup.topEquiv.isCyclic, ← f.range_eq_top.mpr hf] at hN
  rw [← Subgroup.card_top (G := N), ← f.range_eq_top.mpr hf] at h
  exact isCyclic_of_coprime_card_range_card_ker f h

section

variable (M N : Type*) [Group M] [Group N] [cyc : IsCyclic (M × N)]
include M N

@[to_additive isAddCyclic_left_of_prod] theorem isCyclic_left_of_prod : IsCyclic M :=
    isCyclic_of_surjective (MonoidHom.fst M N) Prod.fst_surjective

@[to_additive isAddCyclic_right_of_prod] theorem isCyclic_right_of_prod : IsCyclic N :=
    isCyclic_of_surjective (MonoidHom.snd M N) Prod.snd_surjective

@[to_additive coprime_card_of_isAddCyclic_prod] theorem coprime_card_of_isCyclic_prod
    [Finite M] [Finite N] : (Nat.card M).Coprime (Nat.card N) := by
  have hM := isCyclic_left_of_prod M N
  have hN := isCyclic_right_of_prod M N
  let _ := cyc.commGroup; let _ := hM.commGroup; let _ := hN.commGroup
  rw [IsCyclic.iff_exponent_eq_card, Monoid.exponent_prod, Nat.card_prod, lcm_eq_nat_lcm] at *
  simpa only [hM, hN, Nat.lcm_eq_mul_iff, Nat.card_pos.ne', false_or] using cyc

end

theorem not_isAddCyclic_prod_of_infinite_nontrivial (M N : Type*) [AddGroup M] [AddGroup N]
    [Infinite M] [Nontrivial N] : ¬ IsAddCyclic (M × N) := fun hMN ↦ by
  rw [← ((zmodAddCyclicAddEquiv <| isAddCyclic_left_of_prod M N).prodCongr (zmodAddCyclicAddEquiv <|
    isAddCyclic_right_of_prod M N)).isAddCyclic, Nat.card_eq_zero_of_infinite] at hMN
  cases (finite_or_infinite N).symm
  · rw [Nat.card_eq_zero_of_infinite] at hMN
    let f := (ZMod.castHom (dvd_zero _) (ZMod 2)).toAddMonoidHom
    have hf := ZMod.castHom_surjective (dvd_zero 2)
    have := isAddCyclic_of_surjective (f.prodMap f) (Prod.map_surjective.mpr ⟨hf, hf⟩)
    simpa using coprime_card_of_isAddCyclic_prod (ZMod 2) (ZMod 2)
  let ZN := ZMod (Nat.card N)
  have : NeZero (Nat.card N) := ⟨Nat.card_pos.ne'⟩
  have := isAddCyclic_of_surjective ((ZMod.castHom (dvd_zero _) ZN).toAddMonoidHom.prodMap (.id ZN))
    (Prod.map_surjective.mpr ⟨ZMod.castHom_surjective (dvd_zero _), Function.surjective_id⟩)
  exact Finite.one_lt_card (α := N).ne' (by simpa [ZN] using coprime_card_of_isAddCyclic_prod ZN ZN)

@[to_additive existing not_isAddCyclic_prod_of_infinite_nontrivial]
theorem not_isCyclic_prod_of_infinite_nontrivial (M N : Type*) [Group M] [Group N]
    [Infinite M] [Nontrivial N] : ¬ IsCyclic (M × N) := by
  rw [← isAddCyclic_additive_iff, (AddEquiv.prodAdditive ..).isAddCyclic]
  apply not_isAddCyclic_prod_of_infinite_nontrivial

/-- The product of two finite groups is cyclic iff
both of them are cyclic and their orders are coprime. -/
@[to_additive AddGroup.isAddCyclic_prod_iff /-- The product of two finite additive groups is cyclic
iff both of them are cyclic and their orders are coprime. -/]
theorem Group.isCyclic_prod_iff {M N : Type*} [Group M] [Group N] :
    IsCyclic (M × N) ↔ IsCyclic M ∧ IsCyclic N ∧ (Nat.card M).Coprime (Nat.card N) := by
  refine ⟨fun h ↦ ⟨isCyclic_left_of_prod M N, isCyclic_right_of_prod M N, ?_⟩, fun ⟨hM, hN, h⟩ ↦ ?_⟩
  · cases (finite_or_infinite M).symm
    · cases subsingleton_or_nontrivial N; · simp
      exact (not_isCyclic_prod_of_infinite_nontrivial M N h).elim
    cases (finite_or_infinite N).symm
    · cases subsingleton_or_nontrivial M; · simp
      rw [(MulEquiv.prodComm ..).isCyclic] at h
      exact (not_isCyclic_prod_of_infinite_nontrivial N M h).elim
    apply coprime_card_of_isCyclic_prod
  · let f := MonoidHom.snd M N
    let e : f.ker ≃* M := by
      rw [MonoidHom.ker_snd]
      exact ((Subgroup.prodEquiv ..).trans .prodUnique).trans Subgroup.topEquiv
    let _ := hM.commGroup; let _ := hN.commGroup
    rw [← e.isCyclic] at hM
    rw [← Nat.card_congr e.toEquiv] at h
    exact isCyclic_of_coprime_card_ker f h Prod.snd_surjective

end prod

section WithZero

instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
  apply isCyclic_of_injective (G := (WithZero G)ˣ) (WithZero.unitsWithZeroEquiv).toMonoidHom
  apply Equiv.injective

end WithZero
