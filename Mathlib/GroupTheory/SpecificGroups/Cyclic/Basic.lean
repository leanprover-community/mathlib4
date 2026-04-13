/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cyclic groups

`IsCyclic` is a predicate on a group stating that the group is cyclic.
For the concrete cyclic group of order `n`, see `Data.ZMod.Basic`.

* `isCyclic_of_prime_card` proves that a finite group of prime order is cyclic.

cyclic group
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal Field

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
  simp_rw [← map_subtype_inj, ← MonoidHom.range_eq_map,
    H.range_subtype, MonoidHom.map_zpowers, Subtype.exists, coe_subtype, exists_prop]
  exact exists_congr fun g ↦ and_iff_right_of_imp fun h ↦ h ▸ mem_zpowers g

@[to_additive]
instance Subgroup.isCyclic_zpowers [Group G] (g : G) :
    IsCyclic (Subgroup.zpowers g) :=
  (Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨g, rfl⟩

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
instance IsCyclic.isMulCommutative [Group α] [IsCyclic α] : IsMulCommutative α where
  is_comm.comm x y :=
    let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
    let ⟨_, hx⟩ := hg x
    let ⟨_, hy⟩ := hg y
    hy ▸ hx ▸ zpow_mul_comm ..

@[deprecated (since := "2026-04-09")]
alias IsAddCyclic.commutative := IsAddCyclic.isAddCommutative
@[to_additive existing, deprecated (since := "2026-04-09")]
alias IsCyclic.commutative := IsCyclic.isMulCommutative

open scoped IsMulCommutative in
/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive (attr := implicit_reducible)
      /-- A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`. -/]
def IsCyclic.commGroup [Group α] [IsCyclic α] : CommGroup α :=
  inferInstance

variable [Group α] [Group G] [Group G']

/-- A non-cyclic multiplicative group is non-trivial. -/
@[to_additive /-- A non-cyclic additive group is non-trivial. -/]
theorem Nontrivial.of_not_isCyclic (nc : ¬IsCyclic α) : Nontrivial α := by
  contrapose! nc
  exact isCyclic_of_subsingleton

@[to_additive]
theorem MonoidHom.map_cyclic [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [map_zpow, ← hm, ← zpow_mul, ← zpow_mul']

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
theorem orderOf_eq_card_of_forall_mem_powers {g : α} (hx : ∀ x, x ∈ Submonoid.powers g) :
    orderOf g = Nat.card α := by
  rw [orderOf_eq_card_of_forall_mem_zpowers]
  exact fun x ↦ Submonoid.powers_le_zpowers _ (hx _)

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
  ⟨⟨1, fun x => ⟨0, Subtype.ext <| (zpow_zero (1 : α)).trans <| Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩

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
            · rw [Int.ofNat_eq_natCast, Int.natAbs_natCast k, ← zpow_natCast,
                ← Int.ofNat_eq_natCast, hk]
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
            rw [← zpow_add, Int.emod_add_mul_ediv, hk]; exact hx
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
          Subtype.ext_iff.2
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

@[to_additive]
theorem Subgroup.le_zpowers_iff (g : G) (H : Subgroup G) :
    H ≤ Subgroup.zpowers g ↔ ∃ n : ℕ, H = Subgroup.zpowers (g ^ n) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := (H.isCyclic_iff_exists_zpowers_eq_top).mp (isCyclic_of_le h)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp <| h (mem_zpowers x)
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact ⟨n, by rw [zpow_natCast]⟩
    · exact ⟨n, by simp⟩
  · rintro ⟨k, rfl⟩
    exact zpowers_le_of_mem <| npow_mem_zpowers g k

open Finset Nat

section Classical

open scoped Classical in
@[to_additive IsAddCyclic.card_nsmul_eq_zero_le]
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    #{a : α | a ^ n = 1} ≤ n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    #{a : α | a ^ n = 1} ≤
        #(zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset := by
      gcongr
      intro x hx
      let ⟨m, hm⟩ := show x ∈ Submonoid.powers g from mem_powers_iff_mem_zpowers.2 <| hg x
      refine Set.mem_toFinset.2 ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : ℕ), ?_⟩
      dsimp only at ⊢ hm
      rw [zpow_natCast, ← pow_mul, Nat.mul_div_cancel_left', hm]
      refine Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) ?_
      conv_lhs =>
        rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ← Nat.card_eq_fintype_card,
          ← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one <| by simpa [pow_mul, hm] using (mem_filter.1 hx).2
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

end Cyclic

end
