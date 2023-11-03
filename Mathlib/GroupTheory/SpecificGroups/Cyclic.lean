/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Exponent

#align_import group_theory.specific_groups.cyclic from "leanprover-community/mathlib"@"0f6670b8af2dff699de1c0b4b49039b31bc13c46"

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

section Generator

open Subgroup

/-- An element of an additive group is a *generator*  if any element of the group is a multiple
of the generator. -/
@[ext]
structure AddGroup.Generator (α : Type u) [AddGroup α] where
  val : α
  generates : ∀ x, x ∈ AddSubgroup.zmultiples val

/-- An element of a group is a *generator*  if any element of the group is a power
of the generator. -/
@[to_additive, ext]
structure Group.Generator (α : Type u) [Group α] where
  val : α
  generates : ∀ x, x ∈ zpowers val

attribute [coe] Group.Generator.val AddGroup.Generator.val

namespace Group.Generator

@[to_additive]
instance instCoeOut (α : Type u) [Group α] : CoeOut (Generator α) α where
  coe := val

@[to_additive]
instance instCanLift {α : Type u} [Group α] : CanLift α (Generator α) val (∀ x, x ∈ zpowers ·) where
  prf g hg := ⟨⟨g, hg⟩, rfl⟩

/-- The subgroup of integer powers of a generator is `⊤`. -/
@[to_additive]
theorem zpowers_eq_top {α : Type u} [Group α] (g : Generator α) : zpowers (g : α) = ⊤ :=
  eq_top_iff' _ |>.mpr g.generates

/-- A power `k : ℤ` such that `g ^ k = x`. If `orderOf g = 0`, then `k` is unique. When `orderOf g`
is positive, we guarantee `0 ≤ k < orderOf g`. -/
@[to_additive]
noncomputable def power {α : Type u} [Group α] (g : Generator α)
    (x : α) : ℤ := by
  letI k := g.generates x |>.choose
  exact if orderOf (g : α) = 0 then k else k % orderOf (g : α)

@[to_additive]
theorem power_spec {α : Type u} [Group α] (g : Generator α)
    (x : α) : (g : α) ^ (g.power x) = x := by
  rw [power]
  split_ifs with h
  · exact g.generates x |>.choose_spec
  · rw [←zpow_eq_mod_orderOf]
    exact g.generates x |>.choose_spec

@[to_additive]
theorem power_lt_orderOf {α : Type u} [Group α] (g : Generator α) (hg : orderOf (g : α) ≠ 0)
    (x : α) : g.power x < orderOf (g : α) := by
  rw [power, if_neg hg]
  simpa using Int.emod_lt _ (by exact_mod_cast hg : (orderOf (g : α) : ℤ) ≠ 0)

@[to_additive]
theorem power_nonneg {α : Type u} [Group α] (g : Generator α) (hg : orderOf (g : α) ≠ 0)
    (x : α) : 0 ≤ g.power x := by
  rw [power, if_neg hg]
  exact Int.emod_nonneg _ (by exact_mod_cast hg)

@[to_additive]
theorem power_mul_modEq {α : Type u} [Group α] (g : Generator α) {x y : α} :
    g.power (x * y) ≡ g.power x + g.power y [ZMOD orderOf (g : α)] := by
  simp only [←zpow_eq_zpow_iff_modEq, zpow_add, g.power_spec]

@[to_additive (attr := simp)]
theorem power_one {α : Type u} [Group α] (g : Generator α) :
    g.power 1 = 0 := by
  have := g.power_spec 1
  rw [zpow_eq_one_iff_modEq] at this
  by_cases hg : orderOf (g : α) = 0
  · simpa [hg] using this
  · simpa only [EuclideanDomain.zero_mod,
      Int.emod_eq_of_lt (g.power_nonneg hg 1) (g.power_lt_orderOf hg 1)] using this.eq

@[to_additive]
theorem ne_one {α : Type u} [Group α] [Nontrivial α] (g : Generator α) :
    (g : α) ≠ 1 :=
  fun hg ↦ by simpa [hg] using g.zpowers_eq_top

@[to_additive]
theorem orderOf_ne_one {α : Type u} [Group α] [Nontrivial α] (g : Generator α) :
    orderOf (g : α) ≠ 1 := by
  by_cases h : orderOf (g : α) = 0
  · norm_num [h]
  · simpa [Ne.def, orderOf_eq_one_iff] using g.ne_one

@[to_additive (attr := simp)]
theorem power_self {α : Type u} [Group α] [Nontrivial α] (g : Generator α) :
    g.power (g : α) = 1 := by
  have := (g.power_spec (g : α)).trans (zpow_one (g : α)).symm
  rw [zpow_eq_zpow_iff_modEq] at this
  by_cases hg : orderOf (g : α) = 0
  · simpa [hg] using this
  · have := Int.emod_eq_of_lt (g.power_nonneg hg (g : α)) (g.power_lt_orderOf hg (g : α)) ▸ this.eq
    have one_lt : 1 < orderOf (g : α) :=
      lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hg) g.orderOf_ne_one.symm
    simpa [Int.emod_eq_of_lt zero_le_one (by exact_mod_cast one_lt : (1 < (orderOf (g : α) : ℤ)))]

/-- The range of a group homomorphism `f` from a group witha generator `g` is exactly the subgroup
of integer powers of `f g`. -/
@[to_additive]
theorem monoidHom_range {α β : Type*} [Group α] [Group β] (g : Generator α) (f : α →* β) :
    f.range = Subgroup.zpowers (f g) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    rw [←g.power_spec x, map_zpow]
    exact zpow_mem_zpowers _ _
  · rintro ⟨k, rfl⟩
    exact ⟨(g : α) ^ k, map_zpow f (g : α) k⟩

/-- Group homomorphisms which agree on a generator are equal. -/
@[to_additive]
theorem monoidHom_ext {F α β : Type*} [Group α] [Group β] [MonoidHomClass F α β] (g : Generator α)
    (f₁ f₂ : F) (h : f₁ (g : α) = f₂ (g : α)) : f₁ = f₂ :=
  FunLike.ext f₁ f₂ fun x ↦ by obtain ⟨k, rfl⟩ := g.generates x; simp only [map_zpow, h]

/-- Given a generator `g` of a group `α` and an element `b` of a group `β` whose order divides the
order of `g`, this is the unique group homomorphism sending `g` to `b`. -/
@[to_additive (attr := simps)]
noncomputable def monoidHom {α β : Type*} [Group α] [Group β] (g : Generator α) {b : β}
    (hb : orderOf b ∣ orderOf (g : α)) : α →* β where
  toFun := (b ^ g.power ·)
  map_one' := by simp
  map_mul' x₁ x₂ := by
    rw [← zpow_add, zpow_eq_zpow_iff_modEq]
    exact Int.ModEq.of_dvd (Int.ofNat_dvd.mpr hb) g.power_mul_modEq

@[to_additive (attr := simp)]
theorem orderOf_subsingleton {α : Type*} [Monoid α] [Subsingleton α] (x : α) :
    orderOf x = 1 := by
  simp [congrArg orderOf <| Subsingleton.elim x 1]

@[to_additive (attr := simp)]
theorem monoidHom_map_self {α β : Type*} [Group α] [Group β] (g : Generator α)
    {b : β} (hb : orderOf b ∣ orderOf (g : α)) : g.monoidHom hb g = b := by
  obtain (h | h) := subsingleton_or_nontrivial α
  · simp only [orderOf_subsingleton (g : α), Nat.isUnit_iff, orderOf_eq_one_iff, Nat.dvd_one] at hb
    simp [hb]
  · simp

/-- The order of a finite group (`Fintype.card`) generated by `g` is the order of `g`. -/
@[to_additive (attr := simp)]
theorem orderOf_eq_card {α : Type*} [Group α] [Fintype α] (g : Generator α) :
    orderOf (g : α) = Fintype.card α := by
  rw [orderOf_eq_card_zpowers]
  apply Fintype.card_of_finset'
  simpa using g.generates
#align order_of_eq_card_of_forall_mem_zpowers Group.Generator.orderOf_eq_card
#align add_order_of_eq_card_of_forall_mem_zmultiples AddGroup.Generator.addOrderOf_eq_card

/-- The order of a generator is positive if and only if the group is finite. -/
@[to_additive]
theorem orderOf_pos_iff_finite {α : Type*} [Group α] (g : Generator α) :
    0 < orderOf (g : α) ↔ Finite α := by
  constructor
  · intro hg
    rw [←Set.finite_univ_iff, ←coe_top, ←g.zpowers_eq_top]
    convert (Finset.range (orderOf (g : α))).finite_toSet.image (fun k : ℕ ↦ (g : α) ^ (k : ℤ))
    ext
    constructor
    · rintro ⟨k, rfl⟩
      simp only [zpow_coe_nat, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨k.natMod <| orderOf (g : α), Int.natMod_lt hg.ne', ?_⟩
      rw [←zpow_ofNat, zpow_eq_zpow_iff_modEq, Int.natMod,
        Int.toNat_of_nonneg (k.emod_nonneg (by exact_mod_cast hg.ne'))]
      exact k.mod_modEq (orderOf (g : α))
    · rintro ⟨k, -, rfl⟩
      use k
  · intro
    have := Fintype.ofFinite α
    rw [orderOf_eq_card]
    exact Fintype.card_pos

/-- The order of a generator is zero if and only if the group is infinite. -/
@[to_additive]
theorem orderOf_eq_zero_iff_infinite {α : Type*} [Group α] (g : Generator α) :
    orderOf (g : α) = 0 ↔ Infinite α := by
  apply not_iff_not.mp
  simp only [← Nat.pos_iff_ne_zero, not_infinite_iff_finite]
  exact g.orderOf_pos_iff_finite

/-- The order of a generator of a finite group is positive. -/
@[to_additive (attr := simp)]
theorem orderOf_pos {α : Type*} [Group α] [Finite α] (g : Generator α) :
    0 < orderOf (g : α) :=
  g.orderOf_pos_iff_finite.mpr ‹_›

/-- The order of a generator of an infinite group is zero. -/
@[to_additive (attr := simp)]
theorem orderOf_eq_zero {α : Type*} [Group α] [Infinite α] (g : Generator α) :
    orderOf (g : α) = 0 :=
  g.orderOf_eq_zero_iff_infinite.mpr ‹_›
#align infinite.order_of_eq_zero_of_forall_mem_zpowers Group.Generator.orderOf_eq_zero
#align infinite.add_order_of_eq_zero_of_forall_mem_zmultiples AddGroup.Generator.addOrderOf_eq_zero

/-- The order of a group (`Nat.card`) generated by `g` is the order of `g`. -/
@[to_additive]
theorem orderOf_eq_nat_card {α : Type*} [Group α] (g : Generator α) :
    orderOf (g : α) = Nat.card α := by
  obtain (h | h) := finite_or_infinite α
  · have := Fintype.ofFinite α
    simp
  · rwa [Nat.card_eq_zero_of_infinite, g.orderOf_eq_zero_iff_infinite]

@[to_additive (attr := simps)]
def of_orderOf_eq_card {α : Type*} [Group α] [Fintype α] (x : α)
    (hx : orderOf x = Fintype.card α) : Generator α where
  val := x
  generates := by
    simp_rw [← SetLike.mem_coe, ← Set.eq_univ_iff_forall]
    rw [← Fintype.card_congr (Equiv.Set.univ α), orderOf_eq_card_zpowers] at hx
    exact Set.eq_of_subset_of_card_le (Set.subset_univ _) (ge_of_eq hx)
#align is_cyclic_of_order_of_eq_card Group.Generator.of_orderOf_eq_card
#align is_add_cyclic_of_order_of_eq_card Group.Generator.of_orderOf_eq_card

instance {α : Type*} [Group α] [Finite α] : Finite (Generator α) :=
  Finite.of_injective val Generator.ext

@[to_additive (attr := simps)]
def ofCoprime {α : Type*} [Group α] [Fintype α] (g : Generator α) {n : ℕ}
    (hn : n.Coprime (Fintype.card α)) : Generator α where
  val := (g : α) ^ n
  generates := by
    simp [← Nat.isCoprime_iff_coprime, Int.isCoprime_iff_gcd_eq_one] at hn
    replace hn := congr_arg ((↑) : ℕ → ℤ) hn
    simp only [Int.coe_gcd, Nat.cast_one] at hn
    obtain ⟨x, y, h⟩ := exists_gcd_eq_mul_add_mul (n : ℤ) (Fintype.card α)
    have := hn.symm.trans h
    rw [← zpow_ofNat]
    intro z
    rw [←sub_eq_iff_eq_add, sub_eq_add_neg, ←mul_neg] at this
    use x * g.power z
    simp only
    rw [zpow_mul, ←zpow_mul _ n, ← this, zpow_add, zpow_mul]
    simp [g.power_spec z]
    -- finally

def _root_.AddGroup.Generator.ofZModUnits {α : Type*} [AddGroup α] [Fintype α]
    (g : AddGroup.Generator α) (n : (ZMod (Fintype.card α))ˣ) : AddGroup.Generator α :=
  g.ofCoprime (ZMod.unitsEquivCoprime n).property

@[to_additive (attr := simps!) existing AddGroup.Generator.ofZModUnits]
def ofZModUnits {α : Type*} [Group α] [Fintype α] (g : Generator α)
    (n : (ZMod (Fintype.card α))ˣ) : Generator α :=
  g.ofCoprime (ZMod.unitsEquivCoprime n).property

instance {α : Type*} [Group α] [Fintype α] : Pow (Generator α) (ZMod (Fintype.card α))ˣ where
  pow g n := g.ofZModUnits n
#help attr to_additive
/-- The inverse of a generator, as a generator. -/
@[to_additive]
def inv {α : Type*} [Group α] (g : Generator α) : Generator α where
  val := (g : α)⁻¹
  generates x := by obtain ⟨k, rfl⟩ := g.generates x; exact ⟨-k, by simp⟩

@[to_additive]
noncomputable def zmodUnitsEquiv {α : Type*} [Group α] [Fintype α] (g : Generator α) :
    Function.Bijective g.ofZModUnits := by
  refine ⟨fun n₁ n₂ h ↦ ?_, fun g' ↦ ?_⟩
  · replace h := congr_arg val h
    simp [pow_inj_mod (g : α)] at h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h
    exact Units.eq_iff.mp <| ZMod.val_injective _ h
  . have hg' := g.power_spec (g' : α)
    have := congr(orderOf $hg')
    lift power g (g' : α) to ℕ using g.power_nonneg (by simp) g' with n
    rw [zpow_ofNat, orderOf_pow] at this
    simp [Nat.div_eq_self, Nat.gcd_comm] at this
    use ZMod.unitOfCoprime n this
    ext
    simp [ZMod.unitsEquivCoprime, ZMod.val_nat_cast]
    rwa [←g.orderOf_eq_card, ←pow_eq_mod_orderOf, ← zpow_ofNat]
-- doesn't work @[to_additive]
/-- The equiv which sends the provided generator `g` to `1`. -/

noncomputable def zmodUnitsEquiv {α : Type*} [Group α] [Fintype α] (g : Generator α) :
    (ZMod (Fintype.card α))ˣ ≃ Generator α :=
  Equiv.ofBijective g.ofZModUnits <| by
    refine ⟨fun n₁ n₂ h ↦ ?_, fun g' ↦ ?_⟩
    · replace h := congr_arg val h
      simp [pow_inj_mod (g : α)] at h
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h
      exact Units.eq_iff.mp <| ZMod.val_injective _ h
    . have hg' := g.power_spec (g' : α)
      have := congr(orderOf $hg')
      lift power g (g' : α) to ℕ using g.power_nonneg (by simp) g' with n
      rw [zpow_ofNat, orderOf_pow] at this
      simp [Nat.div_eq_self, Nat.gcd_comm] at this
      use ZMod.unitOfCoprime n this
      ext
      simp [ZMod.unitsEquivCoprime, ZMod.val_nat_cast]
      rwa [←g.orderOf_eq_card, ←pow_eq_mod_orderOf, ← zpow_ofNat]

end Group.Generator

end Generator

section Cyclic

open BigOperators

attribute [local instance] setFintype

open Subgroup

/-- A group is called *cyclic* if it is generated by a single element. -/
class IsAddCyclic (α : Type u) [AddGroup α] : Prop where
  exists_generator : Nonempty (AddGroup.Generator α)
#align is_add_cyclic IsAddCyclic

/-- A group is called *cyclic* if it is generated by a single element. -/
@[to_additive IsAddCyclic]
class IsCyclic (α : Type u) [Group α] : Prop where
  exists_generator : Nonempty (Group.Generator α)
#align is_cyclic IsCyclic

/-- An aribtrary generator of a cyclic group. -/
@[to_additive]
noncomputable def IsCyclic.generator (α : Type u) [Group α] [IsCyclic α] : Group.Generator α :=
  IsCyclic.exists_generator.some

@[to_additive isAddCyclic_of_subsingleton]
instance (priority := 100) isCyclic_of_subsingleton [Group α] [Subsingleton α] : IsCyclic α where
  exists_generator := ⟨1, fun x => by rw [Subsingleton.elim x 1]; exact mem_zpowers 1⟩
#align is_cyclic_of_subsingleton isCyclic_of_subsingleton
#align is_add_cyclic_of_subsingleton isAddCyclic_of_subsingleton

noncomputable instance Group.Generator.instFintype {α : Type u} [Group α] [Fintype α] [IsCyclic α] :
    Fintype (Generator α) :=
  Fintype.ofEquiv _ (IsCyclic.generator α).zmodUnitsEquiv



/-- A cyclic group is always commutative. This is not an `instance` because often we have a better
proof of `CommGroup`. -/
@[to_additive
      "A cyclic group is always commutative. This is not an `instance` because often we have
      a better proof of `AddCommGroup`."]
def IsCyclic.commGroup [hg : Group α] [IsCyclic α] : CommGroup α :=
  { hg with
    mul_comm := fun x y =>
      let ⟨_, hg⟩ := IsCyclic.generator α
      let ⟨_, hn⟩ := hg x
      let ⟨_, hm⟩ := hg y
      hm ▸ hn ▸ zpow_mul_comm _ _ _ }
#align is_cyclic.comm_group IsCyclic.commGroup
#align is_add_cyclic.add_comm_group IsAddCyclic.addCommGroup

variable [Group α]

@[to_additive MonoidAddHom.map_add_cyclic]
theorem MonoidHom.map_cyclic {G : Type*} [Group G] [h : IsCyclic G] (σ : G →* G) :
    ∃ m : ℤ, ∀ g : G, σ g = g ^ m := by
  obtain ⟨h, hG⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, hm⟩ := hG (σ h)
  refine' ⟨m, fun g => _⟩
  obtain ⟨n, rfl⟩ := hG g
  rw [MonoidHom.map_zpow, ← hm, ← zpow_mul, ← zpow_mul']
#align monoid_hom.map_cyclic MonoidHom.map_cyclic
#align monoid_add_hom.map_add_cyclic MonoidAddHom.map_add_cyclic

/-- A finite group of prime order is cyclic. -/
@[to_additive isAddCyclic_of_prime_card "A finite group of prime order is cyclic."]
theorem isCyclic_of_prime_card {α : Type u} [Group α] [Fintype α] {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card α = p) : IsCyclic α where
  exists_generator := by
    obtain ⟨g, hg⟩ : ∃ g : α, g ≠ 1 := Fintype.exists_ne_of_one_lt_card (h.symm ▸ hp.1.one_lt) 1
    have := h ▸ orderOf_dvd_card_univ (x := g)
    rw [Nat.dvd_prime hp.1] at this
    exact ⟨Group.Generator.of_orderOf_eq_card g <|
      h.symm ▸ this.resolve_left (hg <| orderOf_eq_one_iff.mp ·)⟩
#align is_cyclic_of_prime_card isCyclic_of_prime_card
#align is_add_cyclic_of_prime_card isAddCyclic_of_prime_card

@[to_additive]
instance {M : Type*} [Monoid M] (m : M) : CommMonoid (Submonoid.powers m) where
  mul_comm := by
    rintro ⟨-, ⟨j, rfl⟩⟩ ⟨-, ⟨k, rfl⟩⟩
    ext1
    simp only [Submonoid.coe_mul, ←pow_add, add_comm]


/-- If an `m` is an element of finite order in a monoid `M`, then `Submonoid.powers m` is a
cancellative commutative monoid.

This is not declared as an instance because of the hypothesis `0 < orderOf m`, which is necessary.
Indeed, `M` is a monoid with zero and `m` is nilpotent, then `orderOf m = 0`, but
`Submonoid.powers m` is not cancellative. -/
@[to_additive (attr := reducible)]
def Submonoid.powersCancelCommMonoid {M : Type*} [Monoid M] {m : M} (hm : 0 < orderOf m) :
    CancelCommMonoid (Submonoid.powers m) where
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_left_cancel := by
    rintro ⟨-, ⟨j, rfl⟩⟩ ⟨-, ⟨k, rfl⟩⟩ ⟨-, ⟨l, rfl⟩⟩
    intro h
    replace h := congr_arg Subtype.val h
    ext
    simp only [coe_mul] at h ⊢
    rw [←pow_add, ←pow_add, pow_eq_mod_orderOf, pow_eq_mod_orderOf (n := j + l)] at h
    have := pow_injective_of_lt_orderOf m ((j + k).mod_lt hm) ((j + l).mod_lt hm) h
    simpa [← pow_eq_mod_orderOf] using congr_arg (m ^ ·) <| Nat.ModEq.add_left_cancel rfl this

/-- The equivalence between `Fin (orderOf m)` and `Submonoid.powers m`, sending `i` to `m ^ i`,
under the hypothesis that `orderOf m` is positive. -/
@[to_additive finEquivMultiples']
theorem finEquivPowers' {M : Type*} [Monoid M] {m : M} (hm : 0 < orderOf m) :
    Fin (orderOf m) ≃ Submonoid.powers m :=
  Equiv.ofBijective (fun k ↦ ⟨m ^ (k : ℕ), ⟨k, rfl⟩⟩) -- maybe use `Subtype.coind`? meh ...
    ⟨fun k₁ k₂ hk ↦ Fin.ext <|
      pow_injective_of_lt_orderOf m k₁.prop k₂.prop (congr_arg Subtype.val hk),
    by
      rintro ⟨-, ⟨k, rfl⟩⟩
      exact ⟨⟨k % orderOf m, k.mod_lt hm⟩, by simpa using pow_eq_mod_orderOf.symm⟩⟩

/-- The submonoid of powers of `m` in a monoid `M` is finite if the order of `m` is positive. -/
@[to_additive finite_multiples_of_orderOf_pos]
theorem finite_powers_of_orderOf_pos {M : Type*} [Monoid M] {m : M} (hm : 0 < orderOf m) :
    Finite (Submonoid.powers m) :=
  Finite.intro (finEquivPowers' hm).symm

/-- In a cancellative monoid, if `orderOf m` is zero then `Submonoid.powers m` is infinite. -/
@[to_additive infinite_multiples_of_orderOf_zero]
theorem infinite_powers_of_orderOf_zero {M : Type*} [LeftCancelMonoid M] {m : M}
    (hm : orderOf m = 0) : Infinite (Submonoid.powers m) := by
  rw [orderOf_eq_zero_iff, ← injective_pow_iff_not_isOfFinOrder] at hm
  exact Infinite.of_injective (Subtype.coind (m ^ ·) (fun k ↦ ⟨k, rfl⟩)) <|
    Subtype.coind_injective _ hm

/-- In a cancellative monoid, if `orderOf m` is zero then `Submonoid.powers m` is infinite. -/
@[to_additive addOrderOf_pos_iff_finite_multiples]
theorem orderOf_pos_iff_finite_powers {M : Type*} [LeftCancelMonoid M] {m : M} :
    0 < orderOf m ↔ Finite (Submonoid.powers m) :=
  Iff.intro (finite_powers_of_orderOf_pos ·) <| by
    contrapose
    simpa only [not_lt, nonpos_iff_eq_zero, not_finite_iff_infinite]
      using (infinite_powers_of_orderOf_zero ·)

/-- In a cancellative monoid, if `orderOf m` is zero then `Submonoid.powers m` is infinite. -/
@[to_additive addOrderOf_zero_iff_infinite_multiples]
theorem orderOf_zero_iff_infinite_powers {M : Type*} [LeftCancelMonoid M] {m : M} :
    orderOf m = 0 ↔ Infinite (Submonoid.powers m) :=
  not_iff_not.mp <| by simpa [Nat.pos_iff_ne_zero] using orderOf_pos_iff_finite_powers (m := m)

@[to_additive exists_nsmul_ne_zero_of_isAddCyclic]
theorem exists_pow_ne_one_of_isCyclic {G : Type*} [Group G] [Fintype G] [G_cyclic : IsCyclic G]
    {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) : ∃ a : G, a ^ k ≠ 1 := by
  rcases G_cyclic with ⟨a, ha⟩
  use a
  contrapose! k_lt_card_G
  convert orderOf_le_of_pow_eq_one k_pos.bot_lt k_lt_card_G
  rw [orderOf_eq_card_zpowers, eq_comm, Subgroup.card_eq_iff_eq_top, eq_top_iff]
  exact fun x _ ↦ ha x

@[to_additive Bot.isAddCyclic]
instance Bot.isCyclic {α : Type u} [Group α] : IsCyclic (⊥ : Subgroup α) :=
  ⟨⟨1, fun x => ⟨0, Subtype.eq <| (zpow_zero (1 : α)).trans <| Eq.symm (Subgroup.mem_bot.1 x.2)⟩⟩⟩
#align bot.is_cyclic Bot.isCyclic
#align bot.is_add_cyclic Bot.isAddCyclic

@[to_additive AddSubgroup.isAddCyclic]
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
            · rw [Int.ofNat_eq_coe, Int.natAbs_cast k, ← zpow_ofNat, ←Int.ofNat_eq_coe, hk]
              exact hx₁
            · rw [Int.natAbs_negSucc, ← Subgroup.inv_mem_iff H]; simp_all⟩
    ⟨⟨⟨g ^ Nat.find hex, (Nat.find_spec hex).2⟩, fun ⟨x, hx⟩ =>
        let ⟨k, hk⟩ := hg x
        have hk : g ^ k = x := hk
        have hk₂ : g ^ ((Nat.find hex : ℤ) * (k / Nat.find hex : ℤ)) ∈ H := by
          rw [zpow_mul]
          apply H.zpow_mem
          exact_mod_cast (Nat.find_spec hex).2
        have hk₃ : g ^ (k % Nat.find hex : ℤ) ∈ H :=
          (Subgroup.mul_mem_cancel_right H hk₂).1 <| by
            rw [← zpow_add, Int.emod_add_ediv, hk]; exact hx
        have hk₄ : k % Nat.find hex = (k % Nat.find hex).natAbs := by
          rw [Int.natAbs_of_nonneg
              (Int.emod_nonneg _ (Int.coe_nat_ne_zero_iff_pos.2 (Nat.find_spec hex).1))]
        have hk₅ : g ^ (k % Nat.find hex).natAbs ∈ H := by rwa [← zpow_ofNat, ← hk₄]
        have hk₆ : (k % (Nat.find hex : ℤ)).natAbs = 0 :=
          by_contradiction fun h =>
            Nat.find_min hex
              (Int.ofNat_lt.1 <| by
                rw [← hk₄]; exact Int.emod_lt_of_pos _ (Int.coe_nat_pos.2 (Nat.find_spec hex).1))
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
#align subgroup.is_cyclic Subgroup.isCyclic
#align add_subgroup.is_add_cyclic AddSubgroup.isAddCyclic

open Finset Nat

section Classical

open Classical

@[to_additive IsAddCyclic.card_pow_eq_one_le]
theorem IsCyclic.card_pow_eq_one_le [DecidableEq α] [Fintype α] [IsCyclic α] {n : ℕ} (hn0 : 0 < n) :
    (univ.filter fun a : α => a ^ n = 1).card ≤ n :=
  let ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  calc
    (univ.filter fun a : α => a ^ n = 1).card ≤
        (zpowers (g ^ (Fintype.card α / Nat.gcd n (Fintype.card α))) : Set α).toFinset.card :=
      card_le_of_subset fun x hx =>
        let ⟨m, hm⟩ := show x ∈ Submonoid.powers g from mem_powers_iff_mem_zpowers.2 <| hg x
        Set.mem_toFinset.2
          ⟨(m / (Fintype.card α / Nat.gcd n (Fintype.card α)) : ℕ), by
            dsimp at hm
            have hgmn : g ^ (m * Nat.gcd n (Fintype.card α)) = 1 := by
              rw [pow_mul, hm, ← pow_gcd_card_eq_one_iff]; exact (mem_filter.1 hx).2
            dsimp only
            rw [zpow_ofNat, ← pow_mul, Nat.mul_div_cancel_left', hm]
            refine' Nat.dvd_of_mul_dvd_mul_right (gcd_pos_of_pos_left (Fintype.card α) hn0) _
            conv_lhs =>
              rw [Nat.div_mul_cancel (Nat.gcd_dvd_right _ _), ←
                Group.Generator.orderOf_eq_card ⟨g, hg⟩]
            exact orderOf_dvd_of_pow_eq_one hgmn⟩
    _ ≤ n := by
      let ⟨m, hm⟩ := Nat.gcd_dvd_right n (Fintype.card α)
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by
          rw [hm0, mul_zero, Fintype.card_eq_zero_iff] at hm
          exact hm.elim' 1
      simp only [Set.toFinset_card, SetLike.coe_sort_coe]
      rw [← orderOf_eq_card_zpowers, orderOf_pow g, Group.Generator.orderOf_eq_card ⟨g, hg⟩]
      nth_rw 2 [hm]; nth_rw 3 [hm]
      rw [Nat.mul_div_cancel_left _ (gcd_pos_of_pos_left _ hn0), gcd_mul_left_left, hm,
        Nat.mul_div_cancel _ hm0]
      exact le_of_dvd hn0 (Nat.gcd_dvd_left _ _)
#align is_cyclic.card_pow_eq_one_le IsCyclic.card_pow_eq_one_le
#align is_add_cyclic.card_pow_eq_one_le IsAddCyclic.card_pow_eq_one_le

end Classical

@[to_additive]
theorem IsCyclic.exists_monoid_generator [Finite α] [IsCyclic α] :
    ∃ x : α, ∀ y : α, y ∈ Submonoid.powers x := by
  simp_rw [mem_powers_iff_mem_zpowers]
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := α)
  exact ⟨x, hx⟩
#align is_cyclic.exists_monoid_generator IsCyclic.exists_monoid_generator
#align is_add_cyclic.exists_add_monoid_generator IsAddCyclic.exists_addMonoid_generator

section

variable [DecidableEq α] [Fintype α]

@[to_additive]
theorem Group.Generator.image_range_orderOf (g : Generator α) :
    Finset.image (fun i => (g : α) ^ i) (range (orderOf (g : α))) = univ := by
  simp only [_root_.image_range_orderOf, Set.eq_univ_iff_forall.mpr g.generates, Set.toFinset_univ]
#align is_cyclic.image_range_order_of Group.Generator.image_range_orderOf
#align is_add_cyclic.image_range_order_of AddGroup.Generator.image_range_addOrderOf

@[to_additive]
theorem Group.Generator.image_range_card (g : Generator α) :
    Finset.image (fun i => (g : α) ^ i) (range (Fintype.card α)) = univ := by
  rw [← g.orderOf_eq_card, g.image_range_orderOf]
#align is_cyclic.image_range_card Group.Generator.image_range_card
#align is_add_cyclic.image_range_card AddGroup.Generator.image_range_card

end

section Totient

variable [DecidableEq α] [Fintype α]
  (hn : ∀ n : ℕ, 0 < n → (univ.filter fun a : α => a ^ n = 1).card ≤ n)

private theorem card_pow_eq_one_eq_orderOf_aux (a : α) :
    (Finset.univ.filter fun b : α => b ^ orderOf a = 1).card = orderOf a :=
  le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := orderOf_eq_card_zpowers
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
                  rw [← hi, ← zpow_ofNat, ← zpow_mul, mul_comm, zpow_mul, zpow_ofNat,
                    pow_orderOf_eq_one, one_zpow]⟩⟩)
          fun _ _ h => Subtype.eq (Subtype.mk.inj h))
      _ = (univ.filter fun b : α => b ^ orderOf a = 1).card := Fintype.card_ofFinset _ _
      )

-- Use φ for `Nat.totient`
open Nat
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
    (∑ m in d.properDivisors, (univ.filter fun a : α => orderOf a = m).card) =
      ∑ m in d.properDivisors, φ m := by
    refine' Finset.sum_congr rfl fun m hm => _
    simp only [mem_filter, mem_range, mem_properDivisors] at hm
    refine' IH m hm.2 (hm.1.trans hd) (Finset.card_pos.2 ⟨a ^ (d / m), _⟩)
    simp only [mem_filter, mem_univ, orderOf_pow a, ha, true_and_iff,
      Nat.gcd_eq_right (div_dvd_of_dvd hm.1), Nat.div_div_self hm.1 hd0]
  have h2 :
    (∑ m in d.divisors, (univ.filter fun a : α => orderOf a = m).card) =
      ∑ m in d.divisors, φ m := by
    rw [← filter_dvd_eq_divisors hd0, sum_card_orderOf_eq_card_pow_eq_one hd0,
      filter_dvd_eq_divisors hd0, sum_totient, ← ha, card_pow_eq_one_eq_orderOf_aux hn a]
  simpa [← cons_self_properDivisors hd0, ← h1] using h2

theorem card_orderOf_eq_totient_aux₂ {d : ℕ} (hd : d ∣ Fintype.card α) :
    (univ.filter fun a : α => orderOf a = d).card = φ d := by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  simp only [not_lt, _root_.le_zero_iff, card_eq_zero] at h0
  apply lt_irrefl c
  calc
    c = ∑ m in c.divisors, (univ.filter fun a : α => orderOf a = m).card := by
      simp only [← filter_dvd_eq_divisors hc0.ne', sum_card_orderOf_eq_card_pow_eq_one hc0.ne']
      apply congr_arg card
      simp
    _ = ∑ m in c.divisors.erase d, (univ.filter fun a : α => orderOf a = m).card := by
      rw [eq_comm]
      refine' sum_subset (erase_subset _ _) fun m hm₁ hm₂ => _
      have : m = d := by
        contrapose! hm₂
        exact mem_erase_of_ne_of_mem hm₂ hm₁
      simp [this, h0]
    _ ≤ ∑ m in c.divisors.erase d, φ m := by
      refine' sum_le_sum fun m hm => _
      have hmc : m ∣ c := by
        simp only [mem_erase, mem_divisors] at hm
        tauto
      rcases (filter (fun a : α => orderOf a = m) univ).card.eq_zero_or_pos with (h1 | h1)
      · simp [h1]
      · simp [card_orderOf_eq_totient_aux₁ hn hmc h1]
    _ < ∑ m in c.divisors, φ m :=
      (sum_erase_lt_of_pos (mem_divisors.2 ⟨hd, hc0.ne'⟩) (totient_pos (pos_of_dvd_of_pos hd hc0)))
    _ = c := sum_totient _
#align card_order_of_eq_totient_aux₂ card_orderOf_eq_totient_aux₂

theorem isCyclic_of_card_pow_eq_one_le : IsCyclic α where
  exists_generator :=
    have : (univ.filter fun a : α => orderOf a = Fintype.card α).Nonempty :=
      card_pos.1 <| by
        rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl]
        exact totient_pos (Fintype.card_pos_iff.2 ⟨1⟩)
    let ⟨x, hx⟩ := this
    ⟨Group.Generator.of_orderOf_eq_card x (Finset.mem_filter.1 hx).2⟩
#align is_cyclic_of_card_pow_eq_one_le isCyclic_of_card_pow_eq_one_le

theorem isAddCyclic_of_card_pow_eq_one_le {α} [AddGroup α] [DecidableEq α] [Fintype α]
    (hn : ∀ n : ℕ, 0 < n → (univ.filter fun a : α => n • a = 0).card ≤ n) : IsAddCyclic α := by
  obtain ⟨g, hg⟩ := (@isCyclic_of_card_pow_eq_one_le (Multiplicative α) _ _ (_) hn)
  exact ⟨⟨g, hg⟩⟩
#align is_add_cyclic_of_card_pow_eq_one_le isAddCyclic_of_card_pow_eq_one_le

attribute [to_additive existing isCyclic_of_card_pow_eq_one_le] isAddCyclic_of_card_pow_eq_one_le

end Totient

theorem IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : ℕ}
    (hd : d ∣ Fintype.card α) : (univ.filter fun a : α => orderOf a = d).card = totient d := by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd
#align is_cyclic.card_order_of_eq_totient IsCyclic.card_orderOf_eq_totient

theorem IsAddCyclic.card_orderOf_eq_totient {α : Type*} [AddGroup α] [IsAddCyclic α]
    [Fintype α] {d : ℕ} (hd : d ∣ Fintype.card α) :
    (univ.filter fun a : α => addOrderOf a = d).card = totient d := by
  obtain ⟨g, hg⟩ := id ‹IsAddCyclic α›
  apply @IsCyclic.card_orderOf_eq_totient (Multiplicative α) _ ⟨⟨g, hg⟩⟩ (_) _ hd
#align is_add_cyclic.card_order_of_eq_totient IsAddCyclic.card_orderOf_eq_totient

attribute [to_additive existing IsCyclic.card_orderOf_eq_totient]
  IsAddCyclic.card_orderOf_eq_totient

/-- A finite group of prime order is simple. -/
@[to_additive "A finite group of prime order is simple."]
theorem isSimpleGroup_of_prime_card {α : Type u} [Group α] [Fintype α] {p : ℕ} [hp : Fact p.Prime]
    (h : Fintype.card α = p) : IsSimpleGroup α :=
  have : Nontrivial α := by
    have h' := Nat.Prime.one_lt (Fact.out (p := p.Prime))
    rw [← h] at h'
    exact Fintype.one_lt_card_iff_nontrivial.1 h'
  ⟨fun H _ => by
    classical
      have hcard := card_subgroup_dvd_card H
      rw [h, dvd_prime (Fact.out (p := p.Prime))] at hcard
      refine' hcard.imp (fun h1 => _) fun hp => _
      · haveI := Fintype.card_le_one_iff_subsingleton.1 (le_of_eq h1)
        apply eq_bot_of_subsingleton
      · exact eq_top_of_card_eq _ (hp.trans h.symm)⟩
#align is_simple_group_of_prime_card isSimpleGroup_of_prime_card
#align is_simple_add_group_of_prime_card isSimpleAddGroup_of_prime_card

end Cyclic

section QuotientCenter

open Subgroup

variable {G : Type*} {H : Type*} [Group G] [Group H]

/-- A group is commutative if the quotient by the center is cyclic.
  Also see `commGroup_of_cycle_center_quotient` for the `CommGroup` instance. -/
@[to_additive commutative_of_add_cyclic_center_quotient
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
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x m, hm, inv_mul_self])
  have hb : y ^ (-n) * b ∈ center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x n, hn, inv_mul_self])
  calc
    a * b = y ^ m * (y ^ (-m) * a * y ^ n) * (y ^ (-n) * b) := by simp [mul_assoc]
    _ = y ^ m * (y ^ n * (y ^ (-m) * a)) * (y ^ (-n) * b) := by rw [mem_center_iff.1 ha]
    _ = y ^ m * y ^ n * y ^ (-m) * (a * (y ^ (-n) * b)) := by simp [mul_assoc]
    _ = y ^ m * y ^ n * y ^ (-m) * (y ^ (-n) * b * a) := by rw [mem_center_iff.1 hb]
    _ = b * a := by group
#align commutative_of_cyclic_center_quotient commutative_of_cyclic_center_quotient
#align commutative_of_add_cyclic_center_quotient commutative_of_add_cyclic_center_quotient

/-- A group is commutative if the quotient by the center is cyclic. -/
@[to_additive commutativeOfAddCycleCenterQuotient
      "A group is commutative if the quotient by the center is cyclic."]
def commGroupOfCycleCenterQuotient [IsCyclic H] (f : G →* H) (hf : f.ker ≤ center G) :
    CommGroup G :=
  { show Group G by infer_instance with mul_comm := commutative_of_cyclic_center_quotient f hf }
#align comm_group_of_cycle_center_quotient commGroupOfCycleCenterQuotient
#align commutative_of_add_cycle_center_quotient commutativeOfAddCycleCenterQuotient

end QuotientCenter

namespace IsSimpleGroup

section CommGroup

variable [CommGroup α] [IsSimpleGroup α]

@[to_additive IsSimpleAddGroup.isAddCyclic]
instance (priority := 100) isCyclic : IsCyclic α := by
  cases' subsingleton_or_nontrivial α with hi hi <;> haveI := hi
  · apply isCyclic_of_subsingleton
  · obtain ⟨g, hg⟩ := exists_ne (1 : α)
    refine' ⟨⟨g, fun x => _⟩⟩
    cases' IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers g) with hb ht
    · exfalso
      apply hg
      rw [← Subgroup.mem_bot, ← hb]
      apply Subgroup.mem_zpowers
    · rw [ht]
      apply Subgroup.mem_top
#align is_simple_group.is_cyclic IsSimpleGroup.isCyclic
#align is_simple_add_group.is_add_cyclic IsSimpleAddGroup.isAddCyclic

@[to_additive]
theorem prime_card [Fintype α] : (Fintype.card α).Prime := by
  have h0 : 0 < Fintype.card α := Fintype.card_pos_iff.2 (by infer_instance)
  obtain ⟨g⟩ := IsCyclic.exists_generator (α := α)
  rw [Nat.prime_def_lt'']
  refine' ⟨Fintype.one_lt_card_iff_nontrivial.2 inferInstance, fun n hn => _⟩
  refine' (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers ((g : α) ^ n))).symm.imp _ _
  · intro h
    have hgo := orderOf_pow (n := n) (g : α)
    have := Group.Generator.orderOf_eq_card ⟨(g : α) ^ n, (h ▸ Subgroup.mem_top ·)⟩
    rw [g.orderOf_eq_card, Nat.gcd_eq_right_iff_dvd.1 hn, this, eq_comm,
      Nat.div_eq_iff_eq_mul_left (Nat.pos_of_dvd_of_pos hn h0) hn] at hgo
    exact (mul_left_cancel₀ (ne_of_gt h0) ((mul_one (Fintype.card α)).trans hgo)).symm
  · intro h
    apply le_antisymm (Nat.le_of_dvd h0 hn)
    rw [← g.orderOf_eq_card]
    apply orderOf_le_of_pow_eq_one (Nat.pos_of_dvd_of_pos hn h0)
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_zpowers _
#align is_simple_group.prime_card IsSimpleGroup.prime_card
#align is_simple_add_group.prime_card IsSimpleAddGroup.prime_card

end CommGroup

end IsSimpleGroup

@[to_additive AddCommGroup.is_simple_iff_isAddCyclic_and_prime_card]
theorem CommGroup.is_simple_iff_isCyclic_and_prime_card [Fintype α] [CommGroup α] :
    IsSimpleGroup α ↔ IsCyclic α ∧ (Fintype.card α).Prime := by
  constructor
  · intro h
    exact ⟨IsSimpleGroup.isCyclic, IsSimpleGroup.prime_card⟩
  · rintro ⟨_, hp⟩
    haveI : Fact (Fintype.card α).Prime := ⟨hp⟩
    exact isSimpleGroup_of_prime_card rfl
#align comm_group.is_simple_iff_is_cyclic_and_prime_card CommGroup.is_simple_iff_isCyclic_and_prime_card
#align add_comm_group.is_simple_iff_is_add_cyclic_and_prime_card AddCommGroup.is_simple_iff_isAddCyclic_and_prime_card

section Exponent

open Monoid

@[to_additive]
theorem Group.Generator.exponent_eq_orderOf [Group α] (g : Group.Generator α) :
    Monoid.exponent α = orderOf (g : α) := by
  refine dvd_antisymm ?_ <| Monoid.order_dvd_exponent (g : α)
  refine exponent_dvd_of_forall_pow_eq_one α (orderOf (g : α)) fun x ↦ ?_
  obtain ⟨n, rfl⟩ := g.generates x
  exact zpow_pow_orderOf

@[to_additive]
theorem IsCyclic.exponent_eq_card [Group α] [IsCyclic α] [Fintype α] :
    exponent α = Fintype.card α := by
  obtain ⟨g⟩ := IsCyclic.exists_generator (α := α)
  apply Nat.dvd_antisymm
  · rw [← lcm_order_eq_exponent, Finset.lcm_dvd_iff]
    exact fun b _ => orderOf_dvd_card_univ
  rw [← g.orderOf_eq_card]
  exact order_dvd_exponent _
#align is_cyclic.exponent_eq_card IsCyclic.exponent_eq_card
#align is_add_cyclic.exponent_eq_card IsAddCyclic.exponent_eq_card


@[to_additive]
theorem IsCyclic.of_exponent_eq_card [CommGroup α] [Fintype α] (h : exponent α = Fintype.card α) :
    IsCyclic α where
  exists_generator :=
    let ⟨g, _, hg⟩ := Finset.mem_image.mp <|
      (exponent_eq_max'_orderOf (G := α)).symm ▸ Finset.max'_mem _ _
    ⟨Group.Generator.of_orderOf_eq_card g (hg ▸ h)⟩
#align is_cyclic.of_exponent_eq_card IsCyclic.of_exponent_eq_card
#align is_add_cyclic.of_exponent_eq_card IsAddCyclic.of_exponent_eq_card

@[to_additive]
theorem IsCyclic.iff_exponent_eq_card [CommGroup α] [Fintype α] :
    IsCyclic α ↔ exponent α = Fintype.card α :=
  ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩
#align is_cyclic.iff_exponent_eq_card IsCyclic.iff_exponent_eq_card
#align is_add_cyclic.iff_exponent_eq_card IsAddCyclic.iff_exponent_eq_card

@[to_additive]
theorem IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] :
    exponent α = 0 :=
  let ⟨g⟩ := IsCyclic.exists_generator (α := α)
  exponent_eq_zero_of_order_zero <| g.orderOf_eq_zero
#align is_cyclic.exponent_eq_zero_of_infinite IsCyclic.exponent_eq_zero_of_infinite
#align is_add_cyclic.exponent_eq_zero_of_infinite IsAddCyclic.exponent_eq_zero_of_infinite

/-- `1` as a generator of `ZMod n` as an additive group. -/
def ZMod.one_generator (n : ℕ) : AddGroup.Generator (ZMod n) :=
  ⟨1, fun n ↦ ⟨n, by simp⟩⟩

instance ZMod.instIsAddCyclic (n : ℕ) : IsAddCyclic (ZMod n) where
  exists_generator := ⟨ZMod.one_generator n⟩

protected theorem ZMod.exponent (n : ℕ) : AddMonoid.exponent (ZMod n) = n := by
  rw [(ZMod.one_generator n).addOrderOf_eq_card]

end Exponent
