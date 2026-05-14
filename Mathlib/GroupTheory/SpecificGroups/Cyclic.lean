/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Aut
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Hom.TypeTags
import Mathlib.Algebra.Order.Monoid.TypeTags
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Units
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Further properties of cyclic groups

## Main statements

* `isSimpleGroup_of_prime_card`, `IsSimpleGroup.isCyclic`,
  and `IsSimpleGroup.prime_card` classify finite simple abelian groups.
* `IsCyclic.card_orderOf_eq_totient` computes the number of elements of given order
  in a cyclic group.
* `IsCyclic.exponent_eq_card`: For a finite cyclic group `G`, the exponent is equal to
  the group's cardinality.
* `IsCyclic.exponent_eq_zero_of_infinite`: Infinite cyclic groups have exponent zero.
* `IsCyclic.iff_exponent_eq_card`: A finite commutative group is cyclic iff its exponent
  is equal to its cardinality.
* `IsCyclic.card_mulAut`, cardinality of automorphisms of a finite group.
* `commGroupOfCyclicCenterQuotient`: if the quotient of a group by
  its center is cyclic, then the group is commutative.
* `Group.isCyclic_prod_iff`: the product of two finite cyclic groups is cyclic
  if and only if their orders are relatively prime.

## Tags

cyclic group, exponent, totient
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

variable [Group α] [Group G] [Group G']

open Finset Nat

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
          fun _ _ h => Subtype.ext (Subtype.mk.inj h))
      _ = #{b : α | b ^ orderOf a = 1} := Fintype.card_ofFinset _ _)

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
      gcongr with m hm
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
@[to_additive (attr := implicit_reducible)
/-- A group is commutative if the quotient by the center is cyclic. -/]
def commGroupOfCyclicCenterQuotient [IsCyclic G'] (f : G →* G') (hf : f.ker ≤ center G) :
    CommGroup G where
  mul_comm := commutative_of_cyclic_center_quotient f hf

end QuotientCenter

namespace IsSimpleGroup

section CommSimpleGroup

variable [CommGroup α] [IsSimpleGroup α]

@[to_additive]
instance (priority := 100) isCyclic : IsCyclic α := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_ne (1 : α)
  have : Subgroup.zpowers g = ⊤ :=
    (eq_bot_or_eq_top (Subgroup.zpowers g)).resolve_left (Subgroup.zpowers_ne_bot.2 hg)
  exact ⟨⟨g, (Subgroup.eq_top_iff' _).1 this⟩⟩

@[to_additive]
theorem prime_card : (Nat.card α).Prime := by
  have hα : Nontrivial α := IsSimpleGroup.toNontrivial
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  replace hα : Nat.card α ≠ 1 := by contrapose! hα; exact (Nat.card_eq_one_iff_unique.mp hα).1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg] at hα ⊢
  have h (n : ℕ) : orderOf g ∣ n ∨ n.Coprime (orderOf g) := by
    refine (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers (g ^ n))).imp ?_ fun h ↦ ?_
    · simp [orderOf_dvd_iff_pow_eq_one]
    · simp only [Nat.coprime_iff_gcd_eq_one]
      have hgn : g ∈ Subgroup.zpowers (g ^ n) := by simp_all only [ne_eq, orderOf_eq_one_iff,
        Subgroup.mem_top]
      exact mem_zpowers_pow_iff.mp hgn
  apply Nat.prime_of_coprime
  · refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, hα⟩
    contrapose! h
    exact ⟨37, by simp [h]⟩
  · intro n hn hn0
    exact ((h n).resolve_left (Nat.not_dvd_of_pos_of_lt (Nat.pos_iff_ne_zero.mpr hn0) hn)).symm

/-- A commutative simple group is a finite group. -/
@[to_additive /-- A commutative simple group is a finite group. -/]
theorem finite : Finite α := Nat.finite_of_card_ne_zero prime_card.ne_zero

end CommSimpleGroup

end IsSimpleGroup

open scoped IsMulCommutative in
@[to_additive]
theorem Group.is_simple_iff_prime_card [Group α] [IsMulCommutative α] :
    IsSimpleGroup α ↔ (Nat.card α).Prime :=
  ⟨fun h ↦ h.prime_card, fun h ↦ isSimpleGroup_of_prime_card (hp := ⟨h⟩) rfl⟩

@[to_additive]
theorem CommGroup.is_simple_iff_prime_card [CommGroup α] : IsSimpleGroup α ↔ (Nat.card α).Prime :=
  Group.is_simple_iff_prime_card

@[deprecated (since := "2025-11-19")]
alias CommGroup.is_simple_iff_isCyclic_and_prime_card := CommGroup.is_simple_iff_prime_card

section SpecificInstances

instance : IsAddCyclic ℤ := ⟨1, fun n ↦ ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩

instance ZMod.instIsAddCyclic (n : ℕ) : IsAddCyclic (ZMod n) :=
  isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective

instance ZMod.instIsSimpleAddGroup {p : ℕ} [hp : Fact p.Prime] : IsSimpleAddGroup (ZMod p) :=
  AddCommGroup.is_simple_iff_prime_card.2 (by simpa using hp.out)

end SpecificInstances

section EquivInt

/-- A linearly-ordered additive abelian group is cyclic iff it is isomorphic to `ℤ` as an ordered
additive monoid. -/
lemma LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int {A : Type*}
    [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A] [Nontrivial A] :
    IsAddCyclic A ↔ Nonempty (A ≃+o ℤ) := by
  refine ⟨?_, fun ⟨e⟩ ↦ e.isAddCyclic.mpr inferInstance⟩
  rintro ⟨g, hs⟩
  have h_ne : g ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨m, rfl⟩ := hs a
    aesop
  wlog hg' : 0 < g
  · exact this (g := -g) (by simpa using neg_surjective.comp hs) (by grind) (by grind)
  have hi : (fun n : ℤ ↦ n • g).Injective := injective_zsmul_iff_not_isOfFinAddOrder.mpr
      <| not_isOfFinAddOrder_of_isAddTorsionFree h_ne
  exact ⟨.symm { Equiv.ofBijective _ ⟨hi, hs⟩ with
    map_add' := add_zsmul g
    map_le_map_iff' := zsmul_le_zsmul_iff_left hg' }⟩

/-- A linearly-ordered abelian group is cyclic iff it is isomorphic to `Multiplicative ℤ` as an
ordered monoid. -/
lemma LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [Nontrivial G] :
    IsCyclic G ↔ Nonempty (G ≃*o Multiplicative ℤ) := by
  rw [← isAddCyclic_additive_iff, LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int,
    OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr]

end EquivInt

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
  have : ∃ a < 3, p ^ a = orderOf g := by
    simpa [Nat.divisors_prime_pow hp 2] using this
  obtain ⟨a, ha, ha'⟩ := by simpa using this
  interval_cases a
  · exact False.elim <| hg <| orderOf_eq_one_iff.mp <| by simp_all
  · simp_all
  · exact False.elim <| h_cyc <| isCyclic_of_orderOf_eq_card g <| by lia

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

section addGenerator
variable [AddGroup G] {g : G} (hg : ∀ x, x ∈ zmultiples g) {n : ℕ} (hn : Nat.card G = n)

/-- The isomorphism from `ZMod n` to any additive group of `Nat.card` equal to `n`
generated by a single element `g` which sends `1` to `g`.
See `zmodAddCyclicAddEquiv` for a version which doesn't take an explicit generator,
and instead picks one out with the axiom of choice. -/
noncomputable def zmodAddEquivOfGenerator : ZMod n ≃+ G :=
  have kereq : zmultiples (n : ℤ) = ((zmultiplesHom G) g).ker := by
    rw [zmultiplesHom_ker_eq, ← Nat.card_zmultiples, ← hn,
      Nat.card_congr (Equiv.subtypeUnivEquiv hg)]
  (Int.quotientZMultiplesNatEquivZMod n).symm.trans <|
    QuotientAddGroup.liftEquiv _ (φ := zmultiplesHom G g) hg kereq

@[simp]
theorem zmodAddEquivOfGenerator_apply_intCast (i : ℤ) :
    zmodAddEquivOfGenerator hg hn i = i • g := by
  change (ZMod.cast (i : ZMod n) : ℤ) • g = i • g
  rw [ZMod.coe_intCast, Int.emod_def, eq_comm, ← sub_eq_zero, sub_eq_add_neg, ← sub_zsmul,
    Int.sub_sub_self, mul_zsmul', natCast_zsmul, ← hn, card_nsmul_eq_zero', zsmul_zero]

@[simp]
theorem zmodAddEquivOfGenerator_symm_apply_zsmul (i : ℤ) :
    (zmodAddEquivOfGenerator hg hn).symm (i • g) = i := by
  rw [AddEquiv.symm_apply_eq, zmodAddEquivOfGenerator_apply_intCast]

@[simp]
theorem zmodAddEquivOfGenerator_apply_one : zmodAddEquivOfGenerator hg hn 1 = g := by
  simpa using zmodAddEquivOfGenerator_apply_intCast hg hn 1

@[simp]
theorem zmodAddEquivOfGenerator_symm_apply_generator :
    (zmodAddEquivOfGenerator hg hn).symm g = 1 := by
  simpa using zmodAddEquivOfGenerator_symm_apply_zsmul hg hn 1

end addGenerator

/-- An arbitrary isomorphism from `ZMod n` to any cyclic additive group of `Nat.card` equal to `n`.
See `zmodAddCyclicAddEquiv` for a version which doesn't require an explicit generator,
and instead picks one out with the axiom of choice. -/
noncomputable def zmodAddCyclicAddEquiv [AddGroup G] (h : IsAddCyclic G) :
    ZMod (Nat.card G) ≃+ G :=
  zmodAddEquivOfGenerator h.exists_generator.choose_spec rfl

/-- A commutative simple group is isomorphic to `ZMod p` from some prime `p`. -/
theorem exists_prime_addEquiv_ZMod [CommGroup G] [IsSimpleGroup G] :
    ∃ p : ℕ, Nat.Prime p ∧ Nonempty (Additive G ≃+ ZMod p) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  use orderOf g; rw [orderOf_eq_card_of_zpowers_eq_top hg]
  constructor
  · exact IsSimpleGroup.prime_card
  · exact ⟨(zmodAddCyclicAddEquiv (G := Additive G) inferInstance).symm⟩

section mulGenerator
variable [Group G] {g : G} (hg : ∀ x, x ∈ zpowers g) {n : ℕ} (hn : Nat.card G = n)

/-- The isomorphism from `Multiplicative (ZMod n)` to any multiplicative group
of `Nat.card` equal to `n` generated by a single element `g` which sends
`Multiplicative.ofAdd 1` to `g`.
See `zmodCyclicMulEquiv` for a version which doesn't take an explicit generator,
and instead picks one out with the axiom of choice. -/
noncomputable def zmodMulEquivOfGenerator : Multiplicative (ZMod n) ≃* G :=
  AddEquiv.toMultiplicative <| zmodAddEquivOfGenerator (G := Additive G) hg hn

@[simp]
theorem zmodMulEquivOfGenerator_apply_ofAdd_intCast (i : ℤ) :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd i) = g ^ i :=
  zmodAddEquivOfGenerator_apply_intCast (G := Additive G) hg hn i

@[simp]
theorem zmodMulEquivOfGenerator_symm_apply_zpow (i : ℤ) :
    (zmodMulEquivOfGenerator hg hn).symm (g ^ i) = Multiplicative.ofAdd (i : ZMod n) :=
  zmodAddEquivOfGenerator_symm_apply_zsmul (G := Additive G) hg hn i

@[simp]
theorem zmodMulEquivOfGenerator_apply_ofAdd_one :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd 1) = g :=
  zmodAddEquivOfGenerator_apply_one (G := Additive G) hg hn

@[simp]
theorem zmodMulEquivOfGenerator_symm_apply_generator :
    (zmodMulEquivOfGenerator hg hn).symm g = Multiplicative.ofAdd 1 :=
  zmodAddEquivOfGenerator_symm_apply_generator (G := Additive G) hg hn

end mulGenerator

/-- An arbitrary isomorphism from `Multiplicative (ZMod n)` to any cyclic group
of `Nat.card` equal to `n`.
See `zmodMulEquivOfGenerator` for a version which takes an explicit generator. -/
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

section Infinite

variable [Infinite G]

lemma zpowersHom_bijective [Group G] {g : G} (hg : zpowers g = ⊤) :
    Function.Bijective (zpowersHom G g) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
  simp [zpowersHom_ker_eq, ← infinite_zpowers, hg, Set.infinite_univ]

/-- The isomorphism between `Multiplicative ℤ` and the infinite cyclic group `G` sending
`Multiplicative.ofAdd 1` to the generator `g : G`. -/
@[simps! apply]
noncomputable def intEquivOfZPowersEqTop [Group G] (g : G) (hg : zpowers g = ⊤) :
    Multiplicative ℤ ≃* G :=
  .ofBijective (zpowersHom G g) (zpowersHom_bijective hg)

@[simp]
lemma intEquivOfZPowersEqTop_symm_self [Group G] {g : G} (hg : zpowers g = ⊤) :
    (intEquivOfZPowersEqTop g hg).symm g = Multiplicative.ofAdd 1 := by
  simp [MulEquiv.symm_apply_eq]

lemma mulintEquivOfZPowersEqTop_symm_apply_zpow [Group G] {g : G} (hg : zpowers g = ⊤) (k : ℤ) :
    (intEquivOfZPowersEqTop g hg).symm (g ^ k) = Multiplicative.ofAdd k := by
  simp [← ofAdd_zsmul]

lemma mulintEquivOfZPowersEqTop_strictMono [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : 1 < g) :
    StrictMono (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_lt_zpow_right hg1 hxy

lemma mulintEquivOfZPowersEqTop_strictAnti [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : g < 1) :
    StrictAnti (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_right_strictAnti hg1 hxy

/-- An infinite cyclic group is isomorphic to `Multiplicative ℤ`. -/
noncomputable
abbrev intCyclicMulEquiv [Group G] [IsCyclic G] : Multiplicative ℤ ≃* G :=
  intEquivOfZPowersEqTop _ (isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›).choose_spec

lemma zmultiplesHom_bijective [AddGroup G] {g : G} (hg : zmultiples g = ⊤) :
    Function.Bijective (zmultiplesHom G g) := by
  refine ⟨(AddMonoidHom.ker_eq_bot_iff _).mp ?_, AddMonoidHom.range_eq_top.mp hg⟩
  simp [zmultiplesHom_ker_eq, ← infinite_zmultiples, hg, Set.infinite_univ]

/-- The isomorphism between `ℤ` and the infinite cyclic group `G` sending
`1` to the generator `g : G`. -/
@[simps! apply]
noncomputable def intEquivOfZMultiplesEqTop [AddGroup G] (g : G) (hg : zmultiples g = ⊤) : ℤ ≃+ G :=
  .ofBijective (zmultiplesHom G g) (zmultiplesHom_bijective hg)

@[simp]
lemma intEquivOfZMultiplesEqTop_symm_self [AddGroup G] (g : G) (hg : zmultiples g = ⊤) :
    (intEquivOfZMultiplesEqTop g hg).symm g = 1 := by
  simp [AddEquiv.symm_apply_eq]

lemma intEquivOfZMultiplesEqTop_symm_apply_zsmul [AddGroup G]
    {g : G} (hg : zmultiples g = ⊤) (k : ℤ) :
    (intEquivOfZMultiplesEqTop g hg).symm (k • g) = k := by
  simp

/-- An infinite cyclic additive group is isomorphic to `ℤ`. -/
noncomputable
abbrev intCyclicAddEquiv [AddGroup G] [IsAddCyclic G] : ℤ ≃+ G :=
  intEquivOfZMultiplesEqTop _ (isAddCyclic_iff_exists_zmultiples_eq_top.mp ‹_›).choose_spec

end Infinite

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

include hg in
/-- Two group homomorphisms `G →* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two homomorphisms `G →+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G →* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H ↦ H g, fun H x ↦ ?_⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp <| hg x
  rw [← hn, map_zpow, map_zpow, H]

include hg in
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
def mulEquivOfOrderOfEq : G ≃* G' :=
  (monoidHomOfForallMemZpowers hg h.symm.dvd).toMulEquiv (monoidHomOfForallMemZpowers hg' h.dvd)
    (by simp [MonoidHom.eq_iff_eq_on_generator hg]) (by simp [MonoidHom.eq_iff_eq_on_generator hg'])

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
