/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Torsion groups

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `Monoid.IsTorsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `CommGroup.torsion G`, the torsion subgroup of an abelian group `G`
* `CommMonoid.torsion G`, the above stated for commutative monoids
* `Monoid.IsTorsionFree`, asserting no nontrivial elements have finite order in `G`
* `AddMonoid.IsTorsion` and `AddMonoid.IsTorsionFree` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `Monoid.IsTorsion.group`), but since
the definition can be stated on monoids it is implemented on `Monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/


variable {G H : Type*}

namespace Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def IsTorsion :=
  ∀ g : G, IsOfFinOrder g

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp) "An additive monoid is not a torsion monoid if it
  has an element of infinite order."]
theorem not_isTorsion_iff : ¬IsTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g := by
  rw [IsTorsion, not_forall]

end Monoid

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def IsTorsion.group [Monoid G] (tG : IsTorsion G) : Group G :=
  { ‹Monoid G› with
    inv := fun g => g ^ (orderOf g - 1)
    inv_mul_cancel := fun g => by
      rw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h =>
  Submonoid.isOfFinOrder_coe.1 <| tG h

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive AddIsTorsion.of_surjective
      "The image of a surjective additive torsion group homomorphism is torsion."]
theorem IsTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsTorsion G) :
    IsTorsion H := fun h => by
  obtain ⟨g, hg⟩ := hf h
  rw [← hg]
  exact f.isOfFinOrder (tG g)

/-- Torsion groups are closed under extensions. -/
@[to_additive AddIsTorsion.extension_closed "Additive torsion groups are closed under extensions."]
theorem IsTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsTorsion H)
    (tN : IsTorsion N) : IsTorsion G := fun g => by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr <| ⟨ngn * nn, mul_pos ngnpos nnpos, by
      rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive AddIsTorsion.quotient_iff
      "The image of a quotient is additively torsion iff the group is torsion."]
theorem IsTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsTorsion N) : IsTorsion H ↔ IsTorsion G :=
  ⟨fun tH => IsTorsion.extension_closed hN tH tN, fun tG => IsTorsion.of_surjective hf tG⟩

/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion
      "If a group exponent exists, the group is additively torsion."]
theorem ExponentExists.isTorsion (h : ExponentExists G) : IsTorsion G := fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponentExists
      "The group exponent exists for any bounded additive torsion group."]
theorem IsTorsion.exponentExists (tG : IsTorsion G)
    (bounded : (Set.range fun g : G => orderOf g).Finite) : ExponentExists G :=
  exponent_ne_zero.mp <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g => (tG g).orderOf_pos).mpr bounded

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_finite "Finite additive groups are additive torsion groups."]
theorem isTorsion_of_finite [Finite G] : IsTorsion G :=
  ExponentExists.isTorsion .of_finite

end Group

section CommGroup
variable [CommGroup G]

/-- A nontrivial torsion abelian group is not torsion-free. -/
@[to_additive "A nontrivial additive torsion abelian group is not torsion-free."]
lemma not_isMulTorsionFree_of_isTorsion [Nontrivial G] (hG : IsTorsion G) : ¬ IsMulTorsionFree G :=
  not_isMulTorsionFree_iff_isOfFinOrder.2 <| let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

/-- A nontrivial torsion-free abelian group is not torsion. -/
@[to_additive "A nontrivial additive torsion-free abelian group is not torsion."]
lemma not_isTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] : ¬ IsTorsion G :=
  (not_isMulTorsionFree_of_isTorsion · ‹_›)

end CommGroup

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

namespace AddMonoid

/-- A module whose scalars are additively torsion is additively torsion. -/
theorem IsTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsTorsion R) : IsTorsion M :=
  fun f =>
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr <| by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

/-- A module with a finite ring of scalars is additively torsion. -/
theorem IsTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsTorsion M :=
  (is_add_torsion_of_finite : IsTorsion R).module_of_torsion _ _

end AddMonoid

end Module

section CommMonoid

variable (G) [CommMonoid G]

namespace CommMonoid

/-- The torsion submonoid of a commutative monoid.

(Note that by `Monoid.IsTorsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive addTorsion "The torsion submonoid of an additive commutative monoid."]
def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

variable {G}

/-- Torsion submonoids are torsion. -/
@[to_additive "Additive torsion submonoids are additively torsion."]
theorem torsion.isTorsion : IsTorsion <| torsion G := fun ⟨x, n, npos, hn⟩ =>
  ⟨n, npos,
    Subtype.ext <| by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one, SubmonoidClass.coe_pow, Subtype.coe_mk,
        (isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

variable (G) (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-primary component is the submonoid of elements with order prime-power of `p`. -/
@[to_additive (attr := simps)
      "The `p`-primary component is the submonoid of elements with additive
      order prime-power of `p`."]
def primaryComponent : Submonoid G where
  carrier := { g | ∃ n : ℕ, orderOf g = p ^ n }
  one_mem' := ⟨0, by rw [pow_zero, orderOf_one]⟩
  mul_mem' hg₁ hg₂ :=
    exists_orderOf_eq_prime_pow_iff.mpr <| by
      obtain ⟨m, hm⟩ := exists_orderOf_eq_prime_pow_iff.mp hg₁
      obtain ⟨n, hn⟩ := exists_orderOf_eq_prime_pow_iff.mp hg₂
      exact
        ⟨m + n, by
          rw [mul_pow, pow_add, pow_mul, hm, one_pow, Monoid.one_mul, mul_comm, pow_mul, hn,
            one_pow]⟩

variable {G} {p}

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive primaryComponent.exists_orderOf_eq_prime_nsmul
  "Elements of the `p`-primary component have additive order `p^n` for some `n`"]
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by
      obtain ⟨_, hn⟩ := g.property
      rw [orderOf_submonoid g] at hn
      exact ⟨_, hn⟩

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive "The `p`- and `q`-primary components are disjoint for `p ≠ q`."]
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr <| by
    rintro g ⟨_ | n, hn⟩ ⟨n', hn'⟩
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · exact
        absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn.symm.trans hn')) hne

end CommMonoid

open CommMonoid (torsion)

namespace Monoid.IsTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp) "The additive torsion submonoid of an additive torsion monoid is `⊤`."]
theorem torsion_eq_top (tG : IsTorsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive "An additive torsion monoid is isomorphic to its torsion submonoid."]
def torsionMulEquiv (tG : IsTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

@[to_additive]
theorem torsionMulEquiv_apply (tG : IsTorsion G) (a : torsion G) :
    tG.torsionMulEquiv a = MulEquiv.submonoidCongr tG.torsion_eq_top a :=
  rfl

@[to_additive]
theorem torsionMulEquiv_symm_apply_coe (tG : IsTorsion G) (a : G) :
    tG.torsionMulEquiv.symm a = ⟨Submonoid.topEquiv.symm a, tG _⟩ :=
  rfl

end Monoid.IsTorsion

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[to_additive (attr := simp) AddCommMonoid.Torsion.ofTorsion
      "Additive torsion submonoids of an additive torsion submonoid are
      isomorphic to the submonoid."]
def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoid.IsTorsion.torsionMulEquiv CommMonoid.torsion.isTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive "The torsion subgroup of an additive abelian group."]
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
      "The additive torsion submonoid of an abelian group equals the torsion
      subgroup as a submonoid."]
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl

@[to_additive]
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
lemma isMulTorsionFree_iff_torsion_eq_bot : IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder, eq_bot_iff, SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-primary component is the subgroup of elements with order prime-power of `p`. -/
@[to_additive (attr := simps!)
      "The `p`-primary component is the subgroup of elements with additive order
      prime-power of `p`."]
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨n, hn⟩ => ⟨n, (orderOf_inv g).trans hn⟩ }

variable {G} {p}

/-- The `p`-primary component is a `p` group. -/
theorem primaryComponent.isPGroup : IsPGroup p <| primaryComponent G p := fun g =>
  (propext exists_orderOf_eq_prime_pow_iff.symm).mpr
    (CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow g)

end CommGroup

end CommGroup

namespace Monoid
section Monoid
variable (G) [Monoid G]

/-- A predicate on a monoid saying that only 1 is of finite order.

This definition is mathematically incorrect for monoids which are not groups.
Please use `IsMulTorsionFree` instead. -/
@[to_additive "A predicate on an additive monoid saying that only 0 is of finite order.

This definition is mathematically incorrect for monoids which are not groups.
Please use `IsAddTorsionFree` instead. "]
def IsTorsionFree :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g

attribute [deprecated IsMulTorsionFree (since := "2025-04-23")] Monoid.IsTorsionFree
attribute [deprecated IsAddTorsionFree (since := "2025-04-23")] AddMonoid.IsTorsionFree

variable {G}

set_option linter.deprecated false in
/-- A nontrivial monoid is not torsion-free if any nontrivial element has finite order. -/
@[to_additive (attr := deprecated not_isMulTorsionFree_iff_isOfFinOrder (since := "2025-04-23"))
"An additive monoid is not torsion free if any nontrivial element has finite order."]
theorem not_isTorsionFree_iff : ¬IsTorsionFree G ↔ ∃ g : G, g ≠ 1 ∧ IsOfFinOrder g := by
  simp_rw [IsTorsionFree, Ne, not_forall, Classical.not_not, exists_prop]

set_option linter.deprecated false in
@[to_additive (attr := deprecated Subsingleton.to_isMulTorsionFree (since := "2025-04-23"))]
lemma isTorsionFree_of_subsingleton [Subsingleton G] : IsTorsionFree G :=
  fun _a ha _ => ha <| Subsingleton.elim _ _

set_option linter.deprecated false in
@[to_additive
  (attr := deprecated CommGroup.isMulTorsionFree_iff_torsion_eq_bot (since := "2025-04-23"))]
lemma isTorsionFree_iff_torsion_eq_bot {G} [CommGroup G] :
    IsTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [IsTorsionFree, eq_bot_iff, SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

end Monoid

section Group
variable [Group G]

set_option linter.deprecated false in
/-- A nontrivial torsion group is not torsion-free. -/
@[to_additive (attr := deprecated not_isMulTorsionFree_of_isTorsion (since := "2025-04-23"))
"A nontrivial additive torsion group is not torsion-free."]
theorem IsTorsion.not_torsion_free [hN : Nontrivial G] : IsTorsion G → ¬IsTorsionFree G := fun tG =>
  not_isTorsionFree_iff.mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, hx, tG x⟩

set_option linter.deprecated false in
/-- A nontrivial torsion-free group is not torsion. -/
@[to_additive (attr := deprecated not_isTorsion_of_isMulTorsionFree (since := "2025-04-23"))
"A nontrivial torsion-free additive group is not torsion."]
theorem IsTorsionFree.not_torsion [hN : Nontrivial G] : IsTorsionFree G → ¬IsTorsion G := fun tfG =>
  (not_isTorsion_iff _).mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, (tfG x) hx⟩

set_option linter.deprecated false in
/-- Subgroups of torsion-free groups are torsion-free. -/
@[to_additive (attr := deprecated Subgroup.instIsMulTorsionFree (since := "2025-04-23"))
"Subgroups of additive torsion-free groups are additively torsion-free."]
theorem IsTorsionFree.subgroup (tG : IsTorsionFree G) (H : Subgroup G) : IsTorsionFree H :=
  fun h hne ↦ Submonoid.isOfFinOrder_coe.not.1 <| tG h <| by norm_cast

set_option linter.deprecated false in
/-- Direct products of torsion free groups are torsion free. -/
@[to_additive (attr := deprecated Pi.instIsMulTorsionFree (since := "2025-04-23"))
  AddMonoid.IsTorsionFree.prod
      "Direct products of additive torsion free groups are torsion free."]
theorem IsTorsionFree.prod {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]
    (tfGs : ∀ i, IsTorsionFree (Gs i)) : IsTorsionFree <| ∀ i, Gs i := fun w hne h =>
  hne <|
    funext fun i => Classical.not_not.mp <| mt (tfGs i (w i)) <| Classical.not_not.mpr <| h.apply i

end Group

section CommGroup

open Monoid (IsTorsionFree)

open CommGroup (torsion)

variable (G) [CommGroup G]

/-- Quotienting a group by its torsion subgroup yields a torsion-free group. -/
@[to_additive
"Quotienting a group by its additive torsion subgroup yields an additive torsion-free group."]
instance _root_.QuotientGroup.instIsMulTorsionFree : IsMulTorsionFree <| G ⧸ torsion G := by
  refine .of_not_isOfFinOrder fun g hne hfin ↦ hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)

set_option linter.deprecated false in
/-- Quotienting a group by its torsion subgroup yields a torsion free group. -/
@[to_additive
  (attr := deprecated QuotientGroup.instIsMulTorsionFree (since := "2025-04-23"))
"Quotienting a group by its additive torsion subgroup yields an additive torsion free group."]
theorem IsTorsionFree.quotient_torsion : IsTorsionFree <| G ⧸ torsion G := fun g hne hfin =>
  hne <| by
    obtain ⟨g⟩ := g
    obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
    obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
    exact
      (QuotientGroup.eq_one_iff g).mpr
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)

end CommGroup
end Monoid

namespace AddMonoid

set_option linter.deprecated false in
@[deprecated noZeroSMulDivisors_nat_iff_isAddTorsionFree (since := "2025-04-23")]
lemma isTorsionFree_iff_noZeroSMulDivisors_nat {M : Type*} [AddMonoid M] :
    IsTorsionFree M ↔ NoZeroSMulDivisors ℕ M := by
  simp_rw [AddMonoid.IsTorsionFree, isOfFinAddOrder_iff_nsmul_eq_zero, not_exists, not_and,
    pos_iff_ne_zero, noZeroSMulDivisors_iff, forall_swap (β := ℕ)]
  exact forall₂_congr fun _ _ ↦ by tauto

set_option linter.deprecated false in
@[deprecated noZeroSMulDivisors_int_iff_isAddTorsionFree (since := "2025-04-23")]
lemma isTorsionFree_iff_noZeroSMulDivisors_int [SubtractionMonoid G] :
    IsTorsionFree G ↔ NoZeroSMulDivisors ℤ G := by
  simp_rw [AddMonoid.IsTorsionFree, isOfFinAddOrder_iff_zsmul_eq_zero, not_exists, not_and,
    noZeroSMulDivisors_iff, forall_swap (β := ℤ)]
  exact forall₂_congr fun _ _ ↦ by tauto

set_option linter.deprecated false in
@[deprecated IsAddTorsionFree.of_noZeroSMulDivisors_nat (since := "2025-04-23")]
lemma IsTorsionFree.of_noZeroSMulDivisors {M : Type*} [AddMonoid M] [NoZeroSMulDivisors ℕ M] :
    IsTorsionFree M := isTorsionFree_iff_noZeroSMulDivisors_nat.2 ‹_›

@[deprecated IsAddTorsionFree.to_noZeroSMulDivisors_nat (since := "2025-04-23")]
alias ⟨IsTorsionFree.noZeroSMulDivisors_nat, _⟩ := isTorsionFree_iff_noZeroSMulDivisors_nat
@[deprecated IsAddTorsionFree.to_noZeroSMulDivisors_int (since := "2025-04-23")]
alias ⟨IsTorsionFree.noZeroSMulDivisors_int, _⟩ := isTorsionFree_iff_noZeroSMulDivisors_int

end AddMonoid

section AddCommGroup

instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) :=
  letI : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  inferInstanceAs (Module R (M ⧸ this))

end AddCommGroup

section

variable {M : Type*} [CommMonoid M] [HasDistribNeg M]

theorem neg_one_mem_torsion : -1 ∈ CommMonoid.torsion M :=
  ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

end
