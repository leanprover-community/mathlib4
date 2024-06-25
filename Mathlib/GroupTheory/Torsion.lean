/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.QuotientGroup

#align_import group_theory.torsion from "leanprover-community/mathlib"@"1f4705ccdfe1e557fc54a0ce081a05e33d2e6240"

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
#align monoid.is_torsion Monoid.IsTorsion
#align add_monoid.is_torsion AddMonoid.IsTorsion

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp) "An additive monoid is not a torsion monoid if it
  has an element of infinite order."]
theorem not_isTorsion_iff : ¬IsTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g := by
  rw [IsTorsion, not_forall]
#align monoid.not_is_torsion_iff Monoid.not_isTorsion_iff
#align add_monoid.not_is_torsion_iff AddMonoid.not_isTorsion_iff

end Monoid

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def IsTorsion.group [Monoid G] (tG : IsTorsion G) : Group G :=
  { ‹Monoid G› with
    inv := fun g => g ^ (orderOf g - 1)
    mul_left_inv := fun g => by
      erw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }
#align is_torsion.group IsTorsion.group
#align is_torsion.add_group IsTorsion.addGroup

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h =>
  Submonoid.isOfFinOrder_coe.1 <| tG h
#align is_torsion.subgroup IsTorsion.subgroup
#align is_torsion.add_subgroup IsTorsion.addSubgroup

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive AddIsTorsion.of_surjective
      "The image of a surjective additive torsion group homomorphism is torsion."]
theorem IsTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsTorsion G) :
    IsTorsion H := fun h => by
  obtain ⟨g, hg⟩ := hf h
  rw [← hg]
  exact f.isOfFinOrder (tG g)
#align is_torsion.of_surjective IsTorsion.of_surjective
#align add_is_torsion.of_surjective AddIsTorsion.of_surjective

/-- Torsion groups are closed under extensions. -/
@[to_additive AddIsTorsion.extension_closed "Additive torsion groups are closed under extensions."]
theorem IsTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsTorsion H)
    (tN : IsTorsion N) : IsTorsion G := fun g => by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := f.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr <| ⟨ngn * nn, mul_pos ngnpos nnpos, by
      rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩
#align is_torsion.extension_closed IsTorsion.extension_closed
#align add_is_torsion.extension_closed AddIsTorsion.extension_closed

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive AddIsTorsion.quotient_iff
      "The image of a quotient is additively torsion iff the group is torsion."]
theorem IsTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsTorsion N) : IsTorsion H ↔ IsTorsion G :=
  ⟨fun tH => IsTorsion.extension_closed hN tH tN, fun tG => IsTorsion.of_surjective hf tG⟩
#align is_torsion.quotient_iff IsTorsion.quotient_iff
#align add_is_torsion.quotient_iff AddIsTorsion.quotient_iff

/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion
      "If a group exponent exists, the group is additively torsion."]
theorem ExponentExists.isTorsion (h : ExponentExists G) : IsTorsion G := fun g => by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩
#align exponent_exists.is_torsion ExponentExists.isTorsion
#align exponent_exists.is_add_torsion ExponentExists.is_add_torsion

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponentExists
      "The group exponent exists for any bounded additive torsion group."]
theorem IsTorsion.exponentExists (tG : IsTorsion G)
    (bounded : (Set.range fun g : G => orderOf g).Finite) : ExponentExists G :=
  exponent_ne_zero.mp <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g => (tG g).orderOf_pos).mpr bounded
#align is_torsion.exponent_exists IsTorsion.exponentExists
#align is_add_torsion.exponent_exists IsAddTorsion.exponentExists

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_finite "Finite additive groups are additive torsion groups."]
theorem isTorsion_of_finite [Finite G] : IsTorsion G :=
  ExponentExists.isTorsion .of_finite
#align is_torsion_of_finite isTorsion_of_finite
#align is_add_torsion_of_finite is_add_torsion_of_finite

end Group

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

namespace AddMonoid

/-- A module whose scalars are additively torsion is additively torsion. -/
theorem IsTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsTorsion R) : IsTorsion M :=
  fun f =>
  isOfFinAddOrder_iff_nsmul_eq_zero.mpr <| by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [nsmul_eq_smul_cast R _ f, ← nsmul_one, hn, zero_smul]⟩
#align add_monoid.is_torsion.module_of_torsion AddMonoid.IsTorsion.module_of_torsion

/-- A module with a finite ring of scalars is additively torsion. -/
theorem IsTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsTorsion M :=
  (is_add_torsion_of_finite : IsTorsion R).module_of_torsion _ _
#align add_monoid.is_torsion.module_of_finite AddMonoid.IsTorsion.module_of_finite

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
  one_mem' := isOfFinOrder_one
  mul_mem' hx hy := hx.mul hy
#align comm_monoid.torsion CommMonoid.torsion
#align add_comm_monoid.add_torsion AddCommMonoid.addTorsion

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
#align comm_monoid.torsion.is_torsion CommMonoid.torsion.isTorsion
#align add_comm_monoid.add_torsion.is_torsion AddCommMonoid.addTorsion.isTorsion

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
#align comm_monoid.primary_component CommMonoid.primaryComponent
#align add_comm_monoid.primary_component AddCommMonoid.primaryComponent

variable {G} {p}

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive primaryComponent.exists_orderOf_eq_prime_nsmul
  "Elements of the `p`-primary component have additive order `p^n` for some `n`"]
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by simpa [primaryComponent] using g.property
#align comm_monoid.primary_component.exists_order_of_eq_prime_pow CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow
#align add_comm_monoid.primary_component.exists_order_of_eq_prime_nsmul AddCommMonoid.primaryComponent.exists_orderOf_eq_prime_nsmul

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive "The `p`- and `q`-primary components are disjoint for `p ≠ q`."]
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr <| by
    rintro g ⟨_ | n, hn⟩ ⟨n', hn'⟩
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · exact
        absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn.symm.trans hn')) hne
#align comm_monoid.primary_component.disjoint CommMonoid.primaryComponent.disjoint
#align add_comm_monoid.primary_component.disjoint AddCommMonoid.primaryComponent.disjoint

end CommMonoid

open CommMonoid (torsion)

namespace Monoid.IsTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp) "The additive torsion submonoid of an additive torsion monoid is `⊤`."]
theorem torsion_eq_top (tG : IsTorsion G) : torsion G = ⊤ := by ext; tauto
#align monoid.is_torsion.torsion_eq_top Monoid.IsTorsion.torsion_eq_top
#align add_monoid.is_torsion.torsion_eq_top AddMonoid.IsTorsion.torsion_eq_top

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive "An additive torsion monoid is isomorphic to its torsion submonoid."]
def torsionMulEquiv (tG : IsTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv
#align monoid.is_torsion.torsion_mul_equiv Monoid.IsTorsion.torsionMulEquiv
#align add_monoid.is_torsion.torsion_add_equiv AddMonoid.IsTorsion.torsionAddEquiv

@[to_additive]
theorem torsionMulEquiv_apply (tG : IsTorsion G) (a : torsion G) :
    tG.torsionMulEquiv a = MulEquiv.submonoidCongr tG.torsion_eq_top a :=
  rfl
#align monoid.is_torsion.torsion_mul_equiv_apply Monoid.IsTorsion.torsionMulEquiv_apply
#align add_monoid.is_torsion.torsion_add_equiv_apply AddMonoid.IsTorsion.torsionAddEquiv_apply

@[to_additive]
theorem torsionMulEquiv_symm_apply_coe (tG : IsTorsion G) (a : G) :
    tG.torsionMulEquiv.symm a = ⟨Submonoid.topEquiv.symm a, tG _⟩ :=
  rfl
#align monoid.is_torsion.torsion_mul_equiv_symm_apply_coe Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe
#align add_monoid.is_torsion.torsion_add_equiv_symm_apply_coe AddMonoid.IsTorsion.torsionAddEquiv_symm_apply_coe

end Monoid.IsTorsion

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[to_additive (attr := simp) AddCommMonoid.Torsion.ofTorsion
      "Additive torsion submonoids of an additive torsion submonoid are
      isomorphic to the submonoid."]
def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoid.IsTorsion.torsionMulEquiv CommMonoid.torsion.isTorsion
#align torsion.of_torsion Torsion.ofTorsion
#align add_comm_monoid.torsion.of_torsion AddCommMonoid.Torsion.ofTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive "The torsion subgroup of an additive abelian group."]
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx => IsOfFinOrder.inv hx }
#align comm_group.torsion CommGroup.torsion
#align add_comm_group.torsion AddCommGroup.torsion

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
      "The additive torsion submonoid of an abelian group equals the torsion
      subgroup as a submonoid."]
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl
#align comm_group.torsion_eq_torsion_submonoid CommGroup.torsion_eq_torsion_submonoid
#align add_comm_group.add_torsion_eq_add_torsion_submonoid AddCommGroup.add_torsion_eq_add_torsion_submonoid

@[to_additive]
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-primary component is the subgroup of elements with order prime-power of `p`. -/
@[to_additive (attr := simps!)
      "The `p`-primary component is the subgroup of elements with additive order
      prime-power of `p`."]
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨n, hn⟩ => ⟨n, (orderOf_inv g).trans hn⟩ }
#align comm_group.primary_component CommGroup.primaryComponent
#align add_comm_group.primary_component AddCommGroup.primaryComponent

variable {G} {p}

/-- The `p`-primary component is a `p` group. -/
theorem primaryComponent.isPGroup : IsPGroup p <| primaryComponent G p := fun g =>
  (propext exists_orderOf_eq_prime_pow_iff.symm).mpr
    (CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow g)
#align comm_group.primary_component.is_p_group CommGroup.primaryComponent.isPGroup

end CommGroup

end CommGroup

namespace Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that only 1 is of finite order. -/
@[to_additive "A predicate on an additive monoid saying that only 0 is of finite order."]
def IsTorsionFree :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g
#align monoid.is_torsion_free Monoid.IsTorsionFree
#align add_monoid.is_torsion_free AddMonoid.IsTorsionFree

variable {G}

/-- A nontrivial monoid is not torsion-free if any nontrivial element has finite order. -/
@[to_additive (attr := simp) "An additive monoid is not torsion free if any
  nontrivial element has finite order."]
theorem not_isTorsionFree_iff : ¬IsTorsionFree G ↔ ∃ g : G, g ≠ 1 ∧ IsOfFinOrder g := by
  simp_rw [IsTorsionFree, Ne, not_forall, Classical.not_not, exists_prop]
#align monoid.not_is_torsion_free_iff Monoid.not_isTorsionFree_iff
#align add_monoid.not_is_torsion_free_iff AddMonoid.not_isTorsionFree_iff

@[to_additive (attr := simp)]
lemma isTorsionFree_of_subsingleton [Subsingleton G] : IsTorsionFree G :=
  fun _a ha _ => ha <| Subsingleton.elim _ _

@[to_additive]
lemma isTorsionFree_iff_torsion_eq_bot {G} [CommGroup G] :
    IsTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [IsTorsionFree, eq_bot_iff, SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

end Monoid

section Group

open Monoid

variable [Group G]

/-- A nontrivial torsion group is not torsion-free. -/
@[to_additive AddMonoid.IsTorsion.not_torsion_free
      "A nontrivial additive torsion group is not torsion-free."]
theorem IsTorsion.not_torsion_free [hN : Nontrivial G] : IsTorsion G → ¬IsTorsionFree G := fun tG =>
  not_isTorsionFree_iff.mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, hx, tG x⟩
#align is_torsion.not_torsion_free IsTorsion.not_torsion_free
#align add_monoid.is_torsion.not_torsion_free AddMonoid.IsTorsion.not_torsion_free

/-- A nontrivial torsion-free group is not torsion. -/
@[to_additive AddMonoid.IsTorsionFree.not_torsion
      "A nontrivial torsion-free additive group is not torsion."]
theorem IsTorsionFree.not_torsion [hN : Nontrivial G] : IsTorsionFree G → ¬IsTorsion G := fun tfG =>
  (not_isTorsion_iff _).mpr <| by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, (tfG x) hx⟩
#align is_torsion_free.not_torsion IsTorsionFree.not_torsion
#align add_monoid.is_torsion_free.not_torsion AddMonoid.IsTorsionFree.not_torsion

/-- Subgroups of torsion-free groups are torsion-free. -/
@[to_additive "Subgroups of additive torsion-free groups are additively torsion-free."]
theorem IsTorsionFree.subgroup (tG : IsTorsionFree G) (H : Subgroup G) : IsTorsionFree H :=
  fun h hne ↦ Submonoid.isOfFinOrder_coe.not.1 <| tG h <| by norm_cast
#align is_torsion_free.subgroup IsTorsionFree.subgroup
#align is_torsion_free.add_subgroup IsTorsionFree.addSubgroup

/-- Direct products of torsion free groups are torsion free. -/
@[to_additive AddMonoid.IsTorsionFree.prod
      "Direct products of additive torsion free groups are torsion free."]
theorem IsTorsionFree.prod {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]
    (tfGs : ∀ i, IsTorsionFree (Gs i)) : IsTorsionFree <| ∀ i, Gs i := fun w hne h =>
  hne <|
    funext fun i => Classical.not_not.mp <| mt (tfGs i (w i)) <| Classical.not_not.mpr <| h.apply i
#align is_torsion_free.prod IsTorsionFree.prod
#align add_monoid.is_torsion_free.prod AddMonoid.IsTorsionFree.prod

end Group

section CommGroup

open Monoid (IsTorsionFree)

open CommGroup (torsion)

variable (G) [CommGroup G]

/-- Quotienting a group by its torsion subgroup yields a torsion free group. -/
@[to_additive AddIsTorsionFree.quotient_torsion
      "Quotienting a group by its additive torsion subgroup yields an additive torsion free group."]
theorem IsTorsionFree.quotient_torsion : IsTorsionFree <| G ⧸ torsion G := fun g hne hfin =>
  hne <| by
    induction' g using QuotientGroup.induction_on' with g
    obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
    obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
    exact
      (QuotientGroup.eq_one_iff g).mpr
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)
#align is_torsion_free.quotient_torsion IsTorsionFree.quotient_torsion
#align add_is_torsion_free.quotient_torsion AddIsTorsionFree.quotient_torsion

end CommGroup

lemma isTorsionFree_iff_noZeroSMulDivisors_nat {M : Type*} [AddMonoid M] :
    AddMonoid.IsTorsionFree M ↔ NoZeroSMulDivisors ℕ M := by
  simp_rw [AddMonoid.IsTorsionFree, isOfFinAddOrder_iff_nsmul_eq_zero, not_exists, not_and,
    pos_iff_ne_zero, noZeroSMulDivisors_iff, forall_swap (β := ℕ)]
  exact forall₂_congr fun _ _ ↦ by tauto

lemma isTorsionFree_iff_noZeroSMulDivisors_int [AddGroup G] :
    AddMonoid.IsTorsionFree G ↔ NoZeroSMulDivisors ℤ G := by
  simp_rw [AddMonoid.IsTorsionFree, isOfFinAddOrder_iff_zsmul_eq_zero, not_exists, not_and,
    noZeroSMulDivisors_iff, forall_swap (β := ℤ)]
  exact forall₂_congr fun _ _ ↦ by tauto

@[deprecated (since := "2024-02-29")]
alias AddMonoid.IsTorsionFree_iff_noZeroSMulDivisors := isTorsionFree_iff_noZeroSMulDivisors_int

lemma IsTorsionFree.of_noZeroSMulDivisors {M : Type*} [AddMonoid M] [NoZeroSMulDivisors ℕ M] :
    AddMonoid.IsTorsionFree M := isTorsionFree_iff_noZeroSMulDivisors_nat.2 ‹_›
