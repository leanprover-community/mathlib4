/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Rank
public import Mathlib.LinearAlgebra.Quotient.Defs

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

@[expose] public section


variable {G H : Type*}

section

variable (G) [Monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive
/-- A predicate on an additive monoid saying that all elements are of finite order. -/]
def IsMulTorsion :=
  ∀ g : G, IsOfFinOrder g

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion := IsMulTorsion
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion := IsAddTorsion

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp)
/-- An additive monoid is not a torsion additive monoid if it has an element of infinite order. -/]
theorem not_isMulTorsion_iff : ¬IsMulTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g :=
  not_forall

@[deprecated (since := "2026-07-01")] alias Monoid.not_isTorsion_iff := not_isMulTorsion_iff
@[deprecated (since := "2026-07-01")] alias AddMonoid.not_isTorsion_iff := not_isAddTorsion_iff

end

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive (attr := instance_reducible)
/-- Torsion additive monoids are really additive groups. -/]
noncomputable def IsMulTorsion.group [Monoid G] (tG : IsMulTorsion G) : Group G :=
  { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

@[deprecated (since := "2026-07-01")] alias IsTorsion.group := IsMulTorsion.group
@[deprecated (since := "2026-07-01")] alias IsTorsion.addGroup := IsAddTorsion.addGroup

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive /-- Additive subgroups of torsion additive groups are torsion additive groups. -/]
theorem IsMulTorsion.subgroup (tG : IsMulTorsion G) (H : Subgroup G) : IsMulTorsion H := fun h ↦
  Submonoid.isOfFinOrder_coe.1 <| tG h

@[deprecated (since := "2026-07-01")] alias IsTorsion.subgroup := IsMulTorsion.subgroup
@[deprecated (since := "2026-07-01")] alias IsTorsion.addSubgroup := IsAddTorsion.addSubgroup

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive
/-- The image of a surjective torsion additive group homomorphism is torsion. -/]
theorem IsMulTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsMulTorsion G) :
    IsMulTorsion H := fun h ↦ by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

@[deprecated (since := "2026-06-30")] alias IsTorsion.of_surjective := IsMulTorsion.of_surjective
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.of_surjective := IsAddTorsion.of_surjective

/-- Torsion groups are closed under extensions. -/
@[to_additive
/-- Torsion additive groups are closed under extensions. -/]
theorem IsMulTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsMulTorsion H)
    (tN : IsMulTorsion N) : IsMulTorsion G := fun g ↦ by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr <| ⟨ngn * nn, mul_pos ngnpos nnpos, by
    rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.extension_closed :=
  IsMulTorsion.extension_closed
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.extension_closed :=
  IsAddTorsion.extension_closed

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive
/-- The image of a quotient is torsion iff the additive group is torsion. -/]
theorem IsMulTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsMulTorsion N) : IsMulTorsion H ↔ IsMulTorsion G :=
  ⟨fun tH ↦ IsMulTorsion.extension_closed hN tH tN, fun tG ↦ IsMulTorsion.of_surjective hf tG⟩

@[deprecated (since := "2026-06-30")] alias IsTorsion.quotient_iff := IsMulTorsion.quotient_iff
@[deprecated (since := "2026-06-30")] alias AddIsTorsion.quotient_iff := IsAddTorsion.quotient_iff

/-- If a group exponent exists, the group is torsion. -/
@[to_additive
/-- If a group exponent exists, the additive group is torsion. -/]
theorem ExponentExists.isMulTorsion (h : ExponentExists G) : IsMulTorsion G := fun g ↦ by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

@[deprecated (since := "2026-06-30")] alias ExponentExists.isTorsion := ExponentExists.isMulTorsion
@[deprecated (since := "2026-06-30")] alias ExponentExists.is_add_torsion :=
  ExponentExists.isAddTorsion

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive
/-- The group exponent exists for any bounded torsion additive group. -/]
theorem IsMulTorsion.exponentExists (tG : IsMulTorsion G)
    (bounded : (Set.range fun g : G ↦ orderOf g).Finite) : ExponentExists G :=
  exponent_ne_zero.mp <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g ↦ (tG g).orderOf_pos).mpr bounded

@[deprecated (since := "2026-07-01")] alias IsTorsion.exponentExists := IsMulTorsion.exponentExists

/-- Finite groups are torsion groups. -/
@[to_additive /-- Finite additive groups are torsion additive groups. -/]
theorem isMulTorsion_of_finite [Finite G] : IsMulTorsion G :=
  ExponentExists.isMulTorsion .of_finite

@[deprecated (since := "2026-06-30")] alias isTorsion_of_finite := isMulTorsion_of_finite
@[deprecated (since := "2026-06-30")] alias is_add_torsion_of_finite := isAddTorsion_of_finite

end Group

section CommGroup
variable [CommGroup G]

/-- A nontrivial torsion abelian group is not torsion-free. -/
@[to_additive /-- A nontrivial torsion additive abelian group is not torsion-free. -/]
lemma not_isMulTorsionFree_of_isMulTorsion [Nontrivial G] (hG : IsMulTorsion G) :
    ¬ IsMulTorsionFree G :=
  not_isMulTorsionFree_iff_isOfFinOrder.2 <| let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

@[deprecated (since := "2026-07-01")] alias not_isMulTorsionFree_of_isTorsion :=
  not_isMulTorsionFree_of_isMulTorsion
@[deprecated (since := "2026-07-01")] alias not_isAddTorsionFree_of_isTorsion :=
  not_isAddTorsionFree_of_isAddTorsion

/-- A nontrivial torsion-free abelian group is not torsion. -/
@[to_additive /-- A nontrivial torsion-free additive abelian group is not torsion. -/]
lemma not_isMulTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] : ¬ IsMulTorsion G :=
  (not_isMulTorsionFree_of_isMulTorsion · ‹_›)

@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isMulTorsionFree :=
  not_isMulTorsion_of_isMulTorsionFree
@[deprecated (since := "2026-07-01")] alias not_isTorsion_of_isAddTorsionFree :=
  not_isAddTorsion_of_isAddTorsionFree

end CommGroup

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

/-- A module whose scalars are torsion is torsion. -/
theorem IsAddTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsAddTorsion R) :
    IsAddTorsion M :=
  fun f ↦ isOfFinAddOrder_iff_nsmul_eq_zero.mpr <| by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_torsion :=
  IsAddTorsion.module_of_torsion

/-- A module with a finite ring of scalars is torsion. -/
theorem IsAddTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsAddTorsion M :=
  (isAddTorsion_of_finite : IsAddTorsion R).module_of_torsion _ _

@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.module_of_finite :=
  IsAddTorsion.module_of_finite

end Module

section CommMonoid

variable (G) [CommMonoid G] [CommMonoid H]

namespace CommMonoid

/-- The torsion submonoid of a commutative monoid.

(Note that by `IsMulTorsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive addTorsion /-- The torsion additive submonoid of an additive commutative monoid. -/]
def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := IsOfFinOrder.one
  mul_mem' hx hy := hx.mul hy

@[to_additive]
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Submonoid.ext_iff, Submonoid.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable {G}

set_option backward.isDefEq.respectTransparency false in
/-- Torsion submonoids are torsion. -/
@[to_additive /-- Torsion additive submonoids are torsion. -/]
theorem torsion.isMulTorsion : IsMulTorsion <| torsion G := fun ⟨x, n, npos, hn⟩ ↦
  ⟨n, npos,
    Subtype.ext <| by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one, SubmonoidClass.coe_pow, Subtype.coe_mk,
        (isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

@[deprecated (since := "2026-07-01")] alias torsion.isTorsion := torsion.isMulTorsion
@[deprecated (since := "2026-07-01")] alias _root_.AddCommMonoid.addTorsion.isTorsion :=
  AddCommMonoid.addTorsion.isAddTorsion

variable (G) (p : ℕ)

/-- The `p`-primary component is the submonoid of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the submonoid of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
def primaryComponent : Submonoid G where
  carrier := { g | ∃ k : ℕ, g ^ p ^ k = 1 }
  one_mem' := ⟨0, by simp⟩
  mul_mem' := fun {a b} ⟨m, hm⟩ ⟨n, hn⟩ ↦ ⟨m + n, by
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, one_mul, mul_comm, pow_mul, hn, one_pow]⟩

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
theorem mem_primaryComponent {g : G} : g ∈ primaryComponent G p ↔ ∃ k : ℕ, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g ∈ primaryComponent G p ↔ ∃ n : ℕ, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

variable [hp : Fact p.Prime]

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive primaryComponent.exists_orderOf_eq_prime_nsmul
/-- Elements of the `p`-primary component have additive order `p^n` for some `n`. -/]
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by
  rw [← orderOf_submonoid, ← mem_primaryComponent_iff_orderOf]
  exact g.property

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive /-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/]
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr fun {g} hg hg' ↦ by
    rw [mem_primaryComponent_iff_orderOf] at hg hg'
    obtain ⟨_ | n, hn⟩ := hg
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    · obtain ⟨_, hn'⟩ := hg'
      exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn ▸ hn')) hne

end CommMonoid

open CommMonoid (torsion)

namespace IsMulTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp)
/-- The torsion additive submonoid of a torsion additive monoid is `⊤`. -/]
theorem torsion_eq_top (tG : IsMulTorsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive (attr := simps!)
/-- A torsion additive monoid is isomorphic to its torsion additive submonoid. -/]
def torsionMulEquiv (tG : IsMulTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv

end IsMulTorsion

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsion_eq_top :=
  IsMulTorsion.torsion_eq_top
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsion_eq_top :=
  IsAddTorsion.torsion_eq_top

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv :=
  IsMulTorsion.torsionMulEquiv
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv :=
  IsAddTorsion.torsionAddEquiv

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_apply :=
  IsMulTorsion.torsionMulEquiv_apply
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_apply :=
  IsAddTorsion.torsionAddEquiv_apply

@[deprecated (since := "2026-07-01")] alias Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe :=
  IsMulTorsion.torsionMulEquiv_symm_apply_coe
@[deprecated (since := "2026-07-01")] alias AddMonoid.IsTorsion.torsionAddEquiv_symm_apply_coe :=
  IsAddTorsion.torsionAddEquiv_symm_apply_coe

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[to_additive (attr := simp)
/-- Torsion additive submonoids of a torsion additive submonoid are
isomorphic to the additive submonoid. -/]
def CommMonoid.Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  IsMulTorsion.torsionMulEquiv CommMonoid.torsion.isMulTorsion

@[deprecated (since := "2026-07-01")] alias Torsion.ofTorsion := CommMonoid.Torsion.ofTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G] [CommGroup H]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive /-- The torsion additive subgroup of an additive abelian group. -/]
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx ↦ IsOfFinOrder.inv hx }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive
/-- The torsion additive submonoid of an abelian group equals the torsion
additive subgroup as an additive submonoid. -/]
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl

@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.add_torsion_eq_add_torsion_submonoid :=
  AddCommGroup.torsion_eq_torsion_addSubmonoid

variable {G}

@[to_additive]
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
lemma torsion_eq_top_iff : torsion G = ⊤ ↔ IsMulTorsion G :=
  (torsion G).eq_top_iff'

@[to_additive]
lemma isMulTorsionFree_iff_torsion_eq_bot : IsMulTorsionFree G ↔ CommGroup.torsion G = ⊥ := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder, eq_bot_iff, SetLike.le_def]
  simp [not_imp_not, CommGroup.mem_torsion]

@[to_additive]
lemma le_comap_torsion (f : G →* H) : torsion G ≤ (torsion H).comap f := by
  intro x
  exact f.isOfFinOrder

@[to_additive]
lemma map_torsion_le (f : G →* H) : (torsion G).map f ≤ torsion H :=
  Subgroup.map_le_iff_le_comap.mpr (le_comap_torsion f)

@[to_additive]
lemma comap_torsion_of_injective {f : G →* H} (hf : Function.Injective f) :
    (torsion H).comap f = torsion G := by
  ext x
  exact hf.isOfFinOrder_iff

@[to_additive]
lemma _root_.MulEquiv.comap_torsion (e : G ≃* H) : (torsion H).comap e = torsion G :=
  comap_torsion_of_injective e.injective

@[to_additive]
lemma _root_.MulEquiv.map_torsion (e : G ≃* H) : (torsion G).map e = torsion H := by
  rw [Subgroup.map_equiv_eq_comap_symm, e.symm.comap_torsion]

@[to_additive]
lemma torsion_prod : torsion (G × H) = (torsion G).prod (torsion H) := by
  simp [Subgroup.ext_iff, Subgroup.mem_prod, mem_torsion, IsOfFinOrder.prod_iff]

variable (G)

@[to_additive]
lemma isMulTorsion_quotient_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    IsMulTorsion (G ⧸ (powMonoidHom (α := G) n).range) := by
  simp only [IsMulTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g ↦ QuotientGroup.induction_on g fun a ↦ ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  simp

@[deprecated (since := "2026-07-01")] alias isTorsion_quotient_range_powMonoidHom :=
  isMulTorsion_quotient_range_powMonoidHom
@[deprecated (since := "2026-07-01")] alias
    _root_.AddCommGroup.isTorsion_quotient_range_nsmulAddMonoidHom :=
  AddCommGroup.isAddTorsion_quotient_range_nsmulAddMonoidHom

variable (p : ℕ)

/-- The `p`-primary component is the subgroup of elements `g` such that `g ^ p ^ k = 1`
for some `k`. For prime `p`, these are exactly the elements of `p`-power order. -/
@[to_additive
/-- The additive `p`-primary component is the subgroup of elements `g` such that
`p ^ k • g = 0` for some `k`. For prime `p`, these are exactly the elements of additive
`p`-power order. -/]
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun {g} ⟨k, hk⟩ ↦ ⟨k, by rw [inv_pow, hk, inv_one]⟩ }

variable {G} {p}

/-- `g` lies in the `p`-primary component iff `g ^ p ^ k = 1` for some `k`. -/
@[to_additive (attr := simp)
/-- `g` lies in the additive `p`-primary component iff `p ^ k • g = 0` for some `k`. -/]
theorem mem_primaryComponent {g : G} : g ∈ primaryComponent G p ↔ ∃ k : ℕ, g ^ p ^ k = 1 :=
  .rfl

/-- For prime `p`, `g` lies in the `p`-primary component iff its order is a power of `p`. -/
@[to_additive
/-- For prime `p`, `g` lies in the additive `p`-primary component iff its additive
order is a power of `p`. -/]
theorem mem_primaryComponent_iff_orderOf [Fact p.Prime] {g : G} :
    g ∈ primaryComponent G p ↔ ∃ n : ℕ, orderOf g = p ^ n :=
  exists_orderOf_eq_prime_pow_iff.symm

/-- The `p`-primary component is a `p`-group. -/
theorem primaryComponent.isPGroup : IsPGroup p (primaryComponent G p) := fun g ↦
  g.property.imp fun _ hk ↦ Subtype.ext <| by simpa using hk

variable (G H)

/-- The free rank of a finitely generated abelian group is the rank of its free part. -/
@[to_additive
/-- The free rank of a finitely generated abelian group is the rank of its free part. -/]
noncomputable def freeRank [Group.FG G] : ℕ := Group.rank (G ⧸ torsion G)

@[to_additive]
theorem freeRank_def [Group.FG G] : freeRank G = Group.rank (G ⧸ torsion G) := rfl

variable {G H}

@[to_additive]
theorem freeRank_eq_zero_iff [Group.FG G] : freeRank G = 0 ↔ IsMulTorsion G := by
  rw [freeRank, Group.rank_eq_zero_iff, QuotientGroup.subsingleton_iff, torsion_eq_top_iff]

@[to_additive]
theorem freeRank_eq_zero (hG : IsMulTorsion G) [Group.FG G] : freeRank G = 0 :=
  freeRank_eq_zero_iff.mpr hG

@[to_additive]
theorem freeRank_eq_zero_of_finite [Finite G] : freeRank G = 0 :=
  freeRank_eq_zero isMulTorsion_of_finite

@[to_additive]
theorem freeRank_congr [Group.FG G] [Group.FG H] (e : G ≃* H) : freeRank G = freeRank H :=
  Group.rank_congr (QuotientGroup.congr (torsion G) (torsion H) e e.map_torsion)

-- TODO: Prove monotonicity of `freeRank` along injective homomorphisms. This would require proving
-- monotonicity of `rank` along injective homomorphism of abelian groups.
@[to_additive]
theorem freeRank_ge_of_surjective [Group.FG G] [Group.FG H] (e : G →* H)
    (he : Function.Surjective e) : freeRank H ≤ freeRank G :=
  Group.rank_le_of_surjective _ <| QuotientGroup.map_surjective_of_surjective
    (torsion G) (torsion H) e (QuotientGroup.mk_surjective.comp he) (le_comap_torsion e)

end CommGroup

open CommGroup (torsion)

/-- Quotienting a group by its torsion subgroup yields a torsion-free group. -/
@[to_additive
/-- Quotienting an additive group by its torsion additive subgroup yields a torsion-free additive
group. -/]
instance _root_.QuotientGroup.instIsMulTorsionFree : IsMulTorsionFree <| G ⧸ torsion G := by
  refine .of_not_isOfFinOrder fun g hne hfin ↦ hne ?_
  obtain ⟨g⟩ := g
  obtain ⟨m, mpos, hm⟩ := hfin.exists_pow_eq_one
  obtain ⟨n, npos, hn⟩ := ((QuotientGroup.eq_one_iff _).mp hm).exists_pow_eq_one
  exact (QuotientGroup.eq_one_iff g).mpr
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)

end CommGroup

section AddCommGroup

instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] :
    Module R (M ⧸ AddCommGroup.torsion M) :=
  -- Upgrade the torsion subgroup to a submodule.
  letI S : Submodule R M := { AddCommGroup.torsion M with smul_mem' := fun r m ⟨n, hn, hn'⟩ ↦
    ⟨n, hn, by { simp only [Function.IsPeriodicPt, Function.IsFixedPt, add_left_iterate, add_zero,
      smul_comm n] at hn' ⊢; simp only [hn', smul_zero] }⟩ }
  -- The quotients are the same.
  let e : (M ⧸ AddCommGroup.torsion M) ≃+ (M ⧸ S) := QuotientAddGroup.congr _ _ (.refl _)
    (by simp [S])
  -- So we can copy over scalar multiplication.
  letI : SMul R (M ⧸ AddCommGroup.torsion M) := ⟨fun r m ↦ e.symm (r • e m)⟩
  Function.Injective.module R e.toAddMonoidHom e.injective (fun _ _ ↦
    e.symm.injective (e.symm_apply_apply _))

end AddCommGroup

section

variable {M : Type*} [CommMonoid M] [HasDistribNeg M]

theorem neg_one_mem_torsion : -1 ∈ CommMonoid.torsion M :=
  ⟨2, zero_lt_two, (isPeriodicPt_mul_iff_pow_eq_one _).mpr (by simp)⟩

end
