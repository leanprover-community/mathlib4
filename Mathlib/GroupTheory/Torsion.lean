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

namespace Monoid

variable (G) [Monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive
/-- A predicate on an additive monoid saying that all elements are of finite order. -/]
def IsTorsion :=
  ∀ g : G, IsOfFinOrder g

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[to_additive (attr := simp)
/-- An additive monoid is not a torsion monoid if it has an element of infinite order. -/]
theorem not_isTorsion_iff : ¬IsTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g :=
  not_forall

end Monoid

open Monoid

/-- Torsion monoids are really groups. -/
@[to_additive (attr := implicit_reducible)
/-- Torsion additive monoids are really additive groups -/]
noncomputable def IsTorsion.group [Monoid G] (tG : IsTorsion G) : Group G :=
  { ‹Monoid G› with
    inv g := g ^ (orderOf g - 1)
    inv_mul_cancel g := by
      rw [← pow_succ, tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact (tG g).orderOf_pos }

section Group

variable [Group G] {N : Subgroup G} [Group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive /-- Subgroups of additive torsion groups are additive torsion groups. -/]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h ↦
  Submonoid.isOfFinOrder_coe.1 <| tG h

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive AddIsTorsion.of_surjective
/-- The image of a surjective additive torsion group homomorphism is torsion. -/]
theorem IsTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsTorsion G) :
    IsTorsion H := fun h ↦ by
  obtain ⟨g, rfl⟩ := hf h
  exact f.isOfFinOrder (tG g)

/-- Torsion groups are closed under extensions. -/
@[to_additive AddIsTorsion.extension_closed
/-- Additive torsion groups are closed under extensions. -/]
theorem IsTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsTorsion H)
    (tN : IsTorsion N) : IsTorsion G := fun g ↦ by
  obtain ⟨ngn, ngnpos, hngn⟩ := (tH <| f g).exists_pow_eq_one
  have hmem := MonoidHom.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
  lift g ^ ngn to N using hN.symm ▸ hmem with gn h
  obtain ⟨nn, nnpos, hnn⟩ := (tN gn).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr <| ⟨ngn * nn, mul_pos ngnpos nnpos, by
    rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive AddIsTorsion.quotient_iff
/-- The image of a quotient is additively torsion iff the group is torsion. -/]
theorem IsTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsTorsion N) : IsTorsion H ↔ IsTorsion G :=
  ⟨fun tH ↦ IsTorsion.extension_closed hN tH tN, fun tG ↦ IsTorsion.of_surjective hf tG⟩

/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion
/-- If a group exponent exists, the group is additively torsion. -/]
theorem ExponentExists.isTorsion (h : ExponentExists G) : IsTorsion G := fun g ↦ by
  obtain ⟨n, npos, hn⟩ := h
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, npos, hn g⟩

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponentExists
/-- The group exponent exists for any bounded additive torsion group. -/]
theorem IsTorsion.exponentExists (tG : IsTorsion G)
    (bounded : (Set.range fun g : G ↦ orderOf g).Finite) : ExponentExists G :=
  exponent_ne_zero.mp <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g ↦ (tG g).orderOf_pos).mpr bounded

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_finite /-- Finite additive groups are additive torsion groups. -/]
theorem isTorsion_of_finite [Finite G] : IsTorsion G :=
  ExponentExists.isTorsion .of_finite

end Group

section CommGroup
variable [CommGroup G]

/-- A nontrivial torsion abelian group is not torsion-free. -/
@[to_additive /-- A nontrivial additive torsion abelian group is not torsion-free. -/]
lemma not_isMulTorsionFree_of_isTorsion [Nontrivial G] (hG : IsTorsion G) : ¬ IsMulTorsionFree G :=
  not_isMulTorsionFree_iff_isOfFinOrder.2 <| let ⟨x, hx⟩ := exists_ne (1 : G); ⟨x, hx, hG x⟩

/-- A nontrivial torsion-free abelian group is not torsion. -/
@[to_additive /-- A nontrivial additive torsion-free abelian group is not torsion. -/]
lemma not_isTorsion_of_isMulTorsionFree [Nontrivial G] [IsMulTorsionFree G] : ¬ IsTorsion G :=
  (not_isMulTorsionFree_of_isTorsion · ‹_›)

end CommGroup

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type*) [AddCommMonoid M]

namespace AddMonoid

/-- A module whose scalars are additively torsion is additively torsion. -/
theorem IsTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsTorsion R) : IsTorsion M :=
  fun f ↦ isOfFinAddOrder_iff_nsmul_eq_zero.mpr <| by
    obtain ⟨n, npos, hn⟩ := (tR 1).exists_nsmul_eq_zero
    exact ⟨n, npos, by simp only [← Nat.cast_smul_eq_nsmul R _ f, ← nsmul_one, hn, zero_smul]⟩

/-- A module with a finite ring of scalars is additively torsion. -/
theorem IsTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsTorsion M :=
  (is_add_torsion_of_finite : IsTorsion R).module_of_torsion _ _

end AddMonoid

end Module

section CommMonoid

variable (G) [CommMonoid G] [CommMonoid H]

namespace CommMonoid

/-- The torsion submonoid of a commutative monoid.

(Note that by `Monoid.IsTorsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive addTorsion /-- The torsion submonoid of an additive commutative monoid. -/]
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

/-- Torsion submonoids are torsion. -/
@[to_additive /-- Additive torsion submonoids are additively torsion. -/]
theorem torsion.isTorsion : IsTorsion <| torsion G := fun ⟨x, n, npos, hn⟩ ↦
  ⟨n, npos,
    Subtype.ext <| by
      dsimp
      rw [mul_left_iterate]
      change _ * 1 = 1
      rw [_root_.mul_one, SubmonoidClass.coe_pow, Subtype.coe_mk,
        (isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩

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

namespace Monoid.IsTorsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[to_additive (attr := simp)
/-- The additive torsion submonoid of an additive torsion monoid is `⊤`. -/]
theorem torsion_eq_top (tG : IsTorsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive /-- An additive torsion monoid is isomorphic to its torsion submonoid. -/]
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
/-- Additive torsion submonoids of an additive torsion submonoid are
isomorphic to the submonoid. -/]
def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoid.IsTorsion.torsionMulEquiv CommMonoid.torsion.isTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G] [CommGroup H]

namespace CommGroup

/-- The torsion subgroup of an abelian group. -/
@[to_additive /-- The torsion subgroup of an additive abelian group. -/]
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun hx ↦ IsOfFinOrder.inv hx }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
/-- The additive torsion submonoid of an abelian group equals the torsion
subgroup as a submonoid. -/]
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl

variable {G}

@[to_additive]
theorem mem_torsion (g : G) : g ∈ torsion G ↔ IsOfFinOrder g := Iff.rfl

@[to_additive]
lemma torsion_eq_top_iff : torsion G = ⊤ ↔ IsTorsion G :=
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
lemma isTorsion_quotient_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    Monoid.IsTorsion (G ⧸ (powMonoidHom (α := G) n).range) := by
  simp only [Monoid.IsTorsion, isOfFinOrder_iff_pow_eq_one]
  refine fun g ↦ QuotientGroup.induction_on g fun a ↦ ⟨n, hn.pos, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  simp

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
theorem freeRank_eq_zero_iff [Group.FG G] : freeRank G = 0 ↔ IsTorsion G := by
  rw [freeRank, Group.rank_eq_zero_iff, QuotientGroup.subsingleton_iff, torsion_eq_top_iff]

@[to_additive]
theorem freeRank_eq_zero (hG : IsTorsion G) [Group.FG G] : freeRank G = 0 :=
  freeRank_eq_zero_iff.mpr hG

@[to_additive]
theorem freeRank_eq_zero_of_finite [Finite G] : freeRank G = 0 :=
  freeRank_eq_zero isTorsion_of_finite

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
/-- Quotienting a group by its additive torsion subgroup yields an additive torsion-free group. -/]
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
