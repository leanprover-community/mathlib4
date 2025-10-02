/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Commutative monoids with enough roots of unity

We define a typeclass `HasEnoughRootsOfUnity M n` for a commutative monoid `M` and
a natural number `n` that asserts that `M` contains a primitive `n`th root of unity
and that the group of `n`th roots of unity in `M` is cyclic. Such monoids are suitable
targets for homomorphisms from groups of exponent (dividing) `n`; for example,
the homomorphisms can then be used to separate elements of the source group.
-/

/-- This is a type class recording that a commutative monoid `M` contains primitive `n`th
roots of unity and such that the group of `n`th roots of unity is cyclic.

Such monoids are suitable targets in the context of duality statements for groups
of exponent `n`. -/
class HasEnoughRootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) where
  prim : ∃ m : M, IsPrimitiveRoot m n
  cyc : IsCyclic <| rootsOfUnity n M

namespace HasEnoughRootsOfUnity

lemma exists_primitiveRoot (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    ∃ ζ : M, IsPrimitiveRoot ζ n :=
  HasEnoughRootsOfUnity.prim

instance rootsOfUnity_isCyclic (M : Type*) [CommMonoid M] (n : ℕ) [HasEnoughRootsOfUnity M n] :
    IsCyclic (rootsOfUnity n M) :=
  HasEnoughRootsOfUnity.cyc

/-- If `HasEnoughRootsOfUnity M n` and `m ∣ n`, then also `HasEnoughRootsOfUnity M m`. -/
lemma of_dvd (M : Type*) [CommMonoid M] {m n : ℕ} [NeZero n] (hmn : m ∣ n)
    [HasEnoughRootsOfUnity M n] :
    HasEnoughRootsOfUnity M m where
  prim :=
    have ⟨ζ, hζ⟩ := exists_primitiveRoot M n
    have ⟨k, hk⟩ := hmn
    ⟨ζ ^ k, IsPrimitiveRoot.pow (NeZero.pos n) hζ (mul_comm m k ▸ hk)⟩
  cyc := Subgroup.isCyclic_of_le <| rootsOfUnity_le_of_dvd hmn

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` is finite. -/
instance finite_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Finite <| rootsOfUnity n M := by
  have := rootsOfUnity_isCyclic M n
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n M)
  have hg' : g ^ n = 1 := OneMemClass.coe_eq_one.mp g.prop
  let f (j : ZMod n) : rootsOfUnity n M := g ^ (j.val : ℤ)
  refine Finite.of_surjective f fun x ↦ ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp <| hg x
  refine ⟨k, ?_⟩
  simpa only [ZMod.natCast_val, ← hk, f, ZMod.coe_intCast] using (zpow_eq_zpow_emod' k hg').symm

/-- If `M` satisfies `HasEnoughRootsOfUnity`, then the group of `n`th roots of unity
in `M` (is cyclic and) has order `n`. -/
lemma natCard_rootsOfUnity (M : Type*) [CommMonoid M] (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity M n] :
    Nat.card (rootsOfUnity n M) = n := by
  obtain ⟨ζ, h⟩ := exists_primitiveRoot M n
  rw [← IsCyclic.exponent_eq_card]
  refine dvd_antisymm ?_ ?_
  · exact Monoid.exponent_dvd_of_forall_pow_eq_one fun g ↦ OneMemClass.coe_eq_one.mp g.prop
  · nth_rewrite 1 [h.eq_orderOf]
    rw [← (h.isUnit <| NeZero.pos n).unit_spec, orderOf_units]
    let ζ' : rootsOfUnity n M := ⟨(h.isUnit <| NeZero.pos n).unit, ?_⟩
    · rw [← Subgroup.orderOf_mk]
      exact Monoid.order_dvd_exponent ζ'
    simp only [mem_rootsOfUnity]
    rw [← Units.val_inj, Units.val_pow_eq_pow_val, IsUnit.unit_spec, h.pow_eq_one, Units.val_one]

lemma of_card_le {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n]
    (h : n ≤ Fintype.card (rootsOfUnity n R)) : HasEnoughRootsOfUnity R n where
  prim := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp (le_antisymm (card_rootsOfUnity R n) h)
  cyc := rootsOfUnity.isCyclic R n

end HasEnoughRootsOfUnity

lemma MulEquiv.hasEnoughRootsOfUnity {n : ℕ} [NeZero n] {M N : Type*} [CommMonoid M]
    [CommMonoid N] [hm : HasEnoughRootsOfUnity M n] (e : rootsOfUnity n M ≃* rootsOfUnity n N) :
    HasEnoughRootsOfUnity N n where
  prim := by
    obtain ⟨m, hm⟩ := hm.prim
    use (e hm.toRootsOfUnity).val.val
    rw [IsPrimitiveRoot.coe_units_iff, IsPrimitiveRoot.coe_submonoidClass_iff]
    refine .map_of_injective ?_ e.injective
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, ← IsPrimitiveRoot.coe_units_iff]
  cyc := isCyclic_of_surjective e e.surjective

section cyclic

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into the
group of units of a ring `M` with all roots of unity is isomorphic to `G` -/
lemma IsCyclic.monoidHom_equiv_self (G M : Type*) [CommGroup G] [Finite G]
    [IsCyclic G] [CommMonoid M] [HasEnoughRootsOfUnity M (Nat.card G)] :
    Nonempty ((G →* Mˣ) ≃* G) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hord := HasEnoughRootsOfUnity.natCard_rootsOfUnity M (Nat.card G)
  let e := (IsCyclic.monoidHom_mulEquiv_rootsOfUnity G Mˣ).some
  exact ⟨e.trans (rootsOfUnityUnitsMulEquiv M (Nat.card G)) |>.trans (mulEquivOfCyclicCardEq hord)⟩

end cyclic

instance {M : Type*} [CommMonoid M] : HasEnoughRootsOfUnity M 1 where
  prim := ⟨1, by simp⟩
  cyc := isCyclic_of_subsingleton
