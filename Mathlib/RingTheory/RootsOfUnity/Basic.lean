/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.IntegralDomain
-- TODO: remove Mathlib.Algebra.CharP.Reduced and move the last two lemmas to Lemmas

/-!
# Roots of unity

We define roots of unity in the context of an arbitrary commutative monoid,
as a subgroup of the group of units.

## Main definitions

* `rootsOfUnity n M`, for `n : ℕ` is the subgroup of the units of a commutative monoid `M`
  consisting of elements `x` that satisfy `x ^ n = 1`.

## Main results

* `rootsOfUnity.isCyclic`: the roots of unity in an integral domain form a cyclic group.

## Implementation details

It is desirable that `rootsOfUnity` is a subgroup,
and it will mainly be applied to rings (e.g. the ring of integers in a number field) and fields.
We therefore implement it as a subgroup of the units of a commutative monoid.

We have chosen to define `rootsOfUnity n` for `n : ℕ` and add a `[NeZero n]` typeclass
assumption when we need `n` to be non-zero (which is the case for most interesting statements).
Note that `rootsOfUnity 0 M` is the top subgroup of `Mˣ` (as the condition `ζ^0 = 1` is
satisfied for all units).
-/

noncomputable section

open Polynomial

open Finset

variable {M N G R S F : Type*}
variable [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]

section rootsOfUnity

variable {k l : ℕ}

/-- `rootsOfUnity k M` is the subgroup of elements `m : Mˣ` that satisfy `m ^ k = 1`. -/
def rootsOfUnity (k : ℕ) (M : Type*) [CommMonoid M] : Subgroup Mˣ where
  carrier := {ζ | ζ ^ k = 1}
  one_mem' := one_pow _
  mul_mem' _ _ := by simp_all only [Set.mem_setOf_eq, mul_pow, one_mul]
  inv_mem' _ := by simp_all only [Set.mem_setOf_eq, inv_pow, inv_one]

@[simp]
theorem mem_rootsOfUnity (k : ℕ) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ ζ ^ k = 1 :=
  Iff.rfl

/-- A variant of `mem_rootsOfUnity` using `ζ : Mˣ`. -/
theorem mem_rootsOfUnity' (k : ℕ) (ζ : Mˣ) : ζ ∈ rootsOfUnity k M ↔ (ζ : M) ^ k = 1 := by
  rw [mem_rootsOfUnity]; norm_cast

@[simp]
theorem rootsOfUnity_one (M : Type*) [CommMonoid M] : rootsOfUnity 1 M = ⊥ := by
  ext1
  simp only [mem_rootsOfUnity, pow_one, Subgroup.mem_bot]

@[simp]
lemma rootsOfUnity_zero (M : Type*) [CommMonoid M] : rootsOfUnity 0 M = ⊤ := by
  ext1
  simp only [mem_rootsOfUnity, pow_zero, Subgroup.mem_top]

theorem rootsOfUnity.coe_injective {n : ℕ} :
    Function.Injective (fun x : rootsOfUnity n M ↦ x.val.val) :=
  Units.val_injective.comp Subtype.val_injective

/-- Make an element of `rootsOfUnity` from a member of the base ring, and a proof that it has
a positive power equal to one. -/
@[simps! coe_val]
def rootsOfUnity.mkOfPowEq (ζ : M) {n : ℕ} [NeZero n] (h : ζ ^ n = 1) : rootsOfUnity n M :=
  ⟨Units.ofPowEqOne ζ n h <| NeZero.ne n, Units.pow_ofPowEqOne _ _⟩

@[simp]
theorem rootsOfUnity.coe_mkOfPowEq {ζ : M} {n : ℕ} [NeZero n] (h : ζ ^ n = 1) :
    ((rootsOfUnity.mkOfPowEq _ h : Mˣ) : M) = ζ :=
  rfl

theorem rootsOfUnity_le_of_dvd (h : k ∣ l) : rootsOfUnity k M ≤ rootsOfUnity l M := by
  obtain ⟨d, rfl⟩ := h
  intro ζ h
  simp_all only [mem_rootsOfUnity, pow_mul, one_pow]

theorem map_rootsOfUnity (f : Mˣ →* Nˣ) (k : ℕ) : (rootsOfUnity k M).map f ≤ rootsOfUnity k N := by
  rintro _ ⟨ζ, h, rfl⟩
  simp_all only [← map_pow, mem_rootsOfUnity, SetLike.mem_coe, MonoidHom.map_one]

@[norm_cast]
theorem rootsOfUnity.coe_pow [CommMonoid R] (ζ : rootsOfUnity k R) (m : ℕ) :
    (((ζ ^ m :) : Rˣ) : R) = ((ζ : Rˣ) : R) ^ m := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

/-- The canonical isomorphism from the `n`th roots of unity in `Mˣ`
to the `n`th roots of unity in `M`. -/
def rootsOfUnityUnitsMulEquiv (M : Type*) [CommMonoid M] (n : ℕ) :
    rootsOfUnity n Mˣ ≃* rootsOfUnity n M where
  toFun ζ := ⟨ζ.val, (mem_rootsOfUnity ..).mpr <| (mem_rootsOfUnity' ..).mp ζ.prop⟩
  invFun ζ := ⟨toUnits ζ.val, by
    simp only [mem_rootsOfUnity, ← map_pow, EmbeddingLike.map_eq_one_iff]
    exact (mem_rootsOfUnity ..).mp ζ.prop⟩
  left_inv ζ := by simp only [toUnits_val_apply, Subtype.coe_eta]
  right_inv ζ := by simp only [val_toUnits_apply, Subtype.coe_eta]
  map_mul' ζ ζ' := by simp only [Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk]

section CommMonoid

variable [CommMonoid R] [CommMonoid S] [FunLike F R S]

/-- Restrict a ring homomorphism to the nth roots of unity. -/
def restrictRootsOfUnity [MonoidHomClass F R S] (σ : F) (n : ℕ) :
    rootsOfUnity n R →* rootsOfUnity n S :=
  { toFun := fun ξ ↦ ⟨Units.map σ (ξ : Rˣ), by
      rw [mem_rootsOfUnity, ← map_pow, Units.ext_iff, Units.coe_map, ξ.prop]
      exact map_one σ⟩
    map_one' := by ext1; simp only [OneMemClass.coe_one, map_one]
    map_mul' := fun ξ₁ ξ₂ ↦ by
      ext1; simp only [Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk] }

@[simp]
theorem restrictRootsOfUnity_coe_apply [MonoidHomClass F R S] (σ : F) (ζ : rootsOfUnity k R) :
    (restrictRootsOfUnity σ k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

/-- Restrict a monoid isomorphism to the nth roots of unity. -/
nonrec def MulEquiv.restrictRootsOfUnity (σ : R ≃* S) (n : ℕ) :
    rootsOfUnity n R ≃* rootsOfUnity n S where
  toFun := restrictRootsOfUnity σ n
  invFun := restrictRootsOfUnity σ.symm n
  left_inv ξ := by ext; exact σ.symm_apply_apply _
  right_inv ξ := by ext; exact σ.apply_symm_apply _
  map_mul' := (restrictRootsOfUnity _ n).map_mul

@[simp]
theorem MulEquiv.restrictRootsOfUnity_coe_apply (σ : R ≃* S) (ζ : rootsOfUnity k R) :
    (σ.restrictRootsOfUnity k ζ : Sˣ) = σ (ζ : Rˣ) :=
  rfl

@[simp]
theorem MulEquiv.restrictRootsOfUnity_symm (σ : R ≃* S) :
    (σ.restrictRootsOfUnity k).symm = σ.symm.restrictRootsOfUnity k :=
  rfl

end CommMonoid

section IsDomain

-- The following results need `k` to be nonzero.
variable [NeZero k] [CommRing R] [IsDomain R]

theorem mem_rootsOfUnity_iff_mem_nthRoots {ζ : Rˣ} :
    ζ ∈ rootsOfUnity k R ↔ (ζ : R) ∈ nthRoots k (1 : R) := by
  simp only [mem_rootsOfUnity, mem_nthRoots (NeZero.pos k), Units.ext_iff, Units.val_one,
    Units.val_pow_eq_pow_val]

variable (k R)

/-- Equivalence between the `k`-th roots of unity in `R` and the `k`-th roots of `1`.

This is implemented as equivalence of subtypes,
because `rootsOfUnity` is a subgroup of the group of units,
whereas `nthRoots` is a multiset. -/
def rootsOfUnityEquivNthRoots : rootsOfUnity k R ≃ { x // x ∈ nthRoots k (1 : R) } where
  toFun x := ⟨(x : Rˣ), mem_rootsOfUnity_iff_mem_nthRoots.mp x.2⟩
  invFun x := by
    refine ⟨⟨x, ↑x ^ (k - 1 : ℕ), ?_, ?_⟩, ?_⟩
    all_goals
      rcases x with ⟨x, hx⟩; rw [mem_nthRoots <| NeZero.pos k] at hx
      simp only [← pow_succ, ← pow_succ', hx, tsub_add_cancel_of_le NeZero.one_le]
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, hx, Units.val_one]

variable {k R}

@[simp]
theorem rootsOfUnityEquivNthRoots_apply (x : rootsOfUnity k R) :
    (rootsOfUnityEquivNthRoots R k x : R) = ((x : Rˣ) : R) :=
  rfl

@[simp]
theorem rootsOfUnityEquivNthRoots_symm_apply (x : { x // x ∈ nthRoots k (1 : R) }) :
    (((rootsOfUnityEquivNthRoots R k).symm x : Rˣ) : R) = (x : R) :=
  rfl

variable (k R)

instance rootsOfUnity.fintype : Fintype (rootsOfUnity k R) := by
  classical
  exact Fintype.ofEquiv { x // x ∈ nthRoots k (1 : R) } (rootsOfUnityEquivNthRoots R k).symm

instance rootsOfUnity.isCyclic : IsCyclic (rootsOfUnity k R) :=
  isCyclic_of_subgroup_isDomain ((Units.coeHom R).comp (rootsOfUnity k R).subtype) coe_injective

theorem card_rootsOfUnity : Fintype.card (rootsOfUnity k R) ≤ k := by
  classical
  calc
    Fintype.card (rootsOfUnity k R) = Fintype.card { x // x ∈ nthRoots k (1 : R) } :=
      Fintype.card_congr (rootsOfUnityEquivNthRoots R k)
    _ ≤ Multiset.card (nthRoots k (1 : R)).attach := Multiset.card_le_card (Multiset.dedup_le _)
    _ = Multiset.card (nthRoots k (1 : R)) := Multiset.card_attach
    _ ≤ k := card_nthRoots k 1

variable {k R}

theorem map_rootsOfUnity_eq_pow_self [FunLike F R R] [MonoidHomClass F R R] (σ : F)
    (ζ : rootsOfUnity k R) :
    ∃ m : ℕ, σ (ζ : Rˣ) = ((ζ : Rˣ) : R) ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (restrictRootsOfUnity σ k)
  rw [← restrictRootsOfUnity_coe_apply, hm, ← zpow_mod_orderOf, ← Int.toNat_of_nonneg
      (m.emod_nonneg (Int.natCast_ne_zero.mpr (pos_iff_ne_zero.mp (orderOf_pos ζ)))),
    zpow_natCast, rootsOfUnity.coe_pow]
  exact ⟨(m % orderOf ζ).toNat, rfl⟩

end IsDomain

section Reduced

variable (R) [CommRing R] [IsReduced R]

-- @[simp] -- Porting note: simp normal form is `mem_rootsOfUnity_prime_pow_mul_iff'`
theorem mem_rootsOfUnity_prime_pow_mul_iff (p k : ℕ) (m : ℕ) [ExpChar R p] {ζ : Rˣ} :
    ζ ∈ rootsOfUnity (p ^ k * m) R ↔ ζ ∈ rootsOfUnity m R := by
  simp only [mem_rootsOfUnity', ExpChar.pow_prime_pow_mul_eq_one_iff]

/-- A variant of `mem_rootsOfUnity_prime_pow_mul_iff` in terms of `ζ ^ _` -/
@[simp]
theorem mem_rootsOfUnity_prime_pow_mul_iff' (p k : ℕ) (m : ℕ) [ExpChar R p] {ζ : Rˣ} :
    ζ ^ (p ^ k * m) = 1 ↔ ζ ∈ rootsOfUnity m R := by
  rw [← mem_rootsOfUnity, mem_rootsOfUnity_prime_pow_mul_iff]

end Reduced

end rootsOfUnity

section cyclic

namespace IsCyclic

/-- The isomorphism from the group of group homomorphisms from a finite cyclic group `G` of order
`n` into another group `G'` to the group of `n`th roots of unity in `G'` determined by a generator
`g` of `G`. It sends `φ : G →* G'` to `φ g`. -/
noncomputable
def monoidHomMulEquivRootsOfUnityOfGenerator {G : Type*} [CommGroup G] {g : G}
    (hg : ∀ (x : G), x ∈ Subgroup.zpowers g) (G' : Type*) [CommGroup G'] :
    (G →* G') ≃* rootsOfUnity (Nat.card G) G' where
  toFun φ := ⟨(IsUnit.map φ <| Group.isUnit g).unit, by
    simp only [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      ← map_pow, pow_card_eq_one', map_one, Units.val_one]⟩
  invFun ζ := monoidHomOfForallMemZpowers hg (g' := (ζ.val : G')) <| by
    simpa only [orderOf_eq_card_of_forall_mem_zpowers hg, orderOf_dvd_iff_pow_eq_one,
      ← Units.val_pow_eq_pow_val, Units.val_eq_one] using ζ.prop
  left_inv φ := (MonoidHom.eq_iff_eq_on_generator hg _ φ).mpr <| by
    simp only [IsUnit.unit_spec, monoidHomOfForallMemZpowers_apply_gen]
  right_inv φ := Subtype.ext <| by
    simp only [monoidHomOfForallMemZpowers_apply_gen, IsUnit.unit_of_val_units]
  map_mul' x y := by
    simp only [MonoidHom.mul_apply, MulMemClass.mk_mul_mk, Subtype.mk.injEq, Units.ext_iff,
      IsUnit.unit_spec, Units.val_mul]

/-- The group of group homomorphisms from a finite cyclic group `G` of order `n` into another
group `G'` is (noncanonically) isomorphic to the group of `n`th roots of unity in `G'`. -/
lemma monoidHom_mulEquiv_rootsOfUnity (G : Type*) [CommGroup G] [IsCyclic G]
    (G' : Type*) [CommGroup G'] :
    Nonempty <| (G →* G') ≃* rootsOfUnity (Nat.card G) G' := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨monoidHomMulEquivRootsOfUnityOfGenerator hg G'⟩

end IsCyclic

end cyclic
